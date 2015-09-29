(*
 *
 * Copyright (c) 2006,
 *  Jeremy Condit       <jcondit@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)


module C = Cil
module E = Errormsg

open Ivyutil

let init () : unit =
  (* Make TRUSTED an attribute of types, not names.
   * (This is just for the sake of uniformity) *)
  Hashtbl.add C.attributeHash "trusted" C.AttrType;

  (* Tell cabs2cil to strip dependent attributes from the types of
   * temporaries that it creates and casts that it inserts. Also tell
   * it to alpha-rename Deputy attributes when merging function types. *)
  Cabs2cil.typeForTypeof := Dutil.stripDepsFromType;
  Cabs2cil.typeForInsertedVar := Dutil.stripDepsFromType;
  Cabs2cil.typeForInsertedCast := Dutil.stripDepsFromType;
  Cabs2cil.typeForCombinedArg := Dpatch.patchAttrParamsInType;
  Cabs2cil.attrsForCombinedArg := Dpatch.patchAttrParamsInAttrs;
;;

let root (f: C.file) : C.global -> bool = Dattrs.treatAsRoot f

let preprocess (cil: C.file) : unit =
  List.iter (Dpatch.applyPatch cil) !Ivyoptions.patches;
  if !Ivyoptions.noDeputy then () else begin

      (* If there is no precondition patch file, then make one *)
      if !Ivyoptions.propPreconditions && 
         not(Dprecfinder.applyPrecPatch cil) then begin
        Ivyoptions.findPreconditions := true;
        Ivyoptions.propPreconditions := false
      end;

      if !E.hadErrors then
        E.s (E.error "Cabs2cil had some errors");

      printFile ~extraPrinting:None ~globinit:None cil !Ivyoptions.parseFile;

      Dinfer.preProcessFile cil
  end

let process (cil: C.file) : C.file = 
  (* "marked" is the original file plus NODE() annotations. *)
  if !Ivyoptions.noDeputy then begin
    Cil.visitCilFile Dinfer.postPassVisitor cil;
    cil
  end else begin
  let marked = 
    if !Ivyoptions.inferKinds then
      Stats.time "Interprocedural inference" Inferkinds.inferKinds cil
    else
      cil
  in

  Dinfer.preProcessFileAfterMarking marked;
  (* Now insert the function with the global initializers. Does not insert 
   * it in the file. *)
  let globinit = Dglobinit.prepareGlobalInitializers marked in

  let extraprint = 
    if !Ivyoptions.inferKinds && !Ivyoptions.emitGraphDetailLevel >= 0 then
      Some Ptrnode.printInferGraph
    else
      None
  in
  printFile ~extraPrinting:extraprint 
	    ~globinit:(Some globinit) marked !Ivyoptions.inferFile;

  (* See if we should make use of Preconditions annotations *)
  let fdat : Dprecfinder.functionData =
      if !Ivyoptions.propPreconditions then begin
	  ignore(E.log "Extracting preconditions from annotations\n");
	  let fdat = Dprecfinder.mkFDat() in
	  Dprecfinder.extractPrecsFromAnnots fdat marked;
	  Dmodref.extractModAnnotations fdat marked;
	  fdat
      end else Dprecfinder.mkFDat() (* empty *)
  in

  (* alias analysis *)
  if !Ivyoptions.doPtrAnalysis then begin
      Ptranal.callHasNoSideEffects := Dcheckdef.lvNoSideEffects;
      Stats.time "Pointer analysis" Ptranal.analyze_file marked;
      Stats.time "Pointer analysis" Ptranal.compute_results false
  end;

  (* Initialize the octagon analysis. Revert to level 3 if
   * it's broken. *)
  if !Ivyoptions.optLevel = 4 then
    if not(Doctanalysis.init()) then
      Ivyoptions.optLevel := 3;

  if !Ivyoptions.findPreconditions then begin
      Cfg.clearFileCFG marked;
      Cfg.computeFileCFG marked;
      ignore(Dprecfinder.applyPrecPatch marked); (* for deputy added funs *)
      Dmodref.extractModAnnotations fdat marked;
      Dmodref.registerIgnoreInst Dcheckdef.is_check_instr;
      Dmodref.registerIgnoreCall Dcheckdef.is_deputy_instr;
      Dmodref.registerIgnoreCall Dcheckdef.isLibcNoSideEffects;
      Dmodref.addAllModifications fdat marked;
      Cfg.clearFileCFG marked
  end;

  Dcheck.checkFile marked globinit fdat;

  (* Now do the global initializer *)
  let residualChecks: bool =
    Dglobinit.checkGlobinit marked globinit
      (fun gi -> Dcheck.checkFundec gi)
      (fun gi l -> 
	   Doptimmain.optimFunction gi l fdat;
	   ignore (C.visitCilBlock Dinfer.postPassVisitor gi.C.sbody)) in

  if residualChecks then
    marked.C.globals <- marked.C.globals @ [C.GFun (globinit, C.locUnknown)];

  Dinfer.postProcessFile marked;

  (*let ogchecks, hgchecks = Doptimmain.numGlobalChecks marked in
    E.log("GlobalChecks: %d %d\n") ogchecks hgchecks;*)

  if !Ivyoptions.findNonNull then begin
      Cfg.clearFileCFG marked;
      Cfg.computeFileCFG marked;
      Dnonnullfinder.addNonNullAnnotations fdat marked;
      Dprecfinder.addAnnotsToPatch fdat "nonnull.patch.h";
      Cil.visitCilFile Dinfer.postPassVisitor marked
  end;

  if !Ivyoptions.findPreconditions then begin
      Cfg.clearFileCFG marked;
      Cfg.computeFileCFG marked;
      Dprecfinder.extractPrecsFromAnnots fdat marked;
      Dprecfinder.addAllPreconditions fdat marked;
      let pfn = (Filename.chop_extension marked.Cil.fileName)^".patch.h" in
      Dprecfinder.addAnnotsToPatch fdat pfn;
      Cil.visitCilFile Dinfer.postPassVisitor marked
  end;

  if !Ivyoptions.htmlOutDir <> "" then begin
      Dfdatbrowser.genPageForFile marked fdat
  end;

  if !Ivyoptions.instrument then begin
      Dinstrumenter.instrumentFile marked;
      Cil.visitCilFile Dinfer.postPassVisitor marked
  end;

  if !Ivyoptions.taintflow then begin
      Dtaint.calcTaintFile marked;
      Cil.visitCilFile Dinfer.postPassVisitor marked
  end;

  (* zra: I'm not sure where they're getting unsorted, so I'll just fix the
     problem right before the invarients are checked *)
  if !Ivyoptions.checkCilInvariants && not !E.hadErrors then
      Doptimmain.sortAttributes marked;

  if !Ivyoptions.checkCilInvariants && not !E.hadErrors then begin
    let ignoreInstr i =
      Dcheckdef.is_deputy_instr i ||
	(match i with
	  C.Call (_,f,_,_) when Dattrs.isSpecialFunction (C.typeOf f) -> true
	| _ -> false) ||
      Dinstrumenter.isInstrFun i
    in
    if not(Check.checkFile
	      [Check.IgnoreInstructions ignoreInstr] marked) then
      E.s (Dutil.bug "Check.checkFile failed after optimizations\n");
  end;

  marked
  end

let postprocess (f : Cil.file) : unit = Dinfer.removeDeputyAttributes f

let cleanup () = 
  if !Ivyoptions.countTrustedLines && not !E.hadErrors then
    Dutil.reportTrustedLines ();
  let optTime = Stats.lookupTime "optimizations" in
  if optTime >= 20.0 && !Ivyoptions.optLevel > 1 then
    E.log("\nNote: Optimizations took %.1f s.  For faster (but less precise)"
	  ^^" analysis, you can use a lower optimization level.\n\n")
      optTime;

  Dutil.outputAll ();
;;

