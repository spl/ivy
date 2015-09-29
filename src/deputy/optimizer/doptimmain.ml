(*
 *
 * Copyright (c) 2004, 
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

(*
 *
 * doptimmain.ml
 *
 * This is the interface of the optimizer exposed to Deputy proper.
 *
 *)

open Cil
open Pretty
open Ivyoptions
open Dutil
open Dcheckdef

module E = Errormsg
module AE = Availexps
module AELV = Availexpslv
module RCT = Rmciltmps
module S = Stats

(* optimizer modules *)
module DFI = Dflowinsens
module DFS = Dflowsens
module DSA = Dfwdsubst
module DDE = Ddupcelim
module DLO = Dloopoptim
module DCS = Dcheckstrengthen
module DOU = Doptimutil
module DCH = Dcheckhoister
module DOA = Doctanalysis
module DPF = Dprecfinder

(* Determine some properties of the remaining checks *)
class localFinderClass (fd : fundec) br = object(self)
  inherit nopCilVisitor

  method vvrbl vi =
    let isFormal vi =
      List.exists (fun vi' -> vi'.vid = vi.vid)
	fd.sformals
    in
    if not vi.vglob && not (isFormal vi) then br := true;
    DoChildren

end

class globFormFinderClass (fd : fundec) br = object(self)
  inherit nopCilVisitor

  method vvrbl vi =
    if vi.vglob then br := true;
    DoChildren

end

(* returns true if e only refers to globals. *)
let expOnlyGlobalsAndFormals fd e =
  let br = ref false in
  let vis = new localFinderClass fd br in
  ignore(visitCilExpr vis e);
  not !br

let expHasGlobOrForm fd e =
  let br = ref false in
  let vis = new globFormFinderClass fd br in
  ignore(visitCilExpr vis e);
  !br

class checkPropsClass ogcr hgcr = object(self)
  inherit nopCilVisitor

  val mutable curFunc = None

  method vinst i =
    match instrToCheck i with
    | None -> DoChildren
    | Some c -> begin
	match curFunc with
	| Some fd -> begin
	    let f = expOnlyGlobalsAndFormals fd in
	    if (DOU.test_check ~comb:(fun a b -> a && b) f c) then
	      ogcr := !ogcr + 1;
	    if (DOU.test_check (expHasGlobOrForm fd) c) then
	      hgcr := !hgcr + 1;
	    DoChildren
	end
	| None -> DoChildren
    end

  method vfunc f =
    curFunc <- (Some f);
    DoChildren

end

let numGlobalChecks (f : file) =
  let ogcount = ref 0 in
  let hgcount = ref 0 in
  let vis = new checkPropsClass ogcount hgcount in
  ignore(visitCilFile vis f);
  !ogcount, !hgcount

class checkCounterClass (cr : int ref) = object(self)
    inherit nopCilVisitor
    
    method vinst i =
        match instrToCheck i with
        | None -> DoChildren
        | Some _ -> begin
            incr cr;
            DoChildren
        end
end

let countChecks (fd : fundec) : int =
    let cr = ref 0  in
    let vis = new checkCounterClass cr in
    ignore(visitCilFunction vis fd);
    !cr

let recomputeCfg (fd:fundec) : unit =
  Cfg.clearCFGinfo fd;
  ignore (Cfg.cfgFun fd)

let optLevel1 (fd:fundec) : unit =
  if !verbose then
    log "Doing flow-insensitive optimizations.\n";
  recomputeCfg fd;
  ignore (visitCilFunction (DFI.optimizeVisitor()) fd);
  ignore (visitCilFunction DCS.checkStrengthener fd);
  recomputeCfg fd

let optLevel2 (fd:fundec) (fdat: DPF.functionData) : unit =
  if !verbose then
    log "Doing some flow-sensitive optimizations.\n";
  recomputeCfg fd;
  ignore (visitCilFunction (DFI.optimizeVisitor()) fd);
  DFS.doFlowAnalysis fd fdat;
  ignore (visitCilFunction (DFI.optimizeVisitor()) fd);
  ignore (visitCilFunction DCS.checkStrengthener fd);
  recomputeCfg fd


let optLevel3 (fd:fundec) (fdat : DPF.functionData) : unit =
  if !verbose then
    log "Doing one pass of all optimizations:\n";
  recomputeCfg fd;
  let cf = constFoldVisitor false in
  AE.registerIgnoreInst is_check_instr;
  AE.registerIgnoreCall is_deputy_instr;
  AE.registerIgnoreCall isLibcNoSideEffects;
  AELV.registerIgnoreInst is_check_instr;
  AELV.registerIgnoreCall is_deputy_instr;
  AELV.registerIgnoreCall isLibcNoSideEffects;
  DFS.registerIgnoreCall is_deputy_instr;
  DFS.registerIgnoreCall isLibcNoSideEffects;
  DCH.registerIgnoreCall isLibcNoSideEffects;
  Deadcodeelim.callHasNoSideEffects := is_deputy_fun;

  if !verbose then
    log "\tflow-insensitive opts\n";
  ignore (S.time "flow-insensitive" 
    (visitCilFunction (DFI.optimizeVisitor ~supErr:true ())) fd);

  if !verbose then
    log "\tmatt's opts\n";
  S.time "matts" (DFS.doFlowAnalysis fd) fdat;

  DPF.addChecksAtCallSites fd fdat;
  recomputeCfg fd;
  if !verbose then
    log "\tdup-check-elim\n";
  S.time "dup-check-elim" (DDE.elim_dup_checks fd) fdat;

  if !verbose then
    log "\tcheck-merge\n";
  ignore(S.time "check-merge"
	 (visitCilFunction DCS.checkStrengthener) fd);

  if !findNonNull || !findPreconditions then begin
    recomputeCfg fd;
    S.time "check-hoist" (DCH.hoistChecks fd) fdat
  end;

  (*recomputeCfg fd;
  if !verbose then
    log "\tdce\n";
  ignore(S.time "dce" Deadcodeelim.elim_dead_code fd);*)

  recomputeCfg fd;
  if !verbose then
    log "\tsymbol-eval\n";
  S.time "symbol-eval" DSA.forwardTmpSub fd;
  ignore(S.time "constant-fold" (visitCilFunction cf) fd);

  (* doFlowAnalysis *must* come before the optimizeVisitor
     after fwd subst, const prop, and const folding *)
  recomputeCfg fd;
  if !verbose then
    log "\tmatt's opts\n";
  S.time "matts" (DFS.doFlowAnalysis ~tryReverse:true fd) fdat;

  if !verbose then
    log "\tflow-insensitive opts\n";
  ignore(S.time "flow-insensitive"
	   (visitCilFunction (DFI.optimizeVisitor())) fd);
  if !verbose then
    log "\tcheck-merge\n";
  ignore(S.time "check-merge"
	   (visitCilFunction DCS.checkStrengthener) fd);

  recomputeCfg fd;
  if !verbose then
    log "\tdup-check-elim\n";
  S.time "dup-check-elim" (DDE.elim_dup_checks fd) fdat;

  if !verbose then
    log "\tloopcheck\n";
  recomputeCfg fd;
  S.time "loopcheck" DLO.loopInvCheckMover fd;

  if !findNonNull || !findPreconditions then begin
    recomputeCfg fd;
    S.time "check-hoist" (DCH.hoistChecks fd) fdat;

    recomputeCfg fd;
    S.time "symbol-eval" DSA.forwardTmpSub fd;
    ignore(S.time "constant-fold" (visitCilFunction cf) fd);
    recomputeCfg fd;
    S.time "check-hoist" (DCH.hoistChecks fd) fdat;

    recomputeCfg fd;
    S.time "symbol-eval" DSA.forwardTmpSub fd;
    ignore(S.time "constant-fold" (visitCilFunction cf) fd);
    recomputeCfg fd;
    S.time "check-hoist" (DCH.hoistChecks fd) fdat;
  end;
  recomputeCfg fd



let optLevel4 (fd: fundec) (fdat : DPF.functionData) : unit =
  if (not DOA.real) || !findNonNull || !findPreconditions 
  then optLevel3 fd fdat else begin
  recomputeCfg fd;
  let cf = constFoldVisitor false in
  AE.registerIgnoreInst is_check_instr;
  AE.registerIgnoreCall is_deputy_instr;
  AE.registerIgnoreCall isLibcNoSideEffects;
  AELV.registerIgnoreInst is_check_instr;
  AELV.registerIgnoreCall is_deputy_instr;
  AELV.registerIgnoreCall isLibcNoSideEffects;
  DFS.registerIgnoreCall is_deputy_instr;
  DFS.registerIgnoreCall isLibcNoSideEffects;
  DOA.registerIgnoreCall is_deputy_instr;
  DOA.registerIgnoreCall isLibcNoSideEffects;
  Deadcodeelim.callHasNoSideEffects := is_deputy_fun;


  (*if fd.svar.vname <> "__deputy_global_initializers" then
    ignore(E.log "PreFIChecks %d\n" (countChecks fd));*)
  (*ignore (E.log "flow-insensitive\n");*)
  ignore (S.time "flow-insensitive"
	    (visitCilFunction (DFI.optimizeVisitor ~supErr:true ())) fd);
  (*if fd.svar.vname <> "__deputy_global_initializers" then
      ignore(E.log "PostFIChecks %d\n" (countChecks fd));*)

  (*ignore(E.log "matts\n");*)
  S.time "matts" (DFS.doFlowAnalysis fd) fdat;

  DPF.addChecksAtCallSites fd fdat;
  recomputeCfg fd;
  (*ignore (E.log "dup-check-elim\n");*)
  S.time "dup-check-elim" (DDE.elim_dup_checks fd) fdat;
  (*ignore (E.log "check-merge\n");*)
  ignore(S.time "check-merge"
	   (visitCilFunction DCS.checkStrengthener) fd);

  (*recomputeCfg fd;
  (*ignore (E.log "dce\n");*)
  ignore(S.time "dce" Deadcodeelim.elim_dead_code fd);*)

  recomputeCfg fd;
  (*ignore (E.log "symbol-eval\n");*)
  S.time "symbol-eval" DSA.forwardTmpSub fd;
  (*ignore (E.log "constant-fold\n");*)
  ignore(S.time "constant-fold" (visitCilFunction cf) fd);

  (*ignore (E.log "matts\n");*)
  S.time "matts" (DFS.doFlowAnalysis ~tryReverse:true fd) fdat;
  (*ignore (E.log "flow-insensitive\n");*)
  ignore(S.time "flow-insensitive"
	   (visitCilFunction (DFI.optimizeVisitor())) fd);

  (*ignore(E.log "check-merge\n");*)
  ignore(S.time "check-merge"
	   (visitCilFunction DCS.checkStrengthener) fd);

  recomputeCfg fd;
  (*ignore(E.log "loopcheck\n");*)
  S.time "loopcheck" DLO.loopInvCheckMover fd;

  recomputeCfg fd;
  (*ignore(E.log "oct-analysis\n");*)
  S.time "oct-analysis" (DOA.doOctAnalysis fd) fdat;
  DOA.reportStats();
  
  (*ignore(E.log "dup-check-elim\n");*)
  S.time "dup-check-elim" (DDE.elim_dup_checks fd) fdat
  end;
  recomputeCfg fd

let deadCodeElim (f:file) : unit =
  Cfg.clearFileCFG f; 
  Cfg.computeFileCFG f;
  S.time "dce" Deadcodeelim.dce f;
  List.iter
    (fun g ->
       match g with
       | GFun (fd, _) -> begin
	   RCT.rm_unused_locals fd
       end
       | _ -> ())
    f.globals;
  Cfg.clearFileCFG f;
  ()

class attributeSorterClass = object(self)
    inherit nopCilVisitor

    method private sortAttrs attrs = List.sort compare attrs

    method vvrbl (vi : varinfo) =
        vi.vattr <- self#sortAttrs vi.vattr;
        DoChildren

    method vblock (b : block) =
        b.battrs <- self#sortAttrs b.battrs;
        DoChildren

    method vglob (g : global) =
        match g with
        | GCompTag(ci, _)
        | GCompTagDecl(ci, _) ->
            ci.cattr <- self#sortAttrs ci.cattr;
            List.iter (fun fi -> fi.fattr <- self#sortAttrs fi.fattr) ci.cfields;
            DoChildren
        | GEnumTag(ei, _)
        | GEnumTagDecl(ei, _) ->
            ei.eattr <- self#sortAttrs ei.eattr;
            DoChildren
        | _ -> DoChildren

    method vtype (t : typ) =
        let sortTypeAttrs t =
            setTypeAttrs t (self#sortAttrs (typeAttrs t))
        in
        ChangeDoChildrenPost(sortTypeAttrs t, sortTypeAttrs)

end

let sortAttributes (f : file) : unit =
    visitCilFile (new attributeSorterClass) f

let optimFunction (fd: fundec) (l: location) (fdat : DPF.functionData) =
  currentLoc := l;
  if !optLevel = 1 then
    Stats.time "optimizations" optLevel1 fd
  else if !optLevel = 2 then
    Stats.time "optimizations" (optLevel2 fd) fdat
  else if !optLevel = 3 then
    Stats.time "optimizations" (optLevel3 fd) fdat
  else if !optLevel = 4 then
    Stats.time "optimizations" (optLevel4 fd) fdat



