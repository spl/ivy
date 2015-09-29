(*
 *
 * Copyright (c) 2001-2006, 
 *  Matt Harren        <matth@cs.berkeley.edu>
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

open Cil
open Pretty
open Dutil
open Dattrs

module E = Errormsg
module IH = Inthash
module H = Hashtbl

module N = Ptrnode

(* similar to examineType, but for listGlobalAnnotations instead of
   printGlobalAnnotations. *)
let rec examineNode (where: string) (t:typ): unit =
  let reportNodeDoc (what:doc): unit =
    warn "Type \"%a\" in %s %a" dx_type t where insert what
  in
  let reportNode (what:string): unit =
    reportNodeDoc (text what)
  in
  match unrollType t with
    TVoid _
  | TBuiltin_va_list _
  | TInt _
  | TFloat _
  | TEnum _ -> ()

  | TPtr (bt, a)
  | TArray (bt, _, a) when hasAttribute "trusted" a ->
      ()

  | TPtr (bt, a) ->
      examineNode where bt;
      let k, _ = N.inferredKindOf a in
      let needsBounds =
        N.kindNeedsBounds k &&
        not (hasAttribute "bounds" a) &&
        not (hasAttribute "size" a)
      in
      let needsNT =
        N.kindIsNullterm k &&
        not (hasAttribute "nullterm" a)
      in
      begin
        match needsBounds, needsNT with
        | _, true -> reportNode "should be annotated NT."
        | true, false -> reportNode "needs a bound annotation."
        | false, false -> ()
      end
  | TArray (bt, lo, a) ->
      examineNode where bt;
      let k, _ = N.inferredKindOf a in
      if N.kindIsNullterm k && not (hasAttribute "nullterm" a) then
        reportNode "should be annotated NT.";
      if isOpenArray t && not (hasAttribute "bounds" a) then begin
        reportNode "contains an open array."
      end
  | TFun (rt, args, isva, a) ->
      examineNode "<function pointer return type>" rt;
      List.iter (fun (n, t, _) -> 
                   examineNode ("<function pointer formal "^n^">") t) 
        (argsToList args)
  | TComp _ -> () (* We visit these separately. *)
  | TNamed _ -> E.s (bug "unrollType")


let reportNeededAnnotations (f: file) : unit =
  let oldPCI = !print_CIL_Input in
  print_CIL_Input := true;
  
  let totKind : (N.opointerkind, int ref) H.t = H.create 17 in
  let totalNodes : int ref = ref 0 in
  (* Collect stats on the kinds of every local or cast that might
     need inferred bounds *)
  let visitLocalOrCast (t:typ): unit =
    match unrollType t with
      TPtr(_,a) ->
        incr totalNodes;
        let k,_ = N.inferredKindOf a in
        N.addToHisto totKind 1 k
    | _ -> ()
  in
  let visitAllCasts (fd: fundec) : unit =
    let castVisitor = object (self) 
      inherit nopCilVisitor
      method vexpr e =
        (match e with
           CastE(t, _) -> visitLocalOrCast t
         | _ -> ());
        DoChildren
    end
    in
    ignore(visitCilBlock castVisitor fd.sbody)
  in

  (* Maintain a map from globals to the location of their first declaration.
     If a var has no location (probably because it's Poly), use the 
     location of it's declaration.  *)
  let declarations: location IH.t = IH.create 50 in
  let setLoc vi: unit =
    if !currentLoc == locUnknown then begin
      if IH.mem declarations vi.vid then
        currentLoc := IH.find declarations vi.vid
    end else
      if not (IH.mem declarations vi.vid) then
        IH.add declarations vi.vid !currentLoc
  in
  let globalsVisited: unit IH.t = IH.create 50 in
  let doGlobal g: unit =
    match g with
      GVarDecl (vi, l)
        when Dattrs.isTrustedType vi.vtype 
          || Dattrs.isSpecialFunction vi.vtype    ->
        ()
    | GVarDecl (vi, l) when isFunctionType vi.vtype 
        && not (IH.mem globalsVisited vi.vid) ->
        currentLoc := l;
        setLoc vi;
          let rt, formals, _, _ = splitFunctionType vi.vtype in
          examineNode ("the return value of "^vi.vname) rt;
          List.iter (fun (n,t,_) -> 
                       examineNode ("formal \""^n^"\" of "^vi.vname) t)
            (argsToList formals);
        IH.add globalsVisited vi.vid ()

    | GFun (fdec, l)
        when Dattrs.isTrustedType fdec.svar.vtype 
          || Dattrs.isSpecialFunction fdec.svar.vtype    ->
        ()
    | GFun (fdec, l) ->
        currentLoc := l;
        setLoc fdec.svar;
        if not (IH.mem globalsVisited fdec.svar.vid) then begin
          (* Examine the prototype, since we haven't already seen a
             declaration of this func: *)
          IH.add globalsVisited fdec.svar.vid ();
          let rt, formals, _, _ = splitFunctionType fdec.svar.vtype in
          examineNode ("the return value of "^fdec.svar.vname) rt;
          List.iter (fun vi -> examineNode 
                       ("formal \""^vi.vname^"\" of "^fdec.svar.vname)
                       vi.vtype)
            fdec.sformals;
        end;
        (* Regardless of whether we've seen an earlier declaration, examine
           locals and casts. *)
        (* Locals are mostly covered by inference.  But base types of
           pointers may need annotating. *)
        List.iter (fun vi -> 
                     match unrollType vi.vtype with 
                       TPtr (bt, a) as t-> 
                         visitLocalOrCast t;
                         let descr =
                            if vi.vdescr <> nil then
                                sprint ~width:80 vi.vdescr
                            else vi.vname
                         in
                         examineNode ("local \""^descr^"\"") bt
                         (*examineNode ("local \""^vi.vname^"\"") bt*)
                     | TArray (bt, _, a) -> 
                         visitLocalOrCast bt;
                         let descr =
                            if vi.vdescr <> nil then
                                sprint ~width:80 vi.vdescr
                            else vi.vname
                         in
                         examineNode ("local \""^descr^"\"") bt
                         (*examineNode ("local \""^vi.vname^"\"") bt*)
                     | _ -> ())
          fdec.slocals;
        visitAllCasts fdec

    | GVarDecl (vi, l)
    | GVar (vi, _, l) when not (IH.mem globalsVisited vi.vid) ->
        currentLoc := l;
        setLoc vi;
        IH.add globalsVisited vi.vid ();
        examineNode ("global \""^vi.vname^"\"") vi.vtype
    | GCompTag (ci, l) ->
        currentLoc := l;
        List.iter
          (fun fi -> examineNode ("field \""^fi.fname^"\"") fi.ftype)
          ci.cfields
    | _ -> ()
  in
  iterGlobals f doGlobal;
  print_CIL_Input := oldPCI;
  ()

(* The entry point from Deputy.  Calls Markptr, Solver *)
let inferKinds (f: file) : file = 
  if f.globinit <> None then
    (* CCured has special handling of globinit, but we can't use that
       strategy because main may not be in this file. *)
    ignore (E.warn "Inference: skipping global initializers.");

  let marked = Stats.time "markptr" Markptr.markFile f in

  begin
    try
      Stats.time "solver" (Solver.solve marked) Ptrnode.idNode
    with _ ->
      ()
  end;

  reportNeededAnnotations marked;

  marked
