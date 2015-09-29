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

open Cil
open Pretty
open Dattrs
open Ivyoptions
open Dutil

module E = Errormsg
module IH = Inthash
module VS = Usedef.VS
module DF = Dataflow

(* Liveness analysis for local vars.
 *
 * This has two uses:
 *  1) Any local that's live at the start of the func is used without being initialized.
 *     This is a warning/error.
 *  2) We'll say that variables are only in scope once if they're live.
 *     This reduces the number of variables in the context, and it fixes issues
 *     such as small/locals1 that are caused by CIL moving all locals to the same scope.
 * 
 * A variable is live if
 *  a) it is live in the usual sense, or
 *  b) a live variable depends on it.
 *)


(* A map from variables to the list of variables that the first
 * variable depends on. This is closed under transitivity,
 * but it excludes self-dependencies. *)
let dependsOn: VS.t IH.t = IH.create 40

(* Update a variable set "start" based on the variables defined and used
 * by the current instruction. Ensures that the result is closed w.r.t.
 * the dependsOn relation. *)
let handleDefUse (start: VS.t) (def: VS.t) (use: VS.t): VS.t =
  let addDeps (v:varinfo) (acc: VS.t): VS.t = 
    VS.union (IH.find dependsOn v.vid) acc
  in
  (* Subtract anything in the Def set. Note that acc is no longer closed! *)
  let acc = VS.diff start def in
  (* Add anything that was Used. *)
  let acc = VS.union use acc in
  (* Add anything that the Def set depends on, because we'll need these
   * to check the assignment. *)
  let acc = VS.fold addDeps def acc in
  (* Finally, make sure acc is closed. *)
  let acc = VS.fold addDeps acc acc in
  acc
                    
  
(* The variables that are live at the start of each stmt of this function.
   This is always closed under dependsOn. *)
let liveAtStart: VS.t IH.t = IH.create 50

(* This is copied from liveness.ml, with some extra Deputy magic. *)
module LiveFlow = struct
  let name = "Liveness"
  let debug = ref false
  type t = VS.t

  let pretty () vs =
    (VS.fold
       (fun vi d -> 
          d ++ text "name: " ++ text vi.vname
	  ++ text " id: " ++ num vi.vid ++ text " ")
       vs nil) ++ line

  let stmtStartData = liveAtStart

  let funcExitData = VS.empty

  let combineStmtStartData (stm:stmt) ~(old:t) (now:t) =
    if not(VS.compare old now = 0)
    then Some(VS.union old now)
    else None

  let combineSuccessors = VS.union

  let doStmt stmt =
    if !debug then log "looking at: %a" d_stmt stmt;
    let handle_stm vs = match stmt.skind with
	Instr _ -> vs
      | s -> let u, d = Usedef.computeUseDefStmtKind s in
	handleDefUse vs d u
    in
    DF.Post handle_stm

  let doInstr i vs =
    let transform vs' =
      let u,d = Usedef.computeUseDefInstr i in
      handleDefUse vs' d u
    in
    DF.Post transform

  let filterStmt stm1 stm2 = true

end

module L = DF.BackwardsDataFlow(LiveFlow)


(* What variables does a local depend on? *)
let varDepsOfType (localsList: varinfo list) (t: typ) : VS.t =
  let deps = depsOfType t in
  if deps = [] then VS.empty
  else begin
    List.fold_left 
      (fun acc v ->
         if List.mem v.vname deps then VS.add v acc
         else acc)
      VS.empty
      localsList
  end

(* Finds the (transitive) dependencies of a variable, and adds them to acc *)
let getDepsOf (localsList: varinfo list) (v:varinfo): VS.t =
  let rec helper (v:varinfo) (acc: VS.t): VS.t =
    let deps = varDepsOfType localsList v.vtype in
    let newvars = VS.diff deps acc in
    (* Add in deps *)
    let acc = VS.union acc newvars in
    (* And add in any vars that those vars depend on. *)
    VS.fold helper newvars acc
  in
  let deps = helper v VS.empty in
  (* Finally, remove any self-dependency. *)
  VS.remove v deps


let extraUsesOfExpr (localsList: varinfo list) : (exp -> VS.t) = 
  function
      (* If a cast has an annotation that refers to locals,
         add those locals to the USE set *)
      CastE(t, _) -> varDepsOfType localsList t
    | _ -> VS.empty
 

(* Check for "memset(&v,_,sizeof(v))".
   This is a definition of v, not a use. *)
let interceptMemset (func:exp) (args: exp list):  VS.t * VS.t * exp list =
  (* the default response:  process the args as normal. *)
  let default = (VS.empty, VS.empty, args) in
  if isMemset (typeOf func) then begin
    match args with
    | [(AddrOf lv1 | StartOf lv1); e2; e3] 
        when (isCorrectSizeOf e3 lv1) -> begin
          (* We're memsetting the entire lval.  Consider this a def. *)
          match lv1 with
            Var vi, NoOffset when not vi.vglob -> 
              VS.empty,        (* no extra uses *)
              VS.singleton vi, (* consider vi to be defined *)
              [e2;e3]          (* process the last two args as usual *)
          | _ -> 
              default
        end
    | _ -> default
  end
  else
    default

(**** Set some hooks for Usedef: ****)

let setHooks (f:fundec) : unit = 
  (* Exclude globals: *)
  let notGlobal (v:varinfo): bool = not v.vglob in
  Usedef.considerVariableUse := notGlobal;
  Usedef.considerVariableDef := notGlobal;
  Usedef.considerVariableAddrOfAsUse := notGlobal;
    
  Usedef.onlyNoOffsetsAreDefs := true;
  
  Usedef.extraUsesOfExpr := extraUsesOfExpr (f.sformals @ f.slocals);
  Usedef.getUseDefFunctionRef := interceptMemset;
  ()

let unsetHooks () : unit = 
  Usedef.considerVariableUse := (fun v -> true);
  Usedef.considerVariableDef := (fun v -> true);
  Usedef.considerVariableAddrOfAsUse := (fun v -> true);
  Usedef.onlyNoOffsetsAreDefs := false;
  Usedef.extraUsesOfExpr := (fun e -> VS.empty);
  Usedef.getUseDefFunctionRef := (fun f args -> (VS.empty, VS.empty, args));
  ()



(***************************************************************)


(* Initialize locals to 0, if needed. Some of this initialization may be
   wrong (e.g. initializing NONNULL values), but we should catch that later
   during type checking.*)
let rec initLval (lv: lval) (t: typ) (acc: instr list) : instr list = 
  let t = unrollType t in  
  match t with 
    TInt _ | TEnum _ | TFloat _ | TVoid _ -> acc
  | TBuiltin_va_list _ -> 
      if !Ivyoptions.warnVararg then
        warn "Vararg variables not handled.";
      acc
  | TPtr _ -> Set(lv, zero, !currentLoc) :: acc
  | TArray (bt, _, a) when typeContainsPtrOrNullterm bt -> 
      (* for arrays whose elements contain pointers or nullterminated 
       * arrays, we just memset the whole thing *)
      Call(None, Lval (var memset),
           [mkAddrOrStartOf lv; zero; SizeOf t],
           !currentLoc)::acc
  | TArray(_, sz, a) when hasAttribute "nullterm" a -> 
      (* For arrays whose elements have no pointers, but that are 
       * nullterminated, we just write the last element *)
      let szn = 
        match sz with 
          Some sz -> sz
        | _ -> E.s (unimp "Cannot initialize local null-terminated array with no size")
      in
      Set(addOffsetLval (Index(increm szn (-1), NoOffset)) lv, 
          zero, !currentLoc) :: acc
        
  | TArray _ -> acc
      
  | TComp (comp, _) when not (typeContainsPtrOrNullterm t) -> acc
      
  (* For performance it would be better to go over structs field by
     field, but these assignments might be in the wrong order w.r.t
     dependencies.  We should either move this until after dcheck, or
     replace the memset with individual assignments during
     optimization. *)
(*   | TComp(comp, _) when comp.cstruct ->  *)
(*       List.fold_left *)
(*       (fun acc f ->  *)
(*          initLval (addOffsetLval (Field(f, NoOffset)) lv) *)
(*          f.ftype *)
(*          acc) *)
(*       acc *)
(*       comp.cfields *)

  | TComp (comp, _) -> 
      (* Zero it all *)
      Call(None, Lval (var memset),
           [mkAddrOf lv; zero; SizeOf t],
           !currentLoc)::acc
      
  | TNamed _ -> assert false
  | TFun _ -> assert false


let initOneVar (funcLoc: location) (vi: varinfo) (acc: instr list): instr list
  =
  currentLoc := if vi.vdecl == locUnknown then funcLoc else vi.vdecl;
  
  (* First, report warnings or errors for this var.  Then call initLval *)
  if vi.vaddrof then
    (* It's common to take the address of an uninitialized variable
       and pass it somewhere to be initialized.  Don't warn about this,
       just fix it. *)
    ()
  else begin 
    match unrollType vi.vtype with 
    | TInt _ | TEnum _ | TFloat _ -> 
        (* a scalar is used without being defined.  Give a warning. *)
        warn "Variable %s may be used without being defined." vi.vname
    | TPtr _ ->
        (* a pointer is used without being defined. *)
        (* Should we add a command-line flag that makes this a warning? *)
        error "Pointer variable %s may be used without being defined." vi.vname
    | TBuiltin_va_list _ -> () (* we warn about this in initLval *)
    | TComp (comp, _) when not comp.cstruct -> 
        warn ("Union \"%s\" may be used without being defined.  Therefore, we "
              ^^"also treat its tags as being used before definition.")
          vi.vname

    | TArray _ | TComp _ -> 
        (* Don't warn, because we're not good at deciding when
           compound structures have been initialized. *)
        ()
    | TNamed _ | TFun _ | TVoid _ -> 
        E.s (bug "bad type for local %s: %a" vi.vname dx_type vi.vtype)
  end;
  initLval (var vi) vi.vtype acc

let initVars (func: fundec) : unit =
  let savedLoc = !currentLoc in
  let firstStmt: stmt =
    match func.sbody.bstmts with
      s::rest -> s
    | [] -> E.s (bug "function has no body")
  in
  (* Are any vars live on input? These need initialization,
     unless they're formals. *)
  let vars = IH.find liveAtStart firstStmt.sid in
  if !verbose then
    log "%s: Live on input: %a\n" func.svar.vname
      (docList (fun vi -> text vi.vname)) (VS.elements vars);
  let locals = VS.filter 
                 (fun vi -> not (List.memq vi func.sformals)) 
                 vars in
  let init: instr list =
    VS.fold (initOneVar savedLoc) locals []
  in
  currentLoc := savedLoc;
  (* Now add init to the function body. *)
  match firstStmt.skind with
    (* The first statement should be an instr statement.
       Modify the first statement in place, so that we don't have to
       recompute the CFG. *)
    Instr il -> 
      let il' = Util.list_append init il in
      firstStmt.skind <- Instr il'
  | _ -> 
      E.s (bug "The first statement of %s should have been an Instr."
             func.svar.vname)


(***  This interface is exported to Dcheck:    ******************)

let doLiveness (f:fundec) : unit = 
  assert ((IH.length liveAtStart) = 0);
  assert ((IH.length dependsOn) = 0);
  let savedLoc = !currentLoc in
  setHooks f;
  let localsList = f.sformals @ f.slocals in
  List.iter (fun v -> IH.add dependsOn v.vid (getDepsOf localsList v))
    localsList;
  
  let all_stmts, _ = DF.find_stmts f in
  List.iter (fun s -> 
               IH.add liveAtStart s.sid VS.empty) all_stmts;
  L.compute all_stmts;
  currentLoc := savedLoc;

  unsetHooks ();

  initVars f;
  ()


let clearLiveness () : unit =
  IH.clear liveAtStart;
  IH.clear dependsOn;
  ()

let liveAtStmtStart (s:stmt): VS.t =
  IH.find liveAtStart s.sid

(* What variables does this local depend on? *)
let localDependsOn (v:varinfo): VS.t =
  IH.find dependsOn v.vid
