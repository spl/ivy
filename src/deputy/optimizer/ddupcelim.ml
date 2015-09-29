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
 * ddupcelim.ml
 *
 * A flow sensitive analysis that removes duplicate checks.
 *
 * XXX: This pass might be obviated by other passes.
 *
 *)

open Cil
open Pretty
open Dutil
open Dcheckdef
open Doptimutil
open Ivyoptions

module E = Errormsg
module IH = Inthash
module UD = Usedef
module AELV = Availexpslv
module DF = Dataflow
module S = Stats

module P = Dptranal
module DPF = Dprecfinder

(* For turning on debugging in just this file *)
(*let debug = ref true*)

(**********************************
 * Flow-sensitive optimizer for
 * removing duplicate checks across
 * multiple statements
 **********************************)

(* do two lists contain the same checks *)
let il_equals il1 il2 =
  if not(List.length il1 = List.length il2)
  then false
  else List.fold_left (fun b i1 ->
    b && List.exists (fun i2 ->
      deputyCallsEqual i1 i2) 
      il2) 
      true il1

(* return the intersection of two lists
 * of checks *)
let il_combine il1 il2 =
  List.filter (fun i1 ->
    List.exists (fun i2 ->
      deputyCallsEqual i1 i2) il2) il1

(* add new checks from chks to cl *)
(* instr list -> instr list -> instr list *)
let il_add il newil =
  List.fold_left (fun il' i ->
    if not(List.exists (fun i' ->
      deputyCallsEqual i i') il')
    then i::il' else il')
    il newil

let il_pretty () il = 
  line ++ seq line (fun i ->
    (d_instr () i)) il

(* see if f returns true on an
 * expression in the list *)
let expListTest f el =
  List.fold_left (fun b e ->
    b || (f e))
    false el

(* if f is true on an instruction
 * then filter it out of the list *)
let ilKiller f il =
  List.filter (fun i ->
    match instrToCheck i with
      Some c ->
	not(test_check f c)
    | None -> match i with
	Call(_,_,el,_) ->
	  not(expListTest f el)
      | _ -> true)
    il

(* filter out checks having memory reads *)
let il_kill_mem il eo =
  if !debug then ignore(E.log "VBCFlow: Killing memory reads\n");
  if !doPtrAnalysis then
    match eo with
    | Some ee ->
        ilKiller (P.exp_has_alias_read ee) il
    | None ->
        ilKiller AELV.exp_has_mem_read il  
  else
    ilKiller AELV.exp_has_mem_read il

(* filter out checks refering to vi *)
let il_kill_vi il vi =
  ilKiller (AELV.exp_has_vi vi) il

(* filter out checks refering to lv *)
let il_kill_lval il lv =
  ilKiller (AELV.exp_has_lval lv) il

let il_handle_inst i il = 
  if is_check_instr i then il else
  match i with
    Set((Mem ee, _),_,_) ->
      il_kill_mem il (Some ee)
  | Set((Var vi, NoOffset),e,_) ->
      (match e with
	Lval(Var vi', NoOffset) ->
	  if vi'.vid = vi.vid then il else
	  il_kill_vi il vi
      | _ -> il_kill_vi il vi)
  | Set(lv,_,_) -> il_kill_lval il lv
  | Call(Some(Var vi, NoOffset),_,_,_) ->
      let il' = il_kill_vi il vi in
      if is_deputy_instr i then il' else
      il_kill_mem il' None
  | Call(_,_,_,_) ->
      il_kill_mem il None
  | Asm(_,_,_,_,_,_) ->
      let _, d = UD.computeUseDefInstr i in
      UD.VS.fold (fun vi il' ->
	il_kill_vi il' vi) d il

module AvailChecks =
  struct

    let name = "Available Checks"

    let debug = debug

    (* list of checks that are available *)
    type t = instr list

    let copy il = il

    let stmtStartData = IH.create 64

    let pretty = il_pretty

    let computeFirstPredecessor stm il = il

    let combinePredecessors (stm:stmt) ~(old:t) (il:t) =
      if il_equals old il then None else
      Some(il_combine old il)

    let doInstr i il =
      let action il =
        match instrToCheck i with
        | Some _ -> il_add il [i]
        | None -> 
	    if is_deputy_instr i
	    then il_add il [i]
	    else il_handle_inst i il
      in
      DF.Post action

    let doStmt stm il = 
      (*if !debug then ignore(E.log "AvailChecks: looking at stmt %d %a\n"
        stm.sid d_stmt stm);*)
      DF.SDefault

    let doGuard c il = DF.GDefault

    let filterStmt stm = true

  end

module AC = DF.ForwardsDataFlow(AvailChecks)

let computeACs fd (fdat : DPF.functionData) =
  try let slst = fd.sbody.bstmts in
  let first_stm = List.hd slst in
  let precs =
    match IH.tryfind fdat.DPF.fdPCHash fd.svar.vid with
    | None -> []
    | Some cl -> begin
        if !debug then
            ignore(E.log "computeACs: precs for %s: %a\n" fd.svar.vname
                d_stmt (mkStmt (Instr cl)));
        cl
    end
  in
  IH.clear AvailChecks.stmtStartData;
  IH.add AvailChecks.stmtStartData first_stm.sid precs;
  AC.compute [first_stm]
  with Failure "hd" -> ()
  | Not_found -> ()

let getACs sid =
  try Some(IH.find AvailChecks.stmtStartData sid)
  with Not_found -> None

(* Visitor that eliminates a check at a statement where it is available *)
class dupCheckElimClass = object(self)
  inherit nopCilVisitor

  method private filter_dups ail il =
    (* make in instr that sets the lhs of i
     * to the lhs of ai *)
    let makeSet i ai =
      match i, ai with
	Call(Some lv1,_,_,l),Call(Some lv2,_,_,_) ->
	  Set(lv1,Lval lv2, l)
      | _ -> E.s(E.error "dupCheckElim: bad deputy instrs in list")
    in
    let rec filter_dups' ail il ril =
      match il with [] -> List.rev ril
      | i::rest -> match instrToCheck i with
	| Some _ ->
	    if List.exists (deputyCallsEqual i) ail
	    then (if !debug then ignore(E.log "dupCheckElim: Removing: %a\n"
					  d_instr i);
		  filter_dups' ail rest ril)
	    else let ail' = il_add ail [i] in
	    (if !debug then ignore(E.log "dupCheckElim: Not Removing: %a\n"
				     d_instr i);
	     filter_dups' ail' rest (i::ril))
	| None -> 
	    if is_deputy_instr i then
	      if List.exists (deputyCallsEqual i) ail
	      then let ai = List.find (deputyCallsEqual i) ail in
	      let newi = makeSet i ai in
	      (if !debug then ignore(E.log "dupCheckElim: Removing: %a\n"
				       d_instr i);
	       filter_dups' ail rest (newi::ril))
	      else let ail' = il_add ail [i] in
	      (if !debug then ignore(E.log "dupCheckElim: Not Removing: %a\n"
				       d_instr i);
	       filter_dups' ail' rest (i::ril))
	    else let ail' = il_handle_inst i ail in
	    filter_dups' ail' rest (i::ril)
    in
    filter_dups' ail il []

  method vstmt s =
    match getACs s.sid with
    | None -> SkipChildren
    | Some acs ->
	match s.skind with
	  Instr il -> begin
	    (*if !debug then ignore(E.log "Filtering dups from stmt %d with data %a\n" 
				    s.sid il_pretty acs);*)
	    let il' = self#filter_dups acs il in
	    s.skind <- Instr il';
	    SkipChildren
	  end
	| _ -> DoChildren

end

let dupCheckElimer = new dupCheckElimClass

let elim_dup_checks fd (fdat : DPF.functionData) =
  if !verbose then
    E.log "\t\tComputing available checks\n";
  computeACs fd fdat;
  if !verbose then
    E.log "\t\tEliminating duplicate checks\n";
  ignore(visitCilFunction dupCheckElimer fd)


(* See what checks are available at every return *)
class postConditionFinderClass postcsr = object(self)
    inherit nopCilVisitor

    method vstmt s =
        match s.skind with
        | Return(_,_) -> begin
            match getACs s.sid with
            | None -> DoChildren
            | Some acs -> begin
                postcsr := il_combine acs (!postcsr);
                DoChildren
            end
        end
        | _ -> DoChildren

end

class allChecksBuilderClass clr = object(self)
    inherit nopCilVisitor
    
    method vinst i =
        match instrToCheck i with
        | None -> DoChildren
        | Some c -> begin
            if not(List.exists (deputyCallsEqual i) (!clr)) then
                clr := i :: (!clr);
            DoChildren
        end
end

(* fundec -> instr list *)
let findFnPostConditions (fd : fundec) (fdat : DPF.functionData) =
    let clr = ref [] in
    computeACs fd fdat;
    ignore(visitCilFunction (new allChecksBuilderClass clr) fd);
    ignore(visitCilFunction (new postConditionFinderClass clr) fd);
    !clr
