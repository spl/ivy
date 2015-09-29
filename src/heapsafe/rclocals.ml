(* Copyright (c) 2007 Intel Corporation 
 * All rights reserved. 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 	Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 	Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *     Neither the name of the Intel Corporation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE INTEL OR ITS
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)
(* Add code to maintain the parallel stack of local pointer values, i.e.,
   call __builtin_rcpush/rcpop for the specified local variables around
   function calls *)
open Cil
open Rcutils
open Liveness
module L = List

(* Add pushes and pops for variables in 'oVars' around function calls
   where they are live *)
let rewriteLocals (oVars:varinfo list) =

  (* Add pushes and pops around function call 'i' for all variables in 'live',
     except 'dv' (where the function call result is to be stored) *)
  let rewriteCall i dv live loc =
    let forLiveVars todo v = 
      if (VS.mem v live) && v != dv then
	[ Call(None, (v2e todo), [v2e v], loc) ]
      else
	[ ]
    in
    let pushes = L.concat (L.map (forLiveVars rcFunctions.rcpush) oVars)
    and pops = L.concat (L.map (forLiveVars rcFunctions.rcpop) oVars) in
    pushes @ [i] @ (L.rev pops)
  in
  fun (i:instr) (live:LiveFlow.t) ->
    match i with
    | Call(dest, called, _, loc) when not (nofreeFunction called) -> 
	let dv = 
	  match dest with
	  | Some (Var v, NoOffset) -> v
	  | _ -> dummyVar
	in
	rewriteCall i dv live loc
    | _ -> [ i ]

(* Apply 'fn' to each instruction in list 'il', passing liveness information.
   'fn' receives the liveness start *after* the instruction.
   'liveSet' is the liveness information after the last instruction in 'il'.
*)
let liveWalk (fn:instr -> LiveFlow.t -> instr list) (il:instr list) (liveSet:LiveFlow.t) =
  let foldWalk i (live, il) =
    let newil = (fn i live) @ il
    and u, d = Usedef.computeUseDefInstr i in
    let newlive = VS.union u (VS.diff live d) in
    (newlive, newil) in
  let (_, newil) = L.fold_right foldWalk il (liveSet, []) in
  newil

let getLiveness (s:stmt) = Inthash.find LiveFlow.stmtStartData s.sid

let getPostLiveness (s:stmt) : LiveFlow.t = 
  let foldLiveness live s = VS.union live (getLiveness s) in
  L.fold_left foldLiveness VS.empty s.succs

(* A CIL visitor that applies 'fn' to each instruction with the
   correct liveness information. 
   'fn' receives the liveness start *after* the instruction.
   Assumes that 'computeLiveness' has been called beforehand. *)
class liveVisitor (fn:instr -> LiveFlow.t -> instr list) : cilVisitor = 
  object (self)
    inherit nopCilVisitor as super

    method vstmt (s:stmt) = 
      begin
	match s.skind with
	| Instr ilist ->
	    let live = getPostLiveness s in
	    let newinstrs = liveWalk fn ilist live in
	    s.skind <- Instr newinstrs
	| _ -> ()
      end;
      DoChildren
  end

(* Add rcpush/rcpop calls to function 'f' for all variables in 'oVars' *)
let rcLocals (f:fundec) (oVars:varinfo list) : unit =
  Cfg.clearCFGinfo f;
  ignore(Cfg.cfgFun f);
  computeLiveness f;
  let doLocals = new liveVisitor (rewriteLocals oVars) in
  ignore(visitCilFunction doLocals f)
