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
 * doptimutil.ml
 *
 * This file contains useful utility functions for the Deputy
 * optimizer.
 *
 *)

open Cil
open Expcompare
open Pretty
open Dattrs
open Dutil
open Dcheckdef

module E = Errormsg
module P = Ptranal

module DCE = Dcanonexp

let debug = ref false

let (<%) = (fun x y -> (Int64.compare x y) < 0)
let (<=%) = (fun x y -> (Int64.compare x y) <= 0)
let (>%) = (fun x y -> (Int64.compare x y) > 0)
let (>=%) = (fun x y -> (Int64.compare x y) >= 0)
let (<>%) = (fun x y -> (Int64.compare x y) <> 0)
   
let (+%) = Int64.add
let (-%) = Int64.sub
let ( *% ) = Int64.mul
let (/%) = Int64.div
let (~-%) = Int64.neg

let debugOptim = false

(* let int64to32 (i: int64) : int32 =  *)
(*   let i' = Int64.to_int32 i in (\* Silently drop the high 32 bits *\) *)
(*   if i = Int64.of_int32 i' then i' *)
(*   else E.s (unimp "A constant that doesn't fit in 32 bits.") *)

(* What is the largest number that can be stored in the given integral type,
   assuming it is treated as unsigned? *)
let maxUnsignedInt (t:typ) : int64 =
  (Int64.shift_left 1L (bitsSizeOf t)) -% 1L

let rec isIntOrPtrType (t:typ) : bool =
  match t with
    TInt _ | TPtr _ -> true
  | TNamed (tt,_) -> isIntOrPtrType tt.ttype
  | _ -> false

(* Returns the size of a pointer's base type in bytes, if known *)
let sizeOfBaseType ptrt: int option =
  match unrollType ptrt with
  | TPtr (bt, _) -> begin
      match isInteger (constFold true (SizeOf bt)) with
      | Some n -> Some (to_int n)
      | None -> None
    end
  | _ -> (* maybe the expression is NULL *)
      None

(* Do we need an alignment check for p + x?  Well, that depends on the size of
 *  *p.  If the size is a power of two, p + x will be aligned even if it
 *  overflows, so we can skip the check. *)
let needsAlignCheck ptrt: bool =
  match sizeOfBaseType ptrt with (* Look for common multiples of 2 *)
    Some (1|2|4|8|16|32|64|128|256|512|1024|2048|4096) -> false
  | _ -> true

let false_cond (c:check) = false

(* map f to all the expressions in a check 
 * only if cnd c is false *)
(* (check -> bool) -> (exp -> exp) -> check -> check *)
let map_to_check ?cond:(cnd=false_cond) f c =
  match c with
    CNonNull e ->
      let e' = f e in
      CNonNull e'
  | CEq(e1,e2,why,docs) ->
      let e1' = f e1 in
      if cnd (CEq(e1',e2,why,docs)) then CEq(e1',e2,why,docs) else
      let e2' = f e2 in
      if cnd (CEq(e1,e2',why,docs)) then CEq(e1,e2',why,docs) else
      CEq(e1',e2',why,docs)
  | CMult(e1,e2) ->
      let e1' = f e1 in
      let e2' = f e2 in
      CMult(e1',e2')
  | CPtrArith(e1,e2,e3,e4,sz) ->
      let e1' = f e1 in
      if isZero e1' then CPtrArith(e1',e2,e3,e4,sz) else
      let e2' = f e2 in
      if cnd (CPtrArith(e1',e2',e3,e4,sz)) then CPtrArith(e1',e2',e3,e4,sz) else
      let e3' = f e3 in
      if cnd (CPtrArith(e1',e2,e3',e4,sz)) then CPtrArith(e1',e2,e3',e4,sz) else
      let e4' = f e4 in
      if cnd (CPtrArith(e1',e2,e3',e4',sz)) then CPtrArith(e1',e2,e3',e4',sz) else
      CPtrArith(e1',e2',e3',e4',sz)
  | CPtrArithAccess(e1,e2,e3,e4,sz) ->
      let e1' = f e1 in
      if isZero e1' then CPtrArithAccess(e1',e2,e3,e4,sz) else
      let e2' = f e2 in
      if cnd (CPtrArithAccess(e1',e2',e3,e4,sz)) then CPtrArithAccess(e1',e2',e3,e4,sz) else
      let e3' = f e3 in
      if cnd (CPtrArithAccess(e1',e2,e3',e4,sz)) then CPtrArithAccess(e1',e2,e3',e4,sz) else
      let e4' = f e4 in
      if cnd (CPtrArithAccess(e1',e2,e3',e4',sz)) then CPtrArithAccess(e1',e2,e3',e4',sz) else
      CPtrArithAccess(e1',e2',e3',e4',sz)
  | CPtrArithNT(e1,e2,e3,e4,sz) ->
      let e1' = f e1 in
      if isZero e1' then CPtrArithNT(e1',e2,e3,e4,sz) else
      let e2' = f e2 in
      if cnd (CPtrArithNT(e1',e2',e3,e4,sz)) then CPtrArithNT(e1',e2',e3,e4,sz) else
      let e3' = f e3 in
      if cnd (CPtrArithNT(e1',e2,e3',e4,sz)) then CPtrArithNT(e1',e2,e3',e4,sz) else
      let e4' = f e4 in
      if cnd (CPtrArithNT(e1',e2,e3',e4',sz)) then CPtrArithNT(e1',e2,e3',e4',sz) else
      CPtrArithNT(e1',e2',e3',e4',sz)
  | CLeqInt(e1,e2,why) ->
      let e1' = f e1 in
      let e2' = f e2 in
      CLeqInt(e1',e2',why)
  | CLeq(e1,e2,why) ->
      let e1' = f e1 in
      if cnd (CLeq(e1',e2,why)) then CLeq(e1',e2,why) else
      let e2' = f e2 in
      if cnd (CLeq(e1,e2,why)) then CLeq(e1,e2',why) else
      CLeq(e1',e2',why)
  | CLeqNT(e1,e2,sz,why) ->
      let e1' = f e1 in
      if cnd (CLeqNT(e1',e2,sz,why)) then CLeqNT(e1',e2,sz,why) else
      let e2' = f e2 in
      if cnd (CLeqNT(e1,e2',sz,why)) then CLeqNT(e1,e2',sz,why) else
      CLeqNT(e1',e2',sz,why)
  | CNullOrLeq(e1,e2,e3,why) ->
      let e1' = f e1 in
      if isZero e1' then CNullOrLeq(e1',e2,e3,why) else
      let e2' = f e2 in
      if cnd (CNullOrLeq(e1',e2',e3,why)) then CNullOrLeq(e1',e2',e3,why) else
      let e3' = f e3 in
      if cnd (CNullOrLeq(e1',e2,e3',why)) then CNullOrLeq(e1',e2,e3',why) else
      CNullOrLeq(e1',e2',e3',why)
  | CNullOrLeqNT(e1,e2,e3,sz,why) ->
      let e1' = f e1 in
      if isZero e1' then CNullOrLeqNT(e1',e2,e3,sz,why) else
      let e2' = f e2 in
      if cnd (CNullOrLeqNT(e1',e2',e3,sz,why)) then CNullOrLeqNT(e1',e2',e3,sz,why) else
      let e3' = f e3 in
      if cnd (CNullOrLeqNT(e1',e2,e3',sz,why)) then CNullOrLeqNT(e1',e2,e3',sz,why) else
      CNullOrLeqNT(e1',e2',e3',sz,why)
  | CWriteNT(e1,e2,e3,sz) ->
      let e1' = f e1 in
      let e2' = f e2 in
      let e3' = f e3 in
      CWriteNT(e1',e2',e3',sz)
  | CSelected e ->
      let e' = f e in
      CSelected e'
  | CNotSelected e ->
      let e' = f e in
      CNotSelected e'
  | CNullUnionOrSelected (lv,e) ->
     let e' = f e in
     CNullUnionOrSelected(lv,e')


(* Apply f to all expressions in a check
 * and return the combination of the results
 * specified by comb the default for which is
 * ||.
 *)
(* (bool -> bool -> bool) -> (exp -> bool) -> check -> bool *)
let test_check ?comb:(cmb=(fun a b -> a || b)) f c =
  match c with
    CNonNull e
  | CNotSelected e
  | CSelected e ->
      f e
  | CNullUnionOrSelected (lv,e) ->
      cmb (f (Lval lv)) (f e)
  | CEq(e1,e2,_,_)
  | CMult(e1,e2)
  | CLeq(e1,e2,_)
  | CLeqInt(e1,e2,_)
  | CLeqNT(e1,e2,_,_) ->
      let b1 = f e1 in
      let b2 = f e2 in
      cmb b1 b2
  | CNullOrLeq(e1,e2,e3,why) ->
      let b1 = f e1 in
      let b2 = f e2 in
      let b3 = f e3 in
      cmb b1 (cmb b2 b3)
  | CNullOrLeqNT(e1,e2,e3,sz,_)
  | CWriteNT(e1,e2,e3,sz) ->
      let b1 = f e1 in
      let b2 = f e2 in
      let b3 = f e3 in
      cmb (cmb b1 b2) b3
  | CPtrArith(e1,e2,e3,e4,sz)
  | CPtrArithAccess(e1,e2,e3,e4,sz)
  | CPtrArithNT(e1,e2,e3,e4,sz) ->
      let b1 = f e1 in
      let b2 = f e2 in
      let b3 = f e3 in
      let b4 = f e4 in
      cmb (cmb b1 b2) (cmb b3 b4)

let compareExpLists el1 el2 =
  if List.length el1 <> List.length el2
  then false
  else List.fold_left (fun b (e1,e2) ->
    b && DCE.canonCompareExp(*StripCasts*) e1 e2)
      true (List.combine el1 el2)

let deputyCallsEqual i1 i2 =
  (*ignore(E.log "comparing %a and %a\n" d_instr i1 d_instr i2);*)
  match instrToCheck i1, instrToCheck i2 with
    Some c1, Some c2 -> checks_equal c1 c2
  | Some _, None -> false
  | None, Some _ -> false
  | None, None ->
      if not(is_deputy_instr i1) ||
	not(is_deputy_instr i2)
      then false
      else match i1, i2 with
	Call(_,fn1,el1,_), Call(_,fn2,el2,_) ->
	  if not(compareExp fn1 fn2)
	  then false
	  else compareExpLists el1 el2
      | _ -> false


(* Is the block reachable through a goto? *)
let hasALabel (b:block) : bool =
  let hasLabel = ref false in
  let hasALabelVisitor = object (self)
    inherit nopCilVisitor
    method vstmt s =
      if s.labels <> [] then begin
        hasLabel := true;
      end;
      DoChildren
  end in
  ignore (visitCilBlock hasALabelVisitor b);
  !hasLabel

(* returns the largest prefix of l such that each
 * element of the prefix satisfies p *)
let prefix p l =
  let rec helper p l seen =
    match l with
    | [] -> (List.rev seen, [])
    | x :: rst -> begin
	if p x 
	then helper p rst (x::seen)
	else (List.rev seen, x :: rst)
    end
  in
  helper p l []

