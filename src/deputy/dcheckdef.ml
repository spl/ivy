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
open Expcompare
open Dutil
open Dattrs

module E = Errormsg
module DCE = Dcanonexp

type check =
    CNonNull of exp      (** e != 0 *)
  | CEq of exp * exp * string * doc list
                         (** e1 == e2 *)
  | CMult of exp * exp   (** e1 * k == e2 for some int k *)
  | CPtrArith of exp * exp * exp * exp * int
                         (** e3 + (e4 * size) does not overflow, and
                           * e1 <= e3 + (e4 * size) <= e2. *)
  | CPtrArithNT of exp * exp * exp * exp * int
                         (** e3 + (e4 * size) does not overflow, and
                           * e1 <= e3 + (e4 * size) <= (e2 + sizeof(e2)). *)
  | CPtrArithAccess of exp * exp * exp * exp * int
                         (** e3 + ((e4+1) * size) does not overflow, and
                           * e1 <= e3 + ((e4+1) * size) <= e2. *)
  | CLeqInt of exp * exp * string
                         (** e1 <= e2, unsigned.
                           * Also remember why this check was added. *)
  | CLeq of exp * exp * string
                         (** e1 <= e2, unsigned.
                           * Also remember why this check was added. *)
  | CLeqNT of exp * exp * int * string
                         (** e1 <= (e2 + sizeof(e2)), unsigned.
                           * The int is the size of the base type.
                           * Also remember why this check was added. *)
  | CNullOrLeq of exp * exp * exp * string
                         (** e1 == 0 || e2 <= e3.
                           * Also remember why this check was added. *)
  | CNullOrLeqNT of exp * exp * exp * int * string
                         (** e1 == 0 || e2 <= (e3 + sizeof(e3)).
                           * The int is the size of the base type.
                           * Also remember why this check was added. *)
  | CWriteNT of exp * exp * exp * int
                         (** (e1 == e2) ==> (e3 = 0)
                           * The int is the size of the base type. *)
  | CNullUnionOrSelected of lval * exp
                         (** lv = \vec{0} || e.
                             Here, e is a shortcut saying that if the 
                             newly-active field is the same as the old
                             active field, we don't check for the union 
                             equalling zero.*)
  (* These two are redundant with CNonNull and CEq, but having separate
     checks for unions gives better error messages: *)
  | CSelected of exp     (** e != 0 *)
  | CNotSelected of exp  (** e == 0 *)
(* Other checks will be needed, such as nullterm checks and checks for when
   part of one of the above checks can be proved statically. *)


(* These aren't real variables.  In the output, they'll show up as
   __LOCATION__, which is a macro defined in deputy/checks.h. We use them
   for calling runtime check functions. *)
let locationToken : exp =
  let vi = makeGlobalVar "__LOCATION__" charPtrType in
  Lval (var vi)

let mkFun (name: string) (rt:typ) (args: typ list) (fnAttrs: attributes) : exp = 
  let fdec = emptyFunction name in
  let args = List.map (fun t -> ("", t, [])) args in
  fdec.svar.vtype <- TFun(rt, Some args, false, fnAttrs);
  Lval (var fdec.svar)

let mkCheckFun (name: string) (n: int) : exp = 
 (* A check function takes n void* parameters, a location *)
  let args = Util.list_init n (fun _ -> voidPtrType) in
  let args' = args @ [charPtrType] in
  mkFun name voidType args' Rcutils.nofreeAttr

let cnonnull = mkCheckFun "CNonNull" 1
let ceq = mkCheckFun "CEq" 3
let cmult = mkCheckFun "CMult" 2
let cptrarith = mkCheckFun "CPtrArith" 5
let cptrarithaccess = mkCheckFun "CPtrArithAccess" 5
let cptrarithnt = mkCheckFun "CPtrArithNT" 5
let cleqint = mkCheckFun "CLeqInt" 3
let cleq = mkCheckFun "CLeq" 3
let cleqnt = mkCheckFun "CLeqNT" 4
let cnullorleq = mkCheckFun "CNullOrLeq" 4
let cnullorleqnt = mkCheckFun "CNullOrLeqNT" 5
let cwritent = mkCheckFun "CWriteNT" 4
let cnullunion = mkCheckFun "CNullUnionOrSelected" 3
let cselected = mkCheckFun "CSelected" 1
let cnotselected = mkCheckFun "CNotSelected" 1

let unmkString (e: exp) : string =
  match e with
  | Const (CStr s) -> s
  | _ -> E.s (bug "Expected string constant")

let toInt (e:exp) : int =
  match isInteger e with
    Some i64 -> to_int i64
  | None -> 
      E.s (bug "expected a constant int for the size param in this check.")

let checkFunctions : exp list =
  [ cnonnull; ceq; cmult; cptrarith; cptrarithnt; cleqint;
    cleq; cleqnt; cnullorleq; cnullorleqnt; cwritent; cnullunion;
    cselected; cnotselected; cptrarithaccess ]

(* This function gives a high-level reason for each check.  The text here
 * should mirror the text in the runtime library, where possible. *)
let checkWhy (c: check) : string =
  match c with
  | CNonNull _ -> "non-null check"
  | CEq (_, _, why, _) -> why
  | CMult _ -> "alignment check"
  | CPtrArithAccess _ -> "pointer arithmetic and dereference check"
  | CPtrArith _ -> "pointer arithmetic check"
  | CPtrArithNT _ -> "nullterm pointer arithmetic check"
  | CLeqInt (_, _, why) -> why
  | CLeq (_, _, why) -> why
  | CLeqNT (_, _, _, why) -> why
  | CNullOrLeq (_, _, _, why) -> why
  | CNullOrLeqNT (_, _, _, _, why) -> why
  | CWriteNT _ -> "nullterm write check"
  | CNullUnionOrSelected _ -> "null union check"
  | CSelected _ -> "check that union field is selected"
  | CNotSelected _ -> "check that union field is not selected"

(* This function gives a textual representation of a given check for
 * error-reporting purposes. *)
let checkText (c: check) : doc list =
  startTemps ();
  let docs =
    match c with
    | CNonNull (e) ->
        [dprintf "%a != 0%t" dc_exp e dx_temps]
    | CEq (e1,e2,why,docs) ->
        if docs <> [] then
          docs
        else
          [dprintf "%a == %a%t" dc_exp e1 dc_exp e2 dx_temps]
    | CMult (e1,e2) ->
        [dprintf "%a %% %a == 0%t" dc_exp e2 dc_exp e1 dx_temps]
    | CPtrArithAccess(e1,e2,e3,e4,e5) ->
        [dprintf "%a <= %a + %a + 1 (with no overflow)%t"
                 dc_exp e1 dc_exp e3 dc_exp e4 dx_temps;
         dprintf "%a + %a + 1 <= %a (with no overflow)%t"
                 dc_exp e3 dc_exp e4 dc_exp e2 dx_temps]
    | CPtrArith (e1,e2,e3,e4,e5) ->
        [dprintf "%a <= %a + %a (with no overflow)%t"
                 dc_exp e1 dc_exp e3 dc_exp e4 dx_temps;
         dprintf "%a + %a <= %a (with no overflow)%t"
                 dc_exp e3 dc_exp e4 dc_exp e2 dx_temps]
    | CPtrArithNT (e1,e2,e3,e4,e5) ->
        [dprintf "%a <= %a + %a (with no overflow)%t"
                 dc_exp e1 dc_exp e3 dc_exp e4 dx_temps;
         dprintf "%a + %a <= %a + len(%a) (with no overflow)%t"
                 dc_exp e3 dc_exp e4 dc_exp e2 dc_exp e2 dx_temps]
    | CLeqInt (e1,e2,why) ->
        [dprintf "%a <= %a%t" dc_exp e1 dc_exp e2 dx_temps]
    | CLeq (e1,e2,why) ->
        [dprintf "%a <= %a%t" dc_exp e1 dc_exp e2 dx_temps]
    | CLeqNT (e1,e2,e3,why) ->
        [dprintf "%a <= %a + len(%a)%t" dc_exp e1 dc_exp e2 dc_exp e2 dx_temps]
    | CNullOrLeq (e1,e2,e3,why) ->
        [dprintf "%a == 0 || %a <= %a%t" dc_exp e1 dc_exp e2 dc_exp e3 dx_temps]
    | CNullOrLeqNT (e1,e2,e3,e4,why) ->
        [dprintf "%a == 0 || %a <= %a + len(%a)%t"
                 dc_exp e1 dc_exp e2 dc_exp e3 dc_exp e3 dx_temps]
    | CWriteNT (p,hi,what,sz) ->
        [dprintf "%a != %a || *(%a) != 0 || %a == 0%t"
                 dc_exp p dc_exp hi dc_exp p dc_exp what dx_temps]
    | CNullUnionOrSelected (lv, sameFieldSelected) -> 
        [dprintf "%a || iszero(%a)%t"
                 dc_exp sameFieldSelected dx_lval lv dx_temps]
    | CSelected (e) ->
        [dprintf "%a%t" dc_exp e dx_temps]
    | CNotSelected (e) ->
        [dprintf "! %a%t" dc_exp e dx_temps]
  in
  stopTemps ();
  docs

let instrToCheck (instr: instr) : check option =
  match instr with
  | Call (None, fn, args, _) when List.exists (compareExp fn) checkFunctions ->
      let c =
        match args with
        | [e;_;_] when compareExp fn cnonnull ->
            CNonNull e
        | [e1;e2;why;doc;_] when compareExp fn ceq ->
            CEq (e1,e2,unmkString why,[text (unmkString doc)])
        | [e1;e2;_;_] when compareExp fn cmult ->
            CMult (e1,e2)
        | [e1;e2;e3;e4;e5;_;_;_] when compareExp fn cptrarith ->
            CPtrArith (e1,e2,e3,e4,toInt e5)
	| [e1;e2;e3;e4;e5;_;_;_] when compareExp fn cptrarithaccess ->
	    CPtrArithAccess (e1,e2,e3,e4,toInt e5)
        | [e1;e2;e3;e4;e5;_;_;_] when compareExp fn cptrarithnt ->
            CPtrArithNT (e1,e2,e3,e4,toInt e5)
        | [e1;e2;why;_;_] when compareExp fn cleqint ->
            CLeqInt (e1,e2,unmkString why)
        | [e1;e2;why;_;_] when compareExp fn cleq ->
            CLeq (e1,e2,unmkString why)
        | [e1;e2;e3;why;_;_] when compareExp fn cleqnt ->
            CLeqNT (e1,e2,toInt e3,unmkString why)
        | [e1;e2;e3;why;_;_] when compareExp fn cnullorleq ->
            CNullOrLeq (e1,e2,e3,unmkString why)
        | [e1;e2;e3;e4;why;_;_] when compareExp fn cnullorleqnt ->
            CNullOrLeqNT (e1,e2,e3,toInt e4,unmkString why)
        | [p;hi;what;sz;_;_] when compareExp fn cwritent ->
            CWriteNT (p,hi,what,toInt sz)
        | [AddrOf lv;_;e;_;_] when compareExp fn cnullunion ->
            CNullUnionOrSelected (lv, e)
        | [e;_;_] when compareExp fn cselected ->
            CSelected (e)
        | [e;_;_] when compareExp fn cnotselected ->
            CNotSelected (e)
        | _ ->
            E.s (bug "Check instruction not recognized: %a" d_instr instr)
      in
      Some c
  | _ -> None

let checkToInstr (c:check) : instr =
  let call f args docs =
    (* Append the file and line to the end of the args *)
    let extraArgs =
      List.fold_right
        (fun doc acc -> Const (CStr (sprint 1000000 doc)) :: acc)
        docs [locationToken]
    in
    Call (None, f, args @ extraArgs, !currentLoc) 
  in
  let docs = checkText c in
  (* Use dc_exp instead of dx_exp so we don't print so many casts in the
     "why" messages of checks. *)
  let i =
    match c with
    | CNonNull (e) ->
        call cnonnull [e] docs
    | CEq (e1,e2,why,_) ->
        call ceq [e1;e2;mkString why] docs
    | CMult (e1,e2) ->
        call cmult [e1;e2] docs
    | CPtrArithAccess(e1,e2,e3,e4,e5) ->
	call cptrarithaccess [e1;e2;e3;e4;integer e5] docs
    | CPtrArith (e1,e2,e3,e4,e5) ->
        call cptrarith [e1;e2;e3;e4;integer e5] docs
    | CPtrArithNT (e1,e2,e3,e4,e5) ->
        call cptrarithnt [e1;e2;e3;e4;integer e5] docs
    | CLeqInt (e1,e2,why) ->
        call cleqint [e1;e2;mkString why] docs
    | CLeq (e1,e2,why) ->
        call cleq [e1;e2;mkString why] docs
    | CLeqNT (e1,e2,e3,why) ->
        call cleqnt [e1;e2;integer e3;mkString why] docs
    | CNullOrLeq (e1,e2,e3,why) ->
        call cnullorleq [e1;e2;e3;mkString why] docs
    | CNullOrLeqNT (e1,e2,e3,e4,why) ->
        call cnullorleqnt [e1;e2;e3;integer e4;mkString why] docs
    | CWriteNT (p,hi,what,sz) ->
        call cwritent [p;hi;what;integer sz] docs
    | CNullUnionOrSelected (lv, sameFieldSelected) -> 
        let sz = sizeOf (typeOfLval lv) in
        call cnullunion [mkAddrOf lv; sz; sameFieldSelected] docs
    | CSelected (e) ->
        call cselected [e] docs
    | CNotSelected (e) ->
        call cnotselected [e] docs
  in
  (* For the optimizer to work properly, we must be able to convert instrs
   * back to the original check.  As a sanity check, we verify here that
   * this is possible for each instr we generate. *)
  if instrToCheck i = None then
    E.s (bug "checkToInstr not invertible");
  i

let checks_equal c1 c2 =
let ce = (*deputyStripAndCompareExp*) DCE.canonCompareExp in
match c1, c2 with
| CEq(e11,e12,_,_), CEq(e21,e22,_,_)
| CMult(e11,e12), CMult(e21, e22)
| CLeqInt(e11,e12,_), CLeqInt(e21,e22,_)
| CLeq(e11,e12,_), CLeq(e21,e22,_) ->
    (ce e11 e21) &&
    (ce e12 e22)
| CLeqNT(e11,e12,sz1,_), CLeqNT(e21,e22,sz2,_) ->
    (ce e11 e21) &&
    (ce e12 e22) &&
    sz1 = sz2
| CNullOrLeq(e11,e12,e13,_), CNullOrLeq(e21,e22,e23,_) ->
    (ce e11 e21) &&
    (ce e12 e22) &&
    (ce e13 e23)
| CNullOrLeqNT(e11,e12,e13,sz1,_), CNullOrLeqNT(e21,e22,e23,sz2,_)
| CWriteNT(e11,e12,e13,sz1),CWriteNT(e21,e22,e23,sz2) ->
    (ce e11 e21) &&
    (ce e12 e22) &&
    (ce e13 e23) &&
    sz1 = sz2
| CPtrArithAccess(e11,e12,e13,e14,sz1), CPtrArithAccess(e21,e22,e23,e24,sz2) ->
    (ce e11 e21) &&
    (ce e12 e22) &&
    (ce e13 e23) &&
    (ce e14 e24) &&
    sz1 = sz2
| CPtrArith(e11,e12,e13,e14,sz1), CPtrArith(e21,e22,e23,e24,sz2)
| CPtrArithNT(e11,e12,e13,e14,sz1), CPtrArithNT(e21,e22,e23,e24,sz2) ->
    (ce e11 e21) &&
    (ce e12 e22) &&
    (ce e13 e23) &&
    (ce e14 e24) &&
    sz1 = sz2
| CNullUnionOrSelected(l1, e1), CNullUnionOrSelected(l2, e2) ->
    (compareLval l1 l2) &&
    (ce e1 e2)
| CSelected e1, CSelected e2
| CNotSelected e1, CNotSelected e2
| CNonNull e1, CNonNull e2 ->
    ce e1 e2
| _ -> false


let isDeputyFunctionLval (e:exp) : bool =
  List.exists (compareExp e) checkFunctions ||
  match e with
  | Lval(Var vf,NoOffset) -> begin
      vf.vname = "deputy_findnull" ||
      vf.vname = "__deputy_memset" ||
      vf.vname = "deputy_max"
  end
  | _ -> false

let isDeputyFunctionInstr (i : instr) : bool =
    match i with
    | Call(_,fe,_,_) -> isDeputyFunctionLval fe
    | _ -> false

(*
 * Return true if i is a deputy
 * runtime check.
 *)
let is_check_instr i =
  match instrToCheck i with
    None -> false
  | Some _ -> true

let is_deputy_fun i = match i with
  Call(_,Lval(Var vf,NoOffset),_,_) ->
    vf.vname = "deputy_findnull" ||
    vf.vname = "deputy_max"
  | _ -> false

let alloc_names = [
  "malloc";
  "calloc";
  "realloc";
  "xmalloc";
  "__builtin_alloca";
  "alloca";
  "kmalloc"
]

let libc_no_side_effects = [
  "printf";
] @ alloc_names

let is_alloc_fun i =
  match i with
  | Call(_,Lval(Var vf,NoOffset),_,_) ->
      List.mem vf.vname alloc_names
  | _ -> false

let isLibcNoSideEffects i =
  match i with
  | Call(_,Lval(Var vf,NoOffset),_,_) ->
      List.mem vf.vname libc_no_side_effects ||
      (hasAttribute "pure" vf.vattr) ||
      (hasAttribute "pure" (typeAttrs vf.vtype))
  | _ -> false

let lvNoSideEffects lve =
    List.mem lve checkFunctions ||
    match lve with
    | Lval(Var vf, NoOffset) ->
        List.mem vf.vname libc_no_side_effects ||
        (hasAttribute "pure" vf.vattr) ||
        (hasAttribute "pure" (typeAttrs vf.vtype))
    | _ -> false

(* 
 * Return true if i is any
 * instruction that deputy added.
 *)
let is_deputy_instr i =
  match instrToCheck i with
    Some _ -> true
  | None -> is_deputy_fun i
