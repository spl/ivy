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
 * dflowsens.ml
 *
 * A flow-sensitive optimizer for nonnull, strlen, and inequalities
 *
 *
 *)

open Cil
open Expcompare
open Pretty
open Dattrs
open Dutil
open Dcheckdef
open Doptimutil
open Ivyoptions

open Dflowinsens

module E = Errormsg
module IH = Inthash
module DF = Dataflow
module S = Stats
module P = Dptranal
module DCE = Dcanonexp
module DPF = Dprecfinder
module AELV = Availexpslv

(*let debug = ref true*)

(*
 * When ignore_inst returns true, then
 * the instruction in question has no
 * effects on the abstract state.
 * When ignore_call returns true, then
 * the instruction only has side-effects
 * from the assignment if there is one.
 *)
let ignore_inst = ref (fun i -> false)
let ignore_call = ref (fun i -> false)

let registerIgnoreInst (f : instr -> bool) : unit =
  let f' = !ignore_inst in
  ignore_inst := (fun i -> (f i) || (f' i))

let registerIgnoreCall (f : instr -> bool) : unit =
  let f' = !ignore_call in
  ignore_call := (fun i -> (f i) || (f' i))

type kind =
    | VCV (* var1 + const <= var2 *)
    | VVC (* var1 + var2 <= const *)

type absState = {
  nonNullLvals: (lval * referenced) list; (*varinfo list;*)

  strlenVars: (varinfo * (exp * referenced)) list; 
  (** (v, e, mem, vars) means that v holds the the length of string e.
      For convenience, we also remember whether e involves a memory reference
      and what local vars e contains. *)

  ineqs: (lval * int64 * lval * referenced * kind) list;
  (** (x, c, y, vars, VCV) means that x + c <= y.
      (x, c, y, vars, VVC) means that x + y <= c.
    Also, if x is a pointer and VCV, then x+c < 2^32, so x+c doesn't overflow.
    (We usually get this fact just by knowing that any ptr arith that appears
     in a program has first been checked for overflow with CPtrArith)
    '+' is done on integers, not pointers.
    We also remember the memory/variables that either expression depend on. *)

  preds: (exp * int64 * referenced) list list;
  (** list of true disjunctions. i.e. [[(e,5);(e,8)];[(f,10)]] means
   ((e==5)\/(e==8))/\(f==10) *)

  canIncrement: (lval * exp * referenced) list;
  (** (x, e) means that x is an NT pointer that can safely be incremented
      by e. *)
}


let top = { nonNullLvals = [];
            strlenVars = [];
            ineqs = [];
            preds = [];
            canIncrement = [];
          }

let printIneq (lv1,i,lv2,_,k): doc =
    match k with
    | VCV ->
      dprintf "%a + %Ld <= %a" dx_lval lv1 i dx_lval lv2
    | VVC ->
      dprintf "%a + %a <= %Ld" dx_lval lv1 dx_lval lv2 i

let d_state () a: doc =
  if a.strlenVars == [] then
    dprintf 
      "@[Nonnull lvals:@[%a@]\nInEqs:@[%a@]\nPreds:@[%a@]\nCanIncr:@[%a@]@]"
      (docList (fun (lv,_) -> dx_lval () lv)) a.nonNullLvals
      (docList ~sep:Pretty.line printIneq) a.ineqs
      (docList ~sep:Pretty.line (fun dl -> dprintf "%a"
          (docList (fun (e,i,_) -> dprintf "%a = %Ld" dx_exp e i)) dl)) a.preds
      (docList ~sep:Pretty.line (fun (x,e,_) -> dprintf "%a by %a"
                                   dx_lval x dx_exp e)) a.canIncrement
  else
    dprintf 
      "@[Nonnull lvals:@[%a@]\nStrlenVars:@[%a@]\nInEqs:@[%a@]\nPreds:@[%a@]\nCanIncr:@[%a@]@]"
      (docList (fun (lv,_) -> dx_lval () lv)) a.nonNullLvals
      (docList (fun (vi,(e,_)) -> 
                  text(vi.vname^" for ") ++ dx_exp () e))  a.strlenVars
      (docList ~sep:Pretty.line printIneq) a.ineqs
      (docList ~sep:Pretty.line (fun dl -> dprintf "%a"
          (docList (fun (e,i,_) -> dprintf "%a = %Ld" dx_exp e i)) dl)) a.preds
      (docList ~sep:Pretty.line (fun (x,e,_) -> dprintf "%a by %a"
                                   dx_lval x dx_exp e)) a.canIncrement
      

(* This fake variable is used to represent 0.  It should never appear in
   output code *)
let zeroLv : lval =
  let v = makeVarinfo false "_ZERO_" longType in
  var v

let isNonNull' (a: absState) (lv: lval) : bool =
  List.exists (fun (lv',_) -> DCE.canonCompareLval lv lv')
    a.nonNullLvals

let addNonNull (a:absState) (lv: lval) : absState = 
  if isNonNull' a lv then a
  else begin
    let kill : referenced = Dutil.varsOfExp (Lval lv) in
    { a with nonNullLvals = (lv,kill)::a.nonNullLvals }
  end

let addStringlen (a:absState) (vi:varinfo) (str:exp) : absState =
  try 
    let other,_ = List.assq vi a.strlenVars in
    if DCE.canonCompareExp(*compareExpStripCasts*) other str then
      a
    else
      E.s (unimp "%s is the length of two different strings: %a and %a\n"
             vi.vname dx_exp other dx_exp str)
  with Not_found ->
    let kill : referenced = Dutil.varsOfExp str in          
    { a with strlenVars = (vi,(str,kill))::a.strlenVars }

(* Do we know the length of this string? *)
let hasStringlen (a:absState) (str:exp) : exp option =
  let rec loop = 
    function (vi, (e, _))::rest ->
      if DCE.canonCompareExp(*compareExpStripCasts*) e str then 
        Some (Lval (var vi)) 
      else loop rest
    | [] -> None
  in
  loop a.strlenVars

let addLessEq (a:absState) (lv1: lval) (i:int64) (lv2:lval) (k:kind) : absState = 
  let alreadyExists: bool =
    (* unlike ineqHolds, we look for this exact statement rather than a
       stronger one. *)
    List.exists
      (fun (lv1', i', lv2', _,k') ->
         (DCE.canonCompareLval lv1 lv1') && (DCE.canonCompareLval lv2 lv2') &&
         i' = i && k = k')
      a.ineqs
  in
  if alreadyExists then a
  else begin
    (* make a fake binop so we can get the combined deps of e1 and e2*)
    let e' = BinOp(PlusA, Lval lv1, Lval lv2, intType) in
    let fact = (lv1, i, lv2, Dutil.varsOfExp e', k) in
    let a' = { a with ineqs = fact::a.ineqs } in
    if !debug then log "New State = %a\n" d_state a';
    a'
  end

(* is there some i for which lv1 + i <= lv2 *)
(*let getLessEq (a:absState) (lv1 : lval) (lv2 : lval) : int64 option =*)

(* If k is VCV, Is it true that (lv1 + i <= lv2)?
 * To answer this, we look for (lv1, i', lv2) in the state, where i' >= i.
 * If k is VVC, Is it true that (lv1 + lv2 <= i)?
 * To answer this, we look for (lv1, i', lv2) in the state, where i' <= i. *)
let ineqHolds (a:absState) (lv1: lval) (i:int64) (lv2:lval) (k:kind) : bool =
  let findIneq lv1 i lv2: bool =
    (* Search the state for lv1 + i <= lv2, or a stronger statement. *)
    match k with
    | VCV ->
        List.exists
          (fun (lv1', i', lv2', _, k') ->
             (DCE.canonCompareLval lv1 lv1') && (DCE.canonCompareLval lv2 lv2') &&
              i' >= i && k=k')
          a.ineqs
    | VVC ->
        List.exists
          (fun (lv1', i', lv2', _, k') ->
             (DCE.canonCompareLval lv1 lv1') && (DCE.canonCompareLval lv2 lv2') &&
              i' <= i && k = k')
          a.ineqs
  in
(*   log "Checking inequality %a + %Ld <= %a\n in %a" *)
(*     dx_lval lv1 i dx_lval lv2 d_state a; *)
  if k = VCV && DCE.canonCompareLval lv1 lv2 then
    (i <=% 0L)
  else if findIneq lv1 i lv2 then
    true
  else if lv1 != zeroLv && lv2 != zeroLv && k = VCV then begin
    (* One last shot: If there exists k such that lv1 <= k &&  k + i <= lv2,
       then the inequality holds. *)
    List.exists
      (fun (lv1', negk, z, _, k') ->
         z == zeroLv && k' = VCV && (DCE.canonCompareLval lv1 lv1')
           (* so far, lv + negk <= 0 (i.e. lv <= -negk)
              Now check k + i <= lv2. *)
         && findIneq zeroLv (i -% negk) lv2)
      a.ineqs
  end else
    false

let isLvalZero (a : absState) (lv : lval) : bool =
    ineqHolds a zeroLv Int64.zero lv VCV &&
    ineqHolds a lv Int64.zero zeroLv VCV

(* Is there an integer upper bound for lv1 + lv2 ? *)
let findUpperBoundSum (a:absState) (lv1 : lval) (lv2 : lval) : int64 option =
    let rec helper ineql io : int64 option =
        match ineql with
        | [] -> io
        | (lv1p, i, lv2p, _, VVC) :: rst -> begin
            if DCE.canonCompareLval lv1 lv1p &&
               DCE.canonCompareLval lv2 lv2p then begin
                match io with
                | None -> helper rst (Some i)
                | Some ip ->
                    if i < ip
                    then helper rst (Some i)
                    else helper rst io
            end else helper rst io
        end
        | _ -> io
    in
    helper a.ineqs None

let findUpperBound (a : absState) (lv : lval) : int64 option =
    let rec helper ineql io : int64 option =
        match ineql with
        | [] -> io
        | (lv1p, i, lv2p, _, VCV) :: rst when lv2p == zeroLv -> begin
            if DCE.canonCompareLval lv lv1p then begin
                match io with
                | None -> helper rst (Some (Int64.neg i))
                | Some ip ->
                    if i > ip
                    then helper rst (Some i)
                    else helper rst io
            end else helper rst io
        end
        | _ -> io
    in
    helper a.ineqs None

let addPred (a : absState) (djs : (exp * int64) list) : absState =
    let djs = List.map (fun (e,i) -> (e,i,Dutil.varsOfExp e)) djs in
    let djeq dj =
        List.filter (fun (e,i,_) ->
            not(List.exists (fun (e',i',_) ->
                DCE.canonCompareExp e e' && i = i')
                djs))
            dj = [] &&
        List.filter (fun (e,i,_) ->
            not(List.exists (fun (e',i',_) ->
                DCE.canonCompareExp e e' && i = i')
                dj))
            djs = []
    in
    if List.exists djeq a.preds then a else
    let preds = (* if a term has a disjunct that disagrees with
                   all disjuncts of djs, then filter out the whole term *)
        List.filter (fun dj ->
            not(List.exists (fun (e,i,_) ->
                not(List.exists (fun (e',i',_) ->
                    not(DCE.canonCompareExp e e') || i = i')
                    djs))
                dj))
            a.preds
    in
    let preds = List.filter (fun dj -> dj <> []) preds in
    { a with preds = djs :: preds }

let hasPred (a : absState) (p : (exp * int64) list) : bool =
    List.exists (fun dl -> dl <> [] && List.fold_left
        (fun b (e,i,_) -> b &&
            List.exists (fun (e',i') ->
                i = i' && DCE.canonCompareExp e e')
                p)
        true dl)
        a.preds

let addCanIncrement (a:absState) (p:lval) (howmuch:exp) : absState =
 (* make a fake binop so we can get the combined deps of p and howmuch *)
  let e' = BinOp(PlusA, Lval p, howmuch, intType) in
  let fact = (p, howmuch, Dutil.varsOfExp e') in
  if List.mem fact a.canIncrement then a
  else 
    { a with canIncrement = fact::a.canIncrement }

let canIncrement (a:absState) (p:lval) (howmuch:exp) : bool =
  (* TODO: is it worthwhile to use inequality information here? *)
  (List.exists
     (fun (p', e', _) ->
        (DCE.canonCompareLval p p') && (DCE.canonCompareExp howmuch e') )
     a.canIncrement)
  || 
    (* Is howmuch == strlen(p)? *)
    ((hasStringlen a (Lval p)) = (Some howmuch))

(* Remove certain entries from a list, without preserving order *)
let removeAll (f: 'a -> bool) (l: 'a list): 'a list =
  if List.exists f l then
    List.fold_left
      (fun acc x -> if f x then acc else x::acc)
      []
      l
  else
    l

let updateNonnull (a:absState) nonnull' : absState =
  (*if nonnull' == a.nonNullVars then a
  else*)
    { a with nonNullLvals = nonnull' }

let updateStrlen (a:absState) strlens' : absState =
  if strlens' == a.strlenVars then a
  else 
    { a with strlenVars = strlens' }
let updateIneqs (a:absState) ineqs' : absState =
  if ineqs' == a.ineqs then a
  else 
    { a with ineqs = ineqs' }

let updatePreds (a : absState) preds : absState =
  if preds == a.preds then a
  else { a with preds = preds }

let updateCanIncr (a:absState) ci' : absState =
  if ci' == a.canIncrement then a
  else 
    { a with canIncrement = ci' }

let scrambleVar (a:absState) (v: varinfo) : absState =
  let a =
    let refersToV (_, kill) = (List.memq v kill.varsRead) in
    let nonnull' = removeAll refersToV a.nonNullLvals in
    updateNonnull a nonnull'
  in
  let a = 
    let refersToV (v',(_,kill)) = (v==v') || (List.memq v kill.varsRead) in
    let strlen' = removeAll refersToV a.strlenVars in
    updateStrlen a strlen'
  in
  let a = 
    let refersToV (_,_,_,kill,_) = (List.memq v kill.varsRead) in
    let ineqs' = removeAll refersToV a.ineqs in
    updateIneqs a ineqs'
  in
  let a =
    let reversToV dl = List.exists
        (fun (_,_,kill) -> List.memq v kill.varsRead) dl
    in
    let preds' = removeAll reversToV a.preds in
    updatePreds a preds'
  in
  let a = 
    let refersToV (_,_,kill) = (List.memq v kill.varsRead) in
    let ci' = removeAll refersToV a.canIncrement in
    updateCanIncr a ci'
  in
  a  

(* After a write to memory, scramble all vars whose addresses have been
   taken.*)
let scrambleMem ?(globalsToo=false) (a:absState) (eo : exp option) : absState =
  let scrambled: varinfo -> bool = 
    fun vi -> vi.vaddrof || (vi.vglob && globalsToo)
  in
  let a =
    if !doPtrAnalysis then
        match eo with
        | Some ee ->
            let nonnull =
                List.filter (fun lvr -> not(P.lval_has_alias_read ee (fst lvr)))
                    a.nonNullLvals
            in
            updateNonnull a nonnull
        | None ->
            let refersToMem (_, kill) =
            kill.memRead || (List.exists scrambled kill.varsRead) in
            let nonnull' = removeAll refersToMem a.nonNullLvals in
            updateNonnull a nonnull'
    else
        let refersToMem (_, kill) =
          kill.memRead || (List.exists scrambled kill.varsRead) in
        let nonnull' = removeAll refersToMem a.nonNullLvals in
        updateNonnull a nonnull'
  in
  let a =
    if !doPtrAnalysis then
        match eo with
        | Some ee ->
            let strlen =
                List.filter (fun vir ->
                    not(P.lval_has_alias_read ee (Var (fst vir),NoOffset)))
                    a.strlenVars
            in
            updateStrlen a strlen
        | None ->
            let refersToMem (v',(_,kill)) = 
              kill.memRead || (scrambled v') || (List.exists scrambled kill.varsRead) in
            let strlen' = removeAll refersToMem a.strlenVars in
            updateStrlen a strlen'
    else
        let refersToMem (v',(_,kill)) = 
          kill.memRead || (scrambled v') || (List.exists scrambled kill.varsRead) in
        let strlen' = removeAll refersToMem a.strlenVars in
        updateStrlen a strlen'
  in
  let a =
    if !doPtrAnalysis then
        match eo with
        | Some ee ->
            let ineqs =
                List.filter (fun (lv1,_,lv2,_,_) ->
                    not(P.lval_has_alias_read ee lv1) &&
                    not(P.lval_has_alias_read ee lv2))
                    a.ineqs
            in
            updateIneqs a ineqs
        | None ->
            let refersToMem (_,_,_,kill,_) = 
              kill.memRead || (List.exists scrambled kill.varsRead) in
            let ineqs' = removeAll refersToMem a.ineqs in
            updateIneqs a ineqs'
    else
        let refersToMem (_,_,_,kill,_) = 
          kill.memRead || (List.exists scrambled kill.varsRead) in
        let ineqs' = removeAll refersToMem a.ineqs in
        updateIneqs a ineqs'
  in
  let a =
    if !doPtrAnalysis then
        match eo with
        | Some ee ->
            let preds =
                List.filter (fun dl -> not(List.exists
                    (fun (e,_,_) -> P.exp_has_alias_read ee e) dl))
                    a.preds
            in
            updatePreds a preds
        | None ->
            let refersToMem dl = List.exists
                (fun (_,_,kill) ->
                  kill.memRead || (List.exists scrambled kill.varsRead))
                dl
            in
            let preds = removeAll refersToMem a.preds in
            updatePreds a preds
    else
        let refersToMem dl = List.exists
            (fun (_,_,kill) ->
              kill.memRead || (List.exists scrambled kill.varsRead))
            dl
        in
        let preds = removeAll refersToMem a.preds in
        updatePreds a preds
  in
  let a =
    if !doPtrAnalysis then
        match eo with
        | Some ee ->
            let ci =
                List.filter (fun (lv,e,_) ->
                    not(P.lval_has_alias_read ee lv) &&
                    not(P.exp_has_alias_read ee e))
                    a.canIncrement
            in
            updateCanIncr a ci
        | None ->
            let refersToMem (_,_,kill) = 
              kill.memRead || (List.exists scrambled kill.varsRead) in
            let ci' = removeAll refersToMem a.canIncrement in
            updateCanIncr a ci'
    else
        let refersToMem (_,_,kill) = 
          kill.memRead || (List.exists scrambled kill.varsRead) in
        let ci' = removeAll refersToMem a.canIncrement in
        updateCanIncr a ci'
  in
  a  
  
let stateMap : absState IH.t = IH.create 50

let isNonNull state e: bool = 
(*   log "isNonNull? on %a.\n" d_plainexp e; *)
  (isNonnullType (typeOf e)) ||
  (match stripNopCasts e with
    Lval lv -> 
      isNonNull' state lv
  | BinOp((PlusPI|IndexPI|MinusPI), e1, e2, _) ->
      (* We've disallowed ptr arith if e1 is null. *)
      let t1 = typeOf e1 in
      isPointerType t1 && not (isSentinelType t1)
  | AddrOf lv
  | StartOf lv -> true
  | Const(CStr _) -> true
  | _ -> false)

let isFalse state e =
  match e with
    UnOp(LNot, e', _) -> isNonNull state e'
  | _ -> isZero e


exception CantDecompose

(* Take this sum expression and return p, [off1; off2; ...], c
    where e = p + (off1 + off2 + ... + c), p is a pointer or zeroLv, 
    and the first + is ptr arith (unless p is zeroLv). *)
let rec expToSum (e: exp) : lval * (lval list) * int64 =
  let e' = constFold true (stripCastsForPtrArith e) in
  match e' with
    Lval lv
  | StartOf lv -> (* Treat array references as lvals. *)
      (* we get the type of e, not e', because we want to consider casts
         when deciding whether to classify this as a pointer or an int. *)
      if isPointerType (typeOf e) then
        lv, [], 0L
      else if isArrayType (typeOf e) then
        raise CantDecompose
        (*E.s (bug "expToSum on %a" dx_exp e)*)
      else
        zeroLv, [lv], 0L
  | Const _ when isIntegralType (typeOf e) ->
      let c = match isInteger e' with
          Some i64 -> i64
        | None -> E.s (bug "expected a constant here.")
      in
      zeroLv, [], c
  | BinOp((PlusPI|IndexPI), e1, e2, t) ->
      let lvp1, offs1, c1 = expToSum e1 in
      let lvp2, offs2, c2 = expToSum e2 in
      if lvp2 != zeroLv then
        E.s (bug ("expToSum on \"%a\" returned a pointer, but there should be"
                  ^^" no pointer on the right operand of PlusPI") dx_exp e);
      if lvp1 == zeroLv then
        E.s (unimp "expToSum returned NULL for the left operand of PlusPI");
      lvp1, offs1@offs2, (c1+%c2)
  | BinOp(PlusA, e1, e2, t) when isIntegralType t ->
      let lvp1, offs1, c1 = expToSum e1 in
      let lvp2, offs2, c2 = expToSum e2 in
      if lvp1 != zeroLv || lvp2 != zeroLv then
        E.s (bug ("expToSum on \"%a\" returned a pointer, but there should be"
                  ^^" no pointer with PlusA") dx_exp e);
      zeroLv, offs1@offs2, (c1+%c2)
  | _ ->
      (*if !debug then
        log "Can't decompose %a into a sum." dx_exp e;*)
      raise CantDecompose

(* Given a list of lvals, return an lval representing the sum of the list
   elements, or raise CantDecompose if there are two or more lvals in the list*)
let getOneLval (l:lval list) : lval =
  match l with
    [] -> zeroLv
  | [lv] -> lv
  | _ -> raise CantDecompose


(* Decompose the expression into lv+c (integer arithmetic, not pointer), 
   or raise an exception if this isn't possible *)
let rec expToIntSum (e:exp) : lval * int64 = 
  match expToSum e with
    lv, [], c when lv != zeroLv -> 
      (* FIXME: I'm trusting here that there's no overflow, since 
         that should already be taken care of.  Is there a better way to reason
         about overlfow? *)
      (* This is lv+c.  Do the multiplication now, to handle ptr arith. *)
      if c <> 0L then
        lv, (c *% (Int64.of_int (baseSize (typeOfLval lv))))
      else
        (* if c = 0, don't compute the baseSize, since we don't need to
           (and it could be a pointer to an abstract type.) *)
        lv, 0L
  | z, offs, c when z == zeroLv ->
      (* offs + c, no pointers involved. *)
      getOneLval offs, c
  | _ -> 
      raise CantDecompose

(* Try to find an upper bound for the canon exp ce *)
(* TODO: handle more things than just c + f1*lv1 + f2*lv2 *)
let upperBoundCESum (state : absState) (ce : DCE.Can.t) : DCE.Can.t =
    if !debug then
        log "upperBoundCE: finding ubound for: %a" DCE.Can.d_t ce;
    match ce.DCE.Can.cf with
    | [(f1,e1) ; (f2,e2)] -> begin
        match e1, e2 with
        | (StartOf lv1 | Lval lv1), (StartOf lv2 | Lval lv2) -> begin
            if f1 >=Int64.zero && f1 = f2 then begin
                match findUpperBoundSum state lv1 lv2 with
                | Some c64 ->
                    let c = fst(truncateInteger64 ce.DCE.Can.ck (Int64.add c64 ce.DCE.Can.ct)) in
                    {DCE.Can.ct = c; DCE.Can.cf = []; DCE.Can.ck = ce.DCE.Can.ck}
                | None -> begin
                    if !debug then
                        log "upperBoundCE: no ubound in state %a" DCE.Can.d_t ce;
                    ce
                end
            end else begin
                if !debug then
                    log "upperBoundCE: bad coefs %a" DCE.Can.d_t ce;
                ce
            end
        end
        | _ -> begin
            if !debug then
                log "upperBoundCE: bad form %a" DCE.Can.d_t ce;
            ce
        end
    end
    | _ -> begin
        if !debug then
            log "upperBoundCE: too many %a" DCE.Can.d_t ce;
        ce
    end


(* TODO: overflow? *)
let upperBoundCEAtom (state : absState) (ce : DCE.Can.t) : DCE.Can.t =
    let rec ubExp (e : exp) : int64 option =
        match e with
        | Const(CInt64(i,_,_)) -> Some i
        | Lval lv | StartOf lv -> findUpperBound state lv
        | BinOp(Mult,e1,e2,t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 -> Some(Int64.mul i1 i2)
            | _ -> None
        end
        | BinOp(Div,e1,e2,t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 -> Some(Int64.div i1 i2)
            | _ -> None
        end
        | BinOp(Shiftlt,e1,e2,t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 -> Some(Int64.shift_left i1 (Int64.to_int i2))
            | _ -> None
        end
        | BinOp(Shiftrt,e1,(Const _ as e2),t) when not(isSignedType t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 ->
                Some(Int64.shift_right_logical i1 (Int64.to_int i2))
            | _ -> None
        end
        | BinOp(BAnd,e1,(Const _ as e2),t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 -> Some(Int64.logand i1 i2)
            | _ -> None
        end
        | BinOp(BXor,e1,(Const _ as e2),t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 -> Some(Int64.logxor i1 i2)
            | _ -> None
        end
        | BinOp(BOr,e1,(Const _ as e2),t) -> begin
            match ubExp e1, ubExp e2 with
            | Some i1, Some i2 -> Some(Int64.logor i1 i2)
            | _ -> None
        end
        | _ -> None
    in
    let ubTerm (f, e) : int64 option =
        if f < Int64.zero then None else
        match ubExp e with
        | None -> None
        | Some i -> Some(Int64.mul i f)
    in
    let rec folder sum l r : int64 * (int64 * exp) list =
        match l with
        | [] -> sum, r
        | t :: rst -> begin
            match ubTerm t with
            | Some i -> folder (Int64.add sum i) rst r
            | None -> folder sum rst (t::r)
        end
    in
    let (c,l) = folder ce.DCE.Can.ct ce.DCE.Can.cf [] in
    {DCE.Can.ct = c; DCE.Can.cf = l; DCE.Can.ck = ce.DCE.Can.ck}



let biginteger (i : int64) : exp = Const(CInt64(i,ILongLong,None))




(* cePosInState: "canonical expression positive in state"
 *)
let rec cePosInState (modify : bool)
                 (state : absState)
                 (cdiff : DCE.Can.t)
                 : bool * absState
    =
    if !debug then log "cePosInState: %a" DCE.Can.d_t cdiff;
    match DCE.Can.getSign cdiff with
    | DCE.Can.Pos | DCE.Can.Zero -> (true, state)
    | DCE.Can.Neg -> begin
        if !debug then
            log "doExpLeq: can't prove %a >= 0"
                DCE.Can.d_t cdiff;
        (false, state)
    end
    | DCE.Can.DontKnow -> begin
        match cdiff.DCE.Can.cf with
        | [ f, e ] -> begin
            match e with
            | StartOf lv
            | Lval lv ->
                (* need to get rid of coefs on the lval *)
                if Int64.rem (Int64.abs cdiff.DCE.Can.ct)(Int64.abs f) = Int64.zero then
                let c = Int64.div cdiff.DCE.Can.ct (Int64.abs f) in
                let f = Int64.div f (Int64.abs f) in
                (* need 0 - c <= f*lv --> f*lv + c >= 0 *)
                if f >= Int64.zero then
                    if modify then
                        (true, addLessEq state zeroLv (Int64.neg c) lv VCV) 
                    else if ineqHolds state zeroLv (Int64.neg c) lv VCV then
                        (true, state)
                    else begin
                        if !debug then
                            log "doExpLeq: in state %a\ncan't prove %a >= 0"
                	            d_state state DCE.Can.d_t cdiff;
                        (false, state)
                    end
                else
                    if modify then begin
                        (true, addLessEq state lv (Int64.neg c) zeroLv VCV) 
                    end else
                        if ineqHolds state lv (Int64.neg c) zeroLv VCV then
                            (true, state)
                        else begin
                            if !debug then
                                log "doExpLeq: in state %a\ncan't prove %a >= 0"
                    	            d_state state DCE.Can.d_t cdiff;
                            (false, state)
                        end
                else begin
                    if !debug then
                        log "doExpLeq: bad coefs %a"
                            DCE.Can.d_t cdiff;
                    (false, state)
                end
            | _ -> begin
                if !debug then
                    log "doExpLeq: bad form1: %a"
                        DCE.Can.d_t cdiff;
                    (false, state)
            end
        end
        (* We've only got octagons. *)
        | (f1,e1') :: (f2,e2') :: [] -> begin
	        (* Check that f1*e1 + f2*e2 + c >= 0 *)
	        (* We want to make sure this is non-negative *)
	        (* If f1 f2 and c are >= 0, then check e1, e2 >= 0 *)
	        if f1 >= Int64.zero && f2 >= Int64.zero &&
               cdiff.DCE.Can.ct >= Int64.zero then
        	    match e1', e2' with
        	    | StartOf lv1, StartOf lv2
        	    | StartOf lv1, Lval lv2
        	    | Lval lv1, StartOf lv2
        	    | Lval lv1, Lval lv2 ->
            		if modify then
            		    let state = addLessEq state zeroLv Int64.zero lv1 VCV in
            		    (true, addLessEq state zeroLv Int64.zero lv2 VCV)
                    else if (ineqHolds state zeroLv Int64.zero lv1 VCV) &&
                            (ineqHolds state zeroLv Int64.zero lv2 VCV) then
                        (true, state)
                    else begin
                        if !debug then
                            log "doExpLeq: in state %a\ncan't prove %a >= 0"
                                d_state state DCE.Can.d_t cdiff;
                            (false, state)
                    end
                | _, _ -> begin
                    if !debug then
                        log "doExpLeq: bad form2: %a"
                            DCE.Can.d_t cdiff;
                        (false, state)
                end
            (* If f1 < 0, then check f2*e2 >= -f1*e1 - c *)
            (* If f2 < 0, then check f1*e1 >= -f2*e2 - c *)
            (* If both, then check c >= -f1*e1 + -f2*e2 *)
            else begin
                match e1', e2' with
                | StartOf lv1, StartOf lv2
                | StartOf lv1, Lval lv2
                | Lval lv1, StartOf lv2
                | Lval lv1, Lval lv2 -> begin
                    if (Int64.abs f1) = (Int64.abs f2) &&
                        Int64.rem (Int64.abs cdiff.DCE.Can.ct) (Int64.abs f1) = Int64.zero
                    then
                        let c = Int64.div cdiff.DCE.Can.ct (Int64.abs f1) in
                        let f1 = Int64.div f1 (Int64.abs f1) in
                        (*let f2 = f2 / (abs f2) in*)
                        if f1 < Int64.zero && f2 > Int64.zero then
                            if modify then
                                (true, addLessEq state lv1 (Int64.neg c) lv2 VCV)
                            else if ineqHolds state lv1 (Int64.neg c) lv2 VCV then
                                (true, state)
                            else begin
                                if !debug then
                                    log "doExpLeq: in state %a\ncan't prove %a >= 0"
                                        d_state state DCE.Can.d_t cdiff;
                                (false, state)
                            end
                        else if f2 < Int64.zero && f1 > Int64.zero then (* f2 < 0 *)
                            if modify then
                                (true, addLessEq state lv2 (Int64.neg c) lv1 VCV) 
                            else if ineqHolds state lv2 (Int64.neg c) lv1 VCV then
                                (true, state)
                            else begin
                                if !debug then
                                    log "doExpLeq: in state %a\ncan't prove %a >= 0"
                                        d_state state DCE.Can.d_t cdiff;
                                (false, state)
                            end
                        else if f1 < Int64.zero && f2 < Int64.zero then
                            if modify then
                                (true, addLessEq state lv1 c lv2 VVC)
                            else if ineqHolds state lv1 c lv2 VVC ||
                                    ineqHolds state lv2 c lv1 VVC then
                                (true, state)
                            else begin
                                if !debug then
                                    log "doExpLeq: in state %a\ncan't prove %a >= 0"
                                        d_state state DCE.Can.d_t cdiff;
                                (false, state)
                            end
                        else begin
                            if !debug then
                                log "doExpLeq: bad coefs: %a"
                                    DCE.Can.d_t cdiff;
                            (false, state)
                        end
                    else begin
                        if !debug then
                            log "doExpLeq: bad coefs: %a"
                                DCE.Can.d_t cdiff;
                            (false, state)
                    end
                end
                | _, _ -> begin
                    if !debug then
                        log "doExpLeq: bad form3: %a"
                            DCE.Can.d_t cdiff;
                    (false, state)
                end
            end
        end
        | _ -> begin (false, state)
(*
            match upperBoundCE state ce2, modify with
            | Some c, true ->
                doExpLeq ~modify:modify e1 (biginteger c) state
            | _, _ -> begin
                if !debug then
                    log "doExpLeq: Too Many: %a"
                        DCE.Can.d_t cdiff;
                (false, state)
            end
*)
        end
    end

(* Check that e1 <= e2 in state "state"
 *   fst(doExpLeq false e1 e2 s) is true if e1 <= e2 can be proved
 *   snd(doExpLeq true e1 e2 s) is the state with e1 <= e2 added.
 *   fst(doExpLeq true e1 e2 s) is false if the state couldn't be updated.
 *
 *)
and doExpLeq ?(modify:bool=false) 
              (e1 : exp)
              (e2 : exp)
              (state : absState) 
              : bool * absState 
    =
    let ce1 = DCE.canonExp Int64.one e1 in
    let ce2 = DCE.canonExp Int64.one e2 in
    let cdiff = DCE.Can.sub ce2 ce1 ILong in
    let cdiff =
        if modify then cdiff else
        let nozeroes = List.filter (isNonZeroInState state) cdiff.DCE.Can.cf in
        {cdiff with DCE.Can.cf = nozeroes}
    in
    if modify && !debug then
    	log "doExpLeq: adding %a <= %a" DCE.Can.d_t ce1 DCE.Can.d_t ce2
    else if !debug then
        log "doExpLeq: checking if %a <= %a" DCE.Can.d_t ce1 DCE.Can.d_t ce2;
    let (b, s) = cePosInState modify state cdiff in
    if b then (b,s) else
        (* The inequality could not be proved or added.
         * If we're doing a modify, use an upper bound on e2.
         * If we're doing a check, use an upper bound on e1
         *)
    if modify then begin
        let ce2 = upperBoundCESum state ce2 in
        let cdiff = DCE.Can.sub ce2 ce1 ILong in
        if !debug then
            log "doExpLeq: failed. now trying to add %a <= %a"
                DCE.Can.d_t ce1 DCE.Can.d_t ce2;
        cePosInState modify state cdiff
    end else begin
        let ce1 = upperBoundCEAtom state ce1 in
        let cdiff = DCE.Can.sub ce2 ce1 ILong in
        let nonzeroes = List.filter (isNonZeroInState state) cdiff.DCE.Can.cf in
        let cdiff = {cdiff with DCE.Can.cf = nonzeroes} in
        if !debug then 
            log "doExpLeq: failed. now checking if %a <= %a"
                DCE.Can.d_t ce1 DCE.Can.d_t ce2;
        cePosInState modify state cdiff
    end


(* return true if we know that the expression is zero.
   false is the safe answer *)
and isZeroInState (state : absState) (e : exp) : bool =
    let bigone = Const(CInt64(Int64.of_int 1,IULongLong,None)) in
    match e with
    | Const _ when DCE.canonCompareExp e zero -> true
    | Lval lv -> isLvalZero state lv
    | UnOp(Neg,e,t) -> isZeroInState state e
    | BinOp((PlusA|PlusPI|IndexPI),e1,e2,t) ->
        isZeroInState state e1 &&
        isZeroInState state e2
    | BinOp((MinusA|MinusPI|MinusPP),e1,e2,t) ->
        fst(doExpLeq e1 e2 state) &&
        fst(doExpLeq e2 e1 state)
    | BinOp(Mult,e1,e2,t) ->
        isZeroInState state e1 ||
        isZeroInState state e2
    | BinOp(Div,e1,e2,t) ->
        isZeroInState state e1
    | BinOp(Shiftlt,e1,e2,t) ->
        isZeroInState state e1
    | BinOp(Shiftrt,e1,e2,t) when not(isSignedType t) ->
        isZeroInState state e1 ||
        fst(doExpLeq e1 (constFold true (BinOp(Shiftlt,bigone,e2,t))) state)
    | BinOp(BAnd,e1,e2,t) ->
        isZeroInState state e1 ||
        isZeroInState state e2
    | BinOp(BXor,e1,e2,t) ->
        fst(doExpLeq e1 e2 state) &&
        fst(doExpLeq e2 e1 state)
    | BinOp(BOr,e1,e2,t) ->
        isZeroInState state e1 &&
        isZeroInState state e2
    | CastE(t,e) -> isZeroInState state e
    | _ -> false

and isNonZeroInState (state : absState) (fe : int64 * exp) : bool =
    not(isZeroInState state (snd fe))




(* FIXME: use the sign info!  E.g. add e1 >= 0 *)
let doLessEq a (e1: exp) (e2:exp) ~(signed:bool): absState = 
  if !debug then log "Guard %a <= %a.\n" dx_exp e1 dx_exp e2;
  try
    let t1 = typeOf e1 in
    let t2 = typeOf e2 in
    let lv1, c1 = expToIntSum e1 in
    let lv2, c2 = expToIntSum e2 in
    (* if t1 is unsigned or pointer, then add zeroLv + 0 <= lv1 *)
    let a =
      match t1 with
      | TInt(ku,_) -> addLessEq a zeroLv (~-% c1) lv1 VCV
      | TPtr(_,_) -> addLessEq a zeroLv (~-% c1) lv1 VCV
      | _ -> a
    in
    let a =
      match t2 with
      | TInt(ku,_) -> addLessEq a zeroLv (~-% c2) lv2 VCV
      | TPtr(_,_) -> addLessEq a zeroLv (~-% c2) lv2 VCV
      | _ -> a
    in
    (*addLessEq a lv1 (c1 -% c2) lv2*)
    snd(doExpLeq ~modify:true e1 e2 a)
  with CantDecompose ->
    snd(doExpLeq ~modify:true e1 e2 a)


let doLess a (e1: exp) (e2:exp) ~(signed:bool): absState = 
  if !debug then log "Guard %a < %a.\n" d_exp e1 d_exp e2; 
  try
    let t1 = typeOf e1 in
    let t2 = typeOf e2 in
    let lv1, c1 = expToIntSum e1 in
    let lv2, c2 = expToIntSum e2 in
    (* if t1 is unsigned or pointer, then add zeroLv + 0 <= lv1 *)
    let a =
      match t1 with
      | TInt(ku,_) when not(isSigned ku) -> addLessEq a zeroLv (~-% c1) lv1 VCV
      | TPtr(_,_) -> addLessEq a zeroLv (~-% c1) lv1 VCV
      | _ -> a
    in
    let a =
      match t2 with
      | TInt(ku,_) when not(isSigned ku) -> addLessEq a zeroLv (~-% c2) lv2 VCV
      | TPtr(_,_) -> addLessEq a zeroLv (~-% c2) lv2 VCV
      | _ -> a
    in
    (*addLessEq a lv1 (1L +% c1 -% c2) lv2*)
    let e' = BinOp(PlusPI,e1,one,typeOf e1) in
    snd(doExpLeq ~modify:true e' e2 a)
  with CantDecompose ->
  	let e' = BinOp(PlusPI,e1,one,typeOf e1) in
  	snd(doExpLeq ~modify:true e' e2 a)


(* Turn a conjunction into a list of conjuncts *)
let expToConjList (e:exp) : (exp list) =
  let rec helper e l =
    match e with
    | BinOp(LAnd, e1, e2, _) ->
	let l1 = helper e1 [] in
	let l2 = helper e2 [] in
	l@l1@l2
    | _ -> e::l
  in
  helper e []

let expToDisjList (e:exp) : (exp list) =
    let rec helper e l =
        match e with
        | BinOp(LOr, e1, e2, _) ->
            let l1 = helper e1 [] in
            let l2 = helper e2 [] in
            l@l1@l2
        | _ -> e::l
    in
    helper e []

class nonDisjEqTestFinderClass (b : bool ref) = object(self)
    inherit nopCilVisitor

    method vexpr (e  : exp) =
        match e with
        | BinOp(Eq,_,_,_) -> SkipChildren
        | BinOp(LOr,_,_,_) -> DoChildren
        | BinOp(_,_,_,_)
        | UnOp(_,_,_) ->
            b := true;
            SkipChildren
        | _ -> SkipChildren

end

let onlyDisjEqTests (e : exp) : bool =
    let br = ref false in
    ignore(visitCilExpr (new nonDisjEqTestFinderClass br) e);
    not(!br)

let mkAddablePred (p : exp) : (exp * int64) list =
    let djs = expToDisjList p in
    List.map (fun p -> match p with
        | BinOp(Eq,e1,e2,_) -> begin
            match isInteger e1, isInteger e2 with
            | None, Some i -> (e1,i)
            | Some i, None -> (e2,i)
            | _ -> (p,Int64.one) (* if onlyDisjEqTests p, then impossible *)
        end
        | _ -> (p,Int64.one)) (* if onlyDisjEqTests p, then impossible *)
        djs

let doOneBranch (a:absState) (e:exp) : absState =
  if !debug then
    log "Guard %a.\n" dx_exp e;
  let rec simplifyBoolExp e = 
    match stripNopCasts e with
      UnOp(LNot, UnOp(LNot, e, _), _) -> simplifyBoolExp e
    | BinOp(Ne, e, z, _) when isZero z -> simplifyBoolExp e
    | UnOp(LNot,BinOp(Ne,e1,e2,t),_) ->
        BinOp(Eq,e1,e2,t)
    | UnOp(LNot, BinOp(Eq, e, z, _), _) -> simplifyBoolExp e
    | UnOp(LNot, BinOp(Lt, e1, e2, t), _) ->
        BinOp(Ge, e1, e2, t)
    | UnOp(LNot, BinOp(Le, e1, e2, t), _) ->
        BinOp(Gt, e1, e2, t)
    | UnOp(LNot, BinOp(Gt, e1, e2, t), _) ->
        BinOp(Le, e1, e2, t)
    | UnOp(LNot, BinOp(Ge, e1, e2, t), _) ->
        BinOp(Lt, e1, e2, t)
    | e -> e
  in
  let e = simplifyBoolExp e in
  match e with
  | Lval lv -> begin
    let a = 
	    match lv with
	    | (Mem(Lval lvp), NoOffset) when isNullterm (typeOfLval lvp) ->
	        addCanIncrement a lvp Cil.one
        | _ -> a 
    in
    if isPointerType(typeOf e) then
	    addNonNull a lv
    else
	    a
  end
  | BinOp(Lt, e1, e2, t) when isIntOrPtrType (typeOf e1) ->
    let e1 = stripNopCasts e1 in
    let e2 = stripNopCasts e2 in
      doLess a e1 e2 ~signed:(isSignedType (typeOf e1))
  | BinOp(Le, e1, e2, t) when isIntOrPtrType (typeOf e1) ->
    let e1 = stripNopCasts e1 in
    let e2 = stripNopCasts e2 in
      doLessEq a e1 e2 ~signed:(isSignedType (typeOf e1))
  | BinOp(Gt, e1, e2, t) when isIntOrPtrType (typeOf e1) ->
    let e1 = stripNopCasts e1 in
    let e2 = stripNopCasts e2 in
      doLess a e2 e1 ~signed:(isSignedType (typeOf e1))
  | BinOp(Ge, e1, e2, t) when isIntOrPtrType (typeOf e1) ->
    let e1 = stripNopCasts e1 in
    let e2 = stripNopCasts e2 in
      doLessEq a e2 e1 ~signed:(isSignedType (typeOf e1))
  | e -> if onlyDisjEqTests e then addPred a (mkAddablePred e) else a

(* Update a state to reflect a branch *)
let doBranch (a:absState) (e:exp) : absState =
  if !debug then log "doBranch: for branch %a: state %a ->"
    d_exp e d_state a;
  let conjList = expToConjList e in
  let newstate = List.fold_left doOneBranch a conjList in
  if !debug then log "doBranch: result %a" d_state newstate;
  newstate

(* Add that 
 * lv >= e1 and
 * lv >= e2
 *)
let doMax a lv e1 e2 =
  let a' = doLessEq a e1 (Lval lv) ~signed:(isSignedType(typeOf e1)) in
  let a' = doLessEq a' e2 (Lval lv) ~signed:(isSignedType(typeOf e2)) in
  a'


(* Update a state to reflect a check *)
let processCheck a (c:check) : absState =
  match c with
    CNonNull e -> doBranch a e 
  | CLeq(e1, e2, _) -> doLessEq a e1 e2 ~signed:false
  | CLeqInt(e1, e2, _) -> doLessEq a e1 e2 ~signed:false
  | CPtrArith(lo, hi, p, e, _) ->
      let e' = BinOp(PlusPI,p,e,typeOf p) in
      (*let a = doLessEq a e' (kinteger64 IUInt (maxUnsignedInt(typeOf e'))) ~signed:false in*)
      let a = doLessEq a lo e' ~signed:false in
      doLessEq a e' hi ~signed:false
  | CPtrArithNT(lo, hi, p, e, _) ->
      let e' = BinOp(PlusPI,p,e,typeOf p) in
      (*let a = doLessEq a e' (kinteger64 IUInt (maxUnsignedInt(typeOf e'))) ~signed:false in*)
      let a = doLessEq a lo e' ~signed:false in
      a (* no upper bound *)
  | CPtrArithAccess(lo, hi, p, e, _) ->
      let e' = BinOp(PlusPI,p,e,typeOf p) in
      (*let a = doLessEq a e' (kinteger64 IUInt (maxUnsignedInt(typeOf e'))) ~signed:false in*)
      let a = doLessEq a lo e' ~signed: false in
      doLessEq a (BinOp(PlusPI,p,BinOp(PlusA,e,one,typeOf e),typeOf p)) hi ~signed:false
  | CSelected e -> doBranch a e
  | CNotSelected e -> doBranch a (UnOp(LNot,e,typeOf e))
  | _ -> a

(* Add to anext any relevant inequality information for the assignment
     dest := e     
*)
let doSet ~(aold:absState) ~(anext:absState) (dest: lval) (e:exp) : absState =
  if !debug then log "doSet: %a := %a\n" dx_lval dest dx_exp e;
  match isInteger (constFold true e) with
    Some i ->
      (* Add dest <= i and i <= dest *)
      let anext = addLessEq anext dest (~-% i) zeroLv VCV in
      let anext = addLessEq anext zeroLv i dest VCV in
      anext
  | None -> begin
      let anext = match e with
          Lval lv ->
            (* For each fact about lv in the old state,
               add an analogous fact about dest *)
            List.fold_left 
              (fun anext (lv1, e, _) -> 
                 if DCE.canonCompareLval lv1 lv then
                   addCanIncrement anext dest e
                 else
                   anext)
              anext
              aold.canIncrement
        | _ -> anext
      in
      try 
        let lvrhs, c = expToIntSum e in
        if c = 0L then begin
          (* The assignment is dest := lvrhs *)

          (* For each fact about lvrhs in the old state,
             add an analogous fact about dest *)
          List.fold_left 
            (fun anext (lv1, n, lv2, _, k) -> 
               let anext = if DCE.canonCompareLval lv1 lvrhs then
                 addLessEq anext dest n lv2 k
               else anext in
               let anext = if DCE.canonCompareLval lv2 lvrhs then
                 addLessEq anext lv1 n dest k
               else anext in
               anext)
            anext
            aold.ineqs
        end
        else begin
          (* The assignment is dest := lvrhs+c, where c is an int *)

          (* For each fact about lvrhs in the old state,
             add a fact about dest, after adjusting by c *)
          let anext =
          List.fold_left 
            (fun anext (z, n, lv2, _, k) -> 
               (* We have to be very conservative, because of
                  overflow.  If 0+n <= lvrhs AND lvrhs <= MAXINT-c,
                  then "dest := lvrhs+c" does not overflow, and we
                  get the new fact 0 + (n+c) <= dest *)
               if (z == zeroLv && DCE.canonCompareLval lv2 lvrhs) (*&& k = VCV*)
                 (* so far, 0+n <= lvrhs *)
                 && 
                 (ineqHolds aold lvrhs (c -% (maxUnsignedInt(typeOf e))) zeroLv VCV)
                 (* now lvrhs <= MAXINT-c.  To see this, note that the line
                    above tests lvrhs + c-MAXINT <= 0, i.e. lvrhs <= -(c-MAXINT)
                 *)
               then begin
                 if !debug then log "doSet: adding 0 + %Ld <= %a\n"
                        (n +% c) d_lval dest;
                 addLessEq anext zeroLv (n +% c) dest k
               end else if (DCE.canonCompareLval dest lvrhs) (* y = y + c *)
		   && (DCE.canonCompareLval dest lv2) (* z + n <= y *)
           (*&& k = VCV*)
		   && (ineqHolds aold dest (c -% (maxUnsignedInt(typeOf e))) zeroLv VCV)
		   (* y + c doesn't overflow *)
	       then
		 addLessEq anext z (n +% c) dest k
	       else if (DCE.canonCompareLval dest lvrhs) (* y = y + c *)
		   && (DCE.canonCompareLval dest z) (* y + n <= lv2 *)
           (*&& k = VCV*)
		   && (ineqHolds aold dest (c -% (maxUnsignedInt(typeOf e))) zeroLv VCV)
		   (* y + c doesn't overflow *)
	       then
		 addLessEq anext z (n -% c) lv2 k
	       else
                 anext)
            anext
            aold.ineqs
         in
         if !debug then log "doSet: result = %a\n" d_state anext;
         anext
        end
      with CantDecompose -> 
        anext
    end

let handleCall = P.handleCall (scrambleMem ~globalsToo:true)

let fdato : DPF.functionData option ref = ref None
let flowHandleInstr a i =
  if !debug then E.log "Doing instr %a in state %a\n" d_instr i d_state a;
  match instrToCheck i with
  | Some c -> processCheck a c
  | None -> begin
        match i with
    
        | Set (lh, e, _) when DCE.canonCompareExp (Lval lh) e -> a
        | Set ((Var vi, NoOffset) as dest, e, _) 
          when isPointerType vi.vtype -> begin
            let anext = scrambleVar a vi in
            let anext = if isNonNull a e then
              addNonNull anext dest
            else
              anext
            in
            doSet ~aold:a ~anext dest e
	    end
        | Set ((Var vi, _) as dest, e, _)-> 
            let anext = scrambleVar a vi in
	    let anext = if isNonNull a e then
	      addNonNull anext dest
	    else 
	      anext
	    in
            doSet ~aold:a ~anext dest e
        | Set ((Mem ee, _), _, _)-> 
	    (* FIXME: Is this sound? What if the address of a global is taken
	     * somewhere and then written through the pointer? *)
            scrambleMem a (Some ee)
        | Call (Some(Var vi, NoOffset), Lval (Var vf, NoOffset),
                [estr; bytes], _)
            when (vf.vname = "deputy_findnull") -> begin
              if not (isIntegralType vi.vtype) || not (isPointer estr) then
                E.s (bug "bad arg to %s\n" vf.vname);
              let a = scrambleVar a vi in
              addStringlen a vi estr
            end
        | Call (Some(Var vi, NoOffset), Lval (Var vf, NoOffset),
                [estr], _)
            when (vf.vname = "strlen") -> begin
              if not (isIntegralType vi.vtype) 
                || ((baseSize (typeOf estr)) <> 1) then
                  E.s (bug "bad arg to %s\n" vf.vname);
              let a = scrambleVar a vi in
              addStringlen a vi estr
            end
	    | Call (Some(Var vi, NoOffset), Lval(Var vf, NoOffset),[e1;e2], _)
	      when vf.vname = "deputy_max" -> begin
		  let a' = scrambleVar a vi in
		    doMax a' (Var vi, NoOffset) e1 e2
		end
        | Call (Some (Var vi, NoOffset), f, args, _) when isPointerType vi.vtype ->
	      let a = 
              if is_deputy_instr i || (!ignore_call) i then
                scrambleVar a vi
              else
                handleCall (!fdato) f args (scrambleVar a vi)
                (*scrambleMem ~globalsToo:true (scrambleVar a vi) None*)
          in
          let rt, _, _, _ = splitFunctionType (typeOf f) in
          if isNonnullType rt then
            addNonNull a (Var vi, NoOffset)
          else
            a
        | Call (Some lv, f, args, _) ->
            let a =
                match lv with
                | (Var vi, _) -> scrambleVar a vi
                | (Mem ee, _) -> scrambleMem a (Some ee)
            in
            if !ignore_call i || is_deputy_instr i then
                a
            else
                handleCall (!fdato) f args a
        | Call (_, f, args, _) ->
            if (!ignore_call) i then a else
            handleCall (!fdato) f args a
	        (*scrambleMem ~globalsToo:true a None*)
        | Asm (_, _, writes, _, _, _) -> 
            (* This is a quasi-sound handling of inline assembly *)
            let a = scrambleMem a None in
            List.fold_left (fun a (_,_,(lh,_)) -> 
              match lh with Var vi -> scrambleVar a vi
              | Mem _ -> a)
              a
              writes
  end


module Flow = struct
  let name = "DeputyOpt"
  let debug = debug
  type t = absState
  let copy x = x
  let stmtStartData = stateMap
  let pretty = d_state
  let computeFirstPredecessor s a = a

  let combinePredecessors s ~(old:t) newa = 
    let nnv = List.filter 
                (fun (lv,_) -> isNonNull' newa lv) 
                old.nonNullLvals
    in
    let sv = List.filter 
                (fun x -> List.mem x newa.strlenVars) 
                old.strlenVars
    in
    let ie = List.filter 
                (fun ((lv1, c, lv2, _, k) as x) -> 
                 (* Make sure newa contains something at least as strong as x *)
                   (List.memq x newa.ineqs) (* for performance *)
                   || (ineqHolds newa lv1 c lv2 k)) 
                old.ineqs
    in
    let ps = List.filter
               (fun dl -> hasPred newa (List.map (fun (e,i,_) -> (e,i)) dl))
               old.preds
    in
    let ci = List.filter 
                (fun x -> List.mem x newa.canIncrement) 
                old.canIncrement
    in
    if (List.length nnv <> List.length old.nonNullLvals) 
      || (List.length sv <> List.length old.strlenVars) 
      || (List.length ie <> List.length old.ineqs)
      || (List.length ps <> List.length old.preds)
      || (List.length ci <> List.length old.canIncrement) then
      Some {nonNullLvals = nnv; strlenVars = sv; ineqs = ie; preds = ps; canIncrement = ci}
    else
      None (* at fixed point *)

  let doInstr i a = 
(*     log "Visiting %a  State is %a.\n" dn_instr i d_state a; *)
    DF.Done (flowHandleInstr a i)

  let doStmt s a = 
    curStmt := s.sid;
    DF.SDefault

  let doGuard e a = 
    if isFalse a e then DF.GUnreachable
    else DF.GUse (doBranch a e)

  let filterStmt s = true
end

module FlowEngine = DF.ForwardsDataFlow (Flow)

(* a single term in a.preds precludes every case in djs *)
let predDisjNotSelected (a : absState) (djs : exp) =
    let djs = mkAddablePred djs in
    List.exists (fun adjs ->
        not(List.exists (fun (e,i,_) ->
            List.exists (fun (e',i') ->
                i = i' && DCE.canonCompareExp e e') djs) adjs)) a.preds

let flowOptimizeCheck (c: check) ((inState, acc):(absState * check list))
  : (absState * check list) =
  let isNonNull = isNonNull inState in
  (* Returns true if CPtrArith(lo, hi, p, Lval x, sz) can  be optimized away:*)
  let checkPtrArith lo hi p e : bool =
    let e' = BinOp(PlusPI,p,e,typeOf p) in
    (*(fst (doExpLeq e' (kinteger64 IUInt (maxUnsignedInt(typeOf e'))) inState)) &&*)
    (fst (doExpLeq lo e' inState)) &&
    (fst (doExpLeq e' hi inState))
  in
  (* Returns true if CPtrArithAccess(lo, hi, p, Lval x, sz) can  be optimized away:*)
  let checkPtrArithAccess lo hi p e : bool =
    let e' = BinOp(PlusPI,p,e,typeOf p) in
    (*(fst (doExpLeq e' (kinteger64 IUInt (maxUnsignedInt(typeOf e'))) inState)) &&*)
    (fst (doExpLeq lo e' inState)) &&
    (fst (doExpLeq (BinOp(PlusPI,p,BinOp(PlusA,e,one,typeOf e),typeOf p)) hi inState))
  in
  (* Returns true if CLeq(e1, e2) can  be optimized away:*)
  let checkLeq e1 e2 : bool =
    fst (doExpLeq e1 e2 inState)
  in

  (* doOpt is called recursivly if we simplify the check to a different check
     that has its own optimization rule. 
     It returns the simplified check, or None if we satisfied the check
     completely.*)
  let rec doOpt (c : check) : check option =
    match c with
    | CNonNull e1 when isNonNull e1 ->
        None
    | CNonNull e1 when isZero e1 ->
        error "non-null check will always fail.";
        Some c
    | CNullOrLeq (e1, _, _, why)
    | CNullOrLeqNT (e1, _, _, _, why) when isZero e1 ->
        None
    | CNullOrLeq (e1, e2, e3, why) when isNonNull e1 ->
        doOpt (CLeq(e2, e3, why))
    | CNullOrLeqNT (e1, e2, e3, e4, why) when isNonNull e1 ->
        let c' = CLeqNT(e2, e3, e4, why) in
        doOpt c'
    | CPtrArithAccess (lo, hi, p, e, sz) when checkPtrArithAccess lo hi p e ->
	None
    | CPtrArith (lo, hi, p, e, sz)
    | CPtrArithNT (lo, hi, p, e, sz) when checkPtrArith lo hi p e ->
        None
    | CPtrArithNT (_, _, Lval p, e, _) when canIncrement inState p e ->
        None
    | CLeq (e1, e2, _)
    | CNullOrLeq (_, e1, e2, _)
    | CNullOrLeqNT (_, e1, e2, _, _) when checkLeq e1 e2 ->
        None
    | CLeq(e1, e2, why) when isZero e2 && isNonNull e1 &&
                             not (isSignedType (typeOf e1)) ->
        deputyFail c;
        Some c
    | CEq (e1, e2, why, _) when isZero e2 && isNonNull e1 -> begin
        deputyFail c;
        Some c
    end
    | CLeqNT (e1, e2, sz, why) -> begin
        match hasStringlen inState e2 with
          Some len -> 
            let e2' = BinOp(PlusPI, e2, len, typeOf e2) in
            (* len == strlen(e2).  So rewrite the check as e1 <= e2+len *)
            (* This will often be optimized away completely
               by a later pass, since e1 often equals e2' *)
            doOpt (CLeq(e1, e2', why)) 
        | None -> Some c
      end
    | CLeqInt (e1, (BinOp (MinusPP, hi, p, _)), _) ->
        let e' = BinOp(PlusPI, p, e1, (typeOf p)) in
        if checkLeq e' hi then
          None
        else 
          Some c
    | CSelected e ->
        if onlyDisjEqTests e && hasPred inState (mkAddablePred e)
        then None
        else Some c
    | CNotSelected e ->
        if (onlyDisjEqTests e && predDisjNotSelected inState e)
        then None
        else Some c
    | _ -> Some c
  in
  let acc' = match doOpt c with
     Some c -> c::acc | None -> acc
  in
  (processCheck inState c), acc'


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


class flowOptimizeVisitor tryReverse = object (self)
  inherit nopCilVisitor

  val mutable curSid = -1

  method vstmt s =
    (* now that checks and instructions can be mixed,
     * the state has to be changed when an instruction is
     * visited *)
    let rec filterIl state il fl =
      match il with 
      | [] -> List.rev fl 
      | i::rest -> begin
        (* Make sure to update the location for checkToInstr's use. *)
        currentLoc := get_instrLoc i;
	let new_state = flowHandleInstr state i in
    if !debug then log "state after %a is %a\n" d_instr i d_state new_state;
	match instrToCheck i with
	| Some c -> begin
	    let _, c' = flowOptimizeCheck c (state,[]) in
	    match c' with
	    | [] -> begin
		if !debug then ignore(E.log "fOV: in state %a, optimized %a out\n" 
					d_state state d_instr i);
		     filterIl new_state rest fl
	    end
	    | [nc] -> begin
		let i' = checkToInstr nc in
		if !debug then ignore(E.log "fOV: changed to %a\n" d_instr i');
		filterIl new_state rest (i'::fl)
	    end
	    | _ -> begin
		if !debug then ignore(E.log "fOV: didn't remove %a\n" d_instr i);
		filterIl new_state rest (i::fl)
	    end
	end
	| None -> filterIl new_state rest (i::fl)
      end
    in
    begin
      try
        curSid <- s.sid;
        let state = IH.find stateMap s.sid in
        if !debug then
          E.log "Optimizing statement %a with state %a\n" d_stmt s d_state state;
        begin
          match s.skind with
          (* Don't remove explicit programmer checks. There might be
             special error handling
          | If(e, blk1, blk2, l) when isNonNull state e ->
              if hasALabel blk2 then 
                s.skind <- If(Cil.one, blk1, blk2, l)
              else
                (* blk2 is unreachable *)
                s.skind <- Block blk1
          | If(e, blk1, blk2, l) when isFalse state e ->
              if hasALabel blk1 then
                s.skind <- If(Cil.zero, blk1, blk2, l)
              else
                (* blk1 is unreachable *)
                s.skind <- Block blk2*)
	  | Instr il ->
	      if tryReverse then
		let il' = filterIl state il [] in
		let (pre, rst) = prefix is_check_instr il' in
		let il'' = filterIl state (List.rev pre) [] in
		s.skind <- Instr((List.rev il'')@rst)
	      else
		s.skind <- Instr(filterIl state il [])
          | _ -> ()
        end
      with Not_found -> () (* stmt is unreachable *)
    end;
    DoChildren

  method vfunc fd =
    curFunc := fd;
    let cleanup x = 
      curFunc := dummyFunDec; 
      x
    in
    ChangeDoChildrenPost (fd, cleanup)

end

let addNonNullLocals (fd : fundec) (a : absState) : absState =
    let nnls = List.filter (fun vi ->
        match vi.vtype with 
        | TArray _ -> true
        | _ -> false) fd.slocals
    in
    let nnlvals = List.map (fun vi ->
        let lv = (Var vi, NoOffset) in
        let refd = Dutil.varsOfExp (Lval lv) in
        (Var vi, NoOffset), refd) nnls
    in
    { a with nonNullLvals = nnlvals }

class switchFinderClass (br : bool ref) = object(self)
    inherit nopCilVisitor

    method vstmt (s : stmt) =
        match s.skind with
        | Switch _ ->
            br := true;
            SkipChildren
        | _ -> DoChildren

end

let funHasSwitch (fd : fundec) : bool =
    let br = ref false in
    ignore(visitCilFunction (new switchFinderClass br) fd);
    !br

class cSelectedFinderClass (br : bool ref) = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        match instrToCheck i with
        | Some(CNotSelected _)
        | Some(CSelected _) ->
            br := true;
            SkipChildren
        | _ -> DoChildren

end

let funHasCSelected (fd : fundec) : bool =
    let br = ref false in
    ignore(visitCilFunction (new cSelectedFinderClass br) fd);
    !br

(** flow-sensitive optimizer for nonnull, strlen, and inequalities*)
let doFlowAnalysis ?(tryReverse:bool=false)
                    (fd:fundec)
                    (fdat : DPF.functionData)
                    : unit
  =
  try
    IH.clear stateMap;
    if funHasSwitch fd && funHasCSelected fd then begin
        prepareCFG fd;
        Cfg.clearCFGinfo fd;
        ignore (Cfg.cfgFun fd)
    end;
    let fst = List.hd fd.sbody.bstmts in
    let t = addNonNullLocals fd top in
    let precs =
        match IH.tryfind fdat.DPF.fdPCHash fd.svar.vid with
        | None -> []
        | Some cl -> cl
    in
    let t = List.fold_left flowHandleInstr t precs in
    IH.add stateMap fst.sid t;
    FlowEngine.compute [fst];
    if !debug then
      E.log "%s: finished analysis; starting optimizations.\n" Flow.name;
    ignore (visitCilFunction (new flowOptimizeVisitor tryReverse) fd);
    IH.clear stateMap;
    curStmt := -1; 
    ()
  with Failure "hd" -> ()


class nonNullReturnCheckerClass (br : bool ref) = object(self)
    inherit nopCilVisitor
    
    method vstmt s =
        match s.skind with
        | Return(eo, _) -> begin
            match eo with
            | None -> begin
                br := false;
                SkipChildren
            end
            | Some e -> begin
                match IH.tryfind stateMap s.sid with
                | None -> begin
                    br := false;
                    SkipChildren
                end
                | Some state -> begin
                    br := (!br) && isNonNull state e;
                    DoChildren
                end
            end
        end
        | _ -> DoChildren
end


let isReturnNonNull (fvar : varinfo) (f : file) : bool =
  try
    let fdg = List.find (fun g -> match g with
        | GFun(fd, _ ) -> fd.svar.vname = fvar.vname
        | _ -> false) f.globals
    in
    match fdg with
    | GFun(fd, _) -> begin
        IH.clear stateMap;
        let fst = List.hd fd.sbody.bstmts in
        IH.add stateMap fst.sid top;
        FlowEngine.compute [fst];
        let br = ref true in
        ignore(visitCilFunction (new nonNullReturnCheckerClass br) fd);
        IH.clear stateMap;
        curStmt := -1; 
        !br
    end
    | _ -> false
  with 
  | Failure "hd" -> false
  | Not_found -> false



let reportStats () = ()
