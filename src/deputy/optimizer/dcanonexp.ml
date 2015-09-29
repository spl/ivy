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
 * dcanonexp.ml
 *
 * Canonicalizer for Cil expressions.
 *
 *)

open Cil
open Expcompare
open Pretty
open Ivyoptions
open Dutil
(*open Doptimutil*)
open Dattrs

module E = Errormsg

let rec canTypeOf (e: exp) : typ = 
  match e with
  | Const(CInt64 (_, ik, _)) -> TInt(ik, [])

    (* Character constants have type int.  ISO/IEC 9899:1999 (E),
     * section 6.4.4.4 [Character constants], paragraph 10, if you
     * don't believe me. *)
  | Const(CChr _) -> intType

    (* The type of a string is a pointer to characters ! The only case when 
     * you would want it to be an array is as an argument to sizeof, but we 
     * have SizeOfStr for that *)
  | Const(CStr s) -> charPtrType

  | Const(CWStr s) -> TPtr(!wcharType,[])

  | Const(CReal (_, fk, _)) -> TFloat(fk, [])

  | Const(CEnum(_, _, ei)) -> TEnum(ei, [])

  | Lval(lv) -> canTypeOfLval lv
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> !typeOfSizeOf
  | AlignOf _ | AlignOfE _ -> !typeOfSizeOf
  | UnOp (_, _, t) -> t
  | BinOp (_, _, _, t) -> t
  | CastE (t, _) -> t
  | AddrOf (lv) -> TPtr(canTypeOfLval lv, [])
  | StartOf (lv) -> begin
      match unrollType (canTypeOfLval lv) with
        TArray (t,_, a) -> TPtr(t, a)
     | _ -> E.s (E.bug "canTypeOf: StartOf on a non-array")
  end

and canTypeOfInit (i: init) : typ = 
  match i with 
    SingleInit e -> canTypeOf e
  | CompoundInit (t, _) -> t

and canTypeOfLval = function
    Var vi, off -> canTypeOffset vi.vtype off
  | Mem addr, off -> begin
      match unrollType (canTypeOf addr) with
        TPtr (t, _)
      | TArray(t,_,_) -> canTypeOffset t off
      | _ -> E.s (bug "canTypeOfLval: Mem on a non-pointer (%a):%a" d_exp addr d_type (canTypeOf addr))
  end

and canTypeOffset basetyp =
  let blendAttributes baseAttrs =
    let (_, _, contageous) = 
      partitionAttributes ~default:(AttrName false) baseAttrs in
    typeAddAttributes contageous
  in
  function
    NoOffset -> basetyp
  | Index (_, o) -> begin
      match unrollType basetyp with
        TArray (t, _, baseAttrs) ->
	  let elementType = canTypeOffset t o in
	  blendAttributes baseAttrs elementType
      | t -> E.s (E.bug "canTypeOffset: Index on a non-array")
  end 
  | Field (fi, o) ->
      match unrollType basetyp with
        TComp (_, baseAttrs) ->
	  let fieldType = canTypeOffset fi.ftype o in
	  blendAttributes baseAttrs fieldType
      | _ -> E.s (bug "canTypeOffset: Field on a non-compound")

(** Keep expressions to be compared in a canonical form: a constant + sum of 
 * weighted expressions, where the latter are not something that can be 
 * broken in a canonical expression themselves. These atomic expressions will 
 * be compared for equality.  *)
module Can = struct
  type t = 
      { ct: int64;
        cf: (int64 * exp) list;
        ck: ikind;
      }
  let mkInt n ik = { ct = n; cf = []; ck = ik}
  let atomic (f: int64) (e: exp) (ik : ikind) =
    if f = Int64.zero then { ct = Int64.zero; cf = []; ck = ik } else
        { ct = Int64.zero; cf = [(f, e)]; ck = ik}

  let zero ik = mkInt Int64.zero ik
  let weightedAdd (w1: int64) (c1: t) (cacc: t) (rkind : ikind) =
    let truncate i = fst(truncateInteger64 rkind i) in
    let rec insert (w: int64) (e: exp) = function
        [] -> if w = Int64.zero then [] else [ (w, e) ]
      | (w', e') :: rest -> 
          if deputyCompareExp e e' then 
            let w'' = truncate (Int64.add w w') in 
            if w'' = Int64.zero then 
              rest
            else
              (w'', e') :: rest
          else begin
	      (*log "weightedAdd: %a != %a\n" d_plainexp e d_plainexp e';*)
            (w', e') :: insert w e rest
	  end
    in
    { ct = truncate(Int64.add (Int64.mul w1 c1.ct) cacc.ct);
      cf = List.fold_left (fun acc (w,e) -> insert (truncate (Int64.mul w1 w)) e acc) 
                          cacc.cf c1.cf;
      ck = rkind;
    }

  let add c1 c2 ik = weightedAdd Int64.one c1 c2 ik 
  let sub c1 c2 ik = weightedAdd Int64.minus_one c2 c1 ik
  let mult c n  ik = weightedAdd n c (zero c.ck) ik

  (* do not use *)
  let addConst cnst ik c =
    let ct,cnst,rkind = convertInts c.ct c.ck cnst ik in
    { c with ct = fst(truncateInteger64 rkind (Int64.add cnst c.ct))}

  let d_t () c =
    if c.cf = [] then 
      num64 c.ct
    else begin
      dprintf "%a%a" 
        insert
        (if c.ct = Int64.zero then nil else (d_int64 c.ct))
        (docList ~sep:nil
           (fun (w, e) -> 
             dprintf "%a%a" 
               insert
               (if w = Int64.one then chr '+' 
               else if w = Int64.minus_one then chr '-'
               else 
                 (if w > Int64.zero then chr '+' else nil) ++ 
                   dprintf "%s*" (Int64.to_string w))
               d_exp e))
        c.cf
    end

  type sign = Pos | Neg | Zero | DontKnow

  (* t -> sign *)
  let getSign c =
    let getTermSign (f, e) =
        if f > Int64.zero && not(isSignedType(canTypeOf e))
        then Pos
        else DontKnow
    in
    let cfs = List.map getTermSign c.cf in
    try
        let s = List.fold_left (fun s s' -> 
            match s, s' with
            | Pos, Pos -> Pos
            | Neg, Neg -> Neg
            | _, _ -> DontKnow) (List.hd cfs) cfs
        in
        if s = Pos && c.ct >= Int64.zero then
            Pos
        else if s = Neg && c.ct <= Int64.zero then
            Neg
        else
            DontKnow
    with Failure "hd" -> 
        if c.ct > Int64.zero then 
            Pos 
        else if c.ct < Int64.zero then
            Neg
        else
            Zero

end

(** The arithmetic factor for a base type *)
let arithFactor (t: typ) : int64 = 
  match unrollType t with 
  | TPtr (bt, _)  -> Int64.of_int(bitsSizeOf bt / 8)
  | _ -> Int64.one



(* Convert lh[x] to *(lh + x)
 * Convert &lh[x] to (lh + x)
 *)
let rec canonMemAccess (e : exp) : exp =
    let canonLh (lh : lhost) : lhost =
        match lh with
        | Mem e -> Mem(canonMemAccess e)
        | _ -> lh
    in
    let rec canonOff (off : offset) : offset =
        match off with
        | Index(e, off) -> Index(canonMemAccess e, canonOff off)
        | Field(fi, off) -> Field(fi, canonOff off)
        | NoOffset -> NoOffset
    in
    match e with
    | Lval(lh,Index(e,off))
    | StartOf(lh,Index(e,off)) ->
        let base = StartOf(lh,NoOffset) in
        canonMemAccess (Lval(Mem(BinOp(PlusPI,base,e,canTypeOf base)), off))
    | Lval(lh,off) -> Lval(canonLh lh, canonOff off)
    | StartOf(lh,off) -> StartOf(canonLh lh, canonOff off)
    (* &A[x] -> (A + x) *)
    | AddrOf(lh, off) -> begin
        let rec splitOffset off =
    	    match off with
        	| NoOffset -> NoOffset, NoOffset
    	    | Field(fi, off') ->
    	        let flds, idx = splitOffset off' in
    	        Field(fi, flds), idx
            | Index(e, NoOffset) ->
                NoOffset, Index(e, NoOffset)
    	    | Index(e, off') ->
                let flds, idx = splitOffset off' in
                Index(e,flds), idx
        in
        let (flds, indx) = splitOffset off in
        match indx with
        | Index(e, NoOffset) -> begin
            let base = StartOf(lh, flds) in
            canonMemAccess (BinOp(PlusPI, base, e, canTypeOf base))
        end
        | _ -> AddrOf(canonLh lh, canonOff off)
    end
    | UnOp(uop,e,t) -> UnOp(uop,canonMemAccess e,t)
    | BinOp(bop,e1,e2,t) ->
        BinOp(bop,canonMemAccess e1,canonMemAccess e2,t)
    | CastE(t,e) -> CastE(t,canonMemAccess e)
    | _ -> e

let findIkindSz (unsigned : bool) (sz : int) : ikind =
    (* Test the most common sizes first *)
    if sz = bytesSizeOfInt IInt then 
        if unsigned then IUInt else IInt 
    else if sz = bytesSizeOfInt ILong then 
        if unsigned then IULong else ILong
    else if sz = 1 then 
        if unsigned then IUChar else IChar 
    else if sz = bytesSizeOfInt IShort then
        if unsigned then IUShort else IShort
    else if sz = bytesSizeOfInt ILongLong then
        if unsigned then IULongLong else ILongLong
    else if unsigned then IULong else ILong

(* I need my own versions of isSignedType and typeOf because I need to use them
   after canonMemAccess, wchih breaks some invarients *)

let rec isSignedType (t:typ) : bool =
  match unrollType t with
  | TInt(ik,_) -> isSigned ik
  | TEnum _ -> true
  | TPtr _ -> false
  | TArray _ -> false
  | _ -> false



(** Convert an expression into a canonical expression *)
let rec canonExp (fact: int64) (e: exp) : Can.t =
  match e with 
  | Const (CInt64 (i, ik, _)) -> Can.mkInt (Int64.mul fact i) ik
  | BinOp ((PlusA|PlusPI|IndexPI), e1, e2, t) -> 
      begin
        try
          let facte2 : int64 = Int64.mul fact (arithFactor t) in
          let ik = findIkindSz (not(isSignedType t)) ((bitsSizeOf t)/8) in
          Can.add (canonExp fact e1) (canonExp facte2 e2) ik
        with SizeOfError _ ->
          (*log "canonExp: isSignedType Plus (%a)" d_type t;*)
          let ik = findIkindSz (not(isSignedType t)) ((bitsSizeOf t)/8) in
          Can.atomic fact e ik
      end

  | BinOp ((MinusA|MinusPI|MinusPP), e1, e2, t) -> 
      begin
        try
          let facte2 : int64 = Int64.mul fact (arithFactor t) in
          let ik = findIkindSz (not(isSignedType t)) ((bitsSizeOf t)/8) in
          Can.add (canonExp fact e1) (canonExp (Int64.neg facte2) e2) ik
        with SizeOfError _ ->
          (*log "canonExp: isSignedType Minus (%a)" d_type t;*)
          let ik = findIkindSz (not(isSignedType t)) ((bitsSizeOf t)/8) in
          Can.atomic fact e ik
      end

  | BinOp (Div, BinOp(Mult, e1, e2, tm), e3, td) ->
      if deputyCompareExp e2 e3 then
        canonExp fact e1
      else begin
        (*log "canonExp: isSignedType DivMult (%a)" d_type td;*)
        let ik = findIkindSz (not(isSignedType td)) ((bitsSizeOf td)/8) in
        Can.atomic fact e ik
      end

  | CastE _  -> begin
      let ep = stripNopCasts e in
      if not(Util.equals e ep) then begin
        let ce = canonExp fact ep in
        (*ignore(E.log "canonExp: stripped casts: %a -> %a\n"
            d_plainexp e Can.d_t ce);*)
        ce
      end else begin
        (*log "canonExp: isSignedType CastE (%a)" d_type (canTypeOf ep);*)
        let ik = findIkindSz (not(isSignedType(canTypeOf ep))) ((bitsSizeOf(canTypeOf ep))/8) in
        let ce = Can.atomic fact ep ik in
        (*ignore(E.log "canonExp: cast left: %a\n"
            d_plainexp e);*)
        ce
      end
  end

  (* Let's not distinguish between A[x] and *(A + x) *)
(*
  | Lval(lh, Index(e, off))
  | StartOf(lh, Index(e, off)) -> begin
      let base = StartOf(lh, NoOffset) in
      Can.atomic fact (Lval(Mem(BinOp(PlusPI, base, e, typeOf base)), off))
  end
*)
  (* &A[x] -> (A + x) *)
(*
  | AddrOf(lh, off) -> begin
    let rec splitOffset off =
	    match off with
    	| NoOffset -> NoOffset, NoOffset
	    | Field(fi, off') ->
	        let flds, idx = splitOffset off' in
	        Field(fi, flds), idx
        | Index(e, NoOffset) ->
            NoOffset, Index(e, NoOffset)
	    | Index(e, off') ->
            let flds, idx = splitOffset off' in
            Index(e,flds), idx
    in
    let (flds, indx) = splitOffset off in
    match indx with
    | Index(e, NoOffset) -> begin
        let base = StartOf(lh, flds) in
        canonExp fact (BinOp(PlusPI, base, e, typeOf base))
    end
    | _ -> Can.atomic fact e
  end
*)
  | _ ->
    (*log "canonExp: %a isSignedType _ (%a)" d_exp e d_type (canTypeOf e);*)
    Can.atomic fact e (findIkindSz (not(isSignedType(canTypeOf e)))
                      ((bitsSizeOf(canTypeOf e))/8))


let canonExp (fact: int64) (e: exp) : Can.t = 
  let e = constFold true e in (* Apply constant folding first *)
  let e = canonMemAccess e in (* Canonicalize memory access *)
  if false then begin
    ignore (log "canonicalizing %a\n" d_exp e);
    let res = canonExp fact e in 
    ignore (log "canonExp(%a) = %a\n" d_exp e Can.d_t res);
    res
  end else
    canonExp fact e

let canonCompareExp (e1 : exp) (e2 : exp) : bool =
    let dce1 = canonExp Int64.one e1 in
    let dce2 = canonExp Int64.one e2 in
    let diff = Can.sub dce1 dce2 ILong in
    diff.Can.ct = Int64.zero && diff.Can.cf = []

let canonCompareLval (lv1 : lval) (lv2 : lval) : bool =
    let dce1 = canonExp Int64.one (Lval lv1) in
    let dce2 = canonExp Int64.one (Lval lv2) in
    let diff = Can.sub dce1 dce2 ILong in
    diff.Can.ct = Int64.zero && diff.Can.cf = []
