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
open Ivyoptions
(*open Dattrs*)
open Expcompare

module E = Errormsg
module GA = GrowArray
module H = Hashtbl

let curFunc : fundec ref = ref dummyFunDec
let curStmt : int ref = ref (-1)

(**************************************************************************)
(* Error/log messages *)

type 'a myformat = ('a, unit, doc, unit) format4

let warningQueue : (location * string) list ref = ref []
let errorQueue : (location * string) list ref = ref []

let outputQueue (queue: (location * string) list) : unit =
  let compareMsgs (l1, s1) (l2, s2) =
    let fileResult = compare l1.file l2.file in
    if fileResult != 0 then
      fileResult
    else
      let lineResult = compare l1.line l2.line in
      if lineResult != 0 then
        lineResult
      else
        compare s1 s2
  in
  let sorted = List.sort compareMsgs queue in
  let unique =
    List.fold_right
      (fun msg acc ->
         try
           if msg = List.hd acc then acc else msg :: acc
         with Failure "hd" ->
           msg :: acc)
      sorted []
  in
  List.iter (fun (l, s) -> ignore (eprintf "%a: %s" d_loc l s)) unique;
  flush !E.logChannel

let outputAll () : unit =
  outputQueue !warningQueue;
  outputQueue !errorQueue

let output (isError: bool) (label: string) (coda: string) (msg: doc) : unit =
  if isError then E.hadErrors := true;
  let d = if coda = "" then 
    dprintf "%s%a@!" label insert msg
  else
    dprintf "%s%a@!%s@!" label insert msg coda 
  in
  (* We output log messages immediately; all others are delayed for sorting. *)
  if label = "" then begin
    ignore (eprintf "%a: %a" d_loc !currentLoc insert d);
    flush !E.logChannel
  end else begin
    let item = (!currentLoc, sprint 1000000 d) in
    if isError then
      errorQueue := item :: !errorQueue
    else
      warningQueue := item :: !warningQueue
  end

let bug (fmt: 'a myformat) : 'a = 
  let coda = "Please tell the Deputy team about this error.\n" in
  Pretty.gprintf (output true "Internal error: " coda) fmt

let error (fmt: 'a myformat) : 'a = 
  Pretty.gprintf (output true "Error: " "") fmt

let unimp (fmt: 'a myformat) : 'a = 
  Pretty.gprintf (output true "Unimplemented: " "") fmt

let warn (fmt: 'a myformat) : 'a = 
  Pretty.gprintf (output false "Warning: " "") fmt

let log (fmt: 'a myformat) : 'a = 
  Pretty.gprintf (output false "" "") fmt

let errorwarn (fmt: 'a myformat) : 'a = 
  let f d =
    if !trustAll then
      warn "%a" insert d
    else
      error "%a" insert d
  in
  Pretty.gprintf f fmt

(**************************************************************************)
(* Miscellaneous utility functions *)

let isPointer (e: exp) : bool =
  isPointerType (typeOf e)

let isPtrOrArray (t: typ) : bool =
  match unrollType t with
  | TPtr (bt, _)
  | TArray (bt, _, _) -> true
  | _ -> false

let isUnionType (t: typ) : bool =
  match unrollType t with
  | TComp (ci, _) when not ci.cstruct -> true
  | _ -> false

let isOpenArray (t: typ) : bool =
  match unrollType t with
  | TArray (_, None, _) -> true
  | TArray (_, Some e, _) -> isZero e
  | _ -> false

let isOpenArrayComp (t: typ) : bool =
  match unrollType t with
  | TComp (ci, _) when List.length ci.cfields > 0 ->
      let last = List.nth ci.cfields (List.length ci.cfields - 1) in
      isOpenArray last.ftype
  | _ -> false

let rec typeContainsPointers (t: typ) : bool =
  match t with
  | TPtr _
  | TFun _
  | TBuiltin_va_list _ -> true
  | TVoid _
  | TInt _
  | TFloat _
  | TEnum _ -> false
  | TArray (bt, _, _) -> typeContainsPointers bt
  | TNamed (ti, _) -> typeContainsPointers ti.ttype
  | TComp (ci, _) ->
      not ci.cdefined  (* If we don't know the contents of the struct,
                          conservatively assume it has pointers. *)
      ||
      (List.exists typeContainsPointers
         (List.map (fun fld -> fld.ftype) ci.cfields))

(** We test if a value of the given type contains as an element a pointer or 
 * a nullterminated array. This is used to decide whether to initialize with 
 * 0 an element *)
let typeContainsPtrOrNullterm (t: typ) : bool = 
  existsType 
    (function 
        TPtr _ -> ExistsTrue
      | TBuiltin_va_list _ -> ExistsTrue
      | TComp (ci, _) when not ci.cdefined -> ExistsTrue  (* be conservative *)
      | TArray (_, _, a) when hasAttribute "nullterm" a -> ExistsTrue
      | _ -> ExistsMaybe)
    t
          
(* Is this an undefined struct? *)
let isAbstractType (t: typ) : bool =
  match unrollType t with
    | TComp (ci, _) when ci.cstruct && not ci.cdefined -> true
    | _ -> false

(* Is this a pointer to an undefined struct? *)
let isAbstractPtr (t: typ) : bool =
  match unrollType t with
    | TPtr(bt, _) -> isAbstractType bt
    | _ -> false

(* Return the base type of a pointer or array*)
let baseType (where: string) (t: typ) : typ =
  match unrollType t with
  | TPtr (bt, _)
  | TArray (bt, _, _) -> bt
  | TInt _ -> voidType (* Treat integer type like void*. *)
  | _ -> E.s (bug "Expected pointer/array type for %s, got %a" where d_type t)

(* Return the size of the base type of a pointer or array, in bytes *)
let baseSize (t: typ) : int=
  try
    bitsSizeOf (baseType "(sizeof base type)" t) / 8
  with
  | Cil.SizeOfError (s, _) -> E.s (bug "Computed size of %s" s)
  | e -> raise e

(* Be careful when converting int64 to int.  Int64.to_int
   treats 2^31 the same as 0 *)
let to_int (i: int64) : int = 
  let i': int = Int64.to_int i in (* i.e. i' = i mod 2^31 *)
  if i = Int64.of_int i' then i'
  else E.s (E.error "Int constant too large: %Ld" i)

(* Interpret this integer as a signed 32-bit number.  This means we'll
   convert 0xFFFFFFFF to -1 instead of 4294967295. *)
let to_signedint (i:int64) : int =
  let (<=%) = (fun x y -> (Int64.compare x y) <= 0) in
  if -0x80000000L <=% i && i <=% 0xffffffffL then begin
    (* If 0x80000000 <= i <= 0xFFFFFFFF, subtract 2^32 from i. *)
    if 0x80000000L <=% i then
      Int64.to_int (Int64.sub i 0x1_0000_0000L)
    else
      Int64.to_int i
  end
  else
    E.s (E.error "Int constant too large: %Ld" i)

(* Like iter, but passes an int indicating the current index in the list. *)
let iter_index (fn: 'a -> int -> unit) (a: 'a list) : unit =
  let rec helper a n =
    match a with
    | [] -> ()
    | a1 :: arest -> fn a1 n; helper arest (n + 1)
  in
  helper a 1

(* Like iter2, but passes an int indicating the current index in the lists. *)
let iter2_index (fn: 'a -> 'b -> int -> unit) (a: 'a list) (b: 'b list) : unit =
  let rec helper a b n =
    match a, b with
    | [], [] -> ()
    | a1 :: arest, b1 :: brest -> fn a1 b1 n; helper arest brest (n + 1)
    | _ -> raise (Invalid_argument "iter2index")
  in
  helper a b 1

(* Removes the last element of a list. *)
let rec remove_last (a: 'a list) : 'a list * 'a =
  match a with
  | [] -> raise (Failure "remove_last")
  | [x] -> [], x
  | x :: rest ->
      let y, last = remove_last rest in
      x :: y, last

(* Splits a list into two lists consisting of the first n elements
 * and the remainder. *)
let rec split (l: 'a list) (n: int) : 'a list * 'a list =
  match l with
  | elt :: rest when n > 0 ->
      let x, y = split rest (n - 1) in
      elt :: x, y
  | _ -> [], l



(**************************************************************************)

(* Return a list of vars referenced by an expression, and a boolean
 * saying whether memory is referenced.
 *
 * We remember whether the expressions that we track 
 * during optimization involve a memory reference, 
 * and what local vars they contain.  This makes it easier to kill facts. *)
type referenced = {
  varsRead: varinfo list;
  memRead: bool;
}

let varsOfExp (e:exp) : referenced =
  let readsVars = ref [] in
  let readsMem = ref false in
  let rec loop : exp -> unit = function
      BinOp(_, e1, e2, _) -> loop e1; loop e2
    | UnOp (_, e1, _) -> loop e1
    | CastE(_, e1) -> loop e1
    | Const _
    | SizeOf _ | SizeOfE _ | SizeOfStr _
    | AlignOf _ | AlignOfE _ -> ()
    | StartOf lv | AddrOf lv | Lval lv -> 
        let lh, off = lv in
        loopLh lh;
        loopOff off
  and loopLh: lhost -> unit =function
      Mem _ -> readsMem := true
    | Var vi -> if not (List.memq vi !readsVars) then
        readsVars := vi::!readsVars
  and loopOff: offset -> unit =function
      NoOffset -> ()
    | Field(_, off) -> loopOff off
    | Index(e, off) -> loop e; loopOff off
  in
  loop e;
  {varsRead = !readsVars; memRead = !readsMem}

let d_referenced () (r:referenced) : doc =
  dprintf "vars: %a.  mem: %s"
    (docList (fun vi -> text vi.vname)) r.varsRead
    (if r.memRead then "true" else "false")

(**************************************************************************)

let rec expRefersToVar (name: string) (e: exp) : bool =
  match e with
  | Lval lv -> lvalRefersToVar name lv
  | AddrOf lv -> lvalRefersToVar name lv
  | StartOf lv -> lvalRefersToVar name lv
  | SizeOfE e' -> expRefersToVar name e'
  | AlignOfE e' -> expRefersToVar name e'
  | UnOp (_, e', _) -> expRefersToVar name e'
  | BinOp (_, e1, e2, _) -> expRefersToVar name e1 || expRefersToVar name e2
  | CastE (_, e') -> expRefersToVar name e'
  | Const _
  | SizeOf _
  | SizeOfStr _
  | AlignOf _ -> false

and lvalRefersToVar (name: string) ((host, offset): lval) : bool =
  let rec offsetRefersToVar (offset: offset) =
    match offset with
    | Field (fld, offset') -> offsetRefersToVar offset'
    | Index (e, offset') -> expRefersToVar name e || offsetRefersToVar offset'
    | NoOffset -> false
  in
  match host with
  | Var vi -> vi.vname = name || offsetRefersToVar offset
  | Mem e -> expRefersToVar name e || offsetRefersToVar offset


(* CIL treats these functions specially and uses & in the arguments
   lists for its own reasons.*)
let isVarargOperator (f:exp) : bool =
  let varargOperators = [
    "__builtin_va_arg";
    "__builtin_stdarg_start";
    "__builtin_va_start";
    "__builtin_next_arg";
  ]
  in
  match f with
  | Lval(Var vi, NoOffset) -> List.mem vi.vname varargOperators
  | _ -> false

(* Is "size" the correct size of the given lval?
   We use this when checking calls to memset. *)
let isCorrectSizeOf (size: exp) (lv: lval) : bool =
  (* return true if size is an expression for the size of lv. *)
  let actualSize : int = (bitsSizeOf (typeOfLval lv)) / 8 in
  let size' : int64 option = isInteger (constFold true size) in
  size' = Some (Int64.of_int actualSize)


let memset: varinfo =
    (* Create a decl for "__deputy_memset". This is identical to memset,
       but we give it its own name to avoid conflicts. We add this to the file
       in dinfer. *)
    let memsetType = TFun(voidPtrType, Some [("p", voidPtrType, []);
                                             ("what", intType, []);
                                             ("sz", ulongType, [])],
                          false,
                          [Attr("dmemset", [AInt 1; AInt 2; AInt 3])]) in
    makeGlobalVar "__deputy_memset" memsetType

(******************************************************************************)
(* Expression comparison and cast stripping *)

(* Is this a signed comparison? *)
let rec isSignedType (t:typ) : bool =
  match unrollType t with
  | TInt(ik,_) -> isSigned ik
  | TEnum _ -> true
  | TPtr _ -> false
  | TArray _ -> false
  | _ -> E.s (bug "expecting an int or ptr in isSignedType, got %a" d_type t)

(* A complete list of Deputy attributes.  During postprocessing,
   we'll delete all of these attributes from the file so that the output is
   gcc-ready. *)
let isDeputyAttr (a:attribute): bool =
  match a with
    Attr(("bounds" | "fancybounds" | "nullterm" | "trusted" | "copytype"
         | "size" | "fancysize" | "ntexpand" | "ntdrop"
         | "when" | "fancywhen" | "sentinel" | "nonnull" | "hidden"
         | "dalloc" | "drealloc" | "dfree"
         | "dmemset" | "dmemcpy" | "dmemcmp" | "dvararg"
         | "tyvar" | "typaram"
         | "_ptrnode" | "missing_annot" | "assumeconst" | "Preconditions"
         | "blocking" | "noblocking" | "blockingunless" | "irq_restore"
         | "irq_save"
         | "Modifies" | "Taint" | "CTaint" | "ScanTaint"
         | "tainted" ), _) -> true
  | _ -> false


let hasDeputyAttr (t:typ): bool =
  List.exists isDeputyAttr (typeAttrs t)

let stripDepsFromType (t:typ) : typ =
  let t' = unrollType t in
  typeRemoveAttributes ["bounds"; "size"; "when"] t'


(* type signature w/o Deputy attrs *)
let typeSigNC (t : typ) : typsig =
    let attrFilter (a : attribute) =
        not(isDeputyAttr a)
    in
    typeSigWithAttrs ~ignoreSign:true (List.filter attrFilter) t


(* Two types are equal iff their typeSigs w/o Deputy attrs are equal *)
let deputyCompareTypes (t1 : typ) (t2 : typ) : bool =
    (typeSigNC t1) = (typeSigNC t2)


(* Checks that two types have the same non-Deputy attributes *)
let sameAttrs (t1 : typ) (t2 : typ) : bool =
    let a1 = typeSigAttrs (typeSigNC (unrollType t1)) in
    let a2 = typeSigAttrs (typeSigNC (unrollType t2)) in
    List.filter (fun a -> not(List.mem a a2)) a1 = [] &&
    List.filter (fun a -> not(List.mem a a1)) a2 = []


let rec findInnermostNonCast (e : exp) : exp =
    match e with
    | CastE(t, e) -> findInnermostNonCast e
    | _ -> e


(* Strip casts among pointers where the non-Deputy attributes are the same and
 * the size of the base types are the same.
 * Also, strip casts among integer types of equal bitwidth *)
let rec deputyStripCastsForPtrArith (e:exp): exp =
  if !debug then ignore(E.log "deputyStripCastsForPtrArith %a\n" d_exp e);
  match e with
  | CastE(t, e') (*when not(isTypeVolatile t)*) -> begin
      let e' = deputyStripCastsForPtrArith e' in
      match unrollType (typeOf e'), unrollType t with
      | TPtr (TVoid _, _), TPtr (bt2, _) when not (isVoidType bt2) ->
          CastE(t,e')
      | TPtr(bt1, a1), TPtr(bt2, a2) -> begin
          try
              if bitsSizeOf bt1 = bitsSizeOf bt2 &&
                 sameAttrs (typeOf e') t
              then e'
              else CastE(t,e')
          with SizeOfError _ -> CastE(t,e')
      end
      (* remove casts among integer types of equal bitwidth *)
      | (TInt _ as t1), (TInt _ as t2)
          when bitsSizeOf t1 = bitsSizeOf t2 ->
          if sameAttrs t1 t2 then e' else CastE(t, e')
      | (TPtr _ as t1), (TInt(ik,_) as t2)
          when bitsSizeOf t1 = bitsSizeOf t2 && not (isSigned ik) ->
          if sameAttrs t1 t2 then e' else CastE(t, e')
      | _, _ -> CastE(t, e')
  end
  | UnOp(op,e,t) -> 
      let e = deputyStripCastsForPtrArith e in
      UnOp(op, e, t)
  | BinOp(MinusPP,e1,e2,t) ->
      let e1 = deputyStripCastsForPtrArith e1 in
      let e2 = deputyStripCastsForPtrArith e2 in
      if not(compareTypesNoAttributes ~ignoreSign:false 
	       (typeOf e1) (typeOf e2))
      then BinOp(MinusPP, mkCast ~e:e1 ~newt:(typeOf e2), e2, t)
      else BinOp(MinusPP, e1, e2, t)
  | BinOp(op,e1,e2,t) ->
      let e1 = deputyStripCastsForPtrArith e1 in
      let e2 = deputyStripCastsForPtrArith e2 in
      BinOp(op,e1,e2,t)
  | Lval lv -> Lval(deputyStripCastsForPtrArithLval lv)
  | AddrOf lv -> AddrOf(deputyStripCastsForPtrArithLval lv)
  | StartOf lv -> StartOf(deputyStripCastsForPtrArithLval lv)
  | _ -> e


and deputyStripCastsForPtrArithLval (lv : lval) : lval =
  match lv with
  | (Var vi, off) -> (Var vi, deputyStripCastsForPtrArithOff off)
  | (Mem e, off) ->
      let e = deputyStripCastsForPtrArith e in
      let off = deputyStripCastsForPtrArithOff off in
      (Mem e, off)


and deputyStripCastsForPtrArithOff (off : offset ) : offset =
  match off with
  | NoOffset -> NoOffset
  | Field(fi, off) -> Field(fi, deputyStripCastsForPtrArithOff off)
  | Index(e, off) ->
      let e = deputyStripCastsForPtrArith e in
      let off = deputyStripCastsForPtrArithOff off in
      Index(e, off)


let rec deputyCompareExp (e1 : exp) (e2 : exp) : bool =
    if !debug then ignore(E.log "deputyCompareExp:\n\t%a =\n\t%a\n"
        d_plainexp e1 d_plainexp e2);
    e1 == e2 ||
    match e1, e2 with
    | (Lval lv1|StartOf lv1), (Lval lv2|StartOf lv2)
    (*| StartOf lv1, StartOf lv2*)
    | AddrOf lv1, AddrOf lv2 -> deputyCompareLval lv1 lv2
    | BinOp(op1, l1, r1, _), BinOp(op2, l2, r2, _) ->
        op1 = op2 && (deputyCompareExp l1 l2) && (deputyCompareExp r1 r2)
    | UnOp(op1, e1, _), UnOp(op2, e2, _) ->
        op1 = op2 && (deputyCompareExp e1 e2)
    | SizeOfE e1, SizeOfE e2
    | AlignOfE e1, AlignOfE e2 -> deputyCompareExp e1 e2
    | CastE(t1, e1), CastE(t2, e2) when deputyCompareTypes t1 t2 ->
        deputyCompareExp e1 e2
    | _, _ -> begin
        match isInteger (constFold true e1), isInteger (constFold true e2) with
        | Some i1, Some i2 -> i1 = i2
        | _ -> false
    end

and deputyCompareLval (lv1 : lval) (lv2 : lval) : bool =
  let rec compareOffset (off1: offset) (off2: offset) : bool =
    match off1, off2 with
    | Field (fld1, off1'), Field (fld2, off2') ->
        fld1 == fld2 && compareOffset off1' off2'
    | Index (e1, off1'), Index (e2, off2') ->
        deputyCompareExp e1 e2 && compareOffset off1' off2'
    | NoOffset, NoOffset -> true
    | _ -> false
  in
  if !debug then ignore(E.log "deputyCompareLval:\n\t%a = \n\t%a\n"
    d_lval lv1 d_lval lv2);
  lv1 == lv2 ||
  match lv1, lv2 with
  | (Var vi1, off1), (Var vi2, off2) ->
      vi1 == vi2 && compareOffset off1 off2
  | (Mem e1, off1), (Mem e2, off2) ->
      deputyCompareExp e1 e2 && compareOffset off1 off2
  | _ -> false


let deputyStripAndCompareExp (e1 : exp) (e2 : exp) : bool =
    if !debug then ignore(E.log "deputyStripAndCompareExp\n");
    let e1' = deputyStripCastsForPtrArith e1 in
    let e2' = deputyStripCastsForPtrArith e2 in
    let res = deputyCompareExp e1' e2' in
    if res then begin
        if !debug then ignore(E.log "%a -> %a == %a <- %a\n"
            d_plainexp e1 d_plainexp e1' d_plainexp e2' d_plainexp e2);
        res
    end else begin
        if !debug then ignore(E.log "%a -> %a != %a <- %a\n"
            d_plainexp e1 d_plainexp e1' d_plainexp e2' d_plainexp e2);
        res
    end


(*****************************************************************)
(* Count the lines containing trusted code. *)

(* programLocs is the set of lines where we do at least some checking.
   trustedLocs (a subset of programLocs) is the set of lines where we've 
     skipped some check.

   "check" here includes compile-time type checking in addition to the
   runtime checks.

   These counts are approximate.
 *)
let programLocs : (location, unit) H.t = H.create 50
let trustedLocs : (location, unit) H.t = H.create 50

(* Call this at each location that is checked.  Uses !currentLoc *)
let markLocationChecked () : unit =
  if !Ivyoptions.countTrustedLines && !currentLoc != locUnknown then
    H.replace programLocs !currentLoc ()

(* Call this at each location where a check was skipped due to TRUSTED *)
let markLocationTrusted () : unit =
  if !Ivyoptions.countTrustedLines && !currentLoc != locUnknown then begin
    H.replace trustedLocs !currentLoc ()
  end

let locationVisitor = object(self) 
  inherit nopCilVisitor
  method vstmt s =
    markLocationChecked ();
    markLocationTrusted ();
    DoChildren
  method vinst i =
    markLocationChecked ();
    markLocationTrusted ();
    SkipChildren
  method vexpr e = SkipChildren
  method vtype t = SkipChildren
end

let markTrustedBlock (b: block) : unit =
  if !Ivyoptions.countTrustedLines then
    ignore (visitCilBlock locationVisitor b)

let reportTrustedLines () : unit =
  assert(!Ivyoptions.countTrustedLines);
  currentLoc := locUnknown;
  begin
    (* Sanity check: is programLocs a superset of trustedLocs?  If not,
       then we aren't adding enough locations to programLocs. *)
    H.iter (fun l () ->
              if not (H.mem programLocs l) then
                bug "Location %a not in programLocs" d_loc l)
      trustedLocs
  end;
  let numLines = H.length programLocs in
  let trustedLines = H.length trustedLocs in
  E.log ("The file contains %d non-trivial lines, including %d lines that"^^
       " contain\n   a trusted operation.\n") numLines trustedLines;
  ()

(*********************************************************************)

(* Keyword in bounds attributes representing the current value *)
let thisKeyword = "__this"

(* Keyword in bounds attributes representing the automatic bounds *)
let autoKeyword = "__auto"

module IH = Inthash

(* remember complicated bounds expressions *)
let boundsTable : exp IH.t = IH.create 13
let boundsTableCtr : int ref = ref 0

(* expectedType is the type of the pointer that depends on this
   expression. We'll cast to this type so that pointer arithmetic works. *)
let addBoundsExp ~(expectedType:typ) (e: exp) : int =
  (* First, cast the bound expression e to the expected type *)
  let e': exp = 
    let boundType = typeOf e in
    if compareTypes ~ignoreSign:false boundType expectedType
      || isArrayType expectedType then
      (* no cast needed *)
      e
    else if (isPtrOrArray boundType) && (isPointerType expectedType) then
      begin
        let boundBase = baseType "addBoundsExp" boundType in
        let ptrBase = baseType "addBoundsExp" expectedType in
        if compareTypes ~ignoreSign:false boundBase ptrBase then
          (* no cast needed *)
          e 
        else if (   (not (typeContainsPointers boundBase)) 
                 && (not (typeContainsPointers ptrBase)))
          || (bitsSizeOf boundBase) = (bitsSizeOf ptrBase) then
            begin
              (* Cast the bound to the pointer's type *)
              mkCastT ~e:e ~oldt:boundType ~newt:expectedType
            end 
        else begin
          (* Maybe we should do this check in checkType? *)
          error "The base type of a pointer differs from the base type of its bound expressions.";
          e
        end
      end
    else begin
      (* Cast between an integer and a pointer.  Is it okay to use
         an int as the bound of a pointer? *)
      mkCastT ~e:e ~oldt:boundType ~newt:expectedType
    end
  in
  incr boundsTableCtr;
  if !verbose then
    E.log "%a:   fancybounds(%d) = %a.\n" d_loc !currentLoc
      !boundsTableCtr d_exp e';
  IH.add boundsTable !boundsTableCtr e';
  !boundsTableCtr

let getBoundsExp (n: int) : exp =
  try
    IH.find boundsTable n
  with Not_found ->
    E.s (bug "Couldn't look up expression in bounds table")

let clearBoundsTable () : unit =
  IH.clear boundsTable;
  boundsTableCtr := 0

type paramkind =
| PKNone
| PKThis
| PKOffset of attrparam

let rec checkParam (ap: attrparam) : paramkind =
  match ap with
  | ACons (name, []) when name = thisKeyword -> PKThis
  | ABinOp (PlusA, a1, a2) when checkParam a1 = PKThis ->
      if a2 = AInt 0 then PKThis else PKOffset a2
  | _ -> PKNone

class deputyPrinterClass ~(showBounds: bool) ~(enable: bool) : descriptiveCilPrinter =
object (self)
  inherit descriptiveCilPrinterClass enable as super

  method pExp () (e: exp) : doc =
    let truncate s =
      if String.length s > 40 then
        "\"" ^ String.sub s 0 36 ^ "\" ..."
      else
        "\"" ^ s ^ "\""
    in
    match e with
    | Const (CStr s) ->
        text (truncate (Escape.escape_string s))
    | Const (CWStr s) ->
        let s' =
          List.fold_left
            (fun acc elt ->
               let elt' =
                 if (elt >= Int64.zero &&
                     elt <= (Int64.of_int 255)) then 
                   Escape.escape_char (Char.chr (Int64.to_int elt))
                 else
                   Printf.sprintf "\\x%LX\" \"" elt
               in acc ^ elt')
            "" s
        in
        text ("L" ^ truncate s')
    | _ -> super#pExp () e

  method pAttr (Attr (an, args) : attribute) : doc * bool =
    match an, args with 
    | "fancybounds", [AInt i1; AInt i2] ->
        if showBounds then
          dprintf "BND(%a, %a)" self#pExp (getBoundsExp i1)
                                self#pExp (getBoundsExp i2), false
        else
          text "BND(...)", false
    | "bounds", [a1; a2] ->
        begin
          match checkParam a1, checkParam a2 with
          | PKThis, PKThis ->
              text "COUNT(0)", false
          | PKThis, PKOffset (AInt 1) ->
              text "SAFE", false
          | PKThis, PKOffset a ->
              if showBounds then
                dprintf "COUNT(%a)" self#pAttrParam a, false
              else
                text "COUNT(...)", false
          | _ ->
              if showBounds then
                dprintf "BND(%a, %a)" self#pAttrParam a1
                                      self#pAttrParam a2, false
              else
                text "BND(...)", false
        end
    | "fancysize", [AInt i] ->
        dprintf "SIZE(%a)" self#pExp (getBoundsExp i), false
    | "size", [a] ->
        dprintf "SIZE(%a)" self#pAttrParam a, false
    | "fancywhen", [AInt i] ->
        dprintf "WHEN(%a)" self#pExp (getBoundsExp i), false
    | "when", [a] ->
        dprintf "WHEN(%a)" self#pAttrParam a, false
    | "nullterm", [] ->
        text "NT", false
    | "assumeconst", [] ->
        text "ASSUMECONST", false
    | "trusted", [] ->
        text "TRUSTED", false
    | "copytype", [] ->
        text "COPYTYPE", false
    | "typaram", [ASizeOf t] ->
        dprintf "TP(%a)" (self#pType None) t, false
    | "sentinel", [] ->
        text "SNT", false
    | "nonnull", [] ->
        text "NONNULL", false
    | "dalloc", [a] ->
        dprintf "DALLOC(%a)" self#pAttrParam a, false
    | "dmemset", [AInt i1; AInt i2; AInt i3] ->
        dprintf "DMEMSET(%d, %d, %d)" i1 i2 i3, false
    | "dmemcpy", [AInt i1; AInt i2; AInt i3] ->
        dprintf "DMEMCPY(%d, %d, %d)" i1 i2 i3, false
    | "dmemcmp", [AInt i1; AInt i2; AInt i3] ->
        dprintf "DMEMCMP(%d, %d, %d)" i1 i2 i3, false
    | "_ptrnode", [AInt n] ->
        if !Ivyoptions.emitGraphDetailLevel >= 3 && showBounds then
          dprintf "NODE(%d)" n, false
        else
          nil, false
    | "missing_annot", _->  (* Don't bother printing thess *)
        nil, false
    | "ntdrop", [] ->
        text "NTDROP", false
    | ("always_inline" | "section" | "format" |
       "noreturn" | "regparm" | "aligned"), _ ->
        nil, false
    | _ ->
        super#pAttr (Attr (an, args))

  method pType (nameOpt: doc option) () (t: typ) : doc =
    match unrollType t with
    | TPtr (TVoid _, attrs) when hasAttribute "tyvar" attrs ->
        let name =
          match nameOpt with
          | Some name -> text " " ++ name
          | None -> nil
        in
        let tyvar =
          match filterAttributes "tyvar" attrs with
          | Attr ("tyvar", [ACons (s, [])]) :: _ -> s
          | _ -> E.s (bug "Unexpected attribute.")
        in
        dprintf "TV(%s)%a" tyvar insert name
    | _ ->
        super#pType nameOpt () t
end

let deputyFilePrinter = new deputyPrinterClass ~showBounds:true ~enable:false
let deputyPrinter = new deputyPrinterClass ~showBounds:true ~enable:true

let dx_type () (t: typ) : doc =
  deputyPrinter#pType None () t

let dx_exp () (e: exp) : doc =
  deputyPrinter#pExp () e

let dx_lval () (lv: lval) : doc =
  deputyPrinter#pLval () lv

let dx_instr () (i : instr) : doc =
  deputyPrinter#pInstr () i

let dx_global () (g : global) : doc =
  deputyPrinter#pGlobal () g

let dx_temps () : doc =
  deputyPrinter#pTemps ()

let startTemps () : unit =
  deputyPrinter#startTemps ()

let stopTemps () : unit =
  deputyPrinter#stopTemps ()

let deputyTypePrinter = new deputyPrinterClass ~showBounds:false ~enable:true

let dt_type () (t: typ) : doc =
  deputyTypePrinter#pType None () t

let dt_exp () (e: exp) : doc =
  deputyTypePrinter#pExp () e

let dt_lval () (lv: lval) : doc =
  deputyTypePrinter#pLval () lv

let dt_instr () (i : instr) : doc =
  deputyTypePrinter#pInstr () i

(** Terse printing: strip some casts from the expression. 
  We use this to make runtime errors more legible. *)
let dc_exp () e = 
  dx_exp () (deputyStripCastsForPtrArith e) 


let addTempInfoSet (vi: varinfo) (e: exp) : unit =
  vi.vdescr <- (dx_exp () e);
  vi.vdescrpure <- true

let addTempInfoCall (vi: varinfo) (fn: exp) (args: exp list) : unit =
  vi.vdescr <- (dprintf "%a(%a)" dx_exp fn
                  (docList ~sep:(text ", ") (dx_exp ())) args);
  vi.vdescrpure <- false

(* Don't print leading or trailing underscores on attributes *)
class deputyPatchPrinterClass : cilPrinter = object (self)
    inherit defaultCilPrinterClass as super

    method pAttr (a: attribute) : doc * bool =
        let (d, b) = super#pAttr a in
        let s = sprint ~width:1000 d in
        let s = if String.length s >= 2 &&
                   String.sub s 0 2 = "__"
                then String.sub s 2 ((String.length s) - 2)
                else s
        in
        let s = if String.length s >= 2 &&
                   String.sub s ((String.length s) - 2) 2 = "__"
                then String.sub s 0 ((String.length s) - 2)
                else s
        in
        text s, b
end

let deputyPatchPrinter = new deputyPatchPrinterClass

let dp_global () (g : global) : doc =
    printGlobal deputyPatchPrinter () g
