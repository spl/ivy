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
open Expcompare
open Pretty
open Dattrs
open Ivyoptions
open Dutil
open Dcheckdef
open Dpoly

module DO = Doptimmain
module E = Errormsg
module H = Hashtbl
module IH = Inthash
module S = Stats
module VS = Usedef.VS

module DPF = Dprecfinder
module DCE = Dcanonexp

(**************************************************************************)


let exemptLocalVars : varinfo list ref = ref []

(* Assign to each statement a unique ID. *)
let nextStmtId : int ref = ref 0
let assignID (s:stmt) : unit =
 (* Make sure that no one else has assigned ID numbers *)
  if !optLevel < 2 && s.sid <> -1 then
    E.s (bug "Stmt already has an sid: %a\n" d_stmt s);
  s.sid <- !nextStmtId;
  incr nextStmtId;
  ()

(* Convert instruction lists into individual statements, and give each
  stmt a unique id. *)
let rec fixStmt ?(giveID : bool = true) (s:stmt) : unit =
  if giveID then assignID s;
  match s.skind with 
    Instr [] -> ()
  | Instr [i] -> ()
  | Instr il -> (* Two or more instructions *)
      let sl = List.map mkStmtOneInstr il in
      List.iter fixStmt sl;
      s.skind <- Block (mkBlock sl);
      ()
  | If(_,b1,b2,_) ->
      fixBlock b1;
      fixBlock b2
  | Switch(_,b,_,_) ->
      fixBlock b
  | Loop(b,_,_,_) ->
      fixBlock b
  | Block b -> fixBlock b
  | TryFinally(b1,b2,_) ->
      fixBlock b1;
      fixBlock b2
  | TryExcept(b1,_,b2,_) ->
      fixBlock b1;
      fixBlock b2
  | _ -> ()

and fixBlock ?(giveID : bool = true) (b : block) : unit =
  List.iter (fixStmt ~giveID:giveID) b.bstmts

(* Calls typeOf on an expression, but adds type attributes in appropriate
 * cases.  This allows the checker to use typeOf in a context that expects
 * all types to be annotated. *)
let deputyTypeOf (e: exp) : typ =
  let t =
    match e with
    | AddrOf _ -> typeAddAttributes [safeAttr] (typeOf e)
    | Const (CStr _)
    | Const (CWStr _) -> typeAddAttributes stringAttrs (typeOf e)
    (* StartOf should correctly inherit the array's attributes,
       so we don't need to handle it specially. *)
    | _ -> typeOf e
  in
  if isPointerType t && not (hasAttribute "bounds" (typeAttrs t)) then
    E.s (bug "deputyTypeOf did not add attrs to %a at %a" dx_type t dx_exp e);
  t

let reportPolyFieldError (lv: lval) (fi: fieldinfo) : 'a =
  E.s (error ("Field \"%s\" has generic type, but its containing " ^^
              "structure has not been instantiated properly. " ^^
              "Use the TP(...) annotation on the structure's type.\n" ^^
              "  struct type: %a\n" ^^
              "   field type: %a\n" ^^
              "          exp: %a")
             fi.fname dx_type (TComp (fi.fcomp, []))
             dx_type fi.ftype dx_lval lv)

let reportPolyArgError (aname: string) (atype: typ) (arg: exp) : 'a =
  E.s (error ("Formal parameter \"%s\" has generic type, but an " ^^
              "appropriate instantiation could not be found.\n" ^^
              "  formal type: %a\n" ^^
              "     arg type: %a\n" ^^
              "          exp: %a")
             aname dx_type atype dx_type (typeOf arg) dx_exp arg)

let reportPolyRetError (fn: exp) : 'a =
  let ret =
    match typeOf fn with
    | TFun (ret, _, _, _) -> ret
    | _ -> E.s (bug "Expected function type.")
  in
  E.s (error ("Return type has generic type, but an appropriate " ^^
              "instantiation could not be found.\n" ^^
              "  ret type: %a\n" ^^
              "  function: %a")
             dx_type ret dx_exp fn)


(**************************************************************************)


(* Here we store extra instructions that have been inserted during the
 * checking process.  These instructions include both run-time checks
 * and actual code.  The allowChecks flag indicates whether checks should
 * be added at this time. *)
let allowChecks : bool ref = ref false
let extraInstrs = ref []

let startExtraInstrs () : unit =
  if !extraInstrs <> [] then
    E.s (bug "Extra instruction queue is not empty!")

let endExtraInstrs () : instr list =
  let extras = !extraInstrs in
  extraInstrs := [];
  List.rev extras

let addInstr (i: instr) : unit =
  extraInstrs := i :: !extraInstrs

let addTmpSet (e: exp) : varinfo =
  let tmp = makeTempVar !curFunc ~name:"__dset_tmp"
    (typeRemoveAttributes ["nonnull"] (deputyTypeOf e)) in
  addTempInfoSet tmp e;
  addInstr (Set (var tmp, e, !currentLoc));
  tmp

let addTmpCall (t: typ) (fn: exp) (args: exp list) : varinfo =
  (* TODO: Derive t from type of fn? *)
  let tmp = makeTempVar !curFunc ~name:"__dcall_tmp"
    (typeRemoveAttributes ["nonnull"; "warn_unused_result"] t) in
  addTempInfoCall tmp fn args;
  addInstr (Call (Some (var tmp), fn, args, !currentLoc));
  tmp

let addCheck (c: check) : unit =
  if !verbose then
    log "--> %a" dn_instr (checkToInstr c);
  if !allowChecks then
    addInstr (checkToInstr c)

let addArithChecks (lo: exp) (ptr: exp) (off : exp) (hi : exp) : unit =
  addCheck (CNonNull ptr);
  let t = typeOf ptr in
  let sz = baseSize t in
  if isNullterm t then
    addCheck (CPtrArithNT (lo, hi, ptr, off, sz))
  else
    addCheck (CPtrArith (lo, hi, ptr, off, sz))

(* Returns ceiling(x / n)  *)
let divCeiling (x:exp) (n:int) : exp =
  if not (isIntegralType (typeOf x)) then
    error "Expecting an integer, got %a" dt_exp x;
  (* return the expression (x + n-1)/n *)
  BinOp(Div,
        BinOp(PlusA, x, integer (n-1), !upointType),
        integer n,
        !upointType)
  

let addSizeChecks (t: typ) (e: exp) (bytes: exp) : unit =
  let lo, hi = fancyBoundsOfType t in
  if isNullterm t then begin
    (* We need to leave the type of e alone so that CPtrArithNT can
       work its magic. Note that divCeiling will effectively round the
       size up to the next multiple of (baseSize t).  This could cause
       false positives in the reletively uncommon case where bytes is
       not a multiple of (baseSize t).  *)
    let numElements = divCeiling bytes (baseSize t) in
    addArithChecks lo e numElements hi
  end
  else begin
    (* Just treat e as a char pointer *)
    let cp e = mkCast e charPtrType in
    addArithChecks (cp lo) (cp e) bytes (cp hi)
  end 

let addCoercionCheck (lo_from: exp) (lo_to: exp) (e: exp)
                     (hi_to: exp) (hi_from: exp) (tFrom: typ) : unit =
  (* If the lower bound has changed, do an lbound check. 
   * (we already know that lo_from <= e, so if lo_from=lo_to,
   *  we don't have to check that lo_to <= e)
  *)
  if !optLevel = 0 || not (DCE.canonCompareExp(*StripCasts*) lo_from lo_to) then begin
    addCheck (CNullOrLeq(e, lo_from, lo_to, "lower bound coercion"));
    addCheck (CNullOrLeq(e, lo_to, e, "lower bound check"));
  end;
  if !optLevel = 0 || not (DCE.canonCompareExp(*StripCasts*) hi_from hi_to) then begin
    addCheck (CNullOrLeq(e, e, hi_to, "upper bound check"));
    if isNullterm tFrom then
      addCheck (CNullOrLeqNT(e, hi_to, hi_from, baseSize tFrom,
                            "nullterm upper bound coercion"))
    else
      addCheck (CNullOrLeq(e, hi_to, hi_from, "upper bound coercion"));
  end;
  ()


(**************************************************************************)


let rec expToAttr (e: exp) : attrparam option =
  match stripNopCasts e with
  | Lval (Var vi, NoOffset) -> Some (ACons (vi.vname, []))
  | Const _ ->
      begin
        match isInteger e with
        | Some i -> Some (AInt (to_int i))
        | None -> None
      end
  | BinOp ((MinusA | PlusA) as op, e1, e2, _) ->
      begin
        match expToAttr e1, expToAttr e2 with
        | Some a1, Some a2 -> Some (ABinOp (op, a1, a2))
        | _ -> None
      end
  | _ -> None

(* If this function frees an argument, it returns the index of that
 * argument and its type. *)
let getFreeArg (fnType: typ) : int option =
  let fnAttrs = typeAttrs fnType in
  match getZeroOneAttr ["drealloc"; "dfree"] fnAttrs with
  | Some (Attr ("dfree", [ACons (name, [])]))
  | Some (Attr ("drealloc", [ACons (name, []); _])) ->
      let _, argInfo, _, _ = splitFunctionType fnType in
      let rec getIndex lst index =
        match lst with
        | (argName, _, _) :: rest ->
            if name = argName then Some index else getIndex rest (index + 1)
        | [] -> None
      in
      getIndex (argsToList argInfo) 1
  | Some (Attr ("dfree", _)) -> E.s (error "Malformed free annotation.")
  | Some (Attr ("drealloc", _)) -> E.s (error "Malformed realloc annotation.")
  | Some (Attr _) -> E.s (bug "Unexpected attribute.")
  | None -> None

(* Returns an expression that evaluates to the number of objects of type
 * retType that can fit in the allocated area, as well as an expression
 * that evaluates to the raw number of bytes allocated. *)
let getAllocationExp (retType: typ) (fnType: typ) (args: exp list) : exp * exp =
  let fnAttrs = typeAttrs fnType in
  let size =
    match getOneAttr ["dalloc"; "drealloc"] fnAttrs with
    | Attr ("dalloc", [a])
    | Attr ("drealloc", [_; a]) ->
        let formals =
          match fnType with
          | TFun (_, argInfo, _, _) -> argsToList argInfo
          | _ -> E.s (bug "Expected function type")
        in
        let ctx =
          List.fold_right2
            (fun (name, _, _) arg acc ->
               if name <> "" then addBinding acc name arg else acc)
            formals args emptyContext
        in
        snd (compileAttribute ctx a)
    | Attr ("dalloc", _) -> E.s (error "Malformed alloc annotation.")
    | Attr ("drealloc", _) -> E.s (error "Malformed realloc annotation.")
    | Attr _ -> E.s (bug "Unexpected attribute.")
  in
  let retBaseType =
    match unrollType retType with
    | TPtr (bt, _) -> bt
    | TInt _ -> voidType (* Treat integer types like void*. *)
    | _ -> E.s (error "Left-hand side of allocation is not a pointer type.")
  in
  let count =
    if isOpenArrayComp retBaseType then
      one
    else
      let baseSize =
        if isVoidType retBaseType then one else SizeOf retBaseType
      in
      let count = BinOp (Div, size, baseSize, !upointType) in
      if isNullterm retType then
        BinOp (MinusA, count, one, !upointType)
      else
        count
  in
  count, size

let maxFunction = mkFun "deputy_max" !upointType [!upointType; !upointType] Rcutils.nofreeAttr

let callMax (e1: exp) (e2: exp) : exp =
  let t =
    typeAddAttributes (nulltermAttr :: sentinelAttrs)
      (typeRemoveAttributes ["bounds"] (typeOf e1))
  in
  Lval (var (addTmpCall t maxFunction [e1; e2]))

let isUpcast (btFrom: typ) (btTo: typ) : bool =
  match unrollType btFrom with
  | TComp (ci, _) ->
      begin
        try
          compareTypes ~importantAttr:isDeputyAttr (List.hd ci.cfields).ftype btTo
        with Failure "hd" ->
          false
      end
  | _ -> false

let normalizeCompareTypes (t1: typ) (t2: typ) : bool =
  compareTypes ~importantAttr:isDeputyAttr (normalizeTypeNames t1) (normalizeTypeNames t2)

let checkUnionWhen (ctx:context) (fld:fieldinfo) : unit =
  if not (isTrustedComp fld.fcomp) then
  try 
    let deps = depsOfWhenAttrs fld.fattr in (* may raise Not_found *)
    let deps' = List.filter (fun n -> n <> thisKeyword) deps in
    if not (hasBindings ctx deps) then
      E.s (error ("Field %s of union %s depends on names " ^^
                  "that are not in scope.\n" ^^
                  "  dependencies: {%a}\n" ^^
                  "  names in scope: {%a}")
                 fld.fname fld.fcomp.cname
                 (docList ~sep:(text ", ") text) deps'
                 d_ctx_simple ctx)
  with Not_found ->
    (* Allow missing WHEN clauses for scalars. *)
    if typeContainsPointers fld.ftype then
      E.s (error "Missing WHEN annotation on field %s of union %s."
                 fld.fname fld.fcomp.cname)

(* Determine whether a type is well-formed. 
   If this returns false, it's an error.  So try to give a useful reason
   to return false.
   It's not necessary for ctx to contain __this.  We'll add a binding for
   __this here. *)
let rec checkType (ctx: context) (t: typ) (where: doc) : unit =
  let ctx = addThisBinding ctx t zero in
  let checkPtrArrayAttrs (t: typ) : unit =
    (* TODO: check whether base types for bounds match? *)
    let bt =
      match unrollType t with
      | TPtr (bt, _)
      | TArray (bt, _, _) -> bt
      | _ -> E.s (bug "Expected pointer or array type")
    in
    let deps = if isTrustedType t then [] else depsOfType t in
    let deps' = List.filter (fun n -> n <> thisKeyword) deps in
    if not (hasBindings ctx deps) then begin
      E.s (error ("Type of %a depends on names that are not in scope.\n" ^^
                  "  type: %a\n" ^^
                  "  dependencies: {%a}\n" ^^
                  "  names in scope: {%a}")
                 insert where dx_type t
                 (docList ~sep:(text ", ") text) deps' d_ctx_simple ctx);
    end;
    checkType emptyContext bt where
  in
  match t with
  | TPtr _ ->
      checkPtrArrayAttrs t
  | TArray (_, _, a) ->
      if isOpenArray t then begin
        if not (hasAttribute "bounds" a) && not (isTrustedAttr a) then
          E.s (error "In %a, open array requires bounds information."
                     insert where);
        if hasAttribute "nullterm" a then
          E.s (error "In %a, open array cannot be nullterm."
                     insert where)
      end;
      checkPtrArrayAttrs t
  | TFun (ret, argInfo, _, _) ->
      let ctxFun =
        List.fold_left
          (fun acc (name, _, _) -> addBinding acc name zero)
          emptyContext
          (argsToList argInfo)
      in
      checkType ctxFun ret where;
      List.iter
        (fun (_, t, _) -> checkType ctxFun t where)
        (argsToList argInfo)
  | TComp (ci, _) when not ci.cstruct ->   (* union *)
      List.iter
        (fun fld -> 
           (* Check union fields in the context ["__this"; fieldname].
            * These are redundant ... I'm only including the field
            * name because that's how we did it in the paper. *)
           let ctxField = addBinding emptyContext fld.fname zero in
           checkType ctxField fld.ftype
             (dprintf "field %s of union %s" fld.fname ci.cname);
           (* Now check the when clause. *)
           checkUnionWhen ctx fld)
        ci.cfields
      
  (* Structs and typedefs are checked when defined. *)
  | TComp _
  | TNamed _
  (* The following types are always well-formed. *)
  | TVoid _
  | TInt _
  | TFloat _
  | TEnum _
  | TBuiltin_va_list _ -> ()

(* Add checks for a coercion of e from tFrom to tTo.
   Both tFrom and tTo must have fancy bounds. *)
let rec coerceType (e: exp) ~(tFrom: typ) ~(tTo: typ) : unit =
  if isNonnullType tTo
    && not (isNonnullType tFrom)
    && not (isTrustedType tFrom) then begin
      addCheck (CNonNull e);
  end;
  match unrollType tFrom, unrollType tTo with
  | t1, t2 when isTrustedType t1 || isTrustedType t2 ->
      markLocationTrusted ();
      ()
  | (TInt _ | TPtr _), (TPtr _ as t2) when isZero e || isSentinelType t2 ->
      (* Coerce NULL to pointer.  Do we need to do any well-formedness checks
         here? *)
      ()

  | TPtr _, TPtr _ when isSentinelType tFrom && not (isSentinelType tTo) ->
      (* Sentinel pointers need not be in bounds, so it's illegal to cast 
         away the sentinel qualifier. *)
      errorwarn "A sentinel pointer may not be cast to an ordinary pointer."

  | TPtr _, TPtr _ when isSizePtr tFrom && isSizePtr tTo ->
      let nFrom = fancySizeOfType tFrom in
      let nTo = fancySizeOfType tTo in
      addCheck (CLeqInt (nTo, nFrom, "pointer size coercion"))

  | TPtr (btFrom, _), TPtr _ when not (isSizePtr tFrom) && isSizePtr tTo ->
      if typeContainsPointers btFrom then
        errorwarn "Cast from pointer containing pointers to sized type: %a"
                  dx_exp e;
      if typeContainsNonnull btFrom then
        errorwarn "Cast from pointer containing nonnull to sized type: %a"
                  dx_exp e;
      let n = fancySizeOfType tTo in
      addSizeChecks tFrom e n

  | TPtr (btFrom, _), TPtr (btTo, _) when isSizePtr tFrom &&
                                          not (isSizePtr tTo) ->
      let lo, hi = fancyBoundsOfSizeType tTo tFrom e in
      let tFrom' = makeFancyPtrType btFrom lo hi in
      coerceType e tFrom' tTo

  | TPtr (bt1, _), TPtr (bt2, _) when normalizeCompareTypes bt1 bt2 ->
      if isNullterm tTo && not (isNullterm tFrom) then 
        errorwarn "Cast from ordinary pointer to nullterm: %a" dx_exp e;
      let loFrom, hiFrom = fancyBoundsOfType tFrom in
      let loTo, hiTo = fancyBoundsOfType tTo in
      addCoercionCheck loFrom loTo e hiTo hiFrom tFrom

    (* Allow upcasts. *)
  | TPtr (bt1, _), TPtr (bt2, _) when isUpcast bt1 bt2 ->
      if isNullterm tTo || isNullterm tFrom then 
        errorwarn "Upcasts not allowed on nullterm sequences: %a" dx_exp e;
      (* Check that the source has at least one element. *)
      let loFrom, hiFrom = fancyBoundsOfType tFrom in
      let loTo, hiTo = loFrom, BinOp (PlusPI, loFrom, one, typeOf loFrom) in
      addCoercionCheck loFrom loTo e hiTo hiFrom tFrom;
      (* Check that the destination has at most one element. *)
      let loTo, hiTo = fancyBoundsOfType tTo in
      let loFrom, hiFrom = loTo, BinOp (PlusPI, loTo, one, typeOf loTo) in
      addCoercionCheck loFrom loTo e hiTo hiFrom tTo

    (** Cast between two pointers to different base types *)
  | TPtr (bt1, _), TPtr (bt2, _) when not (typeContainsPointers bt1) &&
                                      not (typeContainsPointers bt2) ->
      if isNullterm tTo && not (isNullterm tFrom) then 
        errorwarn "Cast from ordinary pointer to nullterm: %a" dx_exp e;

      if isNullterm tTo || isNullterm tFrom then 
        E.s (unimp ("Nullterm cast with different base types:\n" ^^
                    "  from: %a\n" ^^
                    "    to: %a\n" ^^
                    "   exp: %a")
                   dt_type tFrom dt_type tTo dx_exp e);
      let loFrom, hiFrom = fancyBoundsOfType tFrom in
      let loTo, hiTo = fancyBoundsOfType tTo in
      addCoercionCheck loFrom loTo e hiTo hiFrom tFrom

    (* Same as above, but for arrays--used for assigning to the length
     * of an open array. *)
  | TArray (bt1, _, _), TArray (bt2, _, _) when normalizeCompareTypes bt1 bt2 ->
      if isNullterm tTo && not (isNullterm tFrom) then 
        errorwarn "Cast from ordinary pointer to nullterm: %a" dx_exp e;
      let loFrom, hiFrom = fancyBoundsOfType tFrom in
      let loTo, hiTo = fancyBoundsOfType tTo in
      let e' =
        match e with
        | Lval lv -> StartOf lv
        | _ -> E.s (bug "Expected lval")
      in
      addCoercionCheck loFrom loTo e' hiTo hiFrom tFrom

  | (TInt _ | TEnum _ | TPtr _ | TFloat _ ), (TInt _ | TEnum _) ->
      (* These are all totally safe. *)
      ()
  | (TInt _ | TFloat _ | TEnum _ ), TFloat _ -> 
      ()
  | TComp (ci, _), TComp (ci', _) when ci == ci' && not ci.cstruct ->
      let whenFrom = fancyWhenOfType tFrom in
      let whenTo = fancyWhenOfType tTo in
      (* If the when maps differ, it's because a WHEN clause depends on
         something in the context that has changed, so we should ensurer the
         union has been zeroed. *)
      if not (Util.equals whenFrom whenTo) then begin
        let lv = match e with Lval lv -> lv 
          | _ -> E.s (bug "union expression must be an lval.")
        in
        (* Maybe we know statically that a field f will be the (only) selected
           field after the coercion.  If f was also selected before the
           coercion, then there's been no change in the selected field,
           and we don't need to check that the union is null. *)
        let sameFieldIsSelected = 
          match getSelectedField whenTo with
            Some f -> 
              List.assq f whenFrom
          | None -> 
              (* No field is selected, or we don't know which field is 
                 selected.  So require that the union be filled with 0. *)
              zero
        in
        (* Check that either sameFieldSelected is true, or that the union
           is filled with zeros. *)
        addCheck (CNullUnionOrSelected(lv, sameFieldIsSelected))
      end
  | _ -> 
    if not (normalizeCompareTypes tFrom tTo) then
      errorwarn ("Type mismatch in coercion:\n" ^^
                 "  from: %a\n" ^^
                 "    to: %a\n" ^^
                 "   exp: %a")
                dt_type tFrom dt_type tTo dx_exp e
        
type whyExp =
| ForInt           (* This expression will be cast to an integer. *)
| ForDeref         (* This expression will be dereferenced. *)
| ForAnything      (* The catch-all case. *)

type whyLval =
| ForRead          (* Reading this lval. *)
| ForAddrOf        (* Taking the address of this lval *)
| ForWrite of exp  (* Writing the specified value. Call checkExp on
                    * this exp before calling checkLval *)
| ForCall          (* Assigning the result of a call.
                    * We don't have an expression representing the new value,
                    * so we have to be more conservative *)

(* Calls checkExp e, then calls coerceType to make sure that
   e can be coerced to tTo.  tTo must have fancy bounds. *)
let rec coerceExp (e: exp) (tTo: typ) : unit =
  (* If we're casting to a sentinel type, we omit many checks.
     Pretend we're casting to long instead.*)
  let tTo = if isSentinelType tTo then !upointType else tTo in
  (* If we're casting to an int or a sentinel, do less-strict checking of e. *)
  let why = if isIntegralType tTo then ForInt else ForAnything in

  let tFrom = checkExp ~why e in
  coerceType e ~tFrom ~tTo
        

and checkExp ?(why: whyExp = ForAnything) (e: exp) : typ =
  match e with
  | UnOp (op, e', t) -> coerceExp e' t; t
  | BinOp ((PlusPI | IndexPI),
           BinOp((PlusPI | IndexPI) as op2,pe,e1,t1), e2, t2) ->
    (* reassociate and try again *)
    let ne = BinOp(op2,pe,BinOp(PlusA,e1,e2,typeOf e1),t1) in
    checkExp ~why:why ne
  | BinOp (MinusPI,
           BinOp((PlusPI | IndexPI) as op2,pe,e1,t1), e2, t2) ->
    (* reassociate and try again *)
    let ne = BinOp(op2,pe,BinOp(MinusA,e1,e2,typeOf e1),t1) in
    checkExp ~why:why ne
  | BinOp ((PlusPI | IndexPI),
           BinOp(MinusPI,pe,e1,t1), e2,t2) ->
    (* reassociate and try again *)
    let ne = BinOp(MinusPI,pe,BinOp(MinusA,e1,e2,typeOf e1),t1) in
    checkExp ~why:why ne
  | BinOp (MinusPI,
           BinOp(MinusPI,pe,e1,t1), e2, t2) ->
    (* reassociate and try again *)
    let ne = BinOp(MinusPI,pe,BinOp(PlusA,e1,e2,typeOf e1),t1) in
    checkExp ~why:why ne
  | BinOp ((PlusPI | IndexPI | MinusPI) as op, e1, e2, t) ->
      let t1 = checkExp ~why e1 in
      (* FIXME: __this can appear in t, so we ignore it for now.
         At some point, we should check it! *)
      (* coerceExp e1 (substType ... t); *)
      coerceExp e2 !upointType;
      if isTrustedType t1 then
        markLocationTrusted ()
      else begin
        let lo, hi = fancyBoundsOfType t1 in
        let e2' =
          match op with
          | MinusPI -> UnOp (Neg, e2, typeOf e2)
          | PlusPI | IndexPI -> e2
          | _ -> E.s (bug "Unexpected operation")
        in
        if why = ForInt then 
          (* We're casting e to a sentinel or integer.  We permit
             sentinels to point anywhere, so skip the bounds checks.  *)
          ()
        else if isAbstractPtr t1 then
          E.s (error "Arithmetic on abstract pointer type %a." dx_type t1)
        else
          addArithChecks lo e1 e2' hi
      end;
      if isNullterm t1 then
        let lo, hi = fancyBoundsOfType t1 in
        let hi' = callMax e hi in
        typeAddAttributes [Attr ("nullterm", [])]
          (makeFancyPtrType (baseType "nullterm arith" t1) lo hi')
      else
        t1
  | BinOp (op, e1, e2, t) -> (* Includes MinusPP *)
      ignore (checkExp e1);
      ignore (checkExp e2);
      t
  | Lval lv -> checkLval ForRead lv
  | CastE (t, e') ->
      if isNulltermDrop t then
        let t' = checkExp e' in
        let lo, hi = fancyBoundsOfType t' in
        let bt = baseType "cast to NT" t' in
        makeFancyPtrType bt (mkCast lo t) (mkCast hi t)
      else begin
        let ctx = addThisBinding (localsContext !curFunc) t e in
        let t' = substType ctx t in
        coerceExp e' t';
        t'
      end
  | SizeOfE _
  | AlignOfE _ ->
      (* We don't check the inner expr because it doesn't get executed. *)
      unrollType (typeOf e)

  (* Treat "&((T* )0)->field" as an integer, and don't insert any checks. *)
  | AddrOf (Mem (CastE(TPtr(bt, _), z)), off)
  | StartOf (Mem (CastE(TPtr(bt, _), z)), off) when isZero z ->
      !typeOfSizeOf
  | AddrOf lv -> begin 
      (* Look first for the special case when the lv is an array element. *)
      match removeOffsetLval lv with  
      | lv', Index (idx, NoOffset) -> 
          (* Turn it into StartOf array + index, so the we account for the 
           * array bounds *)
          checkExp ~why (BinOp (PlusPI, StartOf lv', idx, typeOf (StartOf lv')))
      | _ -> begin
          (* There should be some shared code in checking the StartOf and 
           * AddrOf *)
          ignore (checkLval ForAddrOf lv);
          let bt = typeOfLval lv in
          if List.exists (fun n -> n <> thisKeyword) (depsOfType bt) then
            error "Cannot take address of lval (%a) that has dependencies" d_lval lv;
          if hasExternalDeps lv then
            error "Cannot take address of lval (%a) with external dependencies" d_lval lv;
          (* If this is the address of an element inside an array, then take the 
           * whole array as the bounds *)
          let lo = mkAddrOrStartOf lv in
          let hi = BinOp (PlusPI, lo, one, typeOf lo) in
          makeFancyPtrType bt lo hi
      end
  end
  | StartOf lv ->
      let whyLval =
        match why with
        | ForDeref -> ForRead
        | _ -> ForAddrOf
      in
      let bt, attrs =
        match checkLval whyLval lv with
        | TArray (bt, _, attrs) -> bt, attrs
        | _ -> E.s (bug "Expected array type")
      in
      let attrs' =
        List.filter
          (fun (Attr (name, _)) ->
             name = "fancybounds" || name = "nullterm" || name = "trusted")
          attrs
      in
      TPtr (bt, attrs')
  | Const (CStr s) -> (* String literal *)
      let len = String.length s in
      let lo = e in
      let hi = BinOp (PlusPI, lo, integer len, typeOf lo) in
      makeFancyPtrType ~nullterm:true charType lo hi
  | Const _
  | SizeOf _
  | SizeOfStr _
  | AlignOf _ -> unrollType (typeOf e)

and checkLval (why: whyLval) (lv: lval) : typ =
  let lv', off = removeOffsetLval lv in
  match off with
  | NoOffset ->
      assert (snd lv' = NoOffset);
      let ctx, t =
        match fst lv' with
        | Mem e ->
            let t = checkExp ~why:ForDeref e in
            if isTrustedType t then
              markLocationTrusted ()
            else begin
              if isSizePtr t then
                error "Illegal dereference of a size pointer";
              if isSentinelType t then
                errorwarn "Illegal dereference of a sentinel pointer";
              let lo, hi = fancyBoundsOfType t in
              addCheck (CNonNull e);
              let addUBoundChecks (): unit =
                (* FIXME: Add overflow checking here. *)
                (* addCheck (COverflow (e, one)); *)
                let ePlusOne = BinOp (PlusPI, e, one, t) in
                addCheck (CLeq (ePlusOne, hi, "pointer access check"))
              in
              match why with
              | ForRead ->
                  if not (isNullterm t) then
                    addUBoundChecks ()
              | ForAddrOf ->
                  (* check e != hi even if this is nullterm, because
                   * otherwise we could create a pointer with bounds hi,hi+1. *)
                  addUBoundChecks ()
              | ForCall ->
                  (* Conservatively forbid assignment of a call result
                   * when e=hi. *)
                  addUBoundChecks ()
              | ForWrite what ->
                  if isNullterm t then begin
                    if bitsSizeOf (baseType "mem write" t) > 32 then
                      unimp "Nullterm writes for base type larger than 32 bits";
                    addCheck (CWriteNT (e, hi, mkCast what intType, baseSize t))
                  end else
                    addUBoundChecks ()
            end;
            let bt =
              match unrollType t with
              | TPtr (bt, _) -> bt
              | _ -> E.s (bug "Expected pointer type.")
            in
            emptyContext, bt
        | Var vi ->
            let ctx =
              if not vi.vglob then
                localsContext !curFunc
              else 
                globalsContext vi
            in
            ctx, vi.vtype
      in
      let ctx' = addThisBinding ctx t (Lval lv) in
      substType ctx' t
  | Field (fld, NoOffset) ->
      let compType =
        (* If why = ForWrite, then we are writing to a field or element of
         * lv'. It doesn't make sense to say that we are writing "e" to the
         * entire lval, so use the more conservative ForCall instead. *)
        let why' = match why with
          | ForWrite e -> ForCall
          | _ -> why
        in
        unrollType (checkLval why' lv')
      in
      let ftype' =
        try
          polySubst (polyCompMap compType) fld.ftype
        with PolyError ->
          reportPolyFieldError lv fld
      in
      if fld.fcomp.cstruct then begin
        let ctx = structContext lv' fld.fcomp in
        let ctx' = addThisBinding ctx ftype' (Lval lv) in
        substType ctx' ftype'
      end else begin (* Union *)
        (* check the field access *)
        if isTrustedComp fld.fcomp then
          markLocationTrusted ()
        else
          checkUnionAccess why compType fld;
        (* now do the type of the field itself *)
        let value = Lval lv in
        let ctx  = addBinding emptyContext fld.fname value in
        let ctx' = addThisBinding ctx ftype' value in
        substType ctx' ftype'
      end
  | Index (index, NoOffset) ->
      (* Convert to pointer arithmetic for checking. *)
      let p = StartOf lv' in
      checkLval why (Mem (BinOp (PlusPI, p, index, typeOf p)), NoOffset)
  | _ -> E.s (bug "Unexpected result from removeOffset")

and checkUnionAccess (why:whyLval) (compType: typ) (fld:fieldinfo): unit =
  if (why = ForAddrOf) then
    E.s (error "Can't take the address of a union field");
  let wm = fancyWhenOfType compType in
  (* Check the selector for the current field. *)
  (try
     let s = List.assq fld wm in
     addCheck (CSelected s)
   with Not_found -> () (* a scalar field without a WHEN *)
  );
  if why <> ForRead then begin
    (* Check that the other selectors are 0 *)
    List.iter
      (fun (f,s) -> if f != fld then
         addCheck (CNotSelected s))
      wm
  end;  
  ()

let boundsForLval (fd : fundec) (lv : lval) : exp * exp =
    let oldallowchecks = !allowChecks in
    allowChecks := false;
    curFunc := fd;
    let t = checkExp (Lval lv) in
    let lo, hi = fancyBoundsOfType t in
    curFunc := dummyFunDec;
    allowChecks := oldallowchecks;
    lo, hi

let boundsForExp (fd : fundec) (e : exp) : exp * exp =
    let oldallowchecks = !allowChecks in
    allowChecks := false;
    curFunc := fd;
    let t = checkExp e in
    let lo, hi = fancyBoundsOfType t in
    curFunc := dummyFunDec;
    allowChecks := oldallowchecks;
    lo, hi

let checkSetEnv (ctx: context) (x: 'a) (e: exp) (env: 'a list)
                (expOf: 'a -> exp) (nameOf: 'a -> string)
                (typeOf: 'a -> typ) : unit =
  (* Cast e to its new type, so that we do arithmetic correctly. *)
  let eCast = mkCast ~e ~newt:(typeOf x) in
  let xName = nameOf x in
  List.iter
    (fun y ->
       let yName = nameOf y in
       let yType = typeOf y in
       if xName = yName ||
          isUnionType yType ||
          List.mem xName (depsOfType yType) then begin
         let yExp = expOf y in
         (* ySubst is the new value of y after the assignment.  
          * ySubstCast is ySubst with a cast to its new type, for use in
          * the enviroment.  Without the cast, case cast3 of cast9.c
          * incorrectly passes because the arithmetic is wrong.  *)
         let ySubst, ySubstCast =
           if xName <> yName then
             yExp, yExp
           else
             e, eCast
         in
         let ctx' =
           addBinding (addThisBinding ctx yType ySubstCast) xName eCast
         in
         coerceExp ySubst (substType ctx' yType)
       end)
    env

let checkSet (varsInScope: VS.t) (lv: lval) (e: exp) : unit =
  (* log "checkSet for %a := %a\n" d_lval lv dx_exp e; *)
  let t = checkLval (ForWrite e) lv in
  if isConstType t then
    warn "Assigning to an ASSUMECONST value.  Make sure there are no live values that depend on it.";
  let off1, off2 = removeOffset (snd lv) in
  begin
    match off2 with
    | NoOffset ->
        begin
          match fst lv with
          | Var x ->
              let ctx, env =
                if not x.vglob then begin
                  (* Add x to the scope.  Even if it hasn't been initialized
                     earlier, we'll want to start checking it now. 
                     Also add anything that x depends on, so that we can compile the
                     type of x.*)
                  let varsInScope' = VS.union (Dlocals.localDependsOn x)
                                       (VS.add x varsInScope) in
                  liveLocalsContext varsInScope', VS.elements varsInScope'
                end else 
                  globalsContext x, globalsEnv x
              in
              checkSetEnv ctx x e env
                (fun vi -> Lval (var vi))
                (fun vi -> vi.vname)
                (fun vi -> vi.vtype)
          | Mem addr ->
              let t = typeOfLval lv in
              let ctx = addThisBinding emptyContext t e in
              coerceExp e (substType ctx t)
        end
    | Field (x, NoOffset) when x.fcomp.cstruct -> (* struct *)
        let baseLval = fst lv, off1 in
        let ctx = structContext baseLval x.fcomp in
        let env = x.fcomp.cfields in
        let map = polyCompMap (typeOfLval baseLval) in
        checkSetEnv ctx x e env
          (fun fi -> Lval (addOffsetLval (Field (fi, NoOffset)) baseLval))
          (fun fi -> fi.fname)
          (fun fi ->
             try
               polySubst map fi.ftype
             with PolyError ->
               reportPolyFieldError lv fi)
    | Field (x, NoOffset) ->   (* Union *)
        (* union fields don'
t depend on each other. *)
        ()
    | Index (_, NoOffset) ->
        let ctx = addThisBinding emptyContext (typeOfLval lv) e in
        coerceExp e (substType ctx (typeOfLval lv))
    | _ -> E.s (bug "Unexpected result from removeOffset")
  end;
  addInstr (Set (lv, e, !currentLoc))

(* Check the right-hand side of a call instruction.  The result is an
 * _unchecked_ lval temporary representing the result of the call.  The
 * arguments are the same as for checkCall, although the lval option
 * has been changed to a type option for said lval, since this function
 * is not supposed to do any checking on the left-hand side.  The result
 * of this call is Some _ iff lvTypeOpt is Some _. *)
let checkCallRhs (lvTypeOpt: typ option) (fnType: typ) (func: exp)
                 (args: exp list) (exempt: int list) : lval option =
  let returnType, argInfo, varargs, fnAttrs =
    match fnType with
    | TFun (returnType, argInfo, varargs, fnAttrs) ->
        returnType, argInfo, varargs, fnAttrs
    | _ -> E.s (error "Expected function type at call: %a" dx_exp func)
  in

  (* CIL uses the missingproto attribute to signal that the function
   * was used before being declared. *)
  if hasAttribute "missingproto" fnAttrs then
    errorwarn "Calling function that has no prototype: %a" dx_exp func;

  let returnDeps = if lvTypeOpt <> None then depsOfType returnType else [] in

  let formals : (string * typ * attributes) list = argsToList argInfo in
  let numFormals = List.length formals in
  let numActuals = List.length args in

  (* Check number of arguments.  If there aren't enough actuals, we bail;
   * if there aren't enough formals, we can still proceed. *)
  if numActuals < numFormals then
    E.s (error "Function call has too few arguments")
  else if numFormals < numActuals && not varargs then
    errorwarn "Function call has too many arguments";

  (* Split the actuals between those that match the formals, and the ones 
   * that match the ... *)
  let actualsMain, actualsVararg = split args numFormals in

  (* Set up polymorphism.  First we match up argument types and formals in
   * order to figure out which types are used with which type variables.
   * Then we pick a type from among these (or complain if none is to be
   * found).  Finally, we substitute in the types of formals. *)
  polyStart ();

  List.iter2
    (fun (_, ftype, _) arg -> polyMakeSubst ftype (deputyTypeOf arg))
    formals actualsMain;

  polyResolve ();

  let formals =
    List.map2
      (fun (fname, ftype, fattrs) arg ->
         try
           fname, polySubst polyMap ftype, fattrs
         with PolyError ->
           reportPolyArgError fname ftype arg)
      formals actualsMain
  in

  (* Build the context for the call: the formals mapped to actuals.
   * When needed for the return value, we introduce a temporary to capture
   * the value of the actuals before the call.  The results are:
   * . actualsMain': The new list of actuals (using temporaries).
   * . ctxCall: The context mapping formals to actuals.
   * . tmpMapping: A mapping of formals to temporary locals, used for
   *     any formals that the return type depends upon.
   *)
  let actualsMain', ctxCall, tmpMapping =
    try
      List.fold_right2
        (fun (argName, argType, _) arg (actualsAcc, ctxAcc, mapAcc) ->
          if argName <> "" then
            let arg', mapAcc' =
              if List.mem argName returnDeps then
                (* Optimization: Before inserting a temporary, check to
                 * see whether we already have a local var. In some cases,
                 * preprocessing has already placed a temporary here. *)
                let vi =
                  match arg with
                  | Lval (Var vi, NoOffset)
                      when (not vi.vaddrof) && (not vi.vglob) -> vi
                  | _ -> addTmpSet arg
                in
                Lval (var vi), (argName, vi.vname) :: mapAcc
              else
                arg, mapAcc
            in
            (arg' :: actualsAcc,
             addBinding ctxAcc argName (mkCast arg' argType),
             mapAcc')
          else
            (arg :: actualsAcc, ctxAcc, mapAcc))
        formals
        actualsMain
        ([], emptyContext, [])
    with Invalid_argument _ ->
      E.s (bug "Expected lists with same length")
  in

  (* First check any "free" arguments, which are basically trusted. *)
  let exempt, freeTypeOpt =
    match getFreeArg fnType with
    | Some n ->
        begin
          try
            n :: exempt, Some (checkExp (List.nth actualsMain' (n - 1)))
          with Failure "nth" ->
            E.s (bug "Could not get argument %d." n)
        end
    | None -> exempt, None
  in

  (* Check the actuals that have matching formals. *)
  begin
    try
      iter2_index
        (fun (argName, argType, _) arg i ->
          if not (List.mem i exempt) then
            let ctxCall' = addThisBinding ctxCall argType arg in
            let argType' = substType ctxCall' argType in
            coerceExp arg argType')
        formals
        actualsMain'
    with Invalid_argument _ ->
      E.s (bug "Expected lists with same length")
  end;

  (* Check the actuals that match the ... *)
  iter_index
    (fun arg i ->
       if not (List.mem (i + numFormals) exempt) then
         ignore (checkExp arg))
    actualsVararg;

  let args' = actualsMain' @ actualsVararg in

  (* Update the return type based on the substitutions we've accumulated
   * while checking the arguments.  We can then forget all the info about
   * polymorphism for this call. *)
  let returnType =
    try
      polySubst polyMap returnType
    with PolyError ->
      reportPolyRetError func
  in

  polyClear ();

  (* Now insert the call itself, with the return placed in a temporary. *)
  match lvTypeOpt with
  | Some lvType ->
      (* If we're allocating, we adjust the type of the return value
       * to indicate the number of objects allocated, and we need to do
       * some initialization. *)
      if isAllocator fnType then
        (* Get the base type. *)
        let lvBaseType =
          match unrollType lvType with
          | TPtr (bt, _) -> bt
          | TInt _ -> voidType (* Treat integer types like void*. *)
          | _ -> E.s (error ("Left-hand side of allocation " ^^
                             "is not a pointer type."))
        in
        (* If freeTypeOpt <> None, we're reallocing.  Make sure the freed
         * type is the same as the realloced type. *)
        begin
          match freeTypeOpt with
          | Some freeType ->
              begin
                match unrollType freeType with
                | TPtr (freeBaseType, _) ->
                    if not (compareTypes ~importantAttr:isDeputyAttr freeBaseType lvBaseType) then
                      error ("Reallocator changes type of memory area.\n" ^^
                             "  from: %a\n" ^^
                             "  to: %a")
                             dx_type lvType dx_type freeType
                | _ -> error ("Expected pointer type for freed argument.\n" ^^
                              "  type: %a\n") dx_type freeType
              end
          | None -> ()
        end;
        (* Get the size of the array.  If we're handling an open array,
         * treat "extra" space as the open array, *not* as additional
         * malloced objects. *)
        let openArrayLen = getOpenArrayLength lvBaseType in
        let count, size = getAllocationExp lvType fnType actualsMain' in
        if openArrayLen <> None then begin
          addCheck (CLeqInt (SizeOf lvBaseType, size,
                             "open array allocation test"))
        end;
        let newAttr =
          if openArrayLen <> None then
            safeAttr
          else
            let countVar = addTmpSet count in
            countAttr (ACons (countVar.vname, []))
        in
        let returnType' =
          typeAddAttributes [newAttr]
            (typeRemoveAttributes ["bounds"; "size"; "nonnull"] lvType)
        in
        let returnVar = addTmpCall returnType' func args' in
        (* Now do some initialization. *)
        if typeContainsNonnull (baseType "allocation" returnType') then
          error "Allocation of a buffer containing non-null values";
        if typeContainsPtrOrNullterm lvBaseType && freeTypeOpt = None then begin
          (* If the type contains pointers or nullterm, just zero out
           * the whole thing. *)
          (* TODO: We exclude realloc'ed memory, because we don't want
           * to overwrite the existing data! Fix this somehow! *)
          addInstr (Call (None, Lval (var memset),
                          [Lval (var returnVar); zero; size],
                          !currentLoc))
        end else if isNullterm lvType then begin
          (* We don't need to zero the whole thing, but we do need to
           * zero the last element. *)
          let last = BinOp (PlusPI, Lval (var returnVar), count, returnType') in
          addInstr (Set ((Mem last, NoOffset), zero, !currentLoc))
        end;
        (* Set the size of the open array, if necessary. *)
        begin
          match openArrayLen with
          | Some (fld, atype) ->
              let bt =
                match unrollType atype with
                | TArray (bt, _, _) -> bt
                | _ -> E.s (bug "Expected array type.")
              in
              let loc = Mem (Lval (var returnVar)), Field (fld, NoOffset) in
              let count =
                BinOp (Div,
                       BinOp (MinusA, size, SizeOf lvBaseType, !upointType),
                       SizeOf bt, !upointType)
              in
              addInstr (Set (loc, count, !currentLoc))
          | None -> ()
        end;
        Some (var returnVar)
      else
        (* If we're not allocating, create a temporary with the declared
         * return value. *)
        let returnType' =
          substTypeName tmpMapping (typeRemoveAttributes ["nonnull"] returnType)
        in
        let returnVar = addTmpCall returnType' func args' in
        Some (var returnVar)
  | None ->
      addInstr (Call (None, func, args', !currentLoc));
      None

(* Check a call instruction.  Arguments are the same as for a call
 * instruction with the addition of the exempt list.  The exempt list
 * contains integers indicating which arguments should _not_ be checked.
 * Arguments are numbered starting with 1; the return value is indicated
 * in this list by 0. *)
let checkCall (varsInScope: VS.t) (lvOpt: lval option) (fnType: typ) (func: exp)
              (args: exp list) (exempt: int list) : unit =
  let lvTypeOpt =
    match lvOpt with
    | Some lv -> Some (typeOfLval lv)
    | None -> None
  in
  match lvOpt, checkCallRhs lvTypeOpt fnType func args exempt with
  | Some lv, Some lvTmp ->
      let e = Lval (lvTmp) in
      if not (List.mem 0 exempt) then
        checkSet varsInScope lv e
      else
        addInstr (Set (lv, e, !currentLoc));
      (*if isPointerType (typeOfLval lvTmp) then
        addInstr (Set (lvTmp, zero, !currentLoc)) zra *)
  | None, None -> ()
  | _ -> E.s (bug "Unexpected result from checkCallRhs")

(* FIXME: with all of these special functions, we should pay attention
   to the argument numbers in the annotations (e.g. dmemset(1,2,3)).
   So far, we assume args are in the usual order. *)
let checkMemset (varsInScope: VS.t) 
  (lvOpt: lval option) (fnType: typ) (func:exp) (args: exp list)
  : unit =
  match args with
  | [(AddrOf lv1 | StartOf lv1); e2; e3] 
    when (isZero e2) && (isCorrectSizeOf e3 lv1) ->
      (* Special case: if we're overwriting a complete lval with 0, we
         don't need to check for dependencies within lv1.  We still
         check to make sure nothing outside of lv1 depends on lv1.
         
         We need this when lv1 is a union.  It's okay to zero a union, but it's
         not normally okay to take the address of a union, since it
         depends on its context.
      *)
      ignore (checkLval ForAddrOf lv1);
      if hasExternalDeps lv1 then
        E.s (error
            "Memset: cannot take address of lval with external dependencies");
      if typeContainsNonnull (typeOfLval lv1) then begin
        error "memset on a type containing a nonnull pointer."
      end;
      checkCall varsInScope lvOpt fnType func [mkAddrOrStartOf lv1; e2; e3] [1]
  | e1 :: e2 :: e3 :: rest ->
      let e1Type = checkExp e1 in
      let e1BaseType =
        match unrollType e1Type with
        | TPtr (bt, _) -> bt
        | _ -> E.s (error "First arg to memset is not a pointer")
      in
      if isTrustedType e1Type then
        markLocationTrusted ()
      else begin
        addSizeChecks e1Type e1 e3;
        if typeContainsPointers e1BaseType then begin
          addCheck (CEq (e2, zero, "memset argument", []));
          addCheck (CMult (SizeOf e1BaseType, e3))
        end;
        if typeContainsNonnull e1BaseType then
          errorwarn "Calling memset on a type containing a nonnull pointer";
      end;
      checkCall varsInScope lvOpt fnType func (e1 :: e2 :: e3 :: rest) [1]
  | _ -> E.s (error "Expected three args to memset")

let checkMemcpy (varsInScope: VS.t)
  (lvOpt: lval option) (fnType: typ) (func:exp) (args: exp list) 
  : unit =
  match args with
  | e1 :: e2 :: e3 :: rest ->
      let e1Type = checkExp e1 in
      let e2Type = checkExp e2 in
      let e1BaseType =
        match unrollType e1Type with
        | TPtr (bt, _) -> bt
        | _ -> E.s (error "First arg to memcpy is not a pointer")
      in
      let e2BaseType =
        match unrollType e2Type with
        | TPtr (bt, _) -> bt
        | _ -> E.s (error "Second arg to memcpy is not a pointer")
      in
      if isTrustedType e1Type then
        markLocationTrusted ()
      else begin
        addSizeChecks e1Type e1 e3;
        if typeContainsPointers e1BaseType then begin
          if not (compareTypes ~importantAttr:isDeputyAttr e1BaseType e2BaseType) then
            errorwarn "Calling memcpy on arrays with different base types";
          addCheck (CMult (SizeOf e1BaseType, e3))
        end;
      end;
      if isTrustedType e2Type then
        markLocationTrusted ()
      else
        addSizeChecks e2Type e2 e3;
      checkCall varsInScope lvOpt fnType func (e1 :: e2 :: e3 :: rest) [1; 2]
  | _ -> E.s (error "Expected three args to memcpy")

let checkMemcmp (varsInScope: VS.t)
  (lvOpt: lval option) (fnType: typ) (func:exp) (args: exp list)
  : unit =
  match args with
  | e1 :: e2 :: e3 :: rest ->
      let e1Type = checkExp e1 in
      let e2Type = checkExp e2 in
      if isTrustedType e1Type then markLocationTrusted ()
      else
        addSizeChecks e1Type e1 e3;
      if isTrustedType e2Type then markLocationTrusted ()
      else
        addSizeChecks e2Type e2 e3;
      checkCall varsInScope lvOpt fnType func (e1 :: e2 :: e3 :: rest) [1; 2]
  | _ -> E.s (error "Expected three args to memcmp")

(* Check only the right-hand side of an instruction.  Used when generating
 * automatic bounds for the left-hand side.  Returns an expression
 * representing the right-hand side, the type of that expression, and
 * a list of clean-up instructions to be executed after the expression
 * has been used. *)
let checkInstrRhs (instr: instr) : exp * typ * instr list =
  let e, instrs =
    match instr with
    | Call (Some lv, fn, args, _) ->
        begin
          match checkCallRhs (Some (typeOfLval lv)) (typeOf fn) fn args [] with
          | Some lv -> Lval lv, [(*Set (lv, zero, !currentLoc) zra *)]
          | None -> E.s (bug "Unexpected result from checkCallRhs")
        end
    | Call (None, _, _, _) ->
        E.s (bug "Expected call with return lval")
    | Set (_, e, _) ->
        e, []
    | Asm _ ->
        E.s (bug "Expected call or set")
  in
  e, checkExp e, instrs

(* Check one instruction.
   varsInScope is the set of local variables that have been initialized: i.e.
   are live or have had their addresses taken.  
   We'll use this set as the context in checkSetEnv (the Hoare rule).
   If we write to any variables, add them to the in-scope set and return the
   new set. *)
let checkInstr (varsInScope: VS.t) (instr : instr) : VS.t =
  currentLoc := get_instrLoc instr;
  markLocationChecked ();
  if !verbose then
    log "INSTR: %a" dn_instr instr;
  let addToScope (lv:lval) : VS.t =
    (* We've written to an lval that could be a local var.  
       Update varsInScope.  Also include any vars that vi
       depends on, so that we can compile vi's dependencies. *)
    match lv with
      Var vi,_ when not vi.vglob -> VS.union 
                                      (Dlocals.localDependsOn vi) 
                                      (VS.add vi varsInScope)
    | _ -> varsInScope
  in
  let addToScopeOpt (lvo:lval option) : VS.t =
    match lvo with
      Some lv -> addToScope lv
    | None -> varsInScope
  in
  match instr with
  | Call (lvOpt, Lval (Var vf, NoOffset), args, _) 
      when vf.vname = "strcpy" || vf.vname = "strcat" ->
      (* Without this check, users get a rather cryptic error message when
         using strcpy.  We need a better way to forbid use of certain bad
         API functions. *)
      warn "Calls to %s are unsafe; use newer string functions instead."
           vf.vname;
      addInstr instr;
      addToScopeOpt lvOpt
  | Call (lvOpt, fn, _, _) when fn == maxFunction ->
      (* Ignore the max function for now. *)
      addInstr instr;
      addToScopeOpt lvOpt
  | Call(lvOpt, Lval(Var vf, NoOffset), _, loc)
      when vf.vname = "SCAST" || vf.vname = "SINIT" ->
        addInstr instr;
        addToScopeOpt lvOpt
  | Call (lvOpt, fn, args, _) ->
      let fnType = checkExp fn in
      if isMemset fnType then
        checkMemset varsInScope lvOpt fnType fn args
      else if isMemcpy fnType then
        checkMemcpy varsInScope lvOpt fnType fn args
      else if isMemcmp fnType then
        checkMemcmp varsInScope lvOpt fnType fn args
      else if isVarargOperator fn then begin
        (* skip va_start, va_arg, and family *)
        if !warnVararg then
          warn "Ignoring vararg operator %a" dx_exp fn;
        addInstr instr
      end
      else
        checkCall varsInScope lvOpt fnType fn args [];
      addToScopeOpt lvOpt
  | Set ((Var vi, NoOffset) as lv, _, _) when List.memq vi !exemptLocalVars ->
      addInstr instr;
      addToScope lv
  | Set (lv, e, _) ->
      checkSet varsInScope lv e;
      addToScope lv
  | Asm _ ->
      markLocationTrusted ();
      if !warnAsm then
        warn "Ignoring asm";
      addInstr instr;
      varsInScope

let returnCtx : context ref = ref []

let checkReturn (eo : exp option) : unit =
  let returnType =
    match !curFunc.svar.vtype with
    | TFun (returnType, _, _, _) -> returnType
    | _ -> E.s (bug "Expected function type")
  in
  match eo with
  | Some e ->
      if !verbose then
        log "RETURN: %a" dx_exp e;
      let ctx = addThisBinding !returnCtx returnType e in
      coerceExp e (substType ctx returnType)
  | None ->
      if !verbose then
        log "RETURN: [void]";
      if not (isVoidType returnType) then
        errorwarn "Return type of function is not void"

let rec checkStmt (s : stmt) : unit =
  curStmt := s.sid;
  currentLoc := get_stmtLoc s.skind;
  markLocationChecked ();
  let varsInScope = Dlocals.liveAtStmtStart s in
  if !verbose then 
    log "STMT %d.  Live vars: %a\n" s.sid
      (docList (fun v -> text v.vname)) (VS.elements varsInScope);
  let mkBlockMaybe (instrs: instr list) (sk: stmtkind) =
    if instrs <> [] then
      Block (mkBlock [mkStmt (Instr instrs); mkStmt sk])
    else
      sk
  in
  let sk' =
    match s.skind with
    | Instr instrs ->
        startExtraInstrs ();
        ignore (List.fold_left checkInstr varsInScope instrs);
        Instr (endExtraInstrs ())
    | Return (eo, _) ->
        startExtraInstrs ();
        checkReturn eo;
        mkBlockMaybe (endExtraInstrs ()) s.skind
    | If (e, b1, b2, _) ->
        startExtraInstrs ();
        coerceExp e intType;
        let extras = endExtraInstrs () in
        checkBlock b1;
        checkBlock b2;
        mkBlockMaybe extras s.skind
    | Switch (e, b, _, _) ->
        startExtraInstrs ();
        coerceExp e intType;
        let extras = endExtraInstrs () in
        checkBlock b;
        mkBlockMaybe extras s.skind
    | Loop (b, _, _, _)
    | Block b ->
        checkBlock b;
        s.skind
    | Goto _
    | Break _
    | Continue _ ->
        s.skind
    | TryFinally _
    | TryExcept _ -> E.s (E.unimp "exceptions not supported\n")
  in
  s.skind <- sk'

and checkBlock (b : block) : unit =
  if isTrustedAttr b.battrs then
    markTrustedBlock b
  else
    List.iter
      (fun s ->
         if !multipleErrors then
           try checkStmt s with E.Error -> ()
         else
           checkStmt s)
      b.bstmts

let checkTypedef (ti: typeinfo) : unit =
  checkType emptyContext ti.ttype (dprintf "typedef %s" ti.tname)

let checkStruct (ci: compinfo) : unit =
  let ctx =
    List.fold_left
      (fun acc fld -> addBinding acc fld.fname zero)
      emptyContext
      ci.cfields
  in
  List.iter
    (fun fld -> checkType ctx fld.ftype
                  (dprintf "field %s of struct %s" fld.fname ci.cname))
    ci.cfields

let checkVar (vi: varinfo) (init: initinfo) : unit =
  checkType (globalsContext vi) vi.vtype (dprintf "global %s" vi.vname)

let makeCFG (fd : fundec) : unit =
  Cfg.clearCFGinfo fd; (* zra *)
  let cnt = Cfg.cfgFun fd in
  Cfg.start_id := cnt + !Cfg.start_id

let checkFundec (fd : fundec) : unit =
  if !verbose then
    log "Starting function %s" fd.svar.vname;
  curFunc := fd;
  clearBoundsTable ();
  markLocationChecked ();
  (* Check types of formals. *)
  let ctxFormals = formalsContext fd in
  List.iter
    (fun vi -> checkType ctxFormals vi.vtype
                 (dprintf "formal parameter %s" vi.vname))
    fd.sformals;
  (* Check types of locals. *)
  let ctxLocals = localsContext fd in
  List.iter
    (fun vi -> checkType ctxLocals vi.vtype
                 (dprintf "local variable %s" vi.vname))
    fd.slocals;
  (* Check type of return value. *)
  let returnType =
    match fd.svar.vtype with
    | TFun (returnType, _, _, _) -> returnType
    | _ -> E.s (bug "Expected function type")
  in
  checkType ctxFormals returnType (text "return type");
  (* Now find out which variables the return type depends upon.  Save the
   * values of these variables so that we can check the return type later. *)
  let returnDeps = depsOfType returnType in
  startExtraInstrs ();
  returnCtx :=
    List.fold_right
      (fun name acc ->
         if name <> thisKeyword then
           let vi =
             try
               List.find (fun vi -> vi.vname = name) fd.sformals
             with Not_found ->
               E.s (bug "Expected formal named %s" name)
           in
           addBinding acc name (Lval (var (addTmpSet (Lval (var vi)))))
         else
           acc)
      returnDeps
      emptyContext;
  let instrs = endExtraInstrs () in
  (* We add the instrs to the beginning of the function.  We also add an
   * empty list to the beginning so that Dlocals.doLiveness can add
   * initialization instructions to the first statement without messing up
   * the CFG. *)
  fd.sbody.bstmts <- mkStmt (Instr []) :: mkStmt (Instr instrs) ::
                     fd.sbody.bstmts;
  (* fix block, see if cfg should be used, check block *)
  fixBlock fd.sbody;
  makeCFG fd; (* formerly done only if !optLevel >= 2 *) 
  Stats.time "Liveness" Dlocals.doLiveness fd;
  checkBlock fd.sbody;
  (* Clean up. *)
  curFunc := dummyFunDec;
  curStmt := -1;
  returnCtx := emptyContext;
  Dlocals.clearLiveness ();
  ()


(** Check the functions in a file. *)
let checkFile (f: file) (globinit: fundec) (fdat : DPF.functionData) : unit =
  if !verbose then
    log "Using optimization level %d" !optLevel;
  allowChecks := true;
  iterGlobals f 
    (fun global ->
      match global with
      | GType (ti, _) -> checkTypedef ti
      | GCompTag (ci, _) when ci.cstruct -> checkStruct ci
      | GVar (vi, init, _) -> checkVar vi init
      | GFun (fd, loc) -> 
          if isTrustedType fd.svar.vtype then
            markTrustedBlock fd.sbody
          else begin
            checkFundec fd;
            DO.optimFunction fd loc fdat;
            if !verbose then log "Done with optimizations";
          end
       | _ -> ());
  ()
