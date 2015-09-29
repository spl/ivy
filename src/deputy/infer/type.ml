(*
 *
 * Copyright (c) 2001-2006, 
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
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
 * C Structural Type Equality
 *)
open Cil
open Pretty
module N = Ptrnode
module E = Errormsg

let debugType = false

let useCompatOnRepresentative = false

(* sm: When true, explicit padding elements are inserted, to try
 * to fix the problem demonstrated by test/small2/alignprob.c; when
 * false, we're back to the previous system.
 *
 * NOTE: The current implementation is really just a proof of concept,
 * as the only entities that cause padding to be inserted are 'double's.
 * A more elaborate system, one that ideally works for e.g. 64-bit 
 * aligned 'long' vs. 32-bit 'int', etc., is still future work.
 *)
let newPadding = false (* matth: we don't need this for deputy, because we 
                          don't change any layouts *)

(* When true, if we conclude that two types are incompatible due to
 * padding/alignment issues, log "padding mismatch".  Generally, such
 * cases are exactly those that would have been allowed in the previous
 * system but not in the new system, so we can check that the new
 * system isn't rejecting things that are ok and were allowed before. *)
let logPaddingMismatches = true

let arraysThatHaveBeenComparedWithNonArrays = Hashtbl.create 511
let arraysThatHaveBeenComparedWithArrays = Hashtbl.create 511
(* A hash-table of arrays that have been compared with non-arrays. If that
 * happened to an array that ends up INDEX, we flag an error (because INDEX
 * changes the size/layout of the array, so our previous assessment was
 * incorrect). 
 *)


  (* replace a "void *" type with its representative *)
  (* tau is already unrolled. The chain goes orig_tau -> replacedTau *)
let polymorphic_replace (tau: typ) : typ * N.chain =
  match tau with
  | (TPtr((TVoid _),attr)) -> begin
      match N.nodeOfAttrlist attr with
        Some(n) -> 
          let rep,why_n_rep = N.get_rep_why n in 
          (* gn: use the attributes of the representatives not ours !! *)
          if N.hasFlag rep N.pkCompatWithScalars then begin
            intType, why_n_rep 
            end else
            (TPtr(rep.N.btype, rep.N.attr)), why_n_rep
      | None -> tau, N.mkRIdent
  end
  | _ -> tau, N.mkRIdent

let ok_to_call_compat t1 t2 = 
  isVoidPtrType t1 || isVoidPtrType t2 ||
  (isPointerType t1 && isPointerType t2)


(* A failure handler is called on two nodes whose base types fail to match 
 * up. This should make those nodes have WILD types (and thus force them to 
 * match up) *)
type failureHandler = N.node -> N.chain -> N.node -> unit

(* A compatHandler is called on two nodes that must have an equal
 * representation. This should put an ECompat edge between those two nodes. 
 *)
type compatHandler = N.chain -> Cil.typ -> Cil.typ -> unit

(* Idealized representation of C types to make structural equality
 * comparisons easier. *)
type layout =     
    Scalar of int   (* length in bits *)
  | Array of typ * (layout list) * int
      (* original array type, layout of element type, size *) 
  | Pointer of typ (* original CIL pointer type
                    * either TPtr or TFun *) 
                   (* GN: why not TPtr(TFun... )? *)
  | Function of typ (* GN: add this one for TFun *)
  | Anything of int (* length in bits, matches anything *)
  | Padding of int  (* sm: pad out to a specific bit boundary *)

(* use this instead of "l1 = l2" because OCaml structural equality may 
 * exhaust all memory checking Cil.typ, and layout lists mention Cil.typs. 
 *)
let rec ll_eq_simple (l1 : layout list) (l2 : layout list) : bool = 
  match l1, l2 with
    [], [] -> true
  | Array(_,left,i) :: tl1 , Array(_,right,j) :: tl2 ->
    (i = j) && (ll_eq_simple left right) && (ll_eq_simple tl1 tl2)
  | Pointer(t1) :: tl1, Pointer(t2) :: tl2 
  | Function(t1) :: tl1, Function(t2) :: tl2 ->
    typeSig t1 = typeSig t2 && ll_eq_simple tl1 tl2
  | Anything(i) :: tl1, Anything(j) :: tl2 -> 
    i = j && ll_eq_simple tl1 tl2
  | Padding(i) :: tl1, Padding(j) :: tl2 ->
    i = j && ll_eq_simple tl1 tl2
  | _ -> false
   
let is_array (l: layout) : bool =
  match l with
    Array(_) -> true
  | _ -> false   

(* Pretty printing *)
let rec d_layout () l = match l with
    Scalar(i) -> dprintf "Scalar(%d)" i 
  | Anything(i) -> dprintf "Anything(%d)" i 
  | Array(_,ll,i) -> dprintf "Array %d %a" i d_layout_list ll
  | Pointer(tau) -> dprintf "Ptr (%a)" d_type tau
  | Function(tau) -> dprintf "Fun (%a)" d_type tau
  | Padding(i) -> dprintf "Pad(%d)" i
and d_layout_list () ll = 
  dprintf "@[[%a]@]" (docList ~sep:(chr ';' ++ break) (d_layout ())) ll

let global_layout_list_cache = Hashtbl.create 2047

(* does a CIL type's representation include any doubles? *)
let rec has_doubles (orig_t : typ) : bool =
  let t = unrollType orig_t in
  match t with
  | TFloat (FDouble, _) -> true
  | TArray (tau,_,_) -> (has_doubles tau)    (* should sizeless be false? *)
  | TComp (ci,_) ->
      let test (fi: fieldinfo) : bool =
        (has_doubles fi.ftype)
      in
      (List.exists test ci.cfields)
  | _ -> false

(* Convert a C/CIL type into a list of layouts. This usually amounts
 * to flattening structures and making padding and alignment explicit. *)
let rec convert_type_to_layout_list (orig_t : typ) =
  let t = unrollType orig_t in 
  let result = 
  match t with
    TVoid _ -> (* failwith "convert_type_to_layout_list: void" *) [] 
  | TFloat (FDouble, _) when newPadding ->
      (* sm: wide scalar is preceded by padding to its width; I also
       * follow it with padding to make it clear that it ends on a 64-bit
       * boundary, for compatibility with a type where a struct ends
       * after a double *)
      [Padding(64); Scalar(64); Padding(64)]
  | TInt _ | TFloat _ | TEnum _ -> 
      [Scalar((try bitsSizeOf t with SizeOfError _ -> 0))]
  | TPtr(_) -> [Pointer(t)]
  | TFun(_) -> [Function(t)] (* gn: was [Pointer(t)] *)

  | TArray(tau,Some(e),_) when e = one -> convert_type_to_layout_list tau 
  | TArray(tau,Some(e),_) -> 
      let ll = convert_type_to_layout_list tau in
      let e = constFold true e in 
      let len = begin match isInteger e with
        Some(i64) -> Int64.to_int i64
      | None -> 
          E.s (E.unimp 
            "type: convert_type_to_layout_list: non-const length %a" 
            d_type t)
      end in
      ( match ll with
          [Scalar(length)] -> 
                (* [Scalar(length * len)] *)
                if (length = 0) then begin
                  ignore (E.warn "type: convert_type_to_layout_list: array contains nothing: %a" d_type t) 
                end ; 
                [Array(t,[Scalar(length*len)],1)] 
        | _ -> [Array(t,ll,len)])
  | TArray(tau,None,al) ->
      convert_type_to_layout_list (TArray (tau,Some zero,al))
  | TComp(ci,al) when ci.cstruct ->
      let total_size = try (bitsSizeOf t) with SizeOfError _ -> 0 in
      let seen_size = ref 0 in 
      let ll = ref [] in 
      List.iter (fun fi -> 
        let field_size_bits = 
          match fi.fbitfield with 
            Some(size) -> size
          | None -> (try bitsSizeOf fi.ftype with SizeOfError _ -> 0)
        in 
        let field_offset_bits, field_width_bits = 
          (try bitsOffset t (Field(fi,NoOffset)) with SizeOfError _ -> 0,0) in
        let field_offset = field_offset_bits in 
        if (!seen_size < field_offset) then begin
          ll := !ll @ [Scalar(field_offset - !seen_size)];
          seen_size := field_offset 
        end ;
        let field_ll = match fi.fbitfield with
          Some(size) -> [Scalar(size)]
        | None -> convert_type_to_layout_list fi.ftype 
        in
        ll := !ll @ field_ll ;
        seen_size := !seen_size + field_size_bits ; 
      ) ci.cfields ;
      if (!seen_size < total_size) then begin
        ll := !ll @ [Scalar(total_size - !seen_size)];
      end ;
      if (newPadding && (has_doubles t)) then
        (* sm: alignment padding at start and end *)
        [Padding(64)] @ !ll @ [Padding(64)]
      else
        !ll
   (* Unions. We have already added (in markptr) casts from the longest field 
    * to all of the others. From now on it is safe to work with the longest 
    * field instead of the union *)
  | TComp(ci,al) when not ci.cstruct -> 
       let rec longest (sofar: typ) (sofarsize: int) = function 
           [] -> 
             if sofarsize = 0 then 
               E.s (bug "type: convert_type_to_layout_list: Could not find the longest field in %s\n"
                      (compFullName ci))
             else
               sofar
                 
         | fi :: restfi -> 
             let this_size = 
               try bitsSizeOf fi.ftype with SizeOfError _ -> 0 in
             if this_size > sofarsize then 
               longest fi.ftype this_size restfi
             else
               longest sofar sofarsize restfi
       in
       convert_type_to_layout_list (longest voidType 0 ci.cfields)
  | TComp _ -> E.s (E.bug "type: convert_type_to_layout_list: mystery comp")
  | TNamed _ -> E.s (E.bug "type: convert_type_to_layout_list: named")
  | TBuiltin_va_list _ -> 
      E.s (E.bug "type: convert_type_to_layout_list: va_list")
  in
  
  (* strip leading padding; this is needed so that a struct that has
   * no doubles can be a subtype of one that has them after the common
   * prefix (test/small2/subtypebug2.c) *)
  let rec strip_lead_pad (ll : layout list) : layout list =
    match ll with
    | Padding(i) :: tl -> (strip_lead_pad tl)
    | _ -> ll
  in

  (* peephole optimization for layout lists *)
  let rec peephole ll =
    match ll with
      [] -> []
    | Scalar(i) :: Scalar(j) :: tl -> peephole (Scalar(i+j) :: tl)
    | Padding(i) :: Padding(j) :: tl ->
        (* sm: larger padding dominates (assuming all are powers of 2...) *)
        (peephole ((Padding(max i j)) :: tl))
    | hd :: tl -> hd :: (peephole tl)
  in

  (peephole (strip_lead_pad result))

(* Strips 'i' bits of scalars from the beginning of the layout list 'll'.
 * This is a utility function called by equal_ll. 
 * Returns a boolean success code and new layout list representing the
 * suffix or raises an exception on failure. *)
let rec strip_scalar_prefix (ll : layout list) i =
  if i = 0 then 
    true, ll
  else if i < 0 then 
    true, (Scalar(-i) :: ll)
  else match ll with
    [] -> false, [] 
  | Scalar(j) :: tl -> (strip_scalar_prefix tl (i - j))
  | Anything(j) :: tl -> 
      if (i >= j) then (* eat up the entire "Anything" *)
        (strip_scalar_prefix tl (i - j))
      else
        true, (Anything(j - i) :: tl)
  | Padding(j) :: tl -> E.s (E.bug "strip_scalar_prefix applied to padding")
  | Array(_,inner_ll,0) :: tl -> (strip_scalar_prefix tl i)
  | Array(_,inner_ll,1) :: tl -> (strip_scalar_prefix (inner_ll @ tl) i)
  | Array(tau,inner_ll,j) :: tl -> 
      let new_ll = inner_ll @ (Array(tau,inner_ll,j-1) :: tl) in
      (strip_scalar_prefix new_ll i )
  | Pointer(_) :: tl 
  | Function(_) :: tl -> 
      let _, res = strip_scalar_prefix (Scalar(4*8) :: tl) i in
      false, res
      (* Consider the following code:
       * void ( * fptr )() ;
       * int *x;
       *
       * x = ( int * ) fptr; 
       *
       * In this case, we will end up comparing a scalar with a function,
       * so we will want to call strip_scalar_prefix on a function. It
       * should return false. *)
        
(* When we are computing "t1 < t2" or "t1 > t2", which one can be
 * smaller? *)
type subtype_direction = LeftCanEndEarly | RightCanEndEarly | MustBeEqual

let flip_subtyping st = match st with
    LeftCanEndEarly -> RightCanEndEarly 
  | RightCanEndEarly -> LeftCanEndEarly 
  | MustBeEqual -> MustBeEqual 

(* for debugging output *)
let subtype_direction_name (st: subtype_direction) : string = match st with
    LeftCanEndEarly -> "LeftCanEndEarly"
  | RightCanEndEarly -> "RightCanEndEarly"
  | MustBeEqual -> "MustBeEqual"

(*
 * Check to see if a type is made up entirely of scalars. 
 *)
let all_scalars
  ?(replace=(fun a -> a, N.mkRIdent)) 
  t1
= 
  let t1,ex1 (* ex1: orig_t1 -> t1 *) = replace (unrollType t1) in
  (* GN: another implementation, that seems to work in the presence of unions *)
  not (existsType (function TPtr _ -> ExistsTrue | _ -> ExistsMaybe) t1)
(*
  try
    let ll = convert_type_to_layout_list t1 in
    let rec all_scalars_ll ll = match ll with
      | [] -> true 
      | [Scalar(_)] -> true
      | Array(_,ll,_) :: tl -> (all_scalars_ll ll) && (all_scalars_ll tl)
      | _ -> false
    in 
    all_scalars_ll ll 
  with e -> begin
    ignore (E.warn "all_scalars raises %s" (Printexc.to_string e));
    false
  end
*)

(* These memoization tables store results from previous calls to "compare" *)
let memoize_equal = Hashtbl.create 32767
let memoize_subtype = Hashtbl.create 32767

(* This is the main (conceptual) entry point for this file.
 * 
 * Use physical subtyping (a la Reps, etc.) to determine the relationship
 * between t1 and t2. In general, this is similar to width subtyping (like
 * in object oriented languages) with the following exceptions:
 *
 * (1) "void*" is treated as a type variable and special handling exists
 *     to replace a "void*" with its representative type. Any direct
 *     comparison with a representative-less "void*" type succeeds. 
 * (2) A special "compat" function is called on all pointers that must have
 *     the same physical representation and on all pointers that area
 *     compared against a representative-less "void*" type. 
 * (3) A special "failure" function is called on all internal pointers that
 *     "fail to match up correctly" and must thus have their types checked
 *     at run-time (e.g., by making them WILD in CCured). "compare" can
 *     return true even if some lower-level pointers fail to match up,
 *     provided that it calls "failure" on them. 
 *
 * Because memoization is used to prevent this from taking too much time
 * over the course of the analysis, "compat" and "failure" are only
 * guaranteed to be called once per pair of types, even across many
 * invocations of "compare". 
 *)
let rec compare  
  (compat: compatHandler)
  (failure: failureHandler) 
  (why_t1_t2: N.chain) (* Goes t1 -> t2 *)
  (t1: typ)
  (t2: typ) 
  (mode: subtype_direction) : bool 
=
  let t1r, why_t1_t1r = polymorphic_replace (unrollType t1) in
  let t2r, why_t2_t2r = polymorphic_replace (unrollType t2) in
  (* explanation: t1r -> t1 -> t2 -> t2r *)
  let why_t1r_t2r = 
    N.mkRTrans (N.mkRSym why_t1_t1r) (N.mkRTrans why_t1_t2 why_t2_t2r) in

  if ok_to_call_compat t1r t2r then begin
    if useCompatOnRepresentative then 
      compat why_t1r_t2r t1r t2r
    else
      compat why_t1_t2 t1 t2;
  end ;

  if debugType then begin
    ignore (E.log "compare: %a %a@!" d_type t1r d_type t2r)
  end ; 

  (* Can we short-circuit this calculation because one of them is a
   * "void*", a type variable? *)
  if isVoidPtrType t1r || isVoidPtrType t2r then
    true
  else 
  (* Can we short-circuit this calculation because we have considered these
   * two types before, and they are thus in our memoization tables? *)
    let already_seen, old_answer = 
      (* if they are equal, they are certainly sub-types *)
      if Hashtbl.mem memoize_equal (t1r,t2r) then
        true, Hashtbl.find memoize_equal (t1r,t2r)
      else if Hashtbl.mem memoize_equal (t2r,t1r) then
        true, Hashtbl.find memoize_equal (t2r,t1r)
      (* they are not equal, but perhaps we have considered this
       * subtyping comparison before *)
      else match mode with
        LeftCanEndEarly ->  
          if Hashtbl.mem memoize_subtype (t1r,t2r) then
            true, Hashtbl.find memoize_subtype (t1r,t2r)
          else
            false, false
      | RightCanEndEarly -> 
          if Hashtbl.mem memoize_subtype (t2r,t1r) then
            true, Hashtbl.find memoize_subtype (t2r,t1r)
          else 
            false, false
      | MustBeEqual ->      
            false, false 
    in if already_seen then old_answer 
  else if 
  (* Can we short-circuit this calculation because the sizes are clearly
   * wrong? *)
    let s1 = try Some(bitsSizeOf t1r) with SizeOfError _  -> None in
    let s2 = try Some(bitsSizeOf t2r) with SizeOfError _ -> None in
    match mode,s1,s2 with
      LeftCanEndEarly,Some(s1),Some(s2) -> s1 > s2
    | RightCanEndEarly,Some(s1),Some(s2) -> s1 < s2
    | MustBeEqual,Some(s1),Some(s2) -> s1 <> s2
    | _ -> false 
    then
    false
  else if (* Can we short-circuit this based on typesigs? *)
    (typeSig t1r) = (typeSig t2r) then 
    true
  else 
  (* Looks like we must actually do the calculation. *) 
  let l1 = convert_type_to_layout_list t1r in
  let l2 = convert_type_to_layout_list t2r in
  if debugType then begin
    ignore (E.log "compare: %a = %a@!" d_type t1r d_layout_list l1) ;
    ignore (E.log "compare: %a = %a@!" d_type t2r d_layout_list l2) ;
  end ; 
  let answer = 
    (* Try one last time to short-circuit the long calculation based on a
     * simple equality-check for layout lists *)
    if ll_eq_simple l1 l2 then 
      true
    else begin
      (* In order to make this algorithm terminate, we cannot recursively
       * consider this particular comparison. We know that (t1r,t2r) is
       * not in the memoize_equal hash table at all at this point. *)
      Hashtbl.replace memoize_equal (t1r,t2r) true ;
      let result = equal_ll l1 l2 mode compat failure why_t1r_t2r in
      Hashtbl.remove memoize_equal (t1r,t2r) ;
      result 
    end
  in
  begin 
  (* update our memoization tables so that we never compute this
   * answer again *)
  match mode with
    LeftCanEndEarly ->  Hashtbl.add memoize_subtype (t1r,t2r) answer
  | RightCanEndEarly -> Hashtbl.add memoize_subtype (t2r,t1r) answer
  | MustBeEqual ->      Hashtbl.add memoize_equal (t1r,t2r) answer
  end ;
  if debugType then begin
    ignore (E.log "compare: %b %a %a@!" answer d_type t1r d_type t2r)
  end ; 
  answer 
      
(* 
 * arguments: 
 *   l1 l2     // check and see if these two layout lists are equal
 *   subtyping // which one of these lists can end early? 
 *   compat    // call this function on all lined-up pointers in l1, l2
 *   failure   // call on pointer types that fail to match up 
 *   why_l1_l2 // why are we comparing l1 and l2? 
 *)
and equal_ll 
  (l1:layout list) 
  (l2: layout list)
  (subtyping: subtype_direction)
  (compat: compatHandler)
  (failure: failureHandler) 
  (why_l1_l2: N.chain)
=
  if debugType then 
    ignore (E.log "equal_ll (%s):@!%a@!%a@!" 
                  (subtype_direction_name subtyping)
                  d_layout_list l1 d_layout_list l2);
 
  (* pulled this out b/c ocaml won't let me combine two match clauses
   * when they have 'when' limiters... *)
  let padding_mismatch () : bool =
    if logPaddingMismatches then
      ignore (E.log "padding mismatch:@!  %a@!  %a@!"
                    d_layout_list l1 d_layout_list l2);
    (* sm: Wes and I concluded that we do not need to check the tails,
     * because by returning false here (and not simply calling 'failure'),
     * we guarantee that all pointers in both structures will become wild *)
    false
  in

  let final_answer = 
  match l1, l2 with
    [], [] -> (true)
  | [], _ when subtyping = LeftCanEndEarly -> (true)
  | _, [] when subtyping = RightCanEndEarly -> (true)

  | [], _ 
  | _, [] -> (false)

  (* sm: padding must match with padding *)
  | (Padding(i) :: tl1), (Padding(j) :: tl2) ->
      i = j && equal_ll tl1 tl2 subtyping compat failure why_l1_l2

  (* padding mismatch.
   * hack: If the other side is an Array, then we need to unroll it.
   * So, the 'when' clause prevents this one from matching, so it
   * will instead match the Array clauses below.  I wanted to just move
   * the array clauses to the top, but that causes a problem since
   * the Scalar clause would be below the Array clause; see
   * test/small2/subtypebug1.c.  test/small2/getaddrinfo.c is a
   * test that reveals the need for the 'when' in the first place. *)
  | (Padding(_) :: _), (hd2 :: _) when (not (is_array hd2)) ->
      padding_mismatch()
  | (hd1 :: _), (Padding(_) :: _) when (not (is_array hd1)) ->
      padding_mismatch()

  | (Scalar(i) :: tl), _ -> 
      let new_l1 = tl in
      let worked, new_l2 = strip_scalar_prefix l2 i in
      let answer = equal_ll new_l1 new_l2 subtyping compat failure why_l1_l2 in
      (answer && worked)

  | (Anything(i) :: tl), _ -> 
      let new_l1 = tl in
      let _, new_l2 = strip_scalar_prefix l2 i in
      equal_ll new_l1 new_l2 subtyping compat failure why_l1_l2

  (* array on left *)
  | (Array(tau1,inner_ll1, i1) :: tl1) , _ ->
      (* first, handle special case where we match up arrays *)
      let same = ref false in 
      let remove_1 = ref None in 
      let remove_2 = ref None in 
      (match l2 with
        Array(tau2,inner_ll2, i2) :: tl2 -> 
          Hashtbl.replace arraysThatHaveBeenComparedWithArrays 
                (tau1,tau2) why_l1_l2 ;
          (* When we unpeel these guys, it will look like they are being
           * compared against non-arrays when we compare them against
           * their respective contents. So we remember now if they had
           * a clean slate before and we'll reclean it later before
           * we return. *)
          if not (Hashtbl.mem arraysThatHaveBeenComparedWithNonArrays tau1)
            then remove_1 := Some(tau1) ;
          if not (Hashtbl.mem arraysThatHaveBeenComparedWithNonArrays tau2)
            then remove_2 := Some(tau2) ;
          if (i1 = i2 && ll_eq_simple inner_ll1 inner_ll2) then
            same := true 
      | _ ->  
          Hashtbl.replace arraysThatHaveBeenComparedWithNonArrays 
                tau1 why_l1_l2 
      ) ; 
      if !same then
        true
      else begin
        let new_l1 = 
          if i1 = 0 then
            tl1 
          else if i1 = 1 then 
            inner_ll1 @ tl1 
          else 
            inner_ll1 @ (Array(tau1,inner_ll1,i1-1) :: tl1)
        in 
        let final_answer = equal_ll new_l1 l2 subtyping compat failure why_l1_l2
        in 
        (match !remove_1 with
          Some(t) -> Hashtbl.remove arraysThatHaveBeenComparedWithNonArrays t
        | _ -> () ) ;
        (match !remove_2 with
          Some(t) -> Hashtbl.remove arraysThatHaveBeenComparedWithNonArrays t
        | _ -> () ) ;
        final_answer
      end 

  (* array/anything on right *)
  | _, (Array(_) :: _)
  | _, (Anything(_) :: _) -> 
      (* flip things around, use the code above *)
      equal_ll l2 l1 (flip_subtyping subtyping) compat failure
        (N.mkRSym why_l1_l2)

  | (Pointer(tau1) :: tl1) , (Pointer(tau2) :: tl2) -> 
      (* already unrolled *)
      let tau1r, why_tau1_tau1r = polymorphic_replace (unrollType tau1) in
      let tau2r, why_tau2_tau2r = polymorphic_replace (unrollType tau2) in
      if debugType then 
        ignore (E.log "Type.equal_ll for@!    @[%a@]@!and @[%a@]@!@!"
                  d_type tau1r d_type tau2r);
      (* explanation: tau1r -> tau1 -> tau2 -> tau2r *)
      let why_tau1r_tau2r = 
        N.mkRTrans (N.mkRSym why_tau1_tau1r) 
          (N.mkRTrans why_l1_l2 why_tau2_tau2r) in

      (if useCompatOnRepresentative then
        (if ok_to_call_compat tau1r tau2r then
          compat why_tau1r_tau2r tau1r tau2r)
      else
        (if ok_to_call_compat tau1 tau2 then
          compat why_l1_l2 tau1 tau2));

      if isVoidPtrType tau1r || isVoidPtrType tau2r then 
        () (* no recursive calls *)
      else begin 
        match tau1r, tau2r with
        | TPtr(inner1,a1), TPtr(inner2,a2) -> begin (* two non-fun pointers *)
            if debugType then 
              ignore (E.log "Type.equal_ll doing inner pointers@!    @[%a@]@!and @[%a@]@!@!"
                        d_type inner1 d_type inner2);
            let answer = 
              compare compat failure why_tau1r_tau2r inner1 inner2 MustBeEqual
            in
            if not answer then begin
              (* Get the nodes involved *)
              let n1 = 
                match N.nodeOfAttrlist a1 with
                  Some n1 -> n1
                | _ -> E.s (bug "Type.equal_ll: type %a does not have a node"
                              d_type tau1r)
              in
              let n2 = 
                match N.nodeOfAttrlist a2 with
                  Some n2 -> n2
                | _ -> E.s (bug "Type.equal_ll: type %a does not have a node"
                              d_type tau2r)
              in
              if debugType then 
                ignore (E.log "Call failure %d and %d (from Inner)\n"
                          n1.N.id n2.N.id);
              failure n1 why_tau1r_tau2r n2;
            end
        end

        | TInt _, _
        | _ , TInt _ -> 
          (* We thought one of these was a pointer, but its rep was
           * an integer. In this case we just put the pointer in the same
           * EQ class as the void* and let our logic in the solver work
           * it out. They are not compatible, and our check in the solver
           * with the compatWithScalars flag should notice that and
           * make them WILD. *) 
          if ok_to_call_compat tau1 tau2 then (* should always be true *)
            compat why_l1_l2 tau1 tau2

        | _, _ -> E.s (E.bug "type: unexpected mystery pointers %a and %a"
                         d_type tau1r d_type tau2r) 
      end ; 

      (* Note that because we are assuming that "failure" makes its
       * arguments WILD (or otherwise invisible to physical subtyping), we
       * don't actually need to know whether the above check passed or
       * failed at all. If it passed, the types are fine so far. If it
       * failed, those two pointers will be made WILD, so they will be
       * checked at run-time, so these two lists are still fine. *)
      (* Now check the rest of the layout list! *)
      equal_ll tl1 tl2 subtyping compat failure why_l1_l2

  (* Compare two functions *)
  | Function(TFun(rt1,vlo1,_,_) as t1) :: tl1, 
    Function(TFun(rt2,vlo2,_,_) as t2) :: tl2 -> 
      (* two fun ptrs *)
      (* Check return types *)
      let rt1r, why_rt1_rt1r = polymorphic_replace (unrollType rt1) in
      let rt2r, why_rt2_rt2r = polymorphic_replace (unrollType rt2) in
      (* explanation: rt1r -> rt1 -> rt2 -> rt2r *)
      let why_rt1r_rt2r = N.mkRTrans (N.mkRSym why_rt1_rt1r) 
          (N.mkRTrans why_l1_l2 why_rt2_rt2r) in
      (if useCompatOnRepresentative then 
        (if ok_to_call_compat rt1r rt2r then 
          compat why_rt1r_rt2r rt1r rt2r)
      else
        (if ok_to_call_compat rt1 rt2 then 
          compat why_l1_l2 rt1 rt2));
      let ret_ok = 
        compare compat failure why_rt1r_rt2r rt1r rt2r MustBeEqual in 
      if debugType then 
        ignore (E.log "Type.equal_ll preparing to do arguments of@!    @[%a@]@!and @[%a@]@!@!" d_type t1 d_type t2);
      (* Check the arguments *)
      let al1 = argsToList vlo1 in
      let al2 = argsToList vlo2 in
      let args_ok = 
        if List.length al1 <> List.length al2 then begin 
          false 
        end else begin
          (* check every argument *)
          let answer = ref true in
          let compareFormalNames = ref false in
          List.iter2 (fun (_, arg1t, _) (_, arg2t, _) ->
            let at1r, why_argt1_at1r = polymorphic_replace (unrollType arg1t) in
            let at2r, why_argt2_at2r = polymorphic_replace (unrollType arg2t) in
            (* explanation: at1r -> argt1 -> argt2 -> at2r *)
            let why_at1r_at2r = 
              N.mkRTrans (N.mkRSym why_argt1_at1r) 
                (N.mkRTrans why_l1_l2 why_argt2_at2r) in
            if debugType then 
              ignore (E.log "Type.equal_ll doing argument@!    @[%a@]@!and @[%a@]@!@!" d_type at1r d_type at2r);
            (if useCompatOnRepresentative then 
              (if ok_to_call_compat at1r at2r then 
                        compat why_at1r_at2r at1r at2r)
            else
              (if ok_to_call_compat arg1t arg2t then 
                compat why_l1_l2 arg1t arg2t));
            let ans = 
              compare compat failure why_at1r_at2r at1r at2r MustBeEqual in 
            answer := ans && !answer ;
            
            (* matth: this doesn't belong here, but I don't know where to put
               it.  Make sure the formal types agree on __COUNT and __SIZE
               attributes.  This prevents casting away of these attributes with
               function pointers. *)
            let a1 = typeAttrs at1r in
            let a2 = typeAttrs at2r in
            let doCheck what =
              let a1f = filterAttributes what a1 in
              if a1f <> filterAttributes what a2 then begin
                ignore (warn
                  "Mismatched \"%s\" attributes in@!    @[%a@]@!and @[%a@]@!@!"
                          what d_type at1r d_type at2r);
                answer := false
              end;
              if a1f <> [] then
                compareFormalNames := true;
            in
            doCheck "size";
            doCheck "count";
            ) 
            al1 al2 ; 
          if !compareFormalNames then begin
            (* If any formal has a SIZE or COUNT attribute, make sure that
               all of the names of the formals match.  See small2/size3.c
               test funcptr_wrongorder. *)
            List.iter2 
              (fun (name1, arg1t, _) (name2, _, _) -> 
                 let hasSizeOrCount t =
                   let a = typeAttrs t in
                   (hasAttribute "size" a) || (hasAttribute "count" a)
                 in
                 if name1 <> name2 
                   (* If this formal has a SIZE or COUNT annotation,
                      it's been renamed already.  But no other formal can
                      depend on it, so it's okay to skip this case. *)
                   && (not (hasSizeOrCount arg1t)) then begin
                     ignore (warn
                               "The names of formals \"%s\" and \"%s\" must match when using SIZE/COUNT."
                               name1 name2);
                     answer := false
                   end)
              al1 al2
          end;
          !answer
        end 
      in 
      (* now check the rest of the layout list! *)
      let (restok) = equal_ll tl1 tl2 subtyping compat failure why_l1_l2 in
      (* We have to return false if either the args of the returns are not Ok *)
      (restok && args_ok && ret_ok)
      

  (* This match case is used: in particular 'something' could be
   * Scalar(i) *)
  | (Pointer(p) :: tl1) , something when isVoidType p -> 
      (* special scalar node handling *)
    E.s (E.bug "type: unify Ptr(%a) with the scalar node" d_type p)

  | (_ :: tl1), (_ :: tl2) -> (* NOT EQUAL *)
      (* but check the rest anyway! *)
      let _ = equal_ll tl1 tl2 subtyping compat failure why_l1_l2 in 
      false 
  in 
  (* ignore (E.warn "subtype: %b@!%a@!%a"
    final_answer d_layout_list l1 d_layout_list l2) ;*)
  (final_answer)


(* subtype and equal both just call "compare" *)
let subtype ~(compat:compatHandler) 
            ~(failure:failureHandler) 
            ~(why_small_big:Ptrnode.chain) 
            ~(small:Cil.typ) 
            ~(big:Cil.typ) : bool =
  compare compat failure why_small_big small big LeftCanEndEarly 


let equal ~(compat:compatHandler)
          ~(failure:failureHandler) 
          ~(why_t1_t2:Ptrnode.chain) 
          ~(t1:Cil.typ) 
          ~(t2:Cil.typ) : bool =
  compare compat failure why_t1_t2 t1 t2 MustBeEqual 

(* Ptrnode.ml needs to call subtype *)
let init () = 
  N.isSubtype := 
  fun big small -> 
    try
      subtype 
        ~compat:(fun _ _ _ -> ())
        ~failure:(fun _ _ _ -> raise Not_found)
        ~why_small_big:N.mkRIdent
        ~small:small
        ~big:big 
    with Not_found -> 
      false
