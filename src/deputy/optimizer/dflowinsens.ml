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
 * dflowinsens.ml
 *
 * A flow insensitive pass that looks for
 * easy-to-reason-about checks.
 *
 *
 *)

open Cil
open Expcompare
open Pretty
open Dutil
open Dattrs
open Dcheckdef
open Doptimutil

module DO = Ivyoptions
module E = Errormsg
module S = Stats
module DCE = Dcanonexp
module Z = Zrapp

(* Called when a compile-time assertion failure is detected.  This
 * function should mirror deputy_fail in the runtime library in terms
 * of output formatting. *)
let deputyFail (c: check) : unit =
  let why = checkWhy c in
  let docs = checkText c in
  error "Assertion will always fail in %s:\n  %a"
        why (docList ~sep:(text "\n  ") (insert ())) docs

let deputyFailLe (e1: exp) (e2: exp) (why: string) : unit =
  deputyFail (CLeq (e1, e2, why))

(** Split an expression e into e',i', such that e=e'+i' (pointer arithmetic) *)
let rec getBaseOffset (e: exp) : exp * int =
  match e with
  | BinOp ((PlusPI | IndexPI | MinusPI) as op, e', off, t) ->
      let intFold e = isInteger (constFold true e) in
      begin
        match getBaseOffset e', intFold off, op with
        | (b, n1), Some n2, (PlusPI | IndexPI) ->
            b, n1 + (to_signedint n2)
        | (b, n1), Some n2, MinusPI ->
            b, n1 - (to_signedint n2)
        | _, _, _ ->
            e, 0
      end
  | CastE (t, e') ->
      let strip t = typeRemoveAttributes ["bounds"; "size"; "nullterm"] t in
      let b, n = getBaseOffset e' in
      if compareTypes (strip (typeOf e')) (strip t) then begin
        b, n
      end else begin
        match sizeOfBaseType (typeOf e'), sizeOfBaseType t with
        | Some sz1, Some sz2 when sz1 = sz2 -> b, n
        | Some sz1, Some sz2 when sz1 mod sz2 = 0 ->
            mkCast b t, n * (sz1 / sz2)
        | _ -> e, 0
      end
  | AddrOf (base, off) -> begin (* Look for when off ends in Index *)
      match removeOffset off with 
       off', Index(idx, NoOffset) -> begin
         match isInteger (constFold true idx) with 
           Some n -> mkAddrOrStartOf (base, off'), (to_signedint n)
         | _ -> e, 0
       end
      | _ -> e, 0
  end
      
  | _ ->
      e, 0

let proveLeWithBounds (e1: exp) (e2: exp) : bool =
  let ctx = allContext () in
  let rec getExpBounds (e:exp) : exp option * exp option =
    match e with
      (* TODO: structs, memory *)
    | Lval (Var vi, NoOffset) when isPointerType vi.vtype &&
                                   hasAttribute "bounds" (typeAttrs vi.vtype) ->
        let ctx = addThisBinding ctx vi.vtype e in
        let lo, hi = boundsOfAttrs ctx (typeAttrs vi.vtype) in
(*         log " %a has bounds %a and %a.\n" dx_exp e *)
(*           dx_exp lo dx_exp hi; *)
        Some lo, Some hi
    | CastE (t, e') when (bitsSizeOf t) = (bitsSizeOf voidPtrType) ->
        getExpBounds e'
    | _ -> None, None
  in
  let lo1, hi1 = getExpBounds e1 in
  let lo2, hi2 = getExpBounds e2 in
  (* we know e1 <= hi1 and lo2 <= e2 *)
  match hi1, lo2 with
    Some hi1, Some lo2 ->
      (DCE.canonCompareExp hi1 lo2)
      || (DCE.canonCompareExp hi1 e2)
      || (DCE.canonCompareExp e1 lo2)
  | Some hi1, None ->
      (DCE.canonCompareExp hi1 e2)
  | None, Some lo2 ->
      (DCE.canonCompareExp e1 lo2)
  | None, None ->
      false

let newProveLe ?(allowGt: bool = false) (e1: exp) (e2: exp) : int option =
  let e1c = DCE.canonExp Int64.one e1 in
  let e2c = DCE.canonExp Int64.one e2 in 
  let e1res = DCE.Can.sub e2c e1c ILong in 
  (*log "le(%a, %a) = %a" d_exp e1 d_exp e2 DCE.Can.d_t e1res;*)
  match DCE.Can.getSign e1res with
  | DCE.Can.Zero
  | DCE.Can.Pos -> begin
      (*log "newProveLe : Yes %a" DCE.Can.d_t e1res;*)
      Some 1
  end
  | DCE.Can.Neg -> begin
      (*log "newProveLe : No %a" DCE.Can.d_t e1res;*)
      Some (-1)
  end
  | DCE.Can.DontKnow -> begin
      (* special cases. *)
      match e1res.DCE.Can.cf with
      | [(f, e)] -> begin
	  (* look for C + f * (e & D) >= 0, with f * D >= -C *)
	  match e with
	  | BinOp(BAnd, e1, e2, _) -> begin
	      match isInteger e2 with
	      | None -> begin
		  (*log "newProveLe: mask not const %a" d_plainexp e;*)
		  None
	      end
	      | Some d ->
	      let c = Int64.neg e1res.DCE.Can.ct in
		  if Int64.mul f d >= c
		  then begin
		    (*log "newProveLe: Yes %a" DCE.Can.d_t e1res;*)
		    Some (1)
		  end else begin
		    (*log "newProveLe: couldn't prove %a" DCE.Can.d_t e1res;*)
		    None
		  end
	  end
	  | _ -> begin
	      (*log "newProveLe: not BAnd: %a" d_plainexp e;*)
	      None
	  end
      end
      | _ -> begin
	  (*log "newProveLe: Too Many: %a" DCE.Can.d_t e1res;*)
	  None
      end
  end


type rel = Greater | LessEqual | DontKnow
(** Return true if e1 <= e2 (statically). Reports an error if we can prove 
 * statically e1 > e2, unless allowGt = true *)
let proveLe ?(allowGt: bool = false) (e1: exp) (e2: exp) (why: string) : rel =
  match newProveLe e1 e2 with
  | Some i when i > 0 -> LessEqual
  | Some i -> begin
      if not allowGt then
        deputyFailLe e1 e2 why;
      Greater
  end
  | None -> begin
      let b1, off1 = getBaseOffset (stripNopCasts e1) in
      let b2, off2 = getBaseOffset (stripNopCasts e2) in
      if false then begin
	log "  proveLeq: Comparing:\n";
	log "   %a = (%a) + %d.\n" dx_exp e1 d_plainexp b1 off1; 
	log "   %a = (%a) + %d.\n" dx_exp e2 d_plainexp b2 off2; 
      end;
      if DCE.canonCompareExp b1 b2 then begin
	let doCompare n1 n2 =
	  if n1 > n2 then begin
            if not allowGt then
              deputyFailLe e1 e2 why;
            Greater
	  end else begin
            LessEqual
	  end
	in
	let t1 = typeOf b1 in
	let t2 = typeOf b2 in
	match sizeOfBaseType t1, sizeOfBaseType t2 with
	| Some n1, Some n2 -> doCompare (off1 * n1) (off2 * n2)
	| _ when compareTypes t1 t2 -> doCompare off1 off2
	| _ -> DontKnow
      end else begin
        if (proveLeWithBounds b1 b2 && off1 = 0 && off2 = 0) then
          LessEqual
        else
          DontKnow
      end
  end


(** Optimize an individual check *)
let rec optimizeCheck ?(supErr: bool = false) (c: check) : check list =
  if false then 
    ignore (log "optimizing %a\n"
              d_instr (checkToInstr c)); 
  match c with
  | CNullOrLeq (z, _, _, _) when isZero z -> []

  | CNullOrLeq (e, e1, e2, why) -> begin
      (* There are some user defined reallocaters in bc, for example,
       * that need this to be okay, so errors need to be suppressed until
       * after symbolic evaluation - zra *)
      match proveLe ~allowGt:true e1 e2 why with
      | LessEqual ->  []
      | Greater -> begin
        if isNonnullType (typeOf e) then begin
          deputyFail c;
          [c]
        end else
          optimizeCheck ~supErr:supErr (CEq (e, zero, why, checkText c))
      end
      | DontKnow -> [c]
  end

  | CLeq (e1, e2, why) -> begin
      match proveLe ~allowGt:supErr e1 e2 why with
      | LessEqual -> []
      | _ -> [c]
  end

  | CNullOrLeqNT (z, _, _, _, _) when isZero z -> []

  | CNullOrLeqNT (_, e1, e2, _, why)
  | CLeqNT (e1, e2, _, why) -> begin
      match proveLe ~allowGt:true e1 e2 why with
      | LessEqual ->  []
      | _ -> [c]
  end

  | CEq (e1, e2, why, _) -> begin

      if DCE.canonCompareExp e1 e2 then []
      else begin
        match proveLe ~allowGt:true e1 e2 why,
              proveLe ~allowGt:true e2 e1 why with
        | LessEqual, LessEqual -> []
        | _, _ -> [c]
      end

  end

  | CLeqInt (e1, e2, why) -> begin
    match proveLe ~allowGt:supErr e1 e2 why with
    | LessEqual -> []
    | _ -> [c]
  end

  | CPtrArith (lo, hi, p, e, sz) -> begin
        let ep = BinOp(PlusPI,p,e,typeOf p) in
        match proveLe ~allowGt:supErr lo ep "lower bound check",
              proveLe ~allowGt:supErr ep hi "upper bound check" with
        | LessEqual, LessEqual -> []
        | _, _ -> [c]
  end
    
  | CPtrArithNT (lo, hi, p, e, sz) -> begin
        let ep = BinOp(PlusPI,p,e,typeOf p) in
        match proveLe ~allowGt:supErr lo ep "lower bound check",
              proveLe ~allowGt:true ep hi "nullterm upper bound check" with
        | LessEqual, LessEqual -> []
        | _ -> [c]
  end

  | CPtrArithAccess(lo, hi, p, e, sz) -> begin
    let ep = BinOp(PlusPI,p,e,typeOf p) in
    let epo = (BinOp(PlusPI,p,BinOp(PlusA,e,one,typeOf e),typeOf p)) in
    match proveLe ~allowGt:supErr lo ep "lower bound check",
          proveLe ~allowGt:supErr epo hi "upper bound check" with
    | LessEqual, LessEqual -> []
    | _, _-> [c]
  end

  | CWriteNT (_, _, z, _) when isZero z -> []

  | CWriteNT (p, hi, what, sz) -> begin
      let t = typeOf p in
      assert (sz == (baseSize t));
      let p_plus_one = BinOp(PlusPI, p, one, t) in
      match proveLe ~allowGt:true p_plus_one hi "nullterm write check" with
      | LessEqual -> []
      | _ -> [c]
  end
  | CSelected e when isZero e -> begin
      deputyFail c;
      []
  end
  | _ -> [c]

let opt_deputy_instr i =
  match i with
  | Call(Some(lv), Lval(Var vf,NoOffset), el, l) -> begin
      if not(vf.vname = "deputy_max") then [i] else
	  match el with
	  | [e1;e2] -> begin
    	if DCE.canonCompareExp e1 e2
	    then [Set(lv,e1,l)]
	    else begin
	        match proveLe ~allowGt:true e1 e2 "deputy_max",
	              proveLe ~allowGt:true e2 e1 "deputy_max" with
	        | LessEqual, _ -> [Set(lv,e2,l)]
	        | _, LessEqual -> [Set(lv,e1,l)]
	        | _, _ -> begin
                if !debug then
                    ignore(E.log "opt_deputy_instr: must keep %a\n" d_instr i);
	    	    [i]
	    	end
	    end
	  end
 	  | _ -> begin
 	    if !debug then
 	        ignore(E.log "opt_deputy_instr: not right form %a\n" d_instr i);
		[i]
      end
  end
  | _ -> begin
    if !debug then
        ignore(E.log "opt_deputy_instr: not deputy_max: %a\n" d_instr i);
	[i]
  end

let optimizeVisitor ?(supErr : bool = false) () = object (self)
  inherit nopCilVisitor

  method vinst i =
    match instrToCheck i with
    | Some c -> ChangeTo (List.map checkToInstr (optimizeCheck ~supErr:supErr c))
    | None -> if is_deputy_instr i 
    then ChangeTo(opt_deputy_instr i)
    else DoChildren

  method vfunc fd =
    curFunc := fd;
    let cleanup x =
      curFunc := dummyFunDec;
      x
    in
    ChangeDoChildrenPost (fd, cleanup)

end
