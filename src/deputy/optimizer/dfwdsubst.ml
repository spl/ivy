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
 * dfwdsubst.ml
 *
 * The visitor below symbolically evaluates expressions
 * inside of checks for easy consumption by the other
 * passes.
 *
 *)

open Cil
open Pretty
open Dutil
open Dcheckdef
open Doptimutil

module E = Errormsg
module AE = Availexps
module AELV = Availexpslv
module UD = Usedef
module RCT = Rmciltmps
module S = Stats
module IH = Inthash

module DFI = Dflowinsens

let doTime = ref false

let time s f a =
  if !doTime then
    S.time s f a
  else f a

(* First, some things for handling funkyness created by the composition
 * of CIL transformations and Deputy transormations in regards to
 * temporaries created for function calls. This will make reducing the
 * number of remaining temps(and even some checks) easier. *)

(* Type for the form of temporary variable names *)
type nameform = Suffix of string | Prefix of string | Exact of string

(* check if a name matches a form *)
(* string -> nameform -> bool *)
let check_form s f =
    match f with
      Suffix sfx ->
	let frmlen = String.length sfx in
	let slen = String.length s in
	slen >= frmlen &&
	compare (String.sub s (slen - frmlen) frmlen) sfx = 0
    | Prefix pfx ->
	let frmlen = String.length pfx in
	String.length s >= frmlen &&
	compare (String.sub s 0 frmlen) pfx = 0
    | Exact ext ->
	let frmlen = String.length ext in
	String.length s = frmlen &&
	compare s ext = 0

(* check a name against a list of forms 
   if it matches any then return true *)
(* string -> nameform list -> bool *)
let inTmpForm s fl =
  List.fold_left (fun b f -> b || check_form s f) 
    false fl

let tmpForms = [Exact "tmp";
	     Prefix "tmp___";
	     Prefix "__cil_tmp";
	     Suffix "__e";
	     Suffix "__b";]



(* This will clean up the CIL a bit so that 
   the forward substitution can do a better job *)
(* If we see:
     tmp = f(...);
     notatemp = tmp;
   then replace with:
     notatemp = f(...);
     tmp = notatemp;
 *)
class symEvalPrePass (fd : fundec) = object(self)
  inherit nopCilVisitor

  method private procIl il =
    let rec helper il seen = match il with
    | [] -> List.rev seen
    | [x] -> List.rev (x::seen)
    | i1::i2::rest -> begin
	match i1, i2 with
	| Call(Some(Var rvi, NoOffset), flv, el, l),
	  Set((Var vi', NoOffset), Lval(Var rvi', NoOffset),l')
	  when inTmpForm rvi.vname tmpForms && not(inTmpForm vi'.vname tmpForms)
	      && rvi'.vid = rvi.vid
	  -> begin

	    if !debug then ignore(E.log "Merging Instructions %a and %a\n" 
				    d_instr i1 d_instr i2);
	    let new1 = Call(Some(Var vi',NoOffset),flv,el,l) in
	    let new2 = Set((Var rvi,NoOffset),Lval(Var vi',NoOffset),l') in
	    helper rest (new2::new1::seen)
	  end
	| Set((Var vi1, NoOffset), Lval(Var vir1, NoOffset), l1),
	  Set((Var vi2, NoOffset), Lval(Var vir2, NoOffset), ll2)
	  when inTmpForm vi1.vname tmpForms && 
	       inTmpForm vir1.vname tmpForms &&
	       vir1.vid = vir2.vid &&
	       not(inTmpForm vi2.vname tmpForms) -> begin
	  match seen with
	  | [] -> helper rest (i1::i2::seen)
	  | i3 :: seen -> (* backtrack and try again *)
	      helper (i3 :: i2 :: i1 :: rest) seen
	end
	| _, _ -> begin
	    helper (i2::rest) (i1::seen)
	end
    end
    in
    helper il []

  method private procStmt s =
    match s.skind with
    | Instr il -> begin
	s.skind <- Instr(self#procIl il);
	s
    end
    | _ -> s

  method private processStmts sl =
    let rec helper sl seen = match sl with
    | [] -> List.rev seen
    | [x] -> List.rev ((self#procStmt x)::seen)
    | s1::s2::rest -> begin
	match s1.skind, s2.skind with
	| Instr il1, Instr il2 when s1.labels = [] && s2.labels = [] -> begin
	    s1.skind <- Instr(il1 @ il2);
	    helper (s1 :: rest) seen
	end
	| Instr il1, Instr il2 when il1 <> [] && il2 <> [] -> begin
	    (* get the last instr in il1 and the first in il2 *)
	    let i1 = List.hd (List.rev il1) in
	    let il1' = List.tl (List.rev il1) in
	    let i2 = List.hd il2 in
	    let il2' = List.tl il2 in
	    match i1, i2 with
	    | Call(Some(Var rvi, NoOffset), flv, el, l),
	      Set((Var vi',NoOffset),Lval(Var rvi',NoOffset),l')
	      when inTmpForm rvi.vname tmpForms && not(inTmpForm vi'.vname tmpForms)
		  && rvi'.vid = rvi.vid
	      -> begin

		if !debug then ignore(E.log "Merging Stmts %a and %a\n" d_stmt s1 d_stmt s2);
		let newi1 = Call(Some(Var vi',NoOffset),flv,el,l) in
		let newi2 = Set((Var rvi,NoOffset),Lval(Var vi',NoOffset),l') in
		let new1 = Instr (List.rev (newi1::il1')) in
		let new2 = Instr (newi2::il2') in
		s1.skind <- new1;
		s2.skind <- new2;
		helper rest ((self#procStmt s2)::(self#procStmt s1)::seen)
	      end
	    | Set((Var vi1, NoOffset), Lval(Var vir1, NoOffset), l1),
	      Set((Var vi2, NoOffset), Lval(Var vir2, NoOffset), l2)
	      when inTmpForm vi1.vname tmpForms && 
	 	   inTmpForm vir1.vname tmpForms &&
		   vir1.vid = vir2.vid &&
		   not(inTmpForm vi2.vname tmpForms)
	      -> begin
		match seen with
		| [] -> begin
		    s1.skind <- Instr (List.rev (i2::il1'));
		    s2.skind <- Instr (i1::il2');
		    helper rest ((self#procStmt s2)::(self#procStmt s1)::seen)
		end
		| s3 :: seen -> begin (* backtrack and try again *)
		    s1.skind <- Instr (List.rev (i2::il1'));
		    s2.skind <- Instr (i1::il2');
		    if !debug then ignore(E.log "backtrack: %a\n%a\n" d_stmt s3 d_stmt s1);
		    helper (s3 :: s1 :: s2 :: rest) seen
		end
	      end
	    | _, _ -> helper (s2 :: rest) ((self#procStmt s1) :: seen)
	end
	| _, Instr [] when s2.labels = [] ->
	    (* dump empty statements having no labels *)
	    helper (s1::rest) seen
	| _, _ -> begin 
	    helper (s2::rest) ((self#procStmt s1)::seen)
	end
    end
    in
    helper sl []

  (* Cil.constFold doesn't bother getting rid of addition of zero when
     the result type is a pointer, so handle that here *)
  method vexpr e =
    let rec mkInt = function
        Const(CChr c) -> Const(charConstToInt c)
      | Const(CEnum (v, s, ei)) -> mkInt v
      | CastE(TInt (ik, ta), e) -> begin
          match mkInt e with
            Const(CInt64(i, _, _)) -> 
              let i', _ = truncateInteger64 ik i in
              Const(CInt64(i', ik, None))
          | e' -> CastE(TInt(ik, ta), e')
      end
      | e -> e
    in
    match e with
    | BinOp(bop,e1,e2,typ) -> begin
	match bop, mkInt e1, mkInt e2 with
	| PlusA, Const(CInt64(z,_,_)), e2 when z = Int64.zero -> ChangeTo(e2)
	| PlusA, e1, Const(CInt64(z,_,_)) when z = Int64.zero -> ChangeTo(e1)
	| PlusPI, e1, Const(CInt64(z,_,_)) when z = Int64.zero -> ChangeTo(e1)
	| IndexPI, e1, Const(CInt64(z,_,_)) when z = Int64.zero -> ChangeTo(e1)
	| MinusPI, e1, Const(CInt64(z,_,_)) when z = Int64.zero -> ChangeTo(e1)
	| _,_,_ -> DoChildren
    end
    | _ -> DoChildren

  method vblock b = 
    b.bstmts <- self#processStmts b.bstmts; 
    DoChildren

end

let preFwdSubst (fd : fundec) =
  visitCilFunction (new symEvalPrePass fd) fd


(* Here follows the actual forward substitution transformaction.
   This currently uses some code in rmciltmps, but that code
   isn't really general purpose anymore, and should move here. *)

let can_elim_check c =
  match DFI.optimizeCheck ~supErr:true c with
    [] -> true
  | _ -> false

let checkVisit_change = ref true

let checkAEVisit action (fd : fundec) = object(self)
  inherit AE.aeVisitorClass as super

  method private do_action b e =
    match self#get_cur_eh() with
      None -> e
    | Some eh -> 
	let e', b' = action eh sid e fd b in
	if b' then checkVisit_change := true;
	e'

  method private fix_check =
    let fold_act e = constFold true (self#do_action true e) in
    map_to_check ~cond:can_elim_check fold_act

  method vexpr e = 
    ChangeTo (self#do_action false e)

  method vinst i =
    let action = super#vinst i in
    if action <> DoChildren then
      E.s (bug "Expected DoChildren");
    match instrToCheck i with
    | Some c ->
        let c' = time "handle checks" self#fix_check c in
        ChangeTo [checkToInstr c']
    | None -> begin
	(* see if it's a deputy function *)
	if not (is_deputy_fun i) then
          DoChildren
	else match i with
	| Call(lvo,lv,el,l) ->
	    let el = List.map (self#do_action true) el in
	    ChangeTo [Call(lvo,lv,el,l)]
	| _ -> DoChildren
    end

  method vfunc fd =
    time "available expressions" AE.computeAEs fd;
    curFunc := fd;
    let cleanup x =
      curFunc := dummyFunDec;
      x
    in
    ChangeDoChildrenPost (fd, cleanup)

end

let checkAELVVisit action (fd : fundec) = object(self)
  inherit AELV.aeVisitorClass as super

  method private do_action b e =
    match self#get_cur_eh() with
      None -> e
    | Some eh -> 
	let e', b' = action eh sid e fd b in
	if b' then checkVisit_change := true;
	e'

  method private fix_check =
    let fold_act e = constFold true (self#do_action true e) in
    map_to_check ~cond:can_elim_check fold_act

  method vexpr e = 
    ChangeTo (self#do_action false e)

  method vinst i =
    let action = super#vinst i in
    if action <> DoChildren then
      E.s (bug "Expected DoChildren");
    match instrToCheck i with
    | Some c ->
        let c' = time "handle checks" self#fix_check c in
        ChangeTo [checkToInstr c']
    | None -> begin
	(* see if it's a deputy function *)
	if not (is_deputy_fun i) then
          DoChildren
	else match i with
	| Call(lvo,lv,el,l) ->
	    let el = List.map (self#do_action true) el in
	    ChangeTo [Call(lvo,lv,el,l)]
	| _ -> DoChildren
    end

  method vfunc fd =
    if !debug then ignore(E.log "Computing AELV for %s\n" fd.svar.vname);
    time "available expressions" AELV.computeAEs fd;
    curFunc := fd;
    let cleanup x =
      curFunc := dummyFunDec;
      x
    in
    ChangeDoChildrenPost (fd, cleanup)

end

(* applies the action to the function until
   no changes are made, or lim is reached *)
(* action: 'a -> sid -> exp -> fundec -> bool -> exp * bool *)
(* action -> int -> fundec -> unit *)
let fp cls action lim fd =
  let vis = cls action fd in
  let i = ref 0 in
  checkVisit_change := true;
  while !i < lim && !checkVisit_change do
    if !debug then ignore(E.log "fp: in while loop\n");
    checkVisit_change := false;
    ignore(visitCilFunction (vis :> cilVisitor) fd);
    i := !i + 1;
  done


let forwardTmpSub (fd : fundec) = 
  ignore(preFwdSubst fd);
  fp checkAELVVisit RCT.ae_lv_fwd_subst 4 fd;
  ignore(preFwdSubst fd)

(*let forwardTmpSub = fp checkAEVisit RCT.ae_fwd_subst 4*)

(* Constant propagation into checks. This is probably useless. *)
let constProp = fp checkAEVisit RCT.ae_const_prop 4




