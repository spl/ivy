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
 * dloopoptim.ml
 *
 * Move loop invariant checks out
 * of loops.
 *
 * TODO: identify loop induction variables and move bounds
 * checks on each iteration to one check before the loop.
 *)

open Cil
open Expcompare
open Pretty
open Dutil
open Dcheckdef
open Doptimutil


module E = Errormsg
module IH = Inthash
module RD = Reachingdefs
module AE = Availexps
module AELV = Availexpslv
module RCT = Rmciltmps
module UD = Usedef
module S = Stats


(* stm -> UD.VS.t *)
let find_varying loop_stm =
  let _, d = UD.computeDeepUseDefStmtKind loop_stm.skind in
  d

(* for visiting a block to determine whether it contains
 * a write to memory or a function call *)
class writeOrCallFinderClass br = object(self)
  inherit nopCilVisitor
      method vinst i =
	if is_deputy_instr i then SkipChildren else
	match i with
	  Set((Mem _,_),_,_) -> 
	    br := true;
	    DoChildren
	| Call(_,_,_,_) ->
	    br := true;
	    DoChildren
	| Asm(_,_,_,_,_,_) -> (* Not precisely... *)
	    br := true;
	    DoChildren
	| _ -> DoChildren
end

let writeOrCallFinder = new writeOrCallFinderClass

(* block -> bool *)
let block_has_write_or_call b =
  let br = ref false in
  let vis = new writeOrCallFinderClass br in
  ignore(visitCilBlock vis b);
  !br

(* UD.VS.t -> fundec -> UD.VS.t *)
let add_globs_addrs vvs fd =
  List.fold_left (fun vvs' vi ->
    if vi.vglob || vi.vaddrof
    then UD.VS.add vi vvs'
    else vvs') vvs (fd.sformals@fd.slocals)

(* check -> bool *)
let check_has_mem_read c =
  test_check AELV.exp_has_mem_read c

(* the argument b is the body of a Loop *)
(* returns the loop termination condition along with
 * the checks that must preceed its evaluation *)
(* block -> (exp option * instr list) *)
let get_loop_condition b =
  let isListOfChecks =
    List.fold_left (fun b i ->
      b && (is_check_instr i))
      true
  in
  (* returns the first non-empty, non-check
   * statement of a statement list along with
   * the list of checks that were seen *)
  (* stm list -> stm list * instr list *)
  let rec skipEmpty = function
      [] -> [], []
    | {skind = Instr []; labels = []}::rest ->
	skipEmpty rest
    | ({skind = Instr il; labels = []} as s)::rest ->
	if isListOfChecks il
	then let sl,il' = skipEmpty rest in
	sl, il@il'
	else let sl, _ = skipEmpty rest in
	s::sl, []
    | x -> x, []
  in
  (* stm -> exp option * instr list *)
  let rec get_cond_from_if if_stm =
    match if_stm.skind with
      If(e,tb,fb,_) ->
	let e = stripNopCasts e in
	RCT.fold_blocks tb;
	RCT.fold_blocks fb;
	let tsl, tcil = skipEmpty tb.bstmts in
	let fsl, fcil = skipEmpty fb.bstmts in
	(match tsl, fsl with
	  {skind = Break _} :: _, [] -> Some e, tcil
	| [], {skind = Break _} :: _ -> 
	    Some(UnOp(LNot, e, intType)), fcil
	| ({skind = If(_,_,_,_)} as s) :: _, [] ->
	    let teo, tcil' = get_cond_from_if s in
	    (match teo with
	      None -> None, []
	    | Some te -> 
		Some(BinOp(LAnd,e,stripNopCasts te,intType)), tcil@tcil')
	| [], ({skind = If(_,_,_,_)} as s) :: _ ->
	    let feo, fcil' = get_cond_from_if s in
	    (match feo with
	      None -> None, []
	    | Some fe -> 
		Some(BinOp(LAnd,UnOp(LNot,e,intType),
			   stripNopCasts fe,intType)), fcil@fcil')
	| {skind = Break _} :: _, ({skind = If(_,_,_,_)} as s):: _ ->
	    let feo,fcil' = get_cond_from_if s in
	    (match feo with
	      None -> None, []
	    | Some fe -> 
		Some(BinOp(LOr,e,stripNopCasts fe,intType)), fcil@fcil')
	| ({skind = If(_,_,_,_)} as s) :: _, {skind = Break _} :: _ ->
	    let teo, tcil' = get_cond_from_if s in
	    (match teo with
	      None -> None, []
	    | Some te -> 
		Some(BinOp(LOr,UnOp(LNot,e,intType),
			   stripNopCasts te,intType)), tcil@tcil')
	| ({skind = If(_,_,_,_)} as ts) :: _ , ({skind = If(_,_,_,_)} as fs) :: _ ->
	    let teo, tcil' = get_cond_from_if ts in
	    let feo, fcil' = get_cond_from_if fs in
	    (match teo, feo with
	      Some te, Some fe ->
		Some(BinOp(LOr,BinOp(LAnd,e,stripNopCasts te,intType),
			   BinOp(LAnd,UnOp(LNot,e,intType),
				 stripNopCasts fe,intType),intType)),
		tcil@fcil@tcil'@fcil'
	    | _,_ -> None, [])
	| _, _ -> (if !debug then ignore(E.log "checkMover: branches of %a not good\n"
					   d_stmt if_stm);
		   None, []))
    | _ -> (if !debug then ignore(E.log "checkMover: %a not an if\n" d_stmt if_stm);
	    None, [])
  in
  let sl, cil = skipEmpty b.bstmts in
  match sl with
    ({skind = If(_,_,_,_)} as s) :: _ ->
      let eo, cil' = get_cond_from_if s in
      eo, cil@cil'
  | s :: _ -> 
      (if !debug then ignore(E.log "checkMover: %a is first, not an if\n"
			       d_stmt s);
       None, [])
  | [] ->
      (if !debug then ignore(E.log "checkMover: no statements in loop block?\n");
       None, [])

(* UD.VS.t -> check -> bool *)
let check_has_varying_var vvs c =
  UD.VS.fold (fun vi b ->
    b || test_check (AELV.exp_has_vi vi) c)
    vvs false

(* if the instruction is deputy_findnull or
 * deputy_max, then if the arguments
 * are loop invariant and there is no
 * other definition of vi reaching i, then
 * the instruction can be lifted out of the
 * loop *)
let can_lift_instr i vvs mw iosh =
  let bad_args el =
    List.fold_left (fun b e ->
      b || (UD.VS.fold (fun vi b ->
	b || (AELV.exp_has_vi vi e) ||
	(mw && AELV.exp_has_mem_read e)) vvs false)) 
      false el
  in
  let check_def vi =
    if IH.mem iosh vi.vid then
      let ios = IH.find iosh vi.vid in
      if not(RD.IOS.cardinal ios = 2) then 
	(if !debug then ignore(E.log "checkMover: %d defs reach\n" (RD.IOS.cardinal ios));
	 false)
      else match RD.IOS.elements ios with
	[io1;io2] -> (match io1,io2 with
	  Some did, None |
	  None, Some did -> RD.isDefInstr i did
	| Some d1, Some d2 -> 
	    (if !debug then ignore(E.log "checkMover: more than one real def reaches %d %d\n" d1 d2);
	     false)
	| _ -> false)
      | _ -> (if !debug then ignore(E.log "checkMover: impossible\n");
	      false)
    else (if !debug then ignore(E.log "checkMover: %s not in iosh\n" vi.vname);
	  false)
  in
  match i with
    Call(Some(Var vi,NoOffset),Lval(Var vf,NoOffset),el,_) ->
     if (vf.vname = "deputy_findnull" || vf.vname = "deputy_max")
     then if bad_args el 
     then (if !debug then ignore(E.log "checkMover: has varying arg %a\n" d_instr i);
	   false)
     else if check_def vi
     then (if !debug then ignore(E.log "checkMover: can be moved %a\n" d_instr i);
	   true)
     else (if !debug then ignore(E.log "checkMover: had bad def %a\n" d_instr i);
	   false)
     else false
  | _ -> false	 

(* remove and return a list of check instructions
 * not containing things in vvs and not having
 * memory reads when mw is true.
 *)
(* UD.VS.t -> bool -> (instr * rddat) list -> instr list * instr list *)
let filter_instr_list vvs mw ildl =
  let gir, rir = List.fold_left 
      (fun (gi,ri) (i,(u,s,iosh)) -> match instrToCheck i with
	None -> if can_lift_instr i vvs mw iosh
	then (gi,i::ri)
	else (i::gi,ri)
      | Some c ->
	  (if check_has_varying_var vvs c
	   then (if !debug then ignore(E.log "checkMover: has varying var %a\n" d_instr i);
		 (i::gi,ri))
	   else if mw && check_has_mem_read c
	   then (if !debug then ignore(E.log "checkMover: has memory read %a\n" d_instr i);
		 (i::gi,ri))
	   else (if !debug then ignore(E.log "checkMover: can be moved %a\n" d_instr i); 
		 (gi, i::ri))))
      ([],[])
      ildl
  in
  List.rev gir, List.rev rir

(* remove loop invariant checks from the block,
 * return a list of checks along with the
 * expression that must guard them *)
(* block -> UD.VS.t -> int -> (exp,instr list) list *)
let rec filter_and_collect_checks b vvs sid =
  let mw = block_has_write_or_call b in
  List.fold_left (fun cl s ->
    match s.skind with 
      Block b' -> cl@(filter_and_collect_checks b' vvs s.sid)
    | If(e,tb,fb,_) ->
	(* see if e is loop invariant *)
	let aedato = AELV.getAEs s.sid in
	(match aedato with None -> cl | Some aedat ->
	  let e',_ = RCT.ae_lv_simp_fwd_subst aedat e true in
	  let e' = stripNopCasts e' in
	  if (UD.VS.exists (fun vi -> AELV.exp_has_vi vi e') vvs) ||
	  (mw && AELV.exp_has_mem_read e) then cl (* can't move *)
	  else let tgcl = filter_and_collect_checks tb vvs s.sid in
	  let fgcl = filter_and_collect_checks fb vvs s.sid in
	  let tgcl' = List.map (fun (g,cl) ->
	    if DCE.canonCompareExp(*StripCasts*) g one
	    then (e',cl)
	    else if DCE.canonCompareExp(*StripCasts*) g e'
	    then (e',cl)
	    else (BinOp(LAnd,e',g,intType),cl)) tgcl in
	  let fgcl' = List.map (fun (g,cl) ->
	    if DCE.canonCompareExp(*StripCasts*) g one
	    then (UnOp(LNot,e',intType),cl)
	    else (BinOp(LAnd,UnOp(LNot,e',intType),g,intType),cl))
	      fgcl in
	  cl@tgcl'@fgcl')
    | Instr il ->
	(match RD.getRDs s.sid with None -> cl | Some(_,x,iosh) ->
	  let rd_dat_lst = RD.instrRDs il s.sid ((),x,iosh) false in
	  let il_dat_lst = List.combine il rd_dat_lst in
	  let gi, ri = filter_instr_list vvs mw il_dat_lst in
	  if !debug then ignore(E.log "checkMover: after filter to move %d\n"
				  (List.length ri));
	  s.skind <- Instr gi;
	  cl@[(one ,ri)])
    | _ -> cl) [] b.bstmts

(* exp -> exp * instr list -> stmt option *)
let eil_to_if_stmt cond (e,il) =
  match il with 
    [] -> (if !debug then ignore(E.log "checkMover: no checks to make\n"); 
	   None)
  | _ ->
      let ifblk = mkBlock [mkStmt(Instr il)] in
      if DCE.canonCompareExp(*StripCasts*) e one ||
         DCE.canonCompareExp(*StripCasts*) e cond
      then (if !debug then ignore(E.log "checkMover: need check %a\n" d_block ifblk); 
	    Some(mkStmt (Block ifblk)))
      else if DCE.canonCompareExp(*StripCasts*) e zero 
      then (if !debug then ignore(E.log "checkMover: checks never made\n");
	    None)
      else (if !debug then ignore(E.log "checkMover: need checks %a\n" d_block ifblk);
	    Some(mkStmt (If(e,ifblk,mkBlock [],locUnknown))))

(* stmt option list -> stmt list *)
let rec filter_sol sol = 
  match sol with [] -> [] |
  so :: rest -> match so with
    None -> filter_sol rest
  | Some s -> s :: (filter_sol rest)

(* return an If statement that does
 * the invariant checks if the condition is true. *)
(* instr list -> (exp, instr list) list -> exp -> stmt -> stmt option *)
let make_pre_header cil gcl cond loop_stm =
  let if_stmo_lst = List.map (eil_to_if_stmt cond) gcl in
  let if_stm_lst = filter_sol if_stmo_lst in
  match if_stm_lst with [] -> None | _ ->
    let preheader_checks = mkStmt (Instr cil) in
    let preheader_if = mkStmt (If(cond, mkBlock if_stm_lst, 
      mkBlock [], locUnknown)) in
    let preheader_block = mkBlock [preheader_checks;
				   preheader_if] in
    let preheader_stm = mkStmt (Block preheader_block) in
    Some preheader_stm

let check_moved = ref false
class loopInvCheckMoverClass fd = object(self)
  inherit nopCilVisitor

  val mutable cur_block = ref {bstmts = []; battrs = []}

  method vstmt s = match s.skind with
    Loop(b,_,_,_) ->
      if !debug then ignore(E.log "checkMover: looking at loop statement\n%a\n" d_stmt s);
      let vvs = find_varying s in
      let vvs = if block_has_write_or_call b
      then add_globs_addrs vvs fd else vvs in
      RCT.fold_blocks b;
      let condo, cil = get_loop_condition b in
      (match condo with 
	None -> 
	  if !debug then ignore(E.log "checkMover: sid %d: no cond\n" s.sid);
	  DoChildren 
      | Some cond ->
	  let cond = UnOp(LNot,cond,intType) in (* Need the opposite of termination cond *)
	  if !debug then ignore(E.log "checkMover: found condition %a\n" d_exp cond);
	  let gcl = filter_and_collect_checks b vvs s.sid in
	  if !debug then ignore(E.log "checkMover: %d checks to move\n"
				  (List.length gcl));
	  match gcl with [] -> DoChildren | _ ->
	    let pho = make_pre_header cil gcl cond s in
	    match pho with None -> DoChildren | Some ph ->
	      check_moved := true;
	      if !debug then ignore(E.log "checkMover: pre-header=\n%a\n" d_stmt ph);
	      (* put the new statement in the current
		 block's statement list before the loop *)
	      let rec insert_before seen to_insert notseen =
		match notseen with [] -> seen
		| s'::rest -> if s'.sid = s.sid
		then (if !debug then ignore(E.log "checkMover: inserting pre-header\n");
		      seen@[to_insert]@notseen)
		else insert_before (seen@[s']) to_insert rest
	      in
	      (!cur_block).bstmts <- insert_before [] ph (!cur_block).bstmts;
	      if !debug then ignore(E.log "checkMover: new enclosing block=\n%a\n" d_block (!cur_block));
	      DoChildren)
  | _ -> DoChildren

  method vblock b =
    let old_block = cur_block in
    cur_block <- ref b;
    let block_restore b' =
      cur_block <- old_block;
      b
    in
    ChangeDoChildrenPost(b,block_restore)

  method vfunc fd =
    Cfg.clearCFGinfo fd;
    ignore (Cfg.cfgFun fd);
    AELV.computeAEs fd;
    RD.computeRDs fd;
    DoChildren

end

let loopInvCheckMover fd =
  check_moved := true;
  while !check_moved do
    check_moved := false;
    ignore(visitCilFunction (new loopInvCheckMoverClass fd) fd)
  done

class checkMoverCleanupClass = object(self)
  inherit nopCilVisitor

  method private is_empty_if s = 
    match s.skind with
      If(_,tb,fb,_) ->
	(match tb.bstmts, fb.bstmts with
	  [],[] -> true
	| _,_ -> false)
    | _ -> false

  method private if_to_block s =
    if self#is_empty_if s 
    then mkStmt(Block(mkBlock []))
    else s

  method vstmt s = match s.skind with
    If(e,tb,fb,l) ->
      let aedato = AELV.getAEs s.sid in
      (match aedato with None -> DoChildren
      | Some aedat -> begin
	  let e',_ = RCT.ae_lv_simp_fwd_subst aedat e true in
	  let e'' = stripNopCasts(constFold true e') in
	  match isInteger e'' with 
	  | Some 0L when not (hasALabel tb) -> (* tb is unreachable *)
              s.skind <- Block fb;
	      DoChildren
          | Some n when not (hasALabel fb)
              && n <> Int64.zero -> (* fb is unreachable *)
	      s.skind <- Block tb;
	      DoChildren
          | _ -> (* Both branches reachable *)
              s.skind <- If(e'',tb,fb,l);
	      ChangeDoChildrenPost(s,self#if_to_block)
        end)
  | _ -> DoChildren

  method vblock b =
    RCT.fold_blocks b;
    let new_stmts = List.filter (fun s ->
      match s.skind with 
	Instr [] when s.labels = [] -> false 
      | _ -> true) b.bstmts in
    b.bstmts <- new_stmts;
    DoChildren

  method vfunc fd =
    Cfg.clearCFGinfo fd;
    ignore (Cfg.cfgFun fd);
    AELV.computeAEs fd;
    DoChildren
end

