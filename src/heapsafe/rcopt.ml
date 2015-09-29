(* Copyright (c) 2007 Intel Corporation 
 * All rights reserved. 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 	Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 	Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *     Neither the name of the Intel Corporation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE INTEL OR ITS
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)
open Cil
open Rcutils
open Ivyoptions
open Rclocals
open Printf

module VS = Usedef.VS
module L = List
type varset = VS.t

(* Some optimizations to apply to generated RC actions
 *)

(* TODO: this code is currently very inefficient.
 * In particular, we walk the tree seperately for each operation *)

(* list all local vars whose values might change in a block *)
(* also see if this block uses "goto" *)
class rcGetModifiedVars =
  object (self)
    inherit nopCilVisitor as super
    
    val modvars = ref VS.empty    
    method get_modvars = !modvars
        
    method vinst (i:instr) = match i with
      | Set((Var v, _), _, _) -> 
	  modvars := VS.add v !modvars; 
	  DoChildren
      | Call(Some (Var v, _), _, _, _) -> 
	  modvars := VS.add v !modvars; 
	  DoChildren
      | _ -> DoChildren
  end
  
let get_modified_vars block =
    let visit = new rcGetModifiedVars in
    ignore (visitCilBlock (visit :> cilVisitor) block);
    visit#get_modvars

let get_modified_vars_stmt (s:stmt) =
    let visit = new rcGetModifiedVars in
    ignore (visitCilStmt (visit :> cilVisitor) s);
    visit#get_modvars

(* HACK: we assume that all CIL labels stay within the current loop, as
 * this appears to be how they are used now *)
let bad_label label = match label with
    | Label (name,_,true) -> true
    | Label (name,_,_) -> false
    | _ -> false
let bad_target stmt = List.exists bad_label stmt.labels

class rcCheckGoto =
  object (self)
    inherit nopCilVisitor as super
    val hasgoto = ref false
    method get_hasgoto = !hasgoto
    
    method vstmt (s:stmt) = 
      if bad_target s then
	hasgoto := true;
      begin
	match s.skind with
	| Goto (lbl,_) when bad_target !lbl -> hasgoto := true
	| _ -> ()
      end;
      DoChildren
  end
  
let block_hasgoto block = 
  let visit = new rcCheckGoto in
  ignore (visitCilBlock (visit :> cilVisitor) block);
  visit#get_hasgoto

let isFun lval func = match lval with
    | Lval (Var vi, NoOffset) when vi == func -> true
    | _ -> false

(* Remove any push/pops for vars, other those vars listed, or whose address
 * is taken *)
class rcStripPushPop (notthese : varset) (onlythese : varset option) =
  object (self)
    inherit nopCilVisitor as super
    
    val strippedvars = ref VS.empty
    method get_strippedvars = !strippedvars
    
    method goodvar (v:varinfo) = match onlythese with
        | Some s -> VS.mem v s
        | None -> true
    
    method vinst (i:instr) = match i with
      | Call (ret, func, [Lval (Var var, NoOffset)], loc) 
                when (isFun func rcFunctions.rcpush 
                        || isFun func rcFunctions.rcpop)
                && not var.vaddrof && not (VS.mem var notthese) 
                && self#goodvar var
        ->
                strippedvars := VS.add var !strippedvars;
                ChangeTo []
      | _ -> DoChildren            
               
  end

(* TODO: stripped vars should be a set, not a list *)
 
let strip_pushpop modvars block goodvars =
  let visit = new rcStripPushPop modvars goodvars in
  let block = visitCilBlock (visit :> cilVisitor) block in
  block, visit#get_strippedvars

let addPops vars skind loc = 
  let pops = List.map 
       (fun v -> Call (None,v2e rcFunctions.rcpop, [v2e v], loc))
       (VS.elements vars) in
  Block (mkBlock ([mkStmt (Instr pops); mkStmt skind]))


(* add pop statements for return statements *)
class rcPopOnReturn (popvars : varset) =
  object (self)
    inherit nopCilVisitor as super      
    method vstmt (s:stmt) = match s.skind with
      | Return (e,loc) -> 
	  s.skind <- addPops popvars s.skind loc;
	  SkipChildren
      | _ -> DoChildren
  end
  
let pop_on_exit popvars block =
  let visit = new rcPopOnReturn popvars in
  let block = visitCilBlock (visit :> cilVisitor) block in
  block

let hoist block loc goodvars =
  let modvars = get_modified_vars block in
  let block,vars = strip_pushpop modvars block goodvars in
  let block = pop_on_exit vars block in
  let varl = VS.elements vars in
  let pushes = List.map 
        (fun v -> Call(None, v2e rcFunctions.rcpush, [v2e v], loc))
        varl in
  let pops = List.map 
        (fun v -> Call(None, v2e rcFunctions.rcpop, [v2e v], loc))
        (List.rev varl) in            
  block,mkStmt (Instr pushes),mkStmt (Instr pops),not (VS.is_empty vars)

let printblock block = 
   let printer = new defaultCilPrinterClass in
   printer#dBlock stdout 0 block

let pvar (v:varinfo) = 
  print_string " ";
  print_string v.vname

let pvlist (s:string) vl =
  print_string s;
  VS.iter pvar vl;
  print_newline ()

let ploc (loc:location) =
  print_string loc.file;
  print_char ':';
  print_int loc.line

let getMyLiveness (s:stmt) = 
  try
    getLiveness s
  with
    Not_found -> 
      (*Cil.dumpStmt Cil.defaultCilPrinter stdout 2 s;
      print_int s.sid; print_newline ();
      exit 2;*)
      VS.empty

(* Hoist push/pop out of a loop or block if the var is not modified *)
class rcHoist : cilVisitor =
  object (self)
    inherit nopCilVisitor as super
           
    method vstmt (s:stmt) = match s.skind with
        | Loop (block,loc,so, Some exit) when not (block_hasgoto block) ->
            let block = visitCilBlock (self :> cilVisitor) block in
            let prelivevars = getMyLiveness s in
            let postlivevars = getMyLiveness exit in
            let livevars = VS.inter prelivevars postlivevars in
	    (*ploc loc;
	    pvlist "prelive" prelivevars;
	    pvlist "postlive" postlivevars;
	    pvlist "both" livevars;*)
            let block,pushes,pops,action = hoist block loc (Some livevars) in
            if action then
	      begin
                let stmts = [pushes; (mkStmt s.skind); pops] in
		s.skind <- Block (mkBlock (compactStmts stmts))
	      end;
            SkipChildren

(* TODO: only do the block trick for live vars *)
(* HACK: temporarily commended out due to a Not_found bug *)
(*        | Block block when not (block_hasgoto block)->
            let block = visitCilBlock (self :> cilVisitor) block in
            let prelivevars = getLiveness s in
            let postlivevars = getPostLiveness s in
            let livevars = VS.inter prelivevars postlivevars in
            let block,pushes,pops,action = hoist block locUnknown (Some livevars) in
            if action then
	      begin
                let stmts = [pushes; (mkStmt s.skind); pops] in
		s.skind <- Block (mkBlock (compactStmts stmts))
	      end;
            SkipChildren
*) 
        | _  -> DoChildren

   
  end
  
let spew pops ops loc =
        let popcalls = List.map 
            (fun v -> Call(None, v2e rcFunctions.rcpop, [v2e v], loc))
            (List.rev pops) in
        popcalls @ (List.rev ops)
        
(* never clear pops/ops without spewing first *)

(* let pvars (vars:varset) = 
  fprintf stderr "set\n";
  VS.iter (fun x -> fprintf stderr "  %s\n" x.vname) vars;
  fprintf stderr "tes\n\n" *)

let rec merge_pushpop pops ops inside l loc modvars = 
  let goodvar v = not (VS.mem v modvars) in
  match pops,l with
  (* a pop - add it to the pops list *)
      | _,Call (_,f,[Lval (Var var, NoOffset)],l)::xs 
                when (isFun f rcFunctions.rcpop) ->
          merge_pushpop (var::pops) ops false xs l modvars
  (* a cancelling push - remove the pop *)
      | lastpop::ps,Call (_,f,[Lval (Var var, NoOffset)],loc)::xs 
                when isFun f rcFunctions.rcpush 
                && lastpop == var && (goodvar var) ->
          merge_pushpop ps ops true xs loc modvars
  (* a non-cancelling push - spew any leftovers and emit *)
      | _,(Call (_,f,[Lval (Var var, NoOffset)],loc) as x)::xs 
                when isFun f rcFunctions.rcpush ->
          spew pops ops loc @ x::merge_pushpop [] [] true xs loc modvars
  (* a write to a popped variable - reset the state *)
      | _,(Set ((Var var,NoOffset),e,loc))::xs when List.mem var pops ->
          spew pops ops loc @ merge_pushpop [] [] inside l loc modvars
  (* an operation between pushes and pops - emit it *)
      | _,x::xs when inside -> spew pops ops loc @x::merge_pushpop [] [] true xs loc modvars
  (* an operation after skipped pops - buffer it *)
      | _,x::xs -> merge_pushpop pops (x::ops) false xs loc modvars
  (* no more operations - flush the queue *)
      | ps,[] -> spew pops ops loc
           
   
class rcMerge : cilVisitor =
  object (self)
    inherit nopCilVisitor as super
    
    method vstmt (s:stmt) = match s.skind with
       | Instr insts ->
	   let modvars = get_modified_vars_stmt s in
           let insts = merge_pushpop [] [] false insts locUnknown modvars in
	   s.skind <- Instr insts;
	   SkipChildren
       | _ -> DoChildren
  
  end
 
let rcOptimize cil =
  if not !noHoist then
      ignore (visitCilFile (new rcHoist) cil);
  if not !noMerge then
      ignore (visitCilFile (new rcMerge) cil)
 
