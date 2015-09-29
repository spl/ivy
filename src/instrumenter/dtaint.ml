(*
 * dtaint.ml
 *
 * A taint analysis for tracking program inputs.
 *
 *
 *)

open Cil
open Expcompare
open Pretty
open Dattrs
open Dcheckdef
open Dutil

module H = Hashtbl
module IH = Inthash
module E = Errormsg
module DF = Dataflow
module P = Ptranal
module F = Frontc

let debug = ref true

let staint_fname = "staint.patch.h"

module LEH = 
  H.Make(struct
    type t = lval
    let equal lv1 lv2 = compareLval lv1 lv2
    let hash = H.hash
  end)

let leh_tryfind leh k =
	try Some(LEH.find leh k)
	with Not_found -> None

module VS = Usedef.VS

module VEH =
	H.Make(struct
		type t = varinfo
		let equal vi1 vi2 = vi1.vid = vi2.vid
		let hash = H.hash
	end)

let tryfind veh k =
	try Some(H.find veh k)
	with Not_found -> None

let readPatchAnnots () : (string,varinfo) H.t = try
	let dummy = open_in staint_fname in
	close_in dummy;
	let veh = H.create 16 in
	let pfile = F.parse staint_fname () in
	List.iter (fun g -> match g with
		| GVarDecl(fdv, _) -> begin
			if not(H.mem builtinFunctions fdv.vname) then begin
				ignore(E.log "readPatchAnnots: %a\n" dp_global (GVarDecl(fdv,locUnknown)));
				H.replace veh fdv.vname fdv
			end
		end
		| GVar(fdv,_,_) -> begin
			if not(H.mem builtinFunctions fdv.vname) then begin
				ignore(E.log "readPatchAnnots: %a\n" dp_global (GVarDecl(fdv,locUnknown)));
				H.replace veh fdv.vname fdv
			end
		end
		| _ -> ()) pfile.globals;
	veh
	with Sys_error _ -> H.create 16

let writePatchAnnots (ta : (string,varinfo) H.t) : unit =
	let outpf = open_out staint_fname in
	H.iter (fun _ vi ->
		if not(H.mem builtinFunctions vi.vname) then begin
		ignore(E.log "writePatchAnnot: %a\n" dp_global (GVarDecl(vi,locUnknown)));
		let d = dprintf "%a\n" dp_global (GVarDecl(vi,locUnknown)) in
		fprint outpf ~width:200 d
		end)
		ta;
	close_out outpf

type tData = {
	leh : lval LEH.t;
	vis : VS.t;
	ann : (string,varinfo) H.t;
}

let logArgAnnots (vi : varinfo) : unit =
	match unrollType vi.vtype with
	| TFun(_,al,_,_) -> begin
		List.iter (fun (_,_,an) ->
			List.iter (fun (Attr(a,_)) ->
				ignore(E.log "found arg attr = %s\n" a))
			an)
		(argsToList al)
	end
	| _ -> ()

let addPatchAnnots (td : tData) (vi : varinfo) :  unit =
	ignore(E.log "Dtaint: adding patch: %a\n" dp_global (GVarDecl(vi,locUnknown)));
	logArgAnnots vi;
	H.replace td.ann vi.vname vi

let leh_pretty () leh =
	LEH.fold (fun lv _ d -> d ++ text " " ++ (d_lval () lv)) leh nil
let leh_contains leh1 leh2 =
	LEH.fold (fun lv _ b -> b && LEH.mem leh1 lv) leh2 true
let leh_equals leh1 leh2 =
	(leh_contains leh1 leh2) && (leh_contains leh2 leh1)
let leh_union leh1 leh2 =
	let nleh = LEH.copy leh1 in
	LEH.iter (fun lv _ -> LEH.replace nleh lv lv) leh2;
	nleh

let h_union veh1 veh2 =
	let nveh = H.copy veh1 in
	H.iter (fun n vi -> H.replace nveh n vi) veh2;
	nveh

class taintFinderClass tD br = object(self)
	inherit nopCilVisitor

	method vlval (lv : lval) =
		if LEH.mem tD.leh lv then begin
			br := true;
			SkipChildren
		end else DoChildren

	method vvrbl (vi : varinfo) =
		if H.mem tD.ann vi.vname || vi.vname = "argv" then begin
			br := true;
			SkipChildren
		end else DoChildren
end

let isTainted tD (e : exp) : bool =
	let br = ref false in
	let vis = new taintFinderClass tD br in
	ignore(visitCilExpr vis e);
	!br

class viFinderClass vi br = object(self)
  inherit nopCilVisitor
      
  method vvrbl vi' = 
    if vi.vid = vi'.vid
    then (br := true; SkipChildren)
    else DoChildren

end

let lval_has_vi vi lv =
  let br = ref false in
  let vis = new viFinderClass vi br in
  ignore(visitCilLval vis lv);
  !br

let viTainted tD (vi : varinfo) : bool =
	LEH.fold (fun lv _ b -> b || lval_has_vi vi lv) tD.leh false

let taintArgs tD (el : exp list) : unit =
	List.iter (fun e -> match e with
		| Lval lv
		| AddrOf lv
		| StartOf lv -> begin
			ignore(E.log "taintArgs: %a\n" d_exp e);
			LEH.replace tD.leh lv lv
		end
		| _ -> ()) el

let take (l : 'a list) (n : int) : 'a list =
	let rec h l n acc =
		if n = 0 then List.rev acc else
		match l with [] -> List.rev acc
		| x :: rst -> h rst (n-1) (x :: acc)
	in
	h l n []

let taintSomeArgs tD stal (args : exp list) : unit =
	let args = take args (List.length stal) in
	List.iter2 (fun (s,t,al) a ->
		if List.exists (fun (Attr(an,_)) -> an = "tainted") al then
			taintArgs tD [a]) stal args

let paramTrans (ap : attrparam)
               (args : exp list)
               (ro : lval option) : exp option =
	match ap with
	| AStar(ACons(is,[])) ->
		if String.sub is 0 1 = "$" then begin
			let nstr = String.sub is 1 ((String.length is) - 1) in
			let i = int_of_string nstr in
			if i = 0 then match ro with
			| Some r -> Some(Lval(Mem (Lval r),NoOffset))
			| None -> None
			else Some(Lval(Mem(List.nth args (i-1)),NoOffset))
		end else None
	| ACons(is,[]) ->
		if String.sub is 0 1 = "$" then begin
			let nstr = String.sub is 1 ((String.length is) - 1) in
			let i = int_of_string nstr in
			if i = 0 then match ro with
			| None -> None
			| Some r -> Some(Lval r)
			else Some(List.nth args (i-1))
		end else None
	| AInt i -> Some(integer i)
	| _ -> None

let rec drop (l : 'a list) (n : int) : 'a list =
	if n = 0 then l else
	match l with [] -> []
	| x :: rst -> drop rst (n-1)

let taintVarArg tD (start : int) (args : exp list) : unit =
	let args = drop args start in
	List.iter (fun e -> taintArgs tD [e]) args

let taintCall tD (fvi : varinfo) (args : exp list) (lvo : lval option) : unit =
	let fvi = match tryfind tD.ann fvi.vname with None -> fvi | Some vi -> vi in
	ignore(E.log "taintCall: %s\n" fvi.vname);
	List.iter (fun (Attr(an, apl)) ->
		if an = "Taint" then begin
			match apl with
			| [ap;sz;num] -> begin
				match paramTrans ap args lvo with
				| None -> ()
				| Some a -> taintArgs tD [a]
			end
			| _ -> E.s(bug "taintCall: bad attribute\n")
		end else if an = "CTaint" then begin
			ignore(E.log "Found CTaint function: %s\n" fvi.vname);
			match apl with
			| [iap; oap] -> begin
				match paramTrans iap args lvo,
				      paramTrans oap args lvo with
				| None, _ | _, None -> ()
				| Some ie, Some oe ->
					if isTainted tD ie then taintArgs tD [oe]
					else ()
			end
			| _ -> E.s(bug "taintCall: bad attribute\n")
		end else if an = "ScanTaint" then begin
			ignore(E.log "taintCall: found ScanTaint: %s\n" fvi.vname);
			match apl with
			| [AInt start] -> begin
				taintVarArg tD start args
			end
			| _ -> E.s(bug "taintCall: bad attribute\n")
		end else if an = "tainted" then begin
			(* the return value becomes tainted *)
			match lvo with
			| None -> ()
			| Some lv -> begin
				ignore(E.log "taintCall: adding %a\n" d_exp (Lval lv));
				taintArgs tD [Lval lv]
			end
		end else ()) fvi.vattr

let addTaintAnnots tD (fvi : varinfo) (el : exp list) : unit =
	let fvi = match tryfind tD.ann fvi.vname with None -> fvi | Some vi -> vi in
	match unrollType fvi.vtype with
	| TFun(r,al,b,l) -> begin
		let el = take el (List.length (argsToList al)) in
		let modified = ref false in
		let nal = List.map2 (fun (s,t,an) a ->
			if isTainted tD a then begin
				ignore(E.log "addTaintAnnots: %a is tainted\n" d_exp a);
				modified := true;
				(s,t,addAttribute (Attr("tainted",[])) an)
			end else begin
				ignore(E.log "addTaintAnnots: %a is not tainted\n" d_exp a);
				(s,t,an)
			end)
			(argsToList al) el
		in
		if !modified then begin
			(match al with None -> () | Some _ -> fvi.vtype <- TFun(r,Some nal,b,l));
			addPatchAnnots tD fvi
		end
	end
	| _ -> E.s(bug "non-fun in addTaintAnnots\n")

class globFinderClass (vilr : VS.t ref) = object(self)
	inherit nopCilVisitor

	method vvrbl (vi : varinfo) =
		if vi.vglob then begin
			vilr := VS.add vi (!vilr);
			DoChildren
		end else DoChildren

end

let globals_from_lv (lv : lval) : VS.t =
	let vilr = ref VS.empty in
	let vis = new globFinderClass vilr in
	ignore(visitCilLval vis lv);
	!vilr

let addTaintGlobs tD =
	LEH.iter (fun lv _ ->
		VS.iter (fun gvi ->
			gvi.vattr <- addAttribute (Attr("tainted",[])) gvi.vattr;
			addPatchAnnots tD gvi)
		(globals_from_lv lv))
	tD.leh

let addTaintFormals tD fd =
	let fvi = match tryfind tD.ann fd.svar.vname with None -> fd.svar | Some vi -> vi in
	match unrollType fvi.vtype with
	| TFun(r,al,b,l) -> begin
		let modified = ref false in
		let nal = List.map2 (fun (s,t,an) vi ->
			if viTainted tD vi then begin
				modified := true;
				(s,t,addAttribute (Attr("tainted",[])) an)
			end else (s,t,an))
			(argsToList al) fd.sformals
		in
		if !modified then begin
			(match al with None -> () | Some _ -> fvi.vtype <- TFun(r,Some nal,b,l));
			addPatchAnnots tD fvi
		end
	end
	| _ -> E.s(bug "non-fun in addTaintFormals\n")

let isLibCCall (fvi : varinfo) : bool =
	match fvi.vname with
	| "memcpy" | "memmove" | "strncpy" | "__builtin_strncpy" | "strlcpy"
	| "bzero" | "strdup" | "__strdup" -> true
	| _ -> false

let handleLibCCall (i : instr) (tD : tData) : unit =
	match i with
	| Call(lvo,Lval(Var fvi,NoOffset),[d;s;_],_)
		when fvi.vname = "memcpy" || fvi.vname = "memmove" ||
		     fvi.vname = "strncpy" || fvi.vname = "__builtin_strncpy" ||
		     fvi.vname = "strlcpy" ->
		if isTainted tD s then taintArgs tD [d]
	| Call(lvo,Lval(Var fvi,NoOffset),args,_) when fvi.vname = "bzero" ->
		()
	| Call(Some lv,Lval(Var fvi,NoOffset),[s],_)
		when fvi.vname = "strdup" || fvi.vname = "__strdup" ->
		if isTainted tD s then LEH.replace tD.leh lv lv
	| _ -> ()


(* All of the intelligence goes here *)
let handleInstr i tD =
	ignore(E.log "handleInstr: looking at: %a\n" d_instr i);
	if is_check_instr i then tD else
	match i with
	| Set(lv,e,_) -> begin
		if isTainted tD e then LEH.replace tD.leh lv lv;
		tD
	end
	| Call(_,Lval(Var fvi,NoOffset),_,_) when isLibCCall fvi -> begin
		handleLibCCall i tD;
		tD
	end
	| Call(Some lv,Lval(Var fvi,NoOffset),args,_) -> begin
		addTaintAnnots tD fvi args;
		taintCall tD fvi args (Some lv);
		match unrollType fvi.vtype with
		| TFun(_,al,_,_) -> begin
			taintSomeArgs tD (argsToList al) args;
			tD
		end
		| _ -> E.s(bug "non-fun in handleInstr\n")
	end
	| Call(None,Lval(Var fvi,NoOffset),args,_) -> begin
		addTaintAnnots tD fvi args;
		taintCall tD fvi args None;
		match unrollType fvi.vtype with
		| TFun(_,al,_,_) -> begin
			taintSomeArgs tD (argsToList al) args;
			tD
		end
		| _ -> E.s(bug "non-fun in handleInstr\n")
	end
	| Call(Some lv,fe,args,_) -> begin
		LEH.replace tD.leh lv lv;
		taintArgs tD args;
		tD
	end
	| Call(None,fe,args,_) -> begin
		taintArgs tD args;
		tD
	end
	| Asm(_,_,_,_,_,_) -> tD

module TaintFlow = struct

	let name = "Taint Flow"
	let debug = debug
	type t = tData
	let copy tD = {leh = LEH.copy tD.leh; vis = tD.vis; ann = H.copy tD.ann}

	let stmtStartData = IH.create 64

	let pretty () tD = leh_pretty () tD.leh

	let computeFirstPredecessor stm tD = tD

	let combinePredecessors (stm:stmt) ~(old:t) (tD:t) =
		if leh_equals old.leh tD.leh then None else
		Some({leh=leh_union old.leh tD.leh;vis=old.vis;ann=h_union old.ann tD.ann})

	let doInstr i tD =
		let action = handleInstr i in
		DF.Post(action)

	let doStmt s tD = DF.SDefault

	let doGuard c leh = DF.GDefault

	let filterStmt stm = true

end

module TF = DF.ForwardsDataFlow(TaintFlow)

let recomputeCfg (fd:fundec) : unit =
  Cfg.clearCFGinfo fd;
  ignore (Cfg.cfgFun fd)

let computeTaint (fd : fundec) =
	ignore(E.log "computeTaint: %s\n" fd.svar.vname);
	recomputeCfg fd;
	try let slst = fd.sbody.bstmts in
	let first_stm = List.hd slst in
	(*let fset = List.fold_left (fun s vi -> VS.add vi s) VS.empty fd.sformals in*)
	let fset = VS.empty in
	let fdat = {leh = LEH.create 4;vis = fset;ann=readPatchAnnots()} in
	IH.clear TaintFlow.stmtStartData;
	IH.add TaintFlow.stmtStartData first_stm.sid fdat;
	TF.compute [first_stm]
	with Failure "hd" -> ()
	| Not_found -> ()


let getRetTD (fd : fundec) : tData option =
	let rec h sl =
		match sl with
		| [] -> None
		| s :: rst -> begin
			match s.skind with
			| Return _ -> IH.tryfind TaintFlow.stmtStartData s.sid
			| _ -> h rst
		end
	in
	h fd.sallstmts

let addTaintReturn (tD : tData) (fd : fundec) : unit =
	let fvi = match tryfind tD.ann fd.svar.vname with None -> fd.svar | Some vi -> vi in
	let rec h sl =
		match sl with
		| [] -> ()
		| s :: rst -> begin
			match s.skind with
			| Return(Some re,_) ->
				if isTainted tD re then begin
					fvi.vattr <- addAttribute (Attr("tainted",[])) fvi.vattr;
					addPatchAnnots tD fvi
				end
			| _ -> h rst
		end
	in
	h fd.sallstmts

let updateAnnotations (fd : fundec) =
	match getRetTD fd with
	| None -> None
	| Some returnTD -> begin
		addTaintGlobs returnTD;
		addTaintFormals returnTD fd;
		addTaintReturn returnTD fd;
		(Some returnTD)
	end

let instrContainsTaint (sid : int) (i : instr) : bool =
	match IH.tryfind TaintFlow.stmtStartData sid with
	| None -> false
	| Some tD -> begin
		let tDp = handleInstr i tD in
		let br = ref false in
		let vis = new taintFinderClass tD br in
		let visp = new taintFinderClass tDp br in
		ignore(visitCilInstr vis i);
		ignore(visitCilInstr visp i);
		!br
	end

let expContainsTaint (sid : int) (e : exp) : bool =
	match IH.tryfind TaintFlow.stmtStartData sid with
	| None -> false
	| Some tD -> isTainted tD e


let viTainted (sid: int) (vi : varinfo) : bool =
	match IH.tryfind TaintFlow.stmtStartData sid with
	| None -> false
	| Some tD ->
		LEH.fold (fun lv _ b -> b || lval_has_vi vi lv) tD.leh false

let mergeTaintAnnots (f : file) : unit =
	try
		let fn = "itaint.patch.h" in
		let fh = open_in fn in
		close_in fh;
		Dpatch.applyPatch f fn
	with Sys_error _ -> ignore(E.log "mergeTaintAnnots: failed")

let calcTaintFile (f : file) : unit =
	mergeTaintAnnots f;
	List.iter (fun g ->
		match g with
		| GFun(fd,l) -> begin
			Oneret.oneret fd;
			computeTaint fd;
			match updateAnnotations fd with
			| None -> ()
			| Some tD -> writePatchAnnots tD.ann
		end
		| _ -> ())
	f.globals


