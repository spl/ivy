(*
 * sdynamic.ml
 *
 * Instrument the code for dynamic checking of the dynamic type.
 *
 *)

open Cil
open Pretty
open Ivyutil
open Ivyoptions
open Sutil
open Sfunctions

module E = Errormsg
module VS = Usedef.VS

let mkChkMsg (lv : lval) (loc : location) : exp =
    let lvstr = sprint ~width:80 (sp_lval () lv) in
    let locstr = loc.file^":"^(string_of_int loc.line) in
    mkString(lvstr^" @ "^locstr)

let chk_write loc lval =
    let msg = mkChkMsg lval loc in
    Call (None,v2e sfuncs.write, [AddrOf lval;msg],loc)
let chk_read loc lval =
    let msg = mkChkMsg lval loc in
    Call (None,v2e sfuncs.read, [AddrOf lval;msg], loc)


let chk_init_system loc = Call(None,v2e sfuncs.init_system,[],loc)
let chk_init_thread loc = Call(None,v2e sfuncs.init_thread,[],loc)

let is_dynamic (lv : lval) : bool =
    match qualFromAttrs (typeAttrs (sharCTypeOfLval lv)) with
    | OneQual(Attr(q,_)) when List.mem q sharc_dynamic_attrs ->
        true
    | _ -> false

let is_globfun lval = match lval with 
    | (Var {vtype = TFun _},NoOffset) -> true
    | _ -> false

class dynamicLvalFinderClass (lvals : lval list ref) = object(self)
    inherit nopCilVisitor

    method vlval (lv : lval) =
        if not (is_globfun lv) && is_dynamic lv then
            lvals := lv :: !lvals;
        DoChildren

    method vexpr (e : exp) =
        match e with
        | AlignOfE _ | SizeOfE _ -> SkipChildren
        | AddrOf lv | StartOf lv -> begin
            match lv with
            | (Var _, off) ->
                ignore(self#voffs off);
                SkipChildren
            | (Mem e, off) ->
                ignore(self#vexpr e);
                ignore(self#voffs off);
                SkipChildren
        end
        | _ -> DoChildren

end

let lvals_in_instr (i : instr) : lval list =
    if Dcheckdef.isDeputyFunctionInstr i then [] else
    if Rcutils.isRcInstr i then [] else
    let lvl = ref [] in
    let vis = new dynamicLvalFinderClass lvl in
    ignore(visitCilInstr vis i);
    !lvl

let lvals_in_exp (e : exp) : lval list =
    let lvl = ref [] in
    let vis = new dynamicLvalFinderClass lvl in
    ignore(visitCilExpr vis e);
    !lvl

let instr_loc (i : instr) : location =
    match i with
    | Set(_,_,loc)
    | Call(_,_,_,loc)
    | Asm(_,_,_,_,_,loc) -> loc

let isBitfield (fi : fieldinfo) : bool =
    match fi.fbitfield with
    | Some _ -> true
    | None -> false

(* If the lval is a bitfield access, then strip it off, and *)
let rmBitFieldAccess (lv : lval) : lval =
    let (nlv,last) = removeOffsetLval lv in
    match last with
    | Field(fi,NoOffset) when isBitfield fi -> nlv
    | _ -> lv

class memAccessCheckerClass = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        let readchecks = lvals_in_instr i
            |> List.map rmBitFieldAccess
            |> List.map (chk_read (instr_loc i))
        in
        match i with
        | Set(lv,e,loc) when is_dynamic lv ->
            let lv = rmBitFieldAccess lv in
            ChangeTo ((chk_write loc lv)::readchecks@[i])
        | Call(Some lval,_,_,loc) when is_dynamic lval->
            let lval = rmBitFieldAccess lval in
            ChangeTo ((chk_write loc lval)::readchecks@[i])
        | _ -> ChangeTo (readchecks@[i])

    method vstmt (s : stmt) =
        match s.skind with
        | Return(Some e, loc)
        | If(e,_,_,loc)
        | Switch(e,_,_,loc) -> begin
            let readchecks = lvals_in_exp e
                |> List.map rmBitFieldAccess
                |> List.map (chk_read loc)
            in
            if readchecks = [] then DoChildren else
            let fixed s = mkStmt(Block(mkBlock[mkStmt(Instr readchecks);s])) in
            ChangeDoChildrenPost(s,fixed)
        end
        | _ -> DoChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then SkipChildren
        else DoChildren

end

let processFunc (f:file)
                (fd:fundec)
                (loc:location)
                : unit
    =
    ignore (visitCilFunction (new memAccessCheckerClass) fd)

let processFile (fi:file) : unit =
    iterGlobals fi (onlyFunctions (processFunc fi))
