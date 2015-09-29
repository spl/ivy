(*
 * soptim.ml
 *
 * Remove redundant calls to the instrumentation functions.
 *
 *)

open Cil
open Pretty
open Expcompare
open Ivyutil
open Sutil
open Sfunctions

module E = Errormsg
module DF = Dataflow
module UD = Usedef
module IH = Inthash
module AELV = Availexpslv

let debug = ref false

(*
 * When ignore_inst returns true, then
 * the instruction in question has no
 * effects on the abstract state.
 * When ignore_call returns true, then
 * the instruction only has side-effects
 * from the assignment if there is one.
 *)
let ignore_inst = ref (fun i -> false)
let ignore_call = ref (fun i -> false)

let registerIgnoreInst (f : instr -> bool) : unit =
  let f' = !ignore_inst in
  ignore_inst := (fun i -> (f i) || (f' i))

let registerIgnoreCall (f : instr -> bool) : unit =
  let f' = !ignore_call in
  ignore_call := (fun i -> (f i) || (f' i))

type availRWs = {
    mutable areads  : lval list;
    mutable awrites : lval list;
}

let list_equal (eq : 'a -> 'a -> bool) (l1 : 'a list) (l2 : 'a list) : bool =
    let rec helper b l1 l2 =
        if not b then false else
        match l1, l2 with
        | e1 :: rst1, e2 :: rst2 ->
            helper (eq e1 e2) rst1 rst2
        | [], [] -> true
        | _, _ -> false
    in
    helper true l1 l2

let arws_equal (arw1 : availRWs) (arw2 : availRWs) : bool =
    (list_equal compareLval arw1.areads arw2.areads) &&
    (list_equal compareLval arw1.awrites arw2.awrites)

let arws_pretty () arw =
    text "areads: " ++ seq (text " ") (d_lval ()) arw.areads ++ line ++
    text "awrites: " ++ seq (text " ") (d_lval ()) arw.awrites ++ line

let list_inter (eq : 'a -> 'a -> bool)
               (l1 : 'a list)
               (l2 : 'a list)
               : 'a list
  =
  List.filter (fun e1 ->
    List.exists (fun e2 ->
      eq e1 e2) l2) l1

let arws_combine (arw1 : availRWs) (arw2 : availRWs) : availRWs =
    {areads=list_inter compareLval arw1.areads arw2.areads;
     awrites=list_inter compareLval arw1.awrites arw2.awrites;}

let killForWrite (dst : lval) (arws : availRWs) : availRWs =
    let lacksLval (needle : lval) (haystack : lval) : bool =
        not(AELV.lval_has_lval needle haystack)
    in
    let lacksMemRead (lv : lval) : bool =
        match lv with
        | (Var _, off) -> AELV.offset_has_mem_read off
        | (Mem e, off) ->
            AELV.exp_has_mem_read e ||
            AELV.offset_has_mem_read off
    in
    match dst with
    | (Var vi, _) when not vi.vaddrof ->
        {areads = List.filter (lacksLval dst) arws.areads;
         awrites = List.filter (lacksLval dst) arws.awrites;}
    | _ ->
        {areads = List.filter lacksMemRead arws.areads;
         awrites = List.filter lacksMemRead arws.awrites;}

let killForCall (arws : availRWs) : availRWs =
    let lacksMemRead (lv : lval) : bool =
        not(AELV.lval_has_mem_read lv)
    in
    {areads = List.filter lacksMemRead arws.areads;
     awrites = List.filter lacksMemRead arws.awrites;}

let arws_add_read (arws : availRWs) (lv : lval) : availRWs =
    let areads =
        if List.exists (compareLval lv) arws.areads
        then arws.areads else lv :: arws.areads
    in
    {areads=areads; awrites=arws.awrites}

let arws_add_write (arws : availRWs) (lv : lval) : availRWs =
    let awrites =
        if List.exists (compareLval lv) arws.awrites
        then arws.awrites else lv :: arws.awrites
    in
    {areads=arws.areads; awrites=awrites}

let arws_has_read (arws : availRWs) (lv : lval) : bool =
    List.exists (compareLval lv) arws.areads

let arws_has_write (arws : availRWs) (lv : lval) : bool =
    List.exists (compareLval lv) arws.awrites

let arws_handle_inst (i : instr) (arw : availRWs) : availRWs =
    if (!ignore_inst) i then arw else
    match i with
    | Set(dst,_,_) -> killForWrite dst arw
    | Call(_,Lval(Var vi,NoOffset),[AddrOf lv;_],_)
      when vi.vname = "__sharc_read" ->
        arws_add_read arw lv
    | Call(_,Lval(Var vi,NoOffset),[AddrOf lv;_],_)
      when vi.vname = "__sharc_write" ->
        arws_add_write arw lv
    | Call(dlvo,_,_,_) ->
        if (!ignore_call) i then arw else
        let arw =
            match dlvo with
            | None -> arw
            | Some dst -> killForWrite dst arw
        in
        killForCall arw
    | _ -> arw

module AvailableRWs = struct
    let name = "Available RWs"
    let debug = debug
    type t = availRWs
    let copy (arws : t) = {areads=arws.areads; awrites=arws.awrites}
    let stmtStartData = IH.create 64
    let pretty = arws_pretty
    let computeFirstPredecessor stm arws = arws
    let combinePredecessors (stm:stmt) ~(old:t) (arws:t) =
        if arws_equal old arws then None else
        Some(arws_combine old arws)
    let doInstr (i : instr) (arws : t) = 
        let action = arws_handle_inst i in
        DF.Post(action)
    let doStmt stm arws = DF.SDefault
    let doGuard c arws = DF.GDefault
    let filterStmt stm = true
end

module ARWs = DF.ForwardsDataFlow(AvailableRWs)

let computeARWs (fd : fundec) : unit =
    try let slst = fd.sbody.bstmts in
    let first_stm = List.hd slst in
    IH.clear AvailableRWs.stmtStartData;
    IH.add AvailableRWs.stmtStartData first_stm.sid {areads=[];awrites=[];};
    ARWs.compute [first_stm]
    with Failure "hd" -> if !debug then ignore(E.log "fn w/ no stmts\n")
    | Not_found -> if !debug then ignore(E.log "no data for first_stm?\n")

let getARWs sid =
    try Some(IH.find AvailableRWs.stmtStartData sid)
    with Not_found -> None

let instrARWs il sid arws =
    let proc_one hil i =
        match hil with
        | [] ->
            let arws' = arws_handle_inst i arws in
            arws'::hil
        | arws'::rst as l->
            let arws' = arws_handle_inst i arws' in
            arws'::l
    in
    let folded = List.fold_left proc_one [arws] il in
    let foldednotout = List.rev (List.tl folded) in
    foldednotout

class arwsVisitorClass = object(self)
    inherit nopCilVisitor

    val mutable sid = -1
    val mutable arws_dat_lst = []
    val mutable cur_arws_dat = None

    method vstmt stm =
        sid <- stm.sid;
        match getARWs sid with
        | None -> begin
            cur_arws_dat <- None;
            DoChildren
        end
        | Some arws -> begin
            match stm.skind with
            | Instr il -> begin
                cur_arws_dat <- None;
                arws_dat_lst <- instrARWs il stm.sid arws;
                DoChildren
            end
            | _ -> begin
                cur_arws_dat <- None;
                DoChildren
            end
        end

    method vinst i =
        try
            let data =List.hd arws_dat_lst in
            cur_arws_dat <- Some(data);
            arws_dat_lst <- List.tl arws_dat_lst;
            DoChildren
        with Failure "hd" -> DoChildren

    method get_cur_arws () =
        match cur_arws_dat with
        | None -> getARWs sid
        | Some arws -> Some arws

end

class redundantRWsRemover = object(self)
    inherit arwsVisitorClass as super

    method vinst (i : instr) =
        ignore(super#vinst i);
        match self#get_cur_arws() with
        | None -> DoChildren
        | Some arws -> begin
            match i with
            | Call(_,Lval(Var vi,NoOffset),[AddrOf lv;_],_)
              when vi.vname = "__sharc_read" ->
                if arws_has_read arws lv then ChangeTo[] else DoChildren
            | Call(_,Lval(Var vi,NoOffset),[AddrOf lv;_],_)
              when vi.vname = "__sharc_write" ->
                if arws_has_write arws lv then ChangeTo[] else DoChildren
            | _ -> DoChildren
        end

end

let recomputeCfg (fd:fundec) : unit =
  Cfg.clearCFGinfo fd;
  ignore (Cfg.cfgFun fd)

let removeRedundantRWs (fd : fundec) : unit =
    recomputeCfg fd;
    computeARWs fd;
    ignore(visitCilFunction ((new redundantRWsRemover) :> nopCilVisitor) fd)


(* The entry point *)
let optimFile (f : file) : unit =
    iterGlobals f (fun g -> match g with
    | GFun(fd,_) -> removeRedundantRWs fd
    | _ -> ())
