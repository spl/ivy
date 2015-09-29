(*
 * dptranal.ml
 *
 * This file contains functions that Deputy can use to
 * make queries about aliasing relationships, and some utility
 * functions for using aliasing/mod-ref analysis results in
 * dataflow analysis.
 *
 *)


open Cil
open Pretty
open Ivyoptions

module E = Errormsg
module IH = Inthash
module S = Stats

module P = Ptranal
module DPF = Dprecfinder

(* Basic functions for making queries about aliasing *)

let debug = ref false

let may_alias (e1 : exp) (e2 : exp) : bool =
    if !doPtrAnalysis then
        try P.may_alias e1 e2
        (* If the pointer analysis doesn't know anything about one of the
         * expressions, then return true for soundess *)
        with 
        | P.UnknownLocation
        | Not_found -> true
    else true

let try_resolve_lval (lv : lval) : varinfo list option =
    if !doPtrAnalysis then
        try Some(P.resolve_lval lv)
        with Not_found -> begin
            ignore(E.log "DPtrAnal: Couldn't resolve lval: %a.\n" d_lval lv);
            None
        end
    else None

let try_resolve_exp (e : exp) : varinfo list option =
    if !doPtrAnalysis then
        try Some(P.resolve_exp e)
        with Not_found -> begin
            ignore(E.log "DPtrAnal: Couldn't resolve exp: %a\n" d_exp e);
            None
        end
    else None

let try_resolve_funptr (e : exp) : fundec list option =
    if !doPtrAnalysis then
        try Some(P.resolve_funptr e)
        with Not_found -> begin
            ignore(E.log "DPtrAnal: Couldn't resolve funptr %a\n" d_exp e);
            None
        end
    else None

(* Visitor that finds reads from things that alias the pointer ee *)
class aliasReadFinderClass (br : bool ref) (ee : exp) = object(self)
    inherit nopCilVisitor
    
    method vexpr e = match e with
    | AddrOf(Mem e, _)
    | StartOf(Mem e, _)
    | Lval(Mem e, _) -> begin
        if may_alias ee e then begin
            br := true;
            SkipChildren
        end else DoChildren
    end
    | AddrOf(Var vi, NoOffset) ->
        SkipChildren
    | Lval(Var vi, _ )
    | StartOf(Var vi, _) -> begin
        if vi.vaddrof || vi.vglob then begin
            if may_alias ee e then begin
                br := true;
                SkipChildren
            end else match ee with
            | AddrOf(Var gvi, NoOffset) -> begin
                if gvi.vid = vi.vid then begin
                    br := true;
                    SkipChildren
                end else DoChildren
            end
            | _ -> DoChildren
        end else DoChildren
    end
    | _ -> DoChildren

end

let exp_has_alias_read ee e =
    let br = ref false in
    let vis = new aliasReadFinderClass br ee in
    ignore(visitCilExpr vis e);
    !br

let lval_has_alias_read ee lv =
    let br = ref false in
    let vis = new aliasReadFinderClass br ee in
    ignore(visitCilExpr vis (Lval lv));
    !br

(* Utilities for Dataflow analysis *)

let int_list_union l1 l2 =
    List.fold_left (fun l x ->
        if List.mem x l then l else x :: l) l1 l2

let vi_list_union l1 l2 =
    List.fold_left (fun l x ->
        if List.exists (fun vi -> vi.vid = x.vid) l then l else x :: l)
        l1 l2

let handleCall (memKiller : 'a -> exp option -> 'a)
               (fdato : DPF.functionData option)
               (fe : exp)
               (args : exp list)
               (absState  : 'a) :
               'a
    =
    match fdato with
    | None -> memKiller absState None
    | Some fdat -> begin
        (* find what fe can point to *)
        let fns : varinfo list =
            match fe with
            | Lval(Var vf, NoOffset) -> [vf]
            | Lval(Mem ee, NoOffset) -> begin
                if !doPtrAnalysis then
                    match try_resolve_funptr ee with
                    | None -> begin
                        if !debug then
                            ignore(E.log "Dptranal: try_resolve failed: %a\n"
                                d_exp ee);
                        []
                    end
                    | Some [] -> begin
                        if !debug then
                            ignore(E.log "Dptranal: try_resolve returned empty: %a\n"
                                d_exp ee);
                        []
                    end
                    | Some fds -> List.map (fun fd -> fd.svar) fds
                else []
            end
            | _ -> []
        in
        (* if the function couldn't be identified then kill everything *)
        if fns = [] then begin
            if !debug then
                ignore(E.log "Dptranal: Couldn't resolve call of %a\n"
                    d_exp fe);
            memKiller absState None
        end else
        (* glob vis and arg nums that fns might modify, an option in case
           nothing is known *)
        let modsopt : (varinfo list * int list) option =
            List.fold_left
                (fun modsopt fvi ->
                    match modsopt with None -> None
                    | Some(gmds, amds) -> begin
                        match IH.tryfind fdat.DPF.fdModHash fvi.vid with
                        | None -> None
                        | Some(ngmds, namds) ->
                            Some(vi_list_union ngmds gmds,
                                 int_list_union namds amds)
                    end)
                (Some([],[]))
                fns
        in
        match modsopt with
        | None -> begin
            if !debug then
                ignore(E.log "Dptranal: No mod/ref data for %a\n" d_exp fe);
            memKiller absState None
        end
        | Some(gmds, amds) -> begin
            if !debug then
                ignore(E.log "Dptranal: killing things for %a\n" d_exp fe);
            (* kill lvals refering to globals in gmds *)
            let absState = List.fold_left (fun a gvi ->
                memKiller absState (Some(AddrOf(Var gvi, NoOffset))))
                absState gmds
            in
            (* kill lvals that have reads of things aliasing things in amds *)
            List.fold_left (fun a anum ->
                memKiller absState (Some(List.nth args anum)))
                absState amds
        end
    end
