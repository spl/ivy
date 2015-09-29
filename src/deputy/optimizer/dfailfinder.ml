(*
 * dfailfinder.ml
 *
 * This module tries to find feasible models of parameters and globals
 * under which Deputy checks will fail.
 *
 * The entry point is:
 *
 *   failcheck: Cil.exp list -> DCE.Can.t -> (Cil.exp * int) list
 *
 * When given a list of constraints and a canon exp, it will try to find a model
 * of the constraints under which the canon exp is < 0.
 *)

open Cil
open Pretty
open Dattrs
open Dutil
open Dcheckdef
open Doptimutil

module IH = Inthash
module E  = Errormsg
module S = Stats
module SI = SolverInterface
module DSF = Dsolverfront
module DCE = Dcanonexp
module AELV = Availexpslv (* for AELV.exp_has_lval *)

let debug = ref true

(* If there isn't some fact about each lval in the ce,
 * then return false o/w true *)
let checkFacts (cl : exp list)
               (ce : DCE.Can.t)
               : bool * exp list
    =
    (* filter facts in cl that don't mention lvals in ce *)
    let fcl =
        List.filter (fun c ->
            List.exists (fun (_, (e : exp)) ->
                match e with
                | Lval lv | StartOf lv -> AELV.exp_has_lval lv c
                | _ -> false)
            ce.DCE.Can.cf)
        cl
    in
    let b =
        not(List.exists (fun (_, (e : exp)) ->
            match e with
            | Lval lv
            | StartOf lv -> not(List.exists (AELV.exp_has_lval lv) fcl)
            | _ -> true) ce.DCE.Can.cf)
    in
    (b, fcl)

class lvalCollectorClass (lvalHash : (string, lval) Hashtbl.t) = object(self)
    inherit nopCilVisitor
    method vlval (lv : lval) =
        Hashtbl.add lvalHash (sprint 80 (d_lval () lv)) lv;
        DoChildren
end

(* create a mapping from the string of an lval to the lval *)
let makeLvalHash (cl : exp list)
                 : (string, lval) Hashtbl.t
    =
    let lvalHash = Hashtbl.create 100 in
    List.iter (fun e ->
        ignore(visitCilExpr (new lvalCollectorClass lvalHash) e))
        cl;
    lvalHash


let failCheck (cl : exp list)  (ce : DCE.Can.t) : (exp * int) list =
    try
        (* will raise SI.NYI if there is no solver *)
        if !debug then ignore(E.log "failCheck: getting translator\n");
        let translator = SI.getTranslator 0 in

        (* see if there are a quarum of facts
         * TODO: remove facts that can't be translated *)
        if !debug then ignore(E.log "failCheck: checking facts\n");
        let enoughFacts, factList = checkFacts cl ce in
        if not enoughFacts then [] else begin

        (* translate the canon exp *)
        if !debug then ignore(E.log "failCheck: translating check exp\n");
        let (tce,_) = DSF.transCan translator ce in
        (* ce >= 0 *)
        if !debug then ignore(E.log "failCheck: build 0 <= ce\n");
        let tce = translator.DSF.mkLe (translator.DSF.mkConst 0) tce in

        (* translate the constraints *)
        if !debug then ignore(E.log "failCheck: translate constraints\n");
        let tcl = List.map (DSF.transCilExp translator) factList in

        (* make a conjuction of the constraints *)
        (*
        ignore(E.log "failCheck: build conjunction of constraints\n");
        let conj = List.fold_left (fun conj te ->
            translator.DSF.mkAnd te conj) (translator.DSF.mkTrue()) tcl
        in
        *)

        (* make conj => tce *)
        (*
        ignore(E.log "failCheck: build implication\n");
        let impl = translator.DSF.mkImp conj tce in
        *)

        (* if it's invalid, then ask for a counterexample, if it's
           valid, then return [(Cil.one, 1)] *)
        if !debug then ignore(E.log "failCheck: check validity\n");
        let valid, counterEx = translator.DSF.isValidWithAssumptions tcl tce in
        if valid then [(one, 1)] else begin

        (* a list of translated equalities *)
        if !debug then ignore(E.log "failCheck: make lvhash\n");
        let lvalHash = makeLvalHash cl in

        (* convert strings to Cil expressions and return the list *)
        if !debug then ignore(E.log "failCheck: replace strings with lvals\n");
        let res = List.map (fun (str, i) ->
            try
                (Lval(Hashtbl.find lvalHash str), i)
            with Not_found -> (integer 0, i)) counterEx
        in
        if !debug then ignore(E.log "failCheck: done! returning...\n");
        res
        end
        end
    with 
    | SI.NYI _ -> begin
        if !debug then ignore(E.log "Translation failed\n");
        []
    end
    | DSF.NYI  -> begin
        if !debug then ignore(E.log "Translation failed\n");
        []
    end
    | ex -> begin
        ignore(E.log "failCheck: %s was raised during failCheck\n"
            (Printexc.to_string ex));
        raise ex
    end
