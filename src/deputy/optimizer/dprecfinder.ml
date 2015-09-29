(*
 * Find checks on globals and formals at the beginning of functions.
 * Also, some utilities for filtering the results.
 *
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
module F = Frontc
module DP = Dpatch

let debug = ref false

let patch_fname = "preconditions.patch.h"
let modp_fname = "modifies.patch.h"

type functionData =
    {
        (* Hash from function vids to list of preconditions *)
        fdPCHash : instr list IH.t;
        
        (* Hash from function vids to fundecs. The bool is true
         * if the function has been modified *)
        fdFnHash : (varinfo * bool) IH.t;
        
        (* Hash from the function vids to lists of modified globals and
           parameters *)
        fdModHash : (varinfo list * int list) IH.t
    }

let mkFDat () =
    {
        fdPCHash = IH.create 100;
        fdFnHash = IH.create 100;
        fdModHash = IH.create 100;
    }

(* Visit each function.
 * Find checks before any real instructions.
 * Add checks to entry in fnPCHash for the function
 *)
class preConditionFinderClass (fdat : functionData) = object(self)
    inherit nopCilVisitor

    (* return the checks that are first in the block *)
    method private findDomChecks (blk : block) fd =
        let rec helper (sl : stmt list) (cl : instr list) =
            match sl with
            | [] -> cl
            | s :: rst -> begin
                match s.skind with
                | Instr il -> begin
                    (*if !debug then
                        ignore(E.log "precFinder: LOOKING AT %a in %s\n"
                            d_stmt (mkStmt (Instr il)) fd.svar.vname);*)
                    if List.exists (fun i -> not(is_check_instr i)) il
                    then begin
                        let newcs = fst((prefix is_check_instr il)) in
                        if !debug  && newcs <> [] then
                            ignore(E.log "precFinder: MIXED %a in %s\n"
                                d_stmt (mkStmt (Instr newcs)) fd.svar.vname);
                        newcs@cl
                    end
                    else begin
                        if !debug then
                            ignore(E.log "precFinder: ADDING %a to %s\n"
                                d_stmt (mkStmt (Instr il)) fd.svar.vname);
                        helper rst (il @ cl)
                    end
                end
                | _ -> cl
            end
        in
        helper blk.bstmts []

    method vfunc (fd: fundec) =
        let precs = self#findDomChecks fd.sbody fd in
        IH.replace fdat.fdPCHash fd.svar.vid precs;
        IH.replace fdat.fdFnHash fd.svar.vid (fd.svar, false);
        SkipChildren

end


(* return a hash from function var id to a list of
 * preconditions for the function *)
let preConditionFinder (fdat : functionData) (f : file) : unit =
    let vis = new preConditionFinderClass fdat in
    visitCilFile vis f

(* filter returns true if a precondition should be kept *)
let precFilter (filter : varinfo -> instr -> bool) 
               (fdat : functionData)
               : unit
    =
    IH.iter (fun vid cl ->
        match IH.tryfind fdat.fdFnHash vid with
        | None -> () (* an error message perhaps? *)
        | Some (fvar, _) -> begin
            let newcl = List.filter (filter fvar) cl in
            IH.replace fdat.fdPCHash vid newcl
        end) fdat.fdPCHash

(* get the place of arg in fnargs *)
let argToNumber (arg: varinfo) (fnvi: varinfo) : int option =
    let rec helper (count : int)
                   (args : (string * typ * attributes) list) :
                   int option
        =
        match args with
        | [] -> None
        | (n,_,_) :: rst ->
            if arg.vname = n then (Some count) else
            helper (count + 1) rst
    in
    match fnvi.vtype with
    | TFun(_,Some args,_,_) -> helper 0 args
    | _ -> None
        

(* Convert an expression into an attribute, if possible. Otherwise raise 
 * NotAnAttrParam *)
exception NotAnAttrParam of exp
let rec expToAttrParam (fnvi: varinfo) (e: exp) : attrparam = 
  match e with 
  | Const(CInt64(i,k,_)) ->
      let i', trunc = truncateInteger64 k i in
      if trunc then 
        raise (NotAnAttrParam e);
      let i2 = Int64.to_int i' in 
      if i' <> Int64.of_int i2 then 
        raise (NotAnAttrParam e);
      AInt i2
  | Lval lv -> lvalToAttrParam fnvi lv
  | StartOf lv -> lvalToAttrParam fnvi lv
  | AddrOf lv -> AAddrOf(lvalToAttrParam fnvi lv)
  | SizeOf t -> ASizeOf t
  | SizeOfE e' -> ASizeOfE (expToAttrParam fnvi e')
  | UnOp(uo, e', _)  -> AUnOp (uo, expToAttrParam fnvi e')
  | BinOp(bo, e1',e2', _)  -> ABinOp (bo, expToAttrParam fnvi e1', 
                                      expToAttrParam fnvi e2')
  | CastE(t, e) when deputyCompareTypes t (typeOf e) ->
        expToAttrParam fnvi e
  | _ -> begin
    if !debug then ignore(E.log "expToAttrParam: not a param: %a\n" d_exp e);
    raise (NotAnAttrParam e)
  end

(* Convernt an lvalue to an attribute parameter *)
and lvalToAttrParam (fnvi : varinfo) (lv : lval) : attrparam =
    match lv with
    | (Var vi, off) -> begin
        match argToNumber vi fnvi with
        | None ->
            offToAttrParam fnvi (ACons(vi.vname, [])) off
        | Some i ->
            let vname = "$"^(string_of_int i) in
            offToAttrParam fnvi (ACons(vname,[])) off
    end
    | (Mem e, off) -> begin
        let eattr = expToAttrParam fnvi e in
        offToAttrParam fnvi (AStar eattr) off
    end

(* convert an attrparam with an offset into an attrparam *)
and offToAttrParam (fnvi: varinfo)
                   (ap: attrparam)
                   (off: offset)
                   : attrparam
    =
    match off with
    | NoOffset -> ap
    | Field(fi, off) ->
        offToAttrParam fnvi (ADot(ap,fi.fname)) off
    | Index(e, off) ->
        let eap = expToAttrParam fnvi e in
        offToAttrParam fnvi (AIndex(ap,eap)) off


(* convert an attribute parameter into an expresssion *)

exception NotAnExp of attrparam
let rec attrParamToExp ?(fnargs: varinfo list = [])
                        (globmap: (string,varinfo) Hashtbl.t)
                        (ap: attrparam)
                        : exp
    =
    let attrParamStringToLval (s: string) : exp =
        if String.sub s 0 1 = "$" then begin
            try
                let nstr = String.sub s 1 ((String.length s) - 1) in
                let n = int_of_string nstr in
                let vi = List.nth fnargs n in
                if isArrayType vi.vtype then
                    StartOf(Var vi, NoOffset)
                else
                    Lval(Var vi, NoOffset)
            with 
            | Failure "nth" -> begin
                ignore(E.log "Failure \"nth\" in attrParamStringToLval: %a\n"
                    d_attrparam ap);
                raise (NotAnExp ap)
            end
            (*| Failure "int_of_string" ->
                raise (NotAnExp ap)
              | Invalid_argument ->
                raise (NotAnExp ap) *)
        end else begin
            try
                let vi = Hashtbl.find globmap s in
                if isArrayType vi.vtype then
                    StartOf(Var vi, NoOffset)
                else
                    Lval(Var vi, NoOffset)
            with Not_found -> begin
                ignore(E.log "Not_found in attrParamStringToLval: %a\n"
                    d_attrparam ap);
                raise (NotAnExp ap)
            end
        end
    in
    let fieldInfoFromName (t: typ) (fn: string) : fieldinfo =
        match unrollType t with
        | TComp(ci, _) -> begin
            try List.find (fun fi -> fi.fname = fn) ci.cfields
            with Not_found -> raise (NotAnExp ap)
        end
        | _ -> raise (NotAnExp ap)
    in
    let attrParamToExp = attrParamToExp ~fnargs:fnargs globmap in
    match ap with
    | AInt i -> integer i
    | AStr s -> Const(CStr s)
    | ACons(s, []) -> attrParamStringToLval s
    | ASizeOf typ -> SizeOf typ
    | ASizeOfE ap -> SizeOfE (attrParamToExp ap)
    | AAlignOf typ -> AlignOf typ
    | AAlignOfE ap -> AlignOfE (attrParamToExp ap)
    | AUnOp(op, ap) ->
        let e = attrParamToExp ap in
        UnOp(op, e, typeOf e)
    | ABinOp(op, ap1, ap2) -> begin
        let e1 = attrParamToExp ap1 in
        let e2 = attrParamToExp ap2 in
        (* Need to make sure that op is correct, here *)
        match op, unrollType (typeOf e1) with
        | PlusA, (TPtr _ | TArray _) -> BinOp(PlusPI, e1, e2, typeOf e1)
        | _, _ -> BinOp(op, e1, e2, typeOf e1)
    end
    | ADot(lap, fn) -> begin
        let e = attrParamToExp lap in
        let fi = fieldInfoFromName (typeOf e) fn in
        match e with
        | Lval(lh, off) ->
            let newoff = Field(fi,NoOffset) in
            if isArrayType fi.ftype then
            	StartOf(lh, addOffset newoff off)
            else
	            Lval(lh, addOffset newoff off)
        | _ -> raise (NotAnExp ap)
    end
    | AStar ap ->
        let e = attrParamToExp ap in
        Lval(Mem e, NoOffset)
    | AAddrOf aap -> begin
        let e = attrParamToExp aap in
        match e with
        | Lval lv -> AddrOf lv
        | _ -> raise (NotAnExp ap)
    end
    | AIndex(bap,iap) -> begin
        let be = attrParamToExp bap in
        let ie = attrParamToExp iap in
        match be with
        | Lval(lh,off) ->
            let newoff = Index(ie,NoOffset) in
            Lval(lh, addOffset newoff off)
        | StartOf(lh, off) ->
            let newoff = Index(ie, NoOffset) in
            Lval(lh, addOffset newoff off)
        | _ -> raise (NotAnExp ap)
    end
    | _ -> raise (NotAnExp ap)

class globalMapMakerClass (globmap : (string,varinfo) Hashtbl.t) = object(self)
    inherit nopCilVisitor

    method vvrbl vi =
        if vi.vglob then begin
            Hashtbl.replace globmap vi.vname vi
        end;
        DoChildren

    method vglob = function
    | GVar(vi,_,_)
    | GVarDecl(vi,_) -> begin
        Hashtbl.replace globmap vi.vname vi;
        DoChildren
    end
    | _ -> DoChildren

end



(* Convert a whold deputy check into an attribute parameter *)
let checkToAttrParam (fnvi: varinfo)
                     (i : instr)
                     : attrparam option
    =
    let mkACons ?(sz : int option = None)
                (name : string)
                (el : exp list)
                : attrparam
        =
        let expToAttrParam = expToAttrParam fnvi in
        let ael = List.map expToAttrParam el in
        let asz = match sz with Some sz -> [AInt sz] | None -> [] in
        ACons(name, ael@asz)
    in
    try
        match instrToCheck i with
        | None -> None
        | Some c -> begin
            match c with
            | CNonNull e -> Some(mkACons "_CNonNull" [e])
            | CEq(e1,e2,_,_) -> Some(mkACons "_CEq" [e1;e2])
            | CPtrArith(e1,e2,e3,e4,sz) ->
                Some(mkACons ~sz:(Some sz) "_CPtrArith" [e1;e2;e3;e4])
            | CPtrArithNT(e1,e2,e3,e4,sz) ->
                Some(mkACons ~sz:(Some sz) "_CPtrArithNT" [e1;e2;e3;e4])
            | CPtrArithAccess(e1,e2,e3,e4,sz) ->
                Some(mkACons ~sz:(Some sz) "_CPtrArithAccess" [e1;e2;e3;e4])
            | CLeqInt(e1,e2,_) -> Some(mkACons "_CLeqInt" [e1;e2])
            | CLeq(e1,e2,_) -> Some(mkACons "_CLeq" [e1;e2])
            | CLeqNT(e1,e2,sz,_) -> Some(mkACons ~sz:(Some sz) "_CLeqNT" [e1;e2])
            | CNullOrLeq(e1,e2,e3,_) -> Some(mkACons "_CNullOrLeq" [e1;e2;e3])
            | CNullOrLeqNT(e1,e2,e3,sz,_) ->
                Some(mkACons ~sz:(Some sz) "_CNullOrLeqNT" [e1;e2;e3])
            | CWriteNT(e1,e2,e3,sz) ->
                Some(mkACons ~sz:(Some sz) "_CWriteNT" [e1;e2;e3])
            | CNullUnionOrSelected(lv,e) ->
                Some(mkACons "_CNullUnionOrSelected" [(Lval lv);e])
            | CSelected e -> Some(mkACons "_CSelected" [e])
            | CNotSelected e -> Some(mkACons "_CNotSelected" [e])
            | _ -> None
        end
    with NotAnAttrParam e -> begin
        if !debug then ignore(E.log "checkToAttrParam: %a\n" d_exp e);
        None
    end

type ctxt =
    {
        mutable cGlobMap : (string, varinfo) Hashtbl.t;
        mutable cInited : bool;
        mutable cFile : file
    }

let mkGlobalContext (f : file) : ctxt =
    let cgm = Hashtbl.create 100 in
    ignore(visitCilFile (new globalMapMakerClass cgm) f);
    {
        cGlobMap = cgm;
        cInited = true;
        cFile = f
    }

(* Convert a Precondition attribute into a list of check instructions *)
let attributeToCheckInstrs ?(fnargs : varinfo list = [])
                            (c : ctxt)
                            (a : attribute)
                            : instr list
    =
    let attrParamToCheck (ap : attrparam) : instr list =
        let attrParamToExp = attrParamToExp ~fnargs:fnargs c.cGlobMap in
        match ap with
        | ACons("_CNonNull", [ap]) ->
            let e = attrParamToExp ap in
            [checkToInstr(CNonNull(e))]
        | ACons("_CEq", [ap1;ap2]) ->
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            [checkToInstr(CEq(e1,e2,"precondition",[]))]
        | ACons("_CPtrArith", [ap1;ap2;ap3;ap4;ap5]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            let e4 = attrParamToExp ap4 in
            let e5 = attrParamToExp ap5 in
            match e5 with
            | Const(CInt64(i64,_,_)) ->
                let sz = Int64.to_int i64 in
                [checkToInstr(CPtrArith(e1,e2,e3,e4,sz))]
            | _ -> []
        end
        | ACons("_CPtrArithNT", [ap1;ap2;ap3;ap4;ap5]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            let e4 = attrParamToExp ap4 in
            let e5 = attrParamToExp ap5 in
            match e5 with
            | Const(CInt64(i64,_,_)) ->
                let sz = Int64.to_int i64 in
                [checkToInstr(CPtrArithNT(e1,e2,e3,e4,sz))]
            | _ -> []
        end
        | ACons("_CPtrArithAccess", [ap1;ap2;ap3;ap4;ap5]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            let e4 = attrParamToExp ap4 in
            let e5 = attrParamToExp ap5 in
            match e5 with
            | Const(CInt64(i64,_,_)) ->
                let sz = Int64.to_int i64 in
                [checkToInstr(CPtrArithAccess(e1,e2,e3,e4,sz))]
            | _ -> []
        end
        | ACons("_CLeqInt", [ap1;ap2]) ->
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            [checkToInstr(CLeqInt(e1,e2,"precondition"))]
        | ACons("_CLeq", [ap1; ap2]) ->
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            [checkToInstr(CLeq(e1,e2,"precondition"))]
        | ACons("_CLeqNT", [ap1;ap2;ap3]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            match e3 with
            | Const(CInt64(i64,_,_)) ->
                let sz = Int64.to_int i64 in
                [checkToInstr(CLeqNT(e1,e2,sz,"precondition"))]
            | _ -> []
        end
        | ACons("_CNullOrLeq", [ap1;ap2;ap3]) ->
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            [checkToInstr(CNullOrLeq(e1,e2,e3,"precondition"))]
        | ACons("_CNullOrLeqNT", [ap1;ap2;ap3;ap4]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            let e4 = attrParamToExp ap4 in
            match e4 with
            | Const(CInt64(i64,_,_)) ->
                let sz = Int64.to_int i64 in
                [checkToInstr(CNullOrLeqNT(e1,e2,e3,sz,"precondition"))]
            | _ -> []
        end
        | ACons("_CWriteNT", [ap1;ap2;ap3;ap4]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            let e3 = attrParamToExp ap3 in
            let e4 = attrParamToExp ap4 in
            match e4 with
            | Const(CInt64(i64,_,_)) ->
                let sz = Int64.to_int i64 in
                [checkToInstr(CWriteNT(e1,e2,e3,sz))]
            | _ -> []
        end
        | ACons("_CNullUnionOrSelected", [ap1; ap2]) -> begin
            let e1 = attrParamToExp ap1 in
            let e2 = attrParamToExp ap2 in
            match e1 with
            | Lval lv ->
                [checkToInstr(CNullUnionOrSelected(lv,e2))]
            | _ -> []
        end
        | ACons("_CSelected", [ap]) ->
            let e1 = attrParamToExp ap in
            [checkToInstr(CSelected(e1))]
        | ACons("_CNotSelected", [ap]) ->
            let e1 = attrParamToExp ap in
            [checkToInstr(CNotSelected(e1))]
        | _ -> []
    in
    match a with
    | Attr("Preconditions",apl) -> begin
        try
            if not c.cInited then
                ignore(visitCilFile (new globalMapMakerClass c.cGlobMap) c.cFile);
            if !debug then
                ignore(E.log "From attr: %a\n" d_attr a);
            let cl = List.concat(List.map attrParamToCheck apl) in
            if !debug then
                ignore(E.log "Extracted: %a\n" d_stmt (mkStmt (Instr cl)));
            cl
        with NotAnExp ap -> begin
            ignore(E.log "Warning: NotAnExp: %a\n" d_attrparam ap);
            []
        end
    end
    | Attr(s, _)  -> begin
        if !debug then
            ignore(E.log "Found attr = %s\n" s);
        []
    end


class precsFromAnnotsClass (c : ctxt) (fdat : functionData) = object(self)
    inherit nopCilVisitor
    
    method vfunc (fd : fundec) =
        try
            if !debug then
                ignore(E.log "Preconditions for: %s : %a\n"
                    fd.svar.vname d_type fd.svar.vtype);
            let attrToChecks = attributeToCheckInstrs ~fnargs:fd.sformals c in
            let attrs = typeAttrs fd.svar.vtype in
            let cl = List.concat(List.map attrToChecks attrs) in
            if cl <> [] then begin
                IH.replace fdat.fdPCHash fd.svar.vid cl;
                match IH.tryfind fdat.fdFnHash fd.svar.vid with
                | None -> IH.add fdat.fdFnHash fd.svar.vid (fd.svar, true)
                | Some _ -> ()
            end;
            SkipChildren
        with Not_found -> SkipChildren
end

let extractPrecsFromAnnots (fdat : functionData) (f : file) : unit =
    let c = mkGlobalContext f in
    ignore(visitCilFile (new precsFromAnnotsClass c fdat) f)

let rec fixIndexLval (lv : lval) : lval =
    let lvp, off = removeOffsetLval lv in
    match off with
    | Index(i, NoOffset) -> begin
        let lvp = fixIndexLval lvp in
        let p = StartOf lvp in
        (Mem (BinOp (PlusPI, p, i, typeOf p)), NoOffset)
    end
    | _ -> lv

class formalSubsterClass stalal = object(self)
    inherit nopCilVisitor

    method vexpr (e : exp) =
        match e with
        | AddrOf(Var vi, off)
        | StartOf(Var vi, off)
        | Lval(Var vi, off) -> begin
            try
                let ((_,t,_),ae) = List.find (fun ((s,_,_),_) -> s = vi.vname)
                    stalal
                in
                match ae with
                | AddrOf(lh, aoff) ->
                    let lv = fixIndexLval (lh, addOffset off aoff) in
                    let newe = mkCast (AddrOf lv) t in
                    ChangeTo(newe)
                | StartOf(lh, aoff) ->
                    let lv = fixIndexLval (lh, addOffset off aoff) in
                    let newe = mkCast (StartOf lv) t in
                    ChangeTo(newe)
                | Lval(lh, aoff) ->
                    let lv = fixIndexLval (lh, addOffset off aoff) in
                    let newe = mkCast (Lval lv) t in
                    ChangeTo(newe)
                | _ -> begin
                    match off with
                    | NoOffset -> ChangeTo (mkCast ae t)
                    | _ -> begin
                        ignore(E.log "%a not a good argument\n" d_exp ae);
                        DoChildren
                    end
                end
            with Not_found -> begin
                if !debug then
                    ignore(E.log "%s not a formal\n" vi.vname);
                DoChildren
            end
        end
        | _ -> begin
            DoChildren
        end

end

(* Replace the formals of t mentioned in ci with the corresponding expr from
   al *)
let substForFormals (t : typ) (al : exp list) (ci : instr) : instr list =
    match t with
    | TFun(rt, Some stal, _, _) -> begin
        let stalal = List.combine stal al in
        let fixedcl = visitCilInstr (new formalSubsterClass stalal) ci in
        if !debug then
            ignore(E.log "type: %a\n oldcheck = %a\n fixedcheck = %a\n"
                d_type t
                d_stmt (mkStmt (Instr [ci])) d_stmt (mkStmt (Instr fixedcl)));
        fixedcl
    end
    | _ -> [ci] (* internal error *)

class callSitePrecAdderClass (fdat : functionData) = object(self)
    inherit nopCilVisitor
    
    method vinst (i : instr) =
        match i with
        | Call(_, Lval(Var fvi, NoOffset), el, _) -> begin
            try
                let cl = IH.find fdat.fdPCHash fvi.vid in
                let clGoodArgs =
                    List.concat(List.map (substForFormals fvi.vtype el) cl)
                in
                ChangeTo(clGoodArgs@[i])
            with Not_found -> DoChildren
        end
        | _ -> DoChildren
end

let addChecksAtCallSites (fd : fundec) (fdat : functionData) : unit =
    ignore(visitCilFunction (new callSitePrecAdderClass fdat) fd)

(* list of options to list of the things inside the Somes *)
let filterNoneAndUnwrap (aol : 'a option list) : 'a list =
    let rec helper aol seen =
        match aol with
        | [] -> List.rev seen
        | x :: rst ->
            match x with
            | None -> helper rst seen
            | Some a -> helper rst (a::seen)
     in
     helper aol []


let addAllPreconditions (fdat : functionData) (f : file) : unit =
    preConditionFinder fdat f
    (*;addPreconditionAttributes fdat*)


(* prints the annotated prototypes from f in file called fname.nonnull.h *)
let printPrototypes (fdat : functionData) (fname : string) : unit =
    let gl = IH.fold (fun vid (fvar,b) gl ->
        if not b then gl else
        (GVarDecl(fvar,locUnknown))::gl)
        fdat.fdFnHash []
    in
    if gl = [] then () else
    let outpf = open_out fname in
    List.iter (fun g ->
        match g with
        | GVarDecl _ ->
            let d = dprintf "%a\n" dp_global g in
            ignore(E.log "Adding %a to %s\n" dp_global g fname);
            fprint outpf ~width:200 d
        | _ -> ()) gl;
    close_out outpf

let binopEqual o1 o2 =
    o1 = o2 ||
    match o1, o2 with
    | PlusA, PlusPI
    | PlusA, IndexPI
    | PlusPI, PlusA
    | PlusPI, IndexPI
    | IndexPI, PlusA
    | IndexPI, PlusPI
    | MinusA, MinusPP
    | MinusA, MinusPI
    | MinusPP, MinusA
    | MinusPP, MinusPI
    | MinusPI, MinusA
    | MinusPI, MinusPP -> true
    | _, _ -> false

let rec attrParamsEqual ap1 ap2 =
    ap1 == ap2 ||
    match ap1, ap2 with
    | AInt i1, AInt i2 -> i1 = i2
    | AStr s1, AStr s2 -> String.compare s1 s2 = 0
    | ASizeOf t1, ASizeOf t2 -> deputyCompareTypes t1 t2
    | ASizeOfE ap1, ASizeOfE ap2 -> attrParamsEqual ap1 ap2
    | ASizeOfS ts1, ASizeOfS ts2 -> Util.equals ts1 ts2
    | AAlignOf t1, AAlignOf t2 -> deputyCompareTypes t1 t2
    | AAlignOfE ap1, AAlignOfE ap2 -> attrParamsEqual ap1 ap2
    | AAlignOfS ts1, AAlignOfS ts2 -> Util.equals ts1 ts2
    | AUnOp(o1,ap1), AUnOp(o2,ap2) -> o1 = o2 && (attrParamsEqual ap1 ap2)
    | ABinOp(o1,ap11,ap12), ABinOp(o2,ap21,ap22) ->
        (binopEqual o1 o2) &&
        (attrParamsEqual ap11 ap21) &&
        (attrParamsEqual ap12 ap22)
    | ADot(ap1,s1), ADot(ap2,s2) ->
        String.compare s1 s2 = 0 &&
        (attrParamsEqual ap1 ap2)
    | AStar ap1, AStar ap2 -> attrParamsEqual ap1 ap2
    | AAddrOf ap1, AAddrOf ap2 -> attrParamsEqual ap1 ap2
    | AIndex(apb1, api1), AIndex(apb2, api2) ->
        (attrParamsEqual apb1 apb2) &&
        (attrParamsEqual api1 api2)
    | AQuestion(ap11,ap12,ap13), AQuestion(ap21,ap22,ap23) ->
        (attrParamsEqual ap11 ap21) &&
        (attrParamsEqual ap12 ap22) &&
        (attrParamsEqual ap13 ap23)
    | ACons(s1,apl1), ACons(s2,apl2) ->
        String.compare s1 s2 = 0 &&
        List.length apl1 = List.length apl2 &&
        List.fold_left (fun b (ap1, ap2) ->
            b && (attrParamsEqual ap1 ap2))
            true (List.combine apl1 apl2)
    | _ -> false


let list_union l1 l2 =
    List.fold_left (fun l x ->
        if List.exists (attrParamsEqual x) l then l
        else x :: l) l1 l2

(* Take two function types and merge the attributes in the names list *)
let mergeAttributes (oldt : typ)
                    (newt : typ)
                    (names : string list)
                    : typ
    =
    List.fold_left (fun oldt name ->
        match oldt, newt with
        | TFun(r1, args1, v1, attrs1), TFun(r2, args2, v2, attrs2) -> begin
            match filterAttributes name attrs1 with
            | [] -> begin
                match filterAttributes name attrs2 with
                | [] -> oldt
                | newprecs :: _ ->
                    TFun(r1, args1, v1, addAttribute newprecs attrs1)
            end
            | (Attr(_,precs1)) :: _ -> begin
                match filterAttributes name attrs2 with
                | [] -> TFun(r1, args1, v1, attrs1)
                | (Attr(_,precs2)) :: _ -> begin
                    let newattrs = dropAttributes [name] attrs1 in
                    let newprecs = Attr(name, list_union precs1 precs2) in
                    let newattrs = addAttribute newprecs newattrs in
                    TFun(r1, args1, v1, newattrs)
                end
            end
        end
        | _, _ -> oldt) oldt names


(* Add Precondition attributes to functions *)
let addPreconditionAttributes (fdat : functionData) : unit =
    IH.iter (fun vid cl ->
        match IH.tryfind fdat.fdFnHash vid with
        | None -> ()
        | Some (fvar, _) -> begin
        	(* HACK: only add if function is static and address is not taken *)
        	if fvar.vstorage <> Static || fvar.vaddrof then () else
            let apl = List.map (checkToAttrParam fvar) cl in
            let apl = filterNoneAndUnwrap apl in
            if apl = [] then begin
                if !debug then
                    ignore(E.log "addPreconditionAttributes: nothing to add for %s : %a\n"
                        fvar.vname d_type fvar.vtype);
                ()
            end else
            let precAttr = [Attr("Preconditions",apl)] in
            fvar.vtype <- typeAddAttributes precAttr fvar.vtype;
            if !debug then
                ignore(E.log "addPreconditionAttributes: new prec for %s = %a\n"
                    fvar.vname d_type fvar.vtype);
            IH.replace fdat.fdFnHash vid (fvar,true)
        end) fdat.fdPCHash

(* add things in fdat.fdModHash to the prototypes in fdat.fdFnHash *)
let addModificationAttributes (fdat : functionData) : unit =
    IH.iter (fun vid (vilst, anlst) ->
        match IH.tryfind fdat.fdFnHash vid with
        | None -> ()
        | Some (fvar, _) -> begin
        	(* HACK: only add if function is static and address is not taken *)
        	if fvar.vstorage <> Static || not(fvar.vaddrof) then () else
            let gattrs = List.map (fun vi -> ACons(vi.vname,[])) vilst in
            let anattrs = List.map (fun i -> ACons("$"^(string_of_int i), [])) anlst in
            let attrs = gattrs @ anattrs in
            let modAttr =
                if attrs = [] then 
                    [Attr("Modifies",[ACons("None",[])])]
                else
                    [Attr("Modifies",attrs)]
            in
            fvar.vtype <- typeAddAttributes modAttr fvar.vtype;
            if !debug then
                ignore(E.log "DModRef: added attr: %s : %a\n"
                    fvar.vname d_type fvar.vtype);
            IH.replace fdat.fdFnHash vid (fvar, true)
        end) fdat.fdModHash

(* Make sure that all the right annotations are on the fundecs in fdFnHash *)
let mergeFunctionData (fdat : functionData) : unit =
    addPreconditionAttributes fdat;
    addModificationAttributes fdat

(* If there is an annotated prototype in the patch file already, then merge
 * these annotations with it, otherwise add the prototype to the patch file *)
let addAnnotsToPatch (fdat : functionData) (pfname : string) : unit =
    mergeFunctionData fdat;
    try
        let dummy = open_in pfname in (* see if the file exists *)
        close_in dummy;
        let pfile = F.parse pfname () in
        IH.iter (fun vid (fvar,b) ->
            let matched = ref false in
            if b then
            List.iter (fun g ->
                match g with
                | GVarDecl(fdv, _) when fdv.vname = fvar.vname -> begin
                    let attrnames = ["Preconditions";"Modifies"] in
                    let newt = mergeAttributes fdv.vtype fvar.vtype attrnames in
                    if !debug then
                        ignore(E.log "addAnnotsToPatch: changing %a to %a\n"
                            d_type fdv.vtype d_type newt);
                    fdv.vtype <- newt;
                    matched := true
                end
                | _ -> ()) pfile.globals;
            if not !matched && b then begin
                pfile.globals <- (GVarDecl(fvar,locUnknown)) :: pfile.globals
            end)
            fdat.fdFnHash;
        let outpf = open_out pfname in
        List.iter (fun g ->
            match g with
            | GVarDecl _ ->
                let d = dprintf "%a\n" dp_global g in
                fprint outpf ~width:200 d
             | _ -> ()) pfile.globals;
        close_out outpf;
    with Sys_error msg -> (* If "Cannot open" is at beginning of msg, then create *)
        printPrototypes fdat pfname
    | x-> begin
        ignore(E.log "%s was raised in addAnnotsToPatch\n" (Printexc.to_string x));
        raise x
    end

let getModifiesPatch (f : file) : unit =
    try
        let fh = open_in modp_fname in
        close_in fh;
        Dpatch.applyPatch f modp_fname
    with Sys_error _ -> ()

(* apply the preconditions patch if it exists. otherwise return false *)
let applyPrecPatch (f : file) : bool =
    let pfn = (Filename.chop_extension f.fileName) ^ ".patch.h" in
    try
		let fh = open_in pfn in
		close_in fh;
		Dpatch.applyPatch f pfn;
		true
    with Sys_error _ -> begin
    	false
    end
(*
    try
        let fh = open_in patch_fname in
        close_in fh;
        let fh = open_in pfn in
        close_in fh;
        Dpatch.applyPatch f patch_fname;
        getModifiesPatch f;
        true
    with Sys_error _ -> begin
        let fh = open_out pfn in
        close_out fh;
        false
    end
*)
