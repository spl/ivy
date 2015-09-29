(*
 *
 * Convert attributes to and from expressions.
 *
 *)

open Cil
open Pretty
open Ivyutil
open Sutil
open Sfunctions

module E = Errormsg

let debug = ref false

type context = {
    cGlobals           : (string, varinfo) Hashtbl.t;
    cFields            : (string, fieldinfo) Hashtbl.t;
}

let newContext () =
    {cGlobals = Hashtbl.create 10;
     cFields = Hashtbl.create 10;}



(* convert an attribute parameter into an expresssion *)
exception NotAnExp of attrparam
let rec attrParamToExp ?(formals: varinfo list = [])
                       ?(actuals: (exp*string) list = [])
                       ?(locals: varinfo list = [])
                       ?(baselv: lval option = None)
                        (ctx : context)
                        (ap: attrparam)
                        : exp
    =
    let attrParamStringToLval (s: string) : exp =
        try
            match formals, actuals, locals with
            | [], actuals, [] -> begin
                fst(List.find (fun (e,n) -> n = s) actuals)
            end
            | formals, [], locals -> begin
                let vi = List.find (fun vi -> vi.vname = s) (formals@locals) in
                if isArrayType vi.vtype then
                    StartOf(Var vi, NoOffset)
                else
                    Lval(Var vi, NoOffset)
            end
            | _ -> begin
                if !debug then
                    E.log "attrParamToExp needs formals XOR actuals for %a"
                        d_attrparam ap;
                raise (NotAnExp ap)
            end
        with
        | Not_found -> begin
            try
                let vi = Hashtbl.find ctx.cGlobals s in
                if isArrayType vi.vtype then
                    StartOf(Var vi, NoOffset)
                else
                    Lval(Var vi, NoOffset)
            with Not_found -> begin
                try let fi = Hashtbl.find ctx.cFields s in
                match baselv with None -> raise(NotAnExp ap)
                | Some blv -> Lval(addOffsetLval (Field(fi,NoOffset)) blv)
                with Not_found ->
                    (* See if it was a renamed static *)
                    let vio = Hashtbl.fold (fun n vi vio ->
                        match vio with
                        | Some vi -> Some vi
                        | None -> begin
                            if Ivystaticrename.alreadyRenamed n &&
                               Filename.check_suffix n s
                            then Some vi
                            else None
                        end) ctx.cGlobals None
                    in
                    match vio with
                    | Some vi ->
                        if isArrayType vi.vtype then
                            StartOf(Var vi, NoOffset)
                        else
                            Lval(Var vi, NoOffset)
                    | None -> begin
                        if !debug then
                            ignore(E.log "Not_found in attrParamStringToLval: %a\n"
                                d_attrparam ap);
                        raise (NotAnExp ap)
                    end
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
    let attrParamToExp =
        attrParamToExp ~formals:formals ~actuals:actuals ~locals:locals ~baselv:baselv ctx
    in
    match ap with
    | AInt i -> integer i
    | AStr s -> Const(CStr s)
    | ACons(s, []) -> attrParamStringToLval s
    | ACons("strlen",[e]) -> CastE(strlenType, attrParamToExp e)
    | ACons("CAST",[ASizeOf t;e]) -> CastE(t, attrParamToExp e)
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

class strlenExtractorClass (fd : fundec) (slil : instr list ref) = object(self)
    inherit nopCilVisitor

    method vexpr (e : exp) =
        match e with
        | CastE(t, ce) when isStrlenType t ->
            let tmp = makeTempVar fd uintType in
            let ce = CastE(charPtrType,ce) in
            let strlen = Call(Some(Var tmp, NoOffset),v2e sfuncs.strlen,[ce],locUnknown) in
            slil := strlen :: (!slil);
            ChangeTo(Lval(Var tmp, NoOffset))
        | _ -> DoChildren

end

let extractStrlenCalls (fd : fundec) (e : exp) : exp * instr list =
    let lr = ref [] in
    let vis = new strlenExtractorClass fd lr in
    let ne = visitCilExpr vis e in
    ne, !lr

(* Convert an expression into an attribute, if possible. Otherwise raise 
 * NotAnAttrParam *)
exception NotAnAttrParam of exp
let rec expToAttrParam (e: exp) : attrparam = 
  match e with 
  | Const(CInt64(i,k,_)) ->
      let i', trunc = truncateInteger64 k i in
      if trunc then 
        raise (NotAnAttrParam e);
      let i2 = Int64.to_int i' in 
      if i' <> Int64.of_int i2 then 
        raise (NotAnAttrParam e);
      AInt i2
  | Lval lv -> lvalToAttrParam lv
  | StartOf lv -> lvalToAttrParam lv
  | AddrOf lv -> AAddrOf(lvalToAttrParam lv)
  | SizeOf t -> ASizeOf t
  | SizeOfE e' -> ASizeOfE (expToAttrParam e')
  | UnOp(uo, e', _)  -> AUnOp (uo, expToAttrParam e')
  | BinOp(bo, e1',e2', _)  -> ABinOp (bo, expToAttrParam e1', 
                                      expToAttrParam e2')
  | _ -> begin
    if !debug then ignore(E.log "expToAttrParam: not a param: %a\n" d_exp e);
    raise (NotAnAttrParam e)
  end

(* Convernt an lvalue to an attribute parameter *)
and lvalToAttrParam (lv : lval) : attrparam =
    match lv with
    | (Var vi, off) -> offToAttrParam (ACons(vi.vname, [])) off
    | (Mem e, off) ->
        let eattr = expToAttrParam e in
        offToAttrParam (AStar eattr) off

(* convert an attrparam with an offset into an attrparam *)
and offToAttrParam (ap: attrparam)
                   (off: offset)
                   : attrparam
    =
    match off with
    | NoOffset -> ap
    | Field(fi, off) -> offToAttrParam (ADot(ap,fi.fname)) off
    | Index(e, off) ->
        let eap = expToAttrParam e in
        offToAttrParam (AIndex(ap,eap)) off

(* build the mapping from names to globals for translation of attrParams *)
class globalFinderClass (ctx : context) = object(self)
    inherit nopCilVisitor as super

    method vvrbl vi =
        if vi.vglob then begin
            Hashtbl.replace ctx.cGlobals vi.vname vi
        end;
        DoChildren

    method vglob = function
    | GVar(vi,_,_)
    | GVarDecl(vi,_) -> begin
        Hashtbl.replace ctx.cGlobals vi.vname vi;
        DoChildren
    end
    | _ -> DoChildren

end

let genContext (f : file) : context =
    let ctx = newContext() in
    visitCilFile (new globalFinderClass ctx) f;
    ctx

let rec findComp (lv : lval) : lval option =
    let rec findInExp (e : exp) : lval option =
        match e with
        | Lval lv -> findComp lv
        | StartOf lv -> findComp lv
        | BinOp(_,e,_,_) -> findInExp e
        | CastE(_,e) -> findInExp e
        | _ -> None
    in
    match removeOffsetLval lv with
    | lv', Field(fi,NoOffset) -> Some lv'
    | lv', (NoOffset | Index _) -> begin
        match lv' with
        | (Var _, NoOffset) -> None
        | (Mem e, NoOffset) -> findInExp e
        | _ -> findComp lv'
    end
    | _ -> None

let addCiToCtx (ctx : context) (ci : compinfo) : unit =
    Hashtbl.clear ctx.cFields;
    if ci.cstruct then
        List.iter (fun fi ->
            Hashtbl.add ctx.cFields fi.fname fi)
            ci.cfields

class attrparamFixerClass ctx (fd : fundec) (lv : lval) = object(self)
    inherit nopCilVisitor

    method vattr (a : attribute) =
        match a with
        | Attr("slocked",apl) -> begin
            match findComp lv with
            | None -> DoChildren
            | Some blv -> begin
                match unrollType(typeOfLval blv) with
                | TComp(ci,_) -> begin
                    addCiToCtx ctx ci;
                    let newapl = List.map (fun ap ->
                        try
                            let ape = attrParamToExp ~formals:fd.sformals
                                                     ~locals:fd.slocals
                                                     ~baselv:(Some blv)
                                                     ctx ap
                            in
                            expToAttrParam ape
                        with NotAnExp ap -> ap) apl
                    in
                    ChangeTo[Attr("slocked", newapl)]
                end
                | _ -> DoChildren (* impossible *)
            end
        end
        | _ -> DoChildren

end

let fixTypeAttrparams ctx (fd : fundec) (lv : lval) (t : typ) : typ =
    let vis = new attrparamFixerClass ctx fd lv in
    visitCilType vis t

let mkTemp (f : file) (fd : fundec) (lv : lval)
           (name : string) (t : typ) : varinfo =
  let rec findUniqueName () : string =
    let n = name ^ (string_of_int (1 + fd.smaxid)) in
    if (List.exists (fun vi -> vi.vname = n) fd.slocals)
      || (List.exists (fun vi -> vi.vname = n) fd.sformals) then begin
        fd.smaxid <- 1 + fd.smaxid;
        findUniqueName ()
      end else
        n
  in
  let name = findUniqueName () in
  let ctx = genContext f in
  let typ' = fixTypeAttrparams ctx fd lv t
      |> typeDropSharCAttrs
      |> typeAddAttributes [sprivate]
  in
  let vi = makeLocalVar fd ~insert:true name typ' in
  vi
