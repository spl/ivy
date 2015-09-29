open Cil
open Pretty
open Ivyoptions
open Sfunctions

module E = Errormsg

let sharc_nonowner_attrs = ["slocked";"sreadonly";"sracy";"sreads";"swrites";
                            "sdynbar";"sctx";"ssame";]

let sharc_nondynamic_attrs = "sprivate" :: sharc_nonowner_attrs

let sharc_dynamic_attrs = ["sdynamic";"sindynamic";"soutdynamic";]

let sharc_nonprivate_attrs = sharc_dynamic_attrs @ sharc_nonowner_attrs

let sharc_sharing_attrs = sharc_dynamic_attrs @ sharc_nondynamic_attrs

let sharc_attrs = ["sinthread";"sfnptr";"shasdef";"spure";"scastedstruct"] @
                  ["stcreate"] @ ["sgroup"] @
                  sharc_sharing_attrs

(* functions for adding, rm'ing, and testing type attrs *)
let isFnPtrType (t : typ) : bool = hasAttribute "sfnptr" (typeAttrs t)
let addFnPtrType (t : typ) : typ = typeAddAttributes [Attr("sfnptr",[])] t

(* if the type is of a thread creation function, then return the
   thread function type, and the argument type. *)
let isTCreateType (t : typ) : (int * int) option =
    match filterAttributes "stcreate" (typeAttrs t) with
    | [] -> None
    | [Attr(_,[AInt fnarg;AInt argarg])] ->
        Some(fnarg, argarg)
    | _ ->
        E.error "Multiple stcreate annotations";
        None

let isInThreadType (t : typ) : bool = hasAttribute "sinthread" (typeAttrs t)
let addInThreadType (t : typ) : typ = typeAddAttributes [Attr("sinthread",[])] t
let isInThreadAttr (a : attribute) : bool =
    match a with
    | Attr("sinthread",_) -> true
    | _ -> false

let isDynamicType (t : typ) : bool = hasAttribute "sdynamic" (typeAttrs t)
let isInDynamicType (t : typ) : bool = hasAttribute "sindynamic" (typeAttrs t)
let isOutDynamicType (t : typ) : bool = hasAttribute "soutdynamic" (typeAttrs t)

let isPrivateType (t : typ) : bool = hasAttribute "sprivate" (typeAttrs t)

let rmDynamicType (t : typ) : typ = typeRemoveAttributes ["sdynamic"] t
let rmInDynamicType (t : typ) : typ = typeRemoveAttributes ["sindynamic"] t
let rmOutDynamicType (t : typ) : typ = typeRemoveAttributes ["soutdynamic"] t

let addDynamicType (t : typ) : typ =
    typeAddAttributes [Attr("sdynamic",[])] (rmInDynamicType (rmOutDynamicType t))
let addInDynamicType (t : typ) : typ =
    typeAddAttributes [Attr("sindynamic",[])] t
let addOutDynamicType (t : typ) : typ = 
    typeAddAttributes [Attr("soutdynamic",[])] t

let isCastedStruct (t : typ) : bool =
    match unrollType t with
    | TComp(ci,_) -> hasAttribute "scastedstruct" ci.cattr
    | _ -> false
let rec addCastedStructType (t : typ) : typ =
    let fC ci =
        if not(isCastedStruct (TComp(ci,[]))) then begin
            ci.cattr <- addAttribute (Attr("scastedstruct",[])) ci.cattr;
            List.iter (fun fi -> fi.ftype <- addCastedStructType fi.ftype)
                ci.cfields
        end
    in
    match unrollType t with
    | TPtr(rt,_) -> begin
        match unrollType rt with
        | TComp(ci, _) -> fC ci; t
        | _ -> t
    end
    | TComp(ci, _) -> fC ci; t
    | _ -> t

type sharingAttr =
    | SInDynamic
    | SOutDynamic
    | SDynamic
    | SNone

let getSharingAttr (t : typ) : sharingAttr =
    if isDynamicType t then SDynamic else
    if isInDynamicType t then SInDynamic else
    if isOutDynamicType t then SOutDynamic else
    SNone

let isCtxType (t : typ) : bool = hasAttribute "sctx" (typeAttrs t)
let isPrivateType (t : typ) : bool = hasAttribute "sprivate" (typeAttrs t)
let isRacyType (t : typ) : bool = hasAttribute "sracy" (typeAttrs t)
let isLockedType (t : typ) : bool = hasAttribute "slocked" (typeAttrs t)
let isReadonlyType (t : typ) : bool = hasAttribute "sreadonly" (typeAttrs t)
let isReadsType (t : typ) : bool = hasAttribute "sreads" (typeAttrs t)
let isWritesType (t : typ) : bool = hasAttribute "swrites" (typeAttrs t)

let isDynBarType (t : typ) : bool = hasAttribute "sdynbar" (typeAttrs t)

let isUnqualifiedType (t : typ) : bool =
    not(List.exists (fun s -> hasAttribute s (typeAttrs t)) sharc_sharing_attrs)

let isReferentUnqualified (t : typ) : bool =
    match unrollType t with
    | TPtr(rt, _) -> isUnqualifiedType rt
    | _ -> true (* true for non-pointer *)

let isNonDynamicType (t : typ) : bool =
    isPrivateType t || isRacyType t || isLockedType t || isReadonlyType t ||
    isReadsType t || isWritesType t

let isReferentNonDynamic (t : typ) : bool =
    match unrollType t with
    | TPtr(rt, _) -> isNonDynamicType rt
    | _ -> true (* true for non-pointer *)

let isPtrType (t : typ) : bool =
    match unrollType t with
    | TPtr _ | TArray _ -> true
    | _ -> false

type qualifier =
    | NoQual
    | OneQual of attribute
    | MultiQual

let qualFromAttrs (a : attributes) : qualifier =
    let quals = 
        List.filter (fun (Attr(an,_)) -> List.mem an sharc_sharing_attrs) a
    in
    match quals with
    | [] -> NoQual
    | [Attr(s,ap)] -> OneQual(Attr(s,ap))
    | _ -> MultiQual

let sdynamic = Attr("sdynamic",[])
let sindynamic = Attr("sindynamic",[])
let soutdynamic = Attr("soutdynamic",[])
let sprivate = Attr("sprivate",[])
let sreadonly = Attr("sreadonly", [])
let sctx = Attr("sctx",[])
let sracy = Attr("sracy",[])

let qle (q1 : string) (q2 : string) : bool =
    match q1, q2 with
    | ("sprivate"|"sctx"), q2 when List.mem q2 sharc_sharing_attrs -> true
    | q1, q2 when List.mem q1 sharc_nonprivate_attrs &&
                  List.mem q2 sharc_nonprivate_attrs -> true
    | _, "sctx" -> true
    | _ -> false

let qeq (q1 : string) (q2 : string) : bool =
    q1 = q2 ||
    match q1, q2 with
    | ("sdynamic"|"sindynamic"|"soutdynamic"),
      ("sdynamic"|"sindynamic"|"soutdynamic") -> true
    | _, _ -> false

let isSharCAttr (a : attribute) : bool =
    match a with
    | Attr(s, _) when List.mem s sharc_attrs -> true
    | _ -> false

let isSharCSharingAttr (a : attribute) : bool =
    (* sgroup is a special attribute. They aren't sharing attributes, but
       they have to be the same when we compare types, and that's what this
       function is used for *)
    match a with
    | Attr(s, _) when List.mem s ("sgroup"::sharc_sharing_attrs) -> true
    | _ -> false

class attrDropperClass (sl : string list) = object(this)
    inherit nopCilVisitor

    method vattr (attr : attribute) =
        ChangeTo(dropAttributes sl [attr])

end

let typeDropSharCAttrs (t : typ) : typ =
    typeRemoveAttributes sharc_attrs t

let dropSharCAttrs (f : file) (sl : string list) : unit =
    let vis = new attrDropperClass sl in
    visitCilFile vis f

let dropGlobalSharCAttrs (sl : string list) (g : global) : unit =
    let vis = new attrDropperClass sl in
    ignore(visitCilGlobal vis g)

(* Apply 'fn' to 'g' if 'g' is a function definition *)
let onlyFunctions (fn : fundec -> location -> unit) (g : global) : unit = 
  match g with
  | GFun(f, loc) -> fn f loc
  | _ -> ()

let strlenType =
    TNamed({tname="sharcStrlenType";ttype=voidType;treferenced=true},[])
let isStrlenType (t : typ) =
    match t with
    | TNamed(ti, _) when ti.tname = "sharcStrlenType" -> true
    | _ -> false


(* I need my own typeOf functions so that I can make the type of
   AddrOf private, and give constants the correct type.
   Assumes that something else makes sure that sctx is only in places
   where it is safe for it to go. *)
let rec sharCTypeOf (e: exp) : typ = 
  match e with
  | Const(CInt64 (_, ik, _)) -> TInt(ik, [sprivate])
  | Const(CChr _) -> TInt(IInt,[sprivate])
  | Const(CStr s) -> TPtr(TInt(IChar,[sprivate]),[sprivate])
  | Const(CWStr s) -> TPtr(!wcharType,[sprivate])
  | Const(CReal (_, fk, _)) -> TFloat(fk, [sprivate])
  | Const(CEnum(_, _, ei)) -> TEnum(ei, [sprivate])
  | Lval(lv) -> sharCTypeOfLval lv
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> !typeOfSizeOf
  | AlignOf _ | AlignOfE _ -> !typeOfSizeOf
  | UnOp (_, _, t) -> t
  | BinOp ((PlusPI|IndexPI|MinusPI), e, _, _) -> sharCTypeOf e
  | BinOp(_,_,_,t) -> t
  | CastE (t, _) -> t
  | AddrOf (lv) -> TPtr(sharCTypeOfLval lv, [sprivate])
  | StartOf (lv) -> begin
      match unrollType (sharCTypeOfLval lv) with
        TArray (t,_, a) -> TPtr(t, a)
     | _ -> E.s (E.bug "sharCTypeOf: StartOf on a non-array")
  end

and sharCTypeOfLval = function
    Var vi, off -> sharCTypeOffset vi.vtype off
  | Mem addr, off -> begin
      match unrollType (sharCTypeOf addr) with
        TPtr (t, _) -> sharCTypeOffset t off
      | _ -> E.s (bug "sharCTypeOfLval: Mem on a non-pointer (%a)" d_exp addr)
  end

and sharCTypeOffset basetyp =
    let rec fillQualContext (a : attributes) (t : typ) : typ =
        match qualFromAttrs a, qualFromAttrs (typeAttrs t) with
        | NoQual, _ | _, NoQual ->
            t
        | MultiQual, _ | _, MultiQual ->
            E.s(bug "sharCTypeOffset: multiple qualifiers")
        | OneQual attr, OneQual(Attr(("sctx"|"ssame"),_)) -> begin
            (* fill in context! *)
            let grpattr = filterAttributes "sgroup" a in
            match t with
            | TPtr(rt,a) ->
                let rt = fillQualContext (attr :: grpattr) rt in
                typeAddAttributes (attr :: grpattr)
                    (typeRemoveAttributes ["sctx";"ssame"] (TPtr(rt,a)))
            | TArray(rt,e,a) ->
                let rt = fillQualContext (attr :: grpattr) rt in
                typeAddAttributes (attr :: grpattr)
                    (typeRemoveAttributes ["sctx";"ssame"] (TArray(rt,e,a)))
            | _ ->
                typeAddAttributes (attr :: grpattr)
                    (typeRemoveAttributes ["sctx";"ssame"] t)
        end
        | OneQual attr, OneQual _ -> begin
            (* no context to fill in at this level. try the next level *)
            let grpattr = filterAttributes "sgroup" a in
            match t with
            | TPtr(rt, a) -> TPtr(fillQualContext (attr :: grpattr) rt,a)
            | TArray(rt,e,a) -> TArray(fillQualContext (attr :: grpattr) rt,e,a)
            | _ -> t
        end
    in
    function
    | NoOffset -> basetyp
    | Index (_, o) -> begin
      match unrollType basetyp with
      | TArray (t, _, baseAttrs) ->
        sharCTypeOffset (fillQualContext baseAttrs t) o
      | t -> E.s (E.bug "sharCTypeOffset: Index on a non-array")
    end 
    | Field (fi, o) -> begin
      match unrollType basetyp with
      |TComp (ci, baseAttrs) ->
        sharCTypeOffset (fillQualContext baseAttrs fi.ftype) o
      | _ -> E.s (bug "sharCTypeOffset: Field on a non-compound")
    end

(* Generate a stmt for single instr 'i' *)
let i2s (i : instr) : stmt = mkStmt(Instr [i])
(* Generate an expression for variable 'v' *)
let v2e (v : varinfo) : exp = Lval(var v)

let isPthreadFnName (s : string) : bool =
    String.length s >= 7 && String.sub s 0 7 = "pthread"

let isPthreadCall (i : instr) : bool =
    match i with
    | Call(_,Lval(Var vi, NoOffset),_,_)
      when isPthreadFnName vi.vname -> true
    | _ -> false

(* Printer that filters out our attributes, and prints adjust functions *)
class sharcPrinterClass : descriptiveCilPrinter = object (self)
  inherit Dutil.deputyPrinterClass ~showBounds:false ~enable:false as super

  method pAttr (a: attribute) : doc * bool =
    match a with
    | Attr("slocked",[ap]) ->
        dprintf "SLOCKED(%a)" self#pAttrParam ap, false
    | Attr("sreadonly",_) ->
        text "SREADONLY", false
    | Attr("sracy",_) ->
        text "SRACY", false
    | Attr("sreads",[ap]) ->
        dprintf "SREADS(%a)" self#pAttrParam ap, false
    | Attr("swrites",[ap]) ->
        dprintf "SWRITES(%a)" self#pAttrParam ap, false
    | Attr("sctx",_) ->
        text "SCTX", false
    | Attr("ssame",_) ->
        text "SSAME", false
    | Attr("sgroup",[ap]) ->
        dprintf "SGROUP(%a)" self#pAttrParam ap, false
    | Attr("sprivate",_) ->
        text "SPRIVATE", false
    | Attr("sdynamic",_) ->
        text "SDYNAMIC", false
    | Attr("sdynbar",[ap]) ->
        dprintf "SDYNBAR(%a)" self#pAttrParam ap, false
    | Attr("sindynamic",_) ->
        text "SINSHARED", false
    | Attr("soutdynamic",_) ->
        text "SOUTSHARED", false
    | Attr("sinthread",_) ->
        text "SINTHREAD", false
    | Attr("sfnptr",_) ->
        text "SFNPTR", false
    | Attr("shasdef",_) ->
        text "SHASDEF", false
    | Attr("spure",_) ->
        text "SPURE", false
    | Attr("stcreate",_) ->
        text "STCREATE", false
    | Attr("scastedstruct",_) ->
        text "SCASTEDSTRUCT", false
    | _ -> super#pAttr a

end

let sharcPrinter = new sharcPrinterClass

let sp_type () (t: typ) : doc =
  sharcPrinter#pType None () t

let sp_attrparam () e : doc =
  sharcPrinter#pAttrParam () e

let sp_exp () (e: exp) : doc =
  sharcPrinter#pExp () e

let sp_lval () (lv: lval) : doc =
  sharcPrinter#pLval () lv

let sp_instr () (i : instr) : doc =
  sharcPrinter#pInstr () i

let sp_global () (g : global) : doc =
  sharcPrinter#pGlobal () g


(* make_sharing_cast is defined in crc.ml *)
class scastConverterClass (fd : fundec) make_sharing_cast = object(self)
    inherit nopCilVisitor

    method private getBaseLval (e : exp) : lval option =
        match e with
        | Lval lv -> Some lv
        | StartOf lv -> begin
            match lv with
            | (Mem e, _) -> self#getBaseLval e
            | _ -> None
        end
        | CastE(_,e)
        | BinOp(_,e,_,_) -> self#getBaseLval e
        | _ -> None

    method vinst (i : instr) =
        match i with
        | Call(Some lv, Lval(Var fvi,NoOffset), [ce], loc)
          when fvi.vname = "SCAST" -> begin
            match self#getBaseLval ce with
            | Some blv ->
                ChangeTo [make_sharing_cast fd lv ce blv loc]
            | None ->
                E.error ("Cannot enforce linearity in cast of %a at %a")
                    sp_exp ce d_loc loc;
                SkipChildren
        end
        | Call(_, Lval(Var fvi, NoOffset), _, loc)
          when fvi.vname = "SCAST" ->
            E.error ("Malformed sharing cast at %a") d_loc loc;
            SkipChildren
        | _ -> DoChildren

end

let convertSCASTs (f : file) make_sharing_cast : unit =
    let fdcheck fd loc =
        let vis = new scastConverterClass fd make_sharing_cast in
        ignore(visitCilFunction vis fd)
    in
    iterGlobals f (onlyFunctions fdcheck)
