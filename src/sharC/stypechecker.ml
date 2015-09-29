(*
 * stypechecker.ml
 *
 * The SharC type checker.
 *
 *
 *)

open Cil
open Expcompare
open Pretty
open Ivyoptions
open Ivyutil
open Sfunctions
open Sutil

module E = Errormsg
module UD = Usedef
module VS = UD.VS

type compatType =
    | Equal
    | CheckRead of attrparam * attrparam option  (* attrparam is size in bytes *)
    | CheckWrite of attrparam * attrparam option
    | Cast
    | NotEqual

let ptrQualsCompatible (da : attributes) (sa : attributes) : compatType =
    match qualFromAttrs da, qualFromAttrs sa with
    | (NoQual | MultiQual), _
    | _, (NoQual | MultiQual) ->
        E.error "Malformed sharing types";
        NotEqual
    | OneQual(Attr(ds,apl)), OneQual(Attr(ss,dapl)) -> begin
        let dgt = hasAttribute "sgroup" da in
        let sgt = hasAttribute "sgroup" sa in
        let onegroup = (dgt && not(sgt)) || (not(dgt) && sgt) in
        if qeq ds ss && onegroup then NotEqual else
        if qeq ds ss then Equal else
        match ds, ss with
        | "sreads", ("sprivate"|"sreadonly"|"sracy") -> Equal
        | "sreads", "sdynbar" -> CheckRead (List.hd apl, Some(List.hd dapl)) 
        | "sreads", _ -> CheckRead (List.hd apl, None)
        | "swrites", ("sprivate"|"sracy") -> Equal
        | "swrites", "sdynbar" -> CheckWrite (List.hd apl, Some(List.hd dapl))
        | "swrites", _ -> CheckWrite (List.hd apl, None)
        | "sindynamic", "sprivate" -> if onegroup then NotEqual else Equal
        | _, _ -> Cast
    end

(** TODO:

An expression of structure type can be opened when it contains fields
with SSAME in their type(otherwise, there's no need to), and when it
is either SPRIVATE, SLOCKED when the lock is heald, or SREADONLY so long
as the SSAME fields are not written.

Maybe...
{ SOPEN(e)

/* in here the SSAME fields of e can be read and written, but not
   aliased. They can be SCAST, though. */

}

*)

(* The Comp is castable if there are no sctx qualifiers on the target types
   of pointers *)
(* CHANGE: This is obviated by placing SDYNAMIC on unqualified target types in
   scasted structs, so just return true *)
let rec isCastableComp ?(ctx : string list = []) (ci : compinfo) : bool = true
(*
    List.mem ci.cname ctx ||
    not(List.exists (fun fi ->
        match unrollType fi.ftype with
        | TPtr(rt,a) | TArray(rt,_,a) -> begin
            isCtxType rt ||
            match unrollType rt with
            | TComp(ci',a) -> isCastableComp ~ctx:(ci.cname::ctx) ci'
            | _ -> false
        end
        | TComp(ci',a) -> isCastableComp ~ctx:(ci.cname::ctx) ci'
        | _ -> false)
        ci.cfields)
*)

(* For type equality purposes, sdynamic == sindynamic == soutdynamic,
   so before comparing types, rename everything to sdynamic *)
class qualMergerClass = object(self)
    inherit nopCilVisitor

    method vattr (a : attribute) =
        match a with
        | Attr(("sindynamic"|"soutdynamic"),ap) ->
            ChangeTo[Attr("sdynamic",ap)]
        | Attr("slocked",_) ->
            ChangeTo[Attr("slocked",[])]
        | _ -> SkipChildren

end

let qualMerger (t : typ) : typ =
    visitCilType (new qualMergerClass) t

let compareSharCTypes = compareTypes ~importantAttr:isSharCSharingAttr

(* are drt and srt compatible pointer target types? *)
(*
    Casting to and from void * is allowed if the sharing doesn't change.
    Casting pointers to structures is allowed when all pointers in the structure
      are explicitly given the ssame qualifier.
    Casting between pointers to pointers is allowed if the referrent types are
      equivalent.
*)
let rec ptrTypesCompatible (drt : typ) (srt : typ) : compatType =
    let qres = ptrQualsCompatible (typeAttrs drt) (typeAttrs srt) in
    let mdrt = qualMerger drt in
    let msrt = qualMerger srt in
    if compareSharCTypes mdrt msrt then qres else
    match drt, srt with
    | TNamed(ti, _), _ -> ptrTypesCompatible ti.ttype srt
    | _, TNamed(ti, _) -> ptrTypesCompatible drt ti.ttype
    | TVoid _, _ | _, TVoid _ when qres <> Cast -> qres
    | TInt _, _ | _, TInt _ when qres <> Cast -> qres (* old code uses char as void *)
    | TComp _, TComp _ when qres <> Cast -> qres
    | TComp(ci1,_),TComp(ci2,_) when qres = Cast ->
        if isCastableComp ci1 then Cast else NotEqual
    | TInt _, (TPtr _ | TArray _) -> qres
    | (TPtr(TVoid da,_)|TArray(TVoid da,_,_)),
      (TPtr(srt,_)|TArray(srt,_,_)) -> begin
        (* Can cast other pointer types to void * when the
           sharing mode is the same *)
        match qualFromAttrs da, qualFromAttrs (typeAttrs srt) with
        | OneQual(Attr(dq,_)), OneQual(Attr(sq,_)) when qeq dq sq -> qres
        | _ -> NotEqual
    end
    | (TPtr(drt,_)|TArray(drt,_,_)), (TPtr(srt,_)|TArray(srt,_,_)) -> 
        let mdrt = qualMerger drt in
        let msrt = qualMerger srt in
        if compareSharCTypes mdrt msrt then
            qres
        else if ptrTypesCompatible mdrt msrt = Equal then
            qres
        else NotEqual
    | (TInt _ | TFloat _ | TEnum _ | TBuiltin_va_list _),
      (TInt _ | TFloat _ | TEnum _ | TBuiltin_va_list _) ->
        qres
    | TFun(voidType,Some tal,false,_), TFun(_,Some sal,false,_)
      when Dattrs.isDeallocator srt ->
        (* pointers to deallocators match function pointer types with the
           correct number of arguments *)
        if List.length tal = List.length sal then
            qres
        else NotEqual
    | _ -> NotEqual


(* x:t1 <-- y:t2, or f(y:t2) where f takes a t1,
   or return y:t2 when the function returns t1 *)
let rec typesCompatible (dstt : typ) (srct : typ) : compatType =
    if not(isPtrType dstt) && not(isPtrType srct) then Equal else
    let mdstt = qualMerger dstt in
    let msrct = qualMerger srct in
    if compareSharCTypes mdstt msrct then Equal else
    match dstt, srct with
    | TNamed(ti,a), _ -> typesCompatible ti.ttype srct
    | _, TNamed(ti,a) -> typesCompatible dstt ti.ttype
    | (TInt(_,_)|TEnum(_,_)), TPtr(_,_) -> Equal (* casting pointer to int OK *)
    | TPtr(rt,_), (TInt(_,_) | TEnum(_,_)) -> begin
        match unrollType rt with
        | TVoid _ -> Equal
        | _ ->
        (* Casting an integer to a pointer is definitely unsound, but it happens
           often enough that we'll allow it and give a very stern warning *)
        E.warn ("Casting an integer to a pointer is unsound at %a."^^
                "You better know what you're doing.") d_loc (!currentLoc);
        Equal
    end
    | (TPtr(drt,da) | TArray(drt,_,da)), (TPtr(srt, sa) | TArray(srt,_,sa)) ->
        ptrTypesCompatible drt srt
    | TPtr _, TFun _ -> (* promote function to function pointer *)
        typesCompatible dstt (TPtr(srct,[sprivate]))
    | _, _ ->
        E.log "typesCompatible: %a != %a\n" sp_type dstt sp_type srct;
        NotEqual

let isAllocator (fe : exp) : bool =
    match fe with
    | Lval(Var fvi, NoOffset)
      when fvi.vname = "malloc" || fvi.vname = "realloc" -> true
    | _ -> Dattrs.isAllocator(typeOf fe)

let isDeallocator (fe : exp) : bool =
    match fe with
    | Lval(Var fvi, NoOffset)
      when fvi.vname = "free" -> true
    | _ -> Dattrs.isDeallocator(typeOf fe)

(* This visitor does the type checking *)
class typeCheckerClass (fd : fundec) (checks : bool ref) = object(self)
    inherit nopCilVisitor(*Liveness.livenessVisitorClass true as super*)

    method private isConst (e : exp) : bool =
        match e with
        | Const _ -> true
        | CastE(_,e) -> self#isConst e
        | _ -> false

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

    method private handleRet loc lvo rt : unit =
        match lvo with
        | None -> ()
        | Some lv ->
            let lvt = sharCTypeOfLval lv in
            match typesCompatible lvt rt with
            | Cast ->
                E.error ("Sharing cast needed for assignment at %a\n\t"^^
                         "Got: %a\n\tExpected: %a")
                    d_loc loc sp_type rt sp_type lvt;
                checks := false
            | NotEqual ->
                E.error ("Types not compatible in assignment at %a\n\t"^^
                         "Got: %a\n\tExpected: %a")
                    d_loc loc sp_type rt sp_type lvt;
                checks := false
            | _ -> ()

    method private checkSingleArg loc (n,t,a) arg : unit =
        if self#isConst arg then () else
        match typesCompatible t (sharCTypeOf arg) with
        | Cast ->
            E.error ("Sharing cast needed for argument: %a at %a\n\t"^^
                     "Got: %a\n\tExpected: %a")
                sp_exp arg d_loc loc sp_type (sharCTypeOf arg) sp_type t;
            checks := false
        | NotEqual ->
            E.error ("Types not compatible for argument %a at %a\n\t"^^
                     "Got: %a\n\tExpected: %a")
                sp_exp arg d_loc loc sp_type (sharCTypeOf arg) sp_type t;
            checks := false
        | _ -> ()

    method private handleArgs loc args argtso : unit =
        match argtso with
        | Some argts -> begin
            if List.length args <> List.length argts then begin
                (*E.warn "Not checking call with wrong number of args at %a"
                    d_loc loc*)
                ()
            end else List.iter2 (self#checkSingleArg loc) argts args
        end
        | None when args <> [] ->
            E.warn "Wrong number of arguments at %a" d_loc loc
        | None -> ()

    method private checkTCreateArgs loc (fnarg,argarg) args : unit =
        try
            let fn = List.nth args fnarg in
            let arg = List.nth args argarg in
            match unrollType(typeOf fn) with
            | TPtr(TFun(_, Some [n,ft,a], _, _),_) -> begin
                self#checkSingleArg loc (n,ft,a) arg;
                match unrollType ft with
                | TPtr(rt,_) when isPrivateType rt -> begin
                    checks := false;
                    E.error "Thread function %a can't take private arg at %a"
                        sp_exp fn d_loc loc
                end
                | _ -> ()
            end
            | _ ->
                checks := false;
                E.error "Bad thread create argument: %a:%a at %a"
                    sp_exp fn sp_type (unrollType(typeOf fn)) d_loc loc
        with _ ->
            checks := false;
            E.error "Malformed stcreate annotations: STCREATE(%d,%d) #args=%d"
                fnarg argarg (List.length args)

    method vinst (i : instr) = (*ignore(super#vinst i);*)
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Set(_, e, _) when self#isConst e -> DoChildren
        | Set(lv, e, loc) -> begin
            let lvt = sharCTypeOfLval lv
            and et = sharCTypeOf e in
            match typesCompatible lvt et with
            | Equal -> DoChildren
            | Cast ->
                E.error ("Sharing cast needed for assignment: %a at %a\n\t"^^
                         "Got: %a\n\tExpected: %a")
                    sp_instr i d_loc loc sp_type et sp_type lvt;
                checks := false;
                DoChildren
            | _ ->
                E.error ("Types not compatible in assignment: %a at %a\n\t"^^
                         "Got: %a\n\tExpected: %a")
                    sp_instr i d_loc loc sp_type et sp_type lvt;
                checks := false;
                DoChildren
        end
        | Call(_, fe, args, loc)
          when isAllocator fe || isDeallocator fe -> begin
            (* Checking malloc and free is handled by heapsafe *)
            DoChildren
        end
        | Call(_, fe, args, loc)
          when isTCreateType(typeOf fe) <> None -> begin
            match isTCreateType(typeOf fe) with
            | None -> DoChildren (* impossible *)
            | Some(fnarg,argarg) ->
                self#checkTCreateArgs loc (fnarg,argarg) args;
                DoChildren
        end
        | Call(Some lv, Lval(Var fvi,NoOffset), [src], loc)
          when fvi.vname = "SINIT" || fvi.vname = "SINIT_DOUBLE" ||
               fvi.vname = "SINIT_FLOAT" ->
            let lvt = sharCTypeOfLval lv in
            let srct = sharCTypeOf src in
            let tcres = typesCompatible lvt srct in
            if tcres <> Equal then
                E.error ("Bad types for SREADONLY initialization at %a\n\t"^^
                         "Got: %a\n\tTarget: %a")
                    d_loc loc sp_type srct sp_type lvt;
            DoChildren
        | Call(Some lv, Lval(Var fvi,NoOffset), ce :: _, loc)
          when fvi.vname = "__sharc_sharing_cast" -> begin
            let lvt = sharCTypeOfLval lv
            and cet = sharCTypeOf ce in
            let tcres = typesCompatible lvt cet in
            if tcres <> Cast && tcres <> Equal then
                E.error ("Types not suitable for sharing cast at %a\n\t"^^
                         "Got: %a\n\tTarget: %a")
                    d_loc loc sp_type cet sp_type lvt;
            if tcres = Equal then
                E.warn ("Types in sharing cast are equal at %a\n"^^
                        "Got: %a\n\tTarget: %a")
                    d_loc loc sp_type cet sp_type lvt;
            ignore(self#vlval lv);
            ignore(self#vexpr ce);
            SkipChildren
(*
            match self#getBaseLval ce with
            | Some blv ->
                ignore(self#vlval lv);
                ignore(self#vexpr ce);
                ChangeTo [make_sharing_cast fd lv ce blv loc]
            | None ->
                E.error ("Cannot enforce linearity in cast of %a at %a")
                    sp_exp ce d_loc loc;
                DoChildren
*)
        end
        | Call(lvo, fe, args, loc) -> begin
            match unrollType (sharCTypeOf fe) with
            | TFun(rt, argtso, va, a) ->
                self#handleRet loc lvo rt;
                self#handleArgs loc args argtso;
                DoChildren
            | _ ->
                E.error "Call on non-function type?? %a at %a"
                    sp_instr i d_loc loc;
                DoChildren
        end
        | Asm(_,_,_,_,_,loc) ->
            E.warn "Unchecked inline assembly at %a" d_loc loc;
            DoChildren

    method vstmt (s : stmt) = (*ignore(super#vstmt s);*)
        match s.skind with
        | Return(Some e, _) when self#isConst e -> DoChildren
        | Return(Some e, loc) -> begin
            let et = sharCTypeOf e in
            match unrollType fd.svar.vtype with
            | TFun(rt,_,_,_) -> begin
                match typesCompatible rt et with
                | Cast ->
                    E.error ("Sharing cast needed for return at %a\n\t"^^
                             "Source: %a\n\tTarget: %a")
                        d_loc loc sp_type et sp_type rt;
                    DoChildren
                | NotEqual ->
                    E.error ("Type not compatible for return at %a\n\t"^^
                             "Got: %a\n\tExpected: %a")
                        d_loc loc sp_type et sp_type rt;
                    DoChildren
                | _ -> DoChildren
            end
            | _ ->
                E.bug "fundec has non-function type?? %s"
                    fd.svar.vname;
                DoChildren
        end
        | _ -> DoChildren

    method vexpr (e : exp) =
        if self#isConst e then SkipChildren else
        match e with
        | CastE(t, e') -> begin
            let et = sharCTypeOf e' in
            match typesCompatible t et with
            | Cast ->
                E.error ("Sharing cast needed for C cast at %a\n\t"^^
                         "Source: %a\n\tTarget: %a")
                    d_loc (!currentLoc) sp_type et sp_type t;
                DoChildren
            | NotEqual ->
                E.error ("Types not compatible in C cast at %a\n\t"^^
                         "Source: %a\n\tTarget: %a")
                    d_loc (!currentLoc) sp_type et sp_type t;
                DoChildren
            | _ -> DoChildren
        end
        | _ -> DoChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then begin
            E.log "Skipping TRUSTED block\n";
            SkipChildren
        end else DoChildren

end

class summaryInstrumenterClass fd ctx = object(self)
    inherit nopCilVisitor

    method private isConst (e : exp) : bool =
        match e with
        | Const _ -> true
        | CastE(_,e) -> self#isConst e
        | _ -> false

    method private checkReadRange arg sz loc =
        let amsg = sprint ~width:80 (sp_exp () arg) in
        let szmsg = sprint ~width:80 (sp_exp () sz) in
        let lmsg = sprint ~width:80 (d_loc () loc) in
        let msg = mkString("Read Range Check: ("^amsg^","^szmsg^") @ "^lmsg) in
        Call(None,v2e sfuncs.readrange,[CastE(voidPtrType,arg);sz;msg],loc)

    method private checkWriteRange arg sz loc =
        let amsg = sprint ~width:80 (sp_exp () arg) in
        let szmsg = sprint ~width:80 (sp_exp () sz) in
        let lmsg = sprint ~width:80 (d_loc () loc) in
        let msg = mkString("Write Range Check: ("^amsg^","^szmsg^") @ "^lmsg) in
        Call(None,v2e sfuncs.writerange,[CastE(voidPtrType,arg);sz;msg],loc)

    method private checkDynBarReadRange bar arg sz loc =
        let amsg = sprint ~width:80 (sp_exp () arg) in
        let szmsg = sprint ~width:80 (sp_exp () sz) in
        let lmsg = sprint ~width:80 (d_loc () loc) in
        let msg = mkString("Read Range Check: ("^amsg^","^szmsg^") @ "^lmsg) in
        Call(None,v2e sfuncs.readdynbarrange,[bar;CastE(voidPtrType,arg);sz;msg],loc)

    method private checkDynBarWriteRange bar arg sz loc =
        let amsg = sprint ~width:80 (sp_exp () arg) in
        let szmsg = sprint ~width:80 (sp_exp () sz) in
        let lmsg = sprint ~width:80 (d_loc () loc) in
        let msg = mkString("Write Range Check: ("^amsg^","^szmsg^") @ "^lmsg) in
        Call(None,v2e sfuncs.writedynbarrange,[bar;CastE(voidPtrType,arg);sz;msg],loc)

    method private handleArgs loc args argtso : instr list =
        match argtso with
        | Some argts ->
            if List.length args <> List.length argts then [] else begin
                List.fold_left2 (fun cl (n,t,_) arg ->
                    if self#isConst arg then cl else
                    match typesCompatible t (sharCTypeOf arg) with
                    | CheckRead (ap, None) ->
                        let actualNames = List.combine args (List.map fst3 argts) in
                        let sz, slis =
                            Sattrconv.attrParamToExp ~actuals:actualNames ctx ap
                            |> Sattrconv.extractStrlenCalls fd
                        in
                        let chk = self#checkReadRange arg sz loc in
                        slis @ (chk :: cl)
                    | CheckRead (ap, Some barap) ->
                        let actualNames = List.combine args (List.map fst3 argts) in
                        let sz, slis =
                            Sattrconv.attrParamToExp ~actuals:actualNames ctx ap
                            |> Sattrconv.extractStrlenCalls fd
                        in
                        let bar =
                            Sattrconv.attrParamToExp ~actuals:actualNames ctx barap
                        in
                        let chk = self#checkDynBarReadRange bar arg sz loc in
                        slis @ (chk :: cl)
                    | CheckWrite (ap, None) ->
                        let actualNames = List.combine args (List.map fst3 argts) in
                        let sz, slis =
                            Sattrconv.attrParamToExp ~actuals:actualNames ctx ap
                            |> Sattrconv.extractStrlenCalls fd
                        in
                        let chk = self#checkWriteRange arg sz loc in
                        slis @(chk :: cl)
                    | CheckWrite (ap, Some barap) ->
                        let actualNames = List.combine args (List.map fst3 argts) in
                        let sz, slis =
                            Sattrconv.attrParamToExp ~actuals:actualNames ctx ap
                            |> Sattrconv.extractStrlenCalls fd
                        in
                        let bar =
                            Sattrconv.attrParamToExp ~actuals:actualNames ctx barap
                        in
                        let chk = self#checkDynBarWriteRange bar arg sz loc in
                        slis @(chk :: cl)
                    | _ -> cl) [] argts args
            end
        | None when args <> [] -> []
        | None -> []

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Call(_, Lval(Var fvi, NoOffset), _, _)
          when fvi.vname = "__sharc_sharing_cast" ->
            SkipChildren
        | Call(lvo, fe, args, loc)
          when not(isAllocator fe) && not(isDeallocator fe) -> begin
            match unrollType (sharCTypeOf fe) with
            | TFun(rt, argtso, va, a) ->
                let checks = self#handleArgs loc args argtso in
                ChangeTo(checks@[i])
            | _ ->
                E.error "Call on non-function type?? %a at %a"
                    sp_instr i d_loc loc;
                SkipChildren
        end
        | _ -> SkipChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then SkipChildren
        else DoChildren

end


(* Warn if the source of a sharing cast is not dead after the cast *)
class scastDeadnessCheckerClass = object(self)
    inherit Liveness.deadnessVisitorClass as super

    method vinst (i:instr) =
        ignore(super#vinst i);
        match i with
        | Call(Some lv, Lval(Var vf,NoOffset), (Lval(Var srcv,_) as src) :: _, loc)
          when vf.vname = "__sharc_sharing_cast" ->
            if not(VS.mem srcv post_dead_vars) then
                E.warn "Failed to prove that %a is dead after Sharing Cast at %a"
                    sp_exp src d_loc loc;
            DoChildren
        | Call(Some lv, Lval(Var vf,NoOffset), src :: _, loc)
          when vf.vname = "__sharc_sharing_cast" ->
            E.warn "Failed to prove that %a is dead after Sharing Cast at %a"
                sp_exp src d_loc loc;
            DoChildren
        | _ -> DoChildren

end

let checkSharingTypes (f : file) : bool =
    let checks = ref true in
    let fdcheck fd loc =
        Cfg.clearCFGinfo fd;
        ignore(Cfg.cfgFun fd);
        Liveness.registerIgnoreInst Rcutils.isRcInstr;
        Liveness.computeLiveness fd;
        ignore(visitCilFunction (new scastDeadnessCheckerClass) fd)
    in
    iterGlobals f (onlyFunctions fdcheck);
    let fdcheck fd loc =
        let vis = new typeCheckerClass fd checks in
        ignore(visitCilFunction vis fd)
    in
    iterGlobals f (onlyFunctions fdcheck);
    let ctx = Sattrconv.genContext f in
    let fdcheck fd loc =
        ignore(visitCilFunction (new summaryInstrumenterClass fd ctx) fd)
    in
    iterGlobals f (onlyFunctions fdcheck);
    !checks
