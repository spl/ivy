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
module SAC = Sattrconv

let mkChkMsg (e : exp) (loc : location) : exp =
    let lvstr = sprint ~width:80 (sp_exp () e) in
    let locstr = loc.file^":"^(string_of_int loc.line) in
    mkString(lvstr^" @ "^locstr)

let barrier_call loc be =
    Call(None, v2e sfuncs.dynbar, [be], loc)
let dynbar_read_call loc be re =
    let msg = mkChkMsg re loc in
    Call(None, v2e sfuncs.dynbar_read, [be;re;msg], loc)
let dynbar_write_call loc be we =
    let msg = mkChkMsg we loc in
    Call(None, v2e sfuncs.dynbar_write, [be;we;msg], loc)
let coerce_dynbar_call loc dst src =
    let dbmsg = sprint ~width:80 (d_loc () loc) in
    let msg = mkString dbmsg in
    Call(None,v2e sfuncs.coerce_dynbar,[dst;src;msg],loc)

(* Remove whatever fields were there, and add some new ones if it's a struct. *)
let addCiToCtx (ctx : SAC.context) (ci : compinfo) : unit =
    Hashtbl.clear ctx.SAC.cFields;
    if ci.cstruct then
        List.iter (fun fi ->
            Hashtbl.add ctx.SAC.cFields fi.fname fi)
            ci.cfields

let getDynBarType (t : typ) : attrparam option =
    match filterAttributes "sdynbar" (typeAttrs t) with
    | [Attr(_,[ap])] -> Some ap
    | [] -> None
    | _ -> E.s (E.error "Malformed sdynbar type: %a" sp_type t)

let rec findDynBarComp (lv : lval) : lval option =
    let rec findInExp (e : exp) : lval option =
        match e with
        | Lval lv -> findDynBarComp lv
        | StartOf lv -> findDynBarComp lv
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
        | _ -> findDynBarComp lv'
    end
    | _ -> None

(* Given an lval, return a pointer to the barrier that protects it if there is one*)
let findBarLval (ctx : SAC.context) (fd : fundec) (lv : lval) : exp option =
    match getDynBarType (typeOfLval lv) with
    | None -> None
    | Some lap -> begin
        match findDynBarComp lv with
        | None -> begin
            (* The attrparam is the pointer to the lock *)
            Hashtbl.clear ctx.SAC.cFields;
            try Some(SAC.attrParamToExp ~formals:fd.sformals ~locals:fd.slocals ctx lap)
            with SAC.NotAnExp ap ->
                E.s(E.error "Malformed sdynbar parameter: %a for lval: %a"
                    sp_attrparam lap sp_lval lv)
        end
        | Some lv' -> begin
            (* lv' is of TComp type, so add the fields to the context *)
            if !debug then
                E.log "findBarLval: typeOfLval(%a) for %a\n"
                    sp_lval lv' sp_lval lv;
            match unrollType(typeOfLval lv') with
            | TComp(ci,_) -> begin
                addCiToCtx ctx ci;
                try
                    let le = SAC.attrParamToExp ~formals:fd.sformals
                                                ~locals:fd.slocals
                                                ~baselv:(Some lv')
                                                ctx lap
                    in
                    Some le
                with SAC.NotAnExp ap ->
                    E.s(E.error "Malformed sdynbar parameter: %a for lval: %a"
                        sp_attrparam lap sp_lval lv)
            end
            | _ -> E.s(E.error "Field offset on non TComp: %a" sp_lval lv)
        end
    end

(* Given a type, return a pointer to the barrier that protects it if there is one *)
let findDynBarType (ctx : SAC.context) (fd : fundec) (t : typ) : exp option =
    match getDynBarType t with
    | None -> None
    | Some lap -> begin
        (* The attrparam is the pointer to the lock *)
        Hashtbl.clear ctx.SAC.cFields;
        try Some(SAC.attrParamToExp ~formals:fd.sformals ~locals:fd.slocals ctx lap)
        with SAC.NotAnExp ap ->
            E.s(E.error "Malformed sdynbar parameter in type: %a" sp_type t)
    end

(* Given a type at a call site, return a pointer to the barrier
   that protects it if there is one *)
let findDynBarTypeAtCall (ctx : SAC.context) 
                         (args : (exp*string) list) 
                         (t : typ)
                         : exp option
    =
    match getDynBarType t with
    | None -> None
    | Some lap -> begin
        (* The attrparam is the pointer to the lock *)
        Hashtbl.clear ctx.SAC.cFields;
        try Some(SAC.attrParamToExp ~actuals:args ctx lap)
        with SAC.NotAnExp ap ->
            E.s(E.error "Malformed sdynbar parameter in type: %a" sp_type t)
    end

(* This is for looking inside of lvals for things that are slocked *)
class dynBarLvalFinder (ctx : SAC.context)
                        (fd : fundec)
                        (leor : exp option ref)
    = object(self)
    inherit nopCilVisitor

    method vlval (lv : lval) =
        match findBarLval ctx fd lv with
        | None -> DoChildren
        | Some le -> begin
            leor := (Some le);
            SkipChildren
        end

end

let isDynBarLval (ctx : SAC.context) (fd : fundec) (lv : lval) : exp option =
    let leor = ref None in
    let vis = new dynBarLvalFinder ctx fd leor in
    ignore(visitCilLval vis lv);
    !leor

let isDynBarExp (ctx : SAC.context) (fd : fundec) (e : exp) : exp option =
    let leor = ref None in
    let vis = new dynBarLvalFinder ctx fd leor in
    ignore(visitCilExpr vis e);
    !leor

(* Make sure that the type of the lock pointer is SPRIVATE or SREADONLY *)
let checkBarType (be : exp) (l : doc) (o : doc) loc : unit =
    let t = sharCTypeOf be in
    if not(isReadonlyType t) && not(isPrivateType t) then
        E.error "The barrier %t is not SREADONLY for SLOCKED object %t at %a"
            (fun () -> l) (fun () -> o) d_loc loc;

class dynBarInstrClass (ctx : SAC.context) (fd : fundec) = object(self)
    inherit nopCilVisitor

    (* lvals gotten at through expressions are for /reads/ *)
    method vexpr (e:exp) = match e with
        | AlignOfE _ | SizeOfE _ | AddrOf _ -> SkipChildren
        | (Lval lv | StartOf lv) -> begin
            match isDynBarLval ctx fd lv with
            | None -> SkipChildren
            | Some be -> begin
                checkBarType be (d_exp () be) (d_exp () e) (!currentLoc);
                self#queueInstr[dynbar_read_call (!currentLoc) be (AddrOf lv)];
                SkipChildren
            end
        end
        | _ -> DoChildren

    (* lvals not gotten at through expressions are due to /writes/ *)
    method vlval (lv : lval) =
        match isDynBarLval ctx fd lv with
        | None -> SkipChildren
        | Some be -> begin
            checkBarType be (d_exp () be) (d_lval () lv) (!currentLoc);
            self#queueInstr[dynbar_write_call (!currentLoc) be (AddrOf lv)];
            SkipChildren
        end

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Call(_,Lval(Var fvi,NoOffset),[barrier],loc)
          when fvi.vname = "pthread_barrier_wait" -> begin
            ChangeTo[barrier_call loc barrier;i]
        end
        | _ -> DoChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then SkipChildren
        else DoChildren

end

let instrumentBarriers (f : file) : unit =
    let ctx = SAC.genContext f in
    let visfunc fd loc =
        ignore(visitCilFunction (new dynBarInstrClass ctx fd) fd)
    in
    iterGlobals f (onlyFunctions visfunc)

class dynBarTypeChecker (checks : bool ref)
                        (ctx : SAC.context)
                        (fd : fundec) = object(self)
    inherit nopCilVisitor

    method private coerceDynBarType loc plvo dstlcko srclcko : unit =
        match dstlcko, srclcko with
        | Some dstlck, Some srclck ->
            self#queueInstr[coerce_dynbar_call loc dstlck srclck]
        | _ -> ()

    method private lvalDynBar = isDynBarLval ctx fd
    method private expDynBar = isDynBarExp ctx fd

    method vinst (i : instr) =
        let handleCall loc rlvo args ft : unit =
            match unrollType ft with
            | TFun(_,_,true,_) -> begin
                (*E.warn "sdynbar: varargs function %s not checked at %a"
                    fvi.vname d_loc loc*)
                ()
            end
            | TFun(rt,Some argts,false,_) -> begin
                if List.length args <> List.length argts then begin
                    E.warn "number of formals and actuals different at %a"
                        d_loc loc
                end else
                let argsWithNames = List.combine args (List.map fst3 argts) in
                begin match rlvo with
                | None -> ()
                | Some rlv -> begin
                    let rtlock = findDynBarTypeAtCall ctx argsWithNames rt in
                    self#coerceDynBarType loc (Some rlv) (self#lvalDynBar rlv) rtlock
                end end;
                List.iter2 (fun a (_,at,_) ->
                    let arglcko = findDynBarTypeAtCall ctx argsWithNames at in
                    self#coerceDynBarType loc None arglcko (self#expDynBar a))
                    args argts
            end
            | TFun(rt,None,_,_) -> begin
                match rlvo with
                | None -> ()
                | Some rlv -> begin
                    let rtlock = findDynBarTypeAtCall ctx [] rt in
                    self#coerceDynBarType loc (Some rlv) (self#lvalDynBar rlv) rtlock
                end
            end
            | _ -> E.s(E.bug "dynBarTypeChecker: handleCall on non-function type\n")
        in
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Set(lv, e, loc) -> begin
            self#coerceDynBarType loc (Some lv) (self#lvalDynBar lv) (self#expDynBar e);
            SkipChildren
        end
        | Call(rlvo,fe,args,loc) -> begin
            handleCall loc rlvo args (sharCTypeOf fe);
            SkipChildren
        end
        | Asm(_,_,outs,ins,_,_) -> begin
            (*List.iter (fun (_,_,lv) -> ()) outs;
            List.iter (fun (_,_,e) -> ()) ins;*)
            SkipChildren
        end

    method vstmt (s : stmt) =
        match s.skind with
        | Return(Some e,loc) -> begin
            match unrollType fd.svar.vtype with
            | TFun(rt,_,_,_) -> begin
                let rtlcko = findDynBarType ctx fd rt in
                self#coerceDynBarType loc None rtlcko (self#expDynBar e);
                SkipChildren
            end
            | _ -> ();
            SkipChildren
        end
        | _ -> DoChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then SkipChildren
        else DoChildren

end


let checkDynBarTypes (f : file) : unit =
    let checks = ref true in
    let ctx = SAC.genContext f in
    let fdchk fd loc =
        let vis = new dynBarTypeChecker checks ctx fd in
        ignore(visitCilFunction vis fd)
    in
    iterGlobals f (onlyFunctions fdchk)
