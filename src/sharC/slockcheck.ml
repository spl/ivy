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

let debug = ref false

let add_lock_call loc le =
    Call(None,v2e sfuncs.add_lock,[le],loc)
let rm_lock_call loc le =
    Call(None,v2e sfuncs.rm_lock,[le],loc)
let chk_lock_call loc le what =
    let lmsg = sprint ~width:80 (d_loc () loc) in
    let msg = mkString lmsg in
    Call(None,v2e sfuncs.chk_lock,[le;what;(SizeOfE what);msg],loc)
let coerce_lock_call loc dst src =
    let lmsg = sprint ~width:80 (d_loc () loc) in
    let msg = mkString lmsg in
    Call(None,v2e sfuncs.coerce_lock,[dst;src;msg],loc)

(* Remove whatever fields were there, and add some new ones if it's a struct. *)
let addCiToCtx (ctx : SAC.context) (ci : compinfo) : unit =
    Hashtbl.clear ctx.SAC.cFields;
    if ci.cstruct then
        List.iter (fun fi ->
            Hashtbl.add ctx.SAC.cFields fi.fname fi)
            ci.cfields

let getLockType (t : typ) : attrparam option =
    match filterAttributes "slocked" (typeAttrs t) with
    | [Attr(_,[ap])] -> Some ap
    | [] -> None
    | _ -> E.s (E.error "Malformed slocked type: %a" sp_type t)

let rec findLockedComp (lv : lval) : lval option =
    let rec findInExp (e : exp) : lval option =
        match e with
        | Lval lv -> findLockedComp lv
        | StartOf lv -> findLockedComp lv
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
        | _ -> findLockedComp lv'
    end
    | _ -> None

(* Given an lval, return a pointer to the lock that protects it if there is one*)
let findLockLval (ctx : SAC.context) (fd : fundec) (lv : lval) : exp option =
    match getLockType (typeOfLval lv) with
    | None -> None
    | Some lap -> begin
        match findLockedComp lv with
        | None -> begin
            (* The attrparam is the pointer to the lock *)
            Hashtbl.clear ctx.SAC.cFields;
            try Some(SAC.attrParamToExp ~formals:fd.sformals ~locals:fd.slocals ctx lap)
            with SAC.NotAnExp ap ->
                E.s(E.error "Malformed slocked parameter: %a for lval: %a"
                    sp_attrparam lap sp_lval lv)
        end
        | Some lv' -> begin
            (* lv' is of TComp type, so add the fields to the context *)
            if !debug then
                E.log "findLockLval: typeOfLval(%a) for %a\n"
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
                    E.s(E.error "Malformed slocked parameter: %a for lval: %a"
                        sp_attrparam lap sp_lval lv)
            end
            | _ -> E.s(E.error "Field offset on non TComp: %a" sp_lval lv)
        end
    end

(* Given a type, return a pointer to the lock that protects it if there is one *)
let findLockType (ctx : SAC.context) (fd : fundec) (t : typ) : exp option =
    match getLockType t with
    | None -> None
    | Some lap -> begin
        (* The attrparam is the pointer to the lock *)
        Hashtbl.clear ctx.SAC.cFields;
        try Some(SAC.attrParamToExp ~formals:fd.sformals ~locals:fd.slocals ctx lap)
        with SAC.NotAnExp ap ->
            E.s(E.error "Malformed slocked parameter in type: %a" sp_type t)
    end

(* Given a type at a call site, return a pointer to the lock
   that protects it if there is one *)
let findLockTypeAtCall (ctx : SAC.context) (args : (exp*string) list) (t : typ) : exp option =
    match getLockType t with
    | None -> None
    | Some lap -> begin
        (* The attrparam is the pointer to the lock *)
        Hashtbl.clear ctx.SAC.cFields;
        try Some(SAC.attrParamToExp ~actuals:args ctx lap)
        with SAC.NotAnExp ap ->
            E.s(E.error "Malformed slocked parameter in type: %a" sp_type t)
    end

(* This is for looking inside of lvals for things that are slocked *)
class slockedLvalFinder (ctx : SAC.context)
                        (fd : fundec)
                        (leor : exp option ref)
    = object(self)
    inherit nopCilVisitor

    method vlval (lv : lval) =
        match findLockLval ctx fd lv with
        | None -> DoChildren
        | Some le -> begin
            leor := (Some le);
            SkipChildren
        end

end

let isSlockedLval (ctx : SAC.context) (fd : fundec) (lv : lval) : exp option =
    let leor = ref None in
    let vis = new slockedLvalFinder ctx fd leor in
    ignore(visitCilLval vis lv);
    !leor

let isSlockedExp (ctx : SAC.context) (fd : fundec) (e : exp) : exp option =
    let leor = ref None in
    let vis = new slockedLvalFinder ctx fd leor in
    ignore(visitCilExpr vis e);
    !leor

(* Make sure that the type of the lock pointer is SPRIVATE or SREADONLY *)
let checkLockType (le : exp) (l : doc) (o : doc) loc : unit =
    let t = sharCTypeOf le in
    if not(isReadonlyType t) && not(isPrivateType t) then
        E.error "The lock %t is not SREADONLY for SLOCKED object %t at %a"
            (fun () -> l) (fun () -> o) d_loc loc;


class lockInstrClass (ctx : SAC.context) (fd : fundec) = object(self)
    inherit nopCilVisitor

    (* TODO *)
    (* optimize chk_lock away through some flow-sensitive analysis *)

    (* lvals gotten at through expressions are for /reads/ *)
    method vexpr (e:exp) = match e with
        | AlignOfE _ | SizeOfE _ | AddrOf _ -> SkipChildren
        | (Lval lv | StartOf lv) -> begin
            match isSlockedLval ctx fd lv with
            | None -> SkipChildren
            | Some le -> begin
                checkLockType le (d_exp () le) (d_exp () e) (!currentLoc);
                self#queueInstr[chk_lock_call (!currentLoc) le (AddrOf lv)];
                SkipChildren
            end
        end
        | _ -> DoChildren

    (* lvals not gotten at through expressions are due to /writes/ *)
    method vlval (lv : lval) =
        match isSlockedLval ctx fd lv with
        | None -> SkipChildren
        | Some le -> begin
            checkLockType le (d_exp () le) (d_lval () lv) (!currentLoc);
            self#queueInstr[chk_lock_call (!currentLoc) le (AddrOf lv)];
            SkipChildren
        end

    (* TODO: If there are no chk_lock_calls between the add_lock_call and the
       rm_lock_call, then they can be removed *)
    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Call(_,Lval(Var fvi,NoOffset),[mutex],loc)
          when fvi.vname = "pthread_mutex_lock" -> begin
            ChangeTo[i;add_lock_call loc mutex]
        end
        | Call(_,Lval(Var fvi,NoOffset),[mutex],loc)
          when fvi.vname = "pthread_mutex_unlock" -> begin
            ChangeTo[rm_lock_call loc mutex;i]
        end
        | _ -> DoChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then SkipChildren
        else DoChildren


end

let instrumentLocks (f : file) : unit =
    let ctx = SAC.genContext f in
    let visfunc fd loc =
        ignore(visitCilFunction (new lockInstrClass ctx fd) fd)
    in
    iterGlobals f (onlyFunctions visfunc)

(* Add coercions where needed *)
class slockedTypeChecker (checks : bool ref)
                         (ctx : SAC.context)
                         (fd : fundec) = object(self)
    inherit nopCilVisitor

    method private coerceLockType loc plvo dstlcko srclcko : unit =
        match dstlcko, srclcko with
        | Some dstlck, Some srclck ->
            self#queueInstr[coerce_lock_call loc dstlck srclck]
        | _ -> ()

    method private lvalSlock = isSlockedLval ctx fd
    method private expSlock = isSlockedExp ctx fd

    method vinst (i : instr) =
        let handleCall loc rlvo args ft : unit =
            match unrollType ft with
            | TFun(_,_,true,_) -> begin
                (*E.warn "slockcheck: varargs function %s not checked at %a"
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
                    let rtlock = findLockTypeAtCall ctx argsWithNames rt in
                    self#coerceLockType loc (Some rlv) (self#lvalSlock rlv) rtlock
                end end;
                List.iter2 (fun a (_,at,_) ->
                    let arglcko = findLockTypeAtCall ctx argsWithNames at in
                    self#coerceLockType loc None arglcko (self#expSlock a))
                    args argts
            end
            | TFun(rt,None,_,_) -> begin
                match rlvo with
                | None -> ()
                | Some rlv -> begin
                    let rtlock = findLockTypeAtCall ctx [] rt in
                    self#coerceLockType loc (Some rlv) (self#lvalSlock rlv) rtlock
                end
            end
            | _ -> E.s(E.bug "slockedTypeChecker: handleCall on non-function type\n")
        in
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Set(lv, e, loc) -> begin
            self#coerceLockType loc (Some lv) (self#lvalSlock lv) (self#expSlock e);
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
                let rtlcko = findLockType ctx fd rt in
                self#coerceLockType loc None rtlcko (self#expSlock e);
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

let checkSlockedTypes (f : file) : unit =
    let checks = ref true in
    let ctx = SAC.genContext f in
    let fdchk fd loc =
        let vis = new slockedTypeChecker checks ctx fd in
        ignore(visitCilFunction vis fd)
    in
    iterGlobals f (onlyFunctions fdchk)
