(* This sharing analysis is a plugin for the ivyglobserver. *)

open Cil
open Pretty
open Ivyoptions
open Ivyutil
open Sutil

module E = Errormsg
module UF = Unionfind

let name = "sharing"

let log_change = ref false

(**
 *
 * A simple-minded flow-insensitive sharing(i.e. thread escape) analysis:
 * 1.) Type-based alias analysis for function pointers.
 * 2.) Find functions that can be run in threads.
 * 3.) Anything reachable from a global touched by a thread is dynamic.
 * 4.) Anything reachable from the argument to pthread_create(and friends) is
 *     dynamic.
 * 5.) Warn about functions with no definition taking dynamic arguments
 * 6.) Mark scastedstruct the structure types whose sharing mode changes.
 *)

(** 1.) Type-based alias analysis for function pointeres *)

module TypHash =
    Hashtbl.Make(struct
        type t = typsig
        let equal = Util.equals
        let hash = Hashtbl.hash
    end)

(* Mapping from types to vi's of function pointers *)
let fnPtrsHash : varinfo list TypHash.t = TypHash.create 50

let typsig (t : typ) : typsig =
    typeSigWithAttrs ~ignoreSign:true (fun _ -> []) t

let addFnPtrAlias (fvi : varinfo) : unit =
    try let fpl = TypHash.find fnPtrsHash (typsig fvi.vtype) in
    TypHash.replace fnPtrsHash (typsig fvi.vtype) (fvi :: fpl)
    with Not_found -> TypHash.add fnPtrsHash (typsig fvi.vtype) [fvi]

let getFnPtrAliases ?(nomapIsError : bool = false) (t : typ) : varinfo list =
    try TypHash.find fnPtrsHash (typsig t)
    with Not_found ->
        if nomapIsError then
            E.s(E.error "getFnPtrAliases: No function pointers of type %a"
                d_typsig (typsig t))
        else []

class fnPtrFinderClass = object(self)
    inherit nopCilVisitor

    method vexpr (e : exp) =
        match e with
        | AddrOf(Var fvi, NoOffset) -> begin
            (*if isBuiltin fvi then DoChildren else*)
            (*if Dattrs.isAllocator (typeOf e) ||
               Dattrs.isDeallocator (typeOf e) then DoChildren else*)
            match unrollType fvi.vtype with
            | TFun _ -> begin
                if not(isFnPtrType fvi.vtype) then begin
                    fvi.vtype <- addFnPtrType fvi.vtype;
                    addFnPtrAlias fvi;
                    if !log_change then
                        E.log "\nCHANGE: %s is sfnptr: %a\n"
                            fvi.vname d_typsig (typsig fvi.vtype);
                end;
                DoChildren
            end
            | _ -> DoChildren
        end
        | _ -> DoChildren

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        DoChildren

end

let fnPtrAnalysis (g : global) : unit =
    ignore(visitCilGlobal (new fnPtrFinderClass) g)

(** 2.) Find functions that can run in threads.
 *
 * Find things in the call graph rooted at functions that can flow to the
 * argument of the thread creation function.
 *
 * Mark these functions, and function pointer types in parameters and struct
 * fields as "pinthread" *)

let inThrCompTyps = Expcompare.compareTypes ~importantAttr:isInThreadAttr

(* iterate through globals and annotate functions as
 * pinthread if they are called by a pinthread function.
 *)
class inThreadPusherClass ?(warnOnChange : bool = false)
                          (changed : bool ref)
                          (fd : fundec)
    = object(self)
    inherit nopCilVisitor

    method private handleArgs args argtyps : unit =
        if List.length args <> List.length argtyps then () else
        List.iter2 (fun a (_,at,_) ->
            if isInThreadType at then begin
                match a with
                | AddrOf(Var fvi,NoOffset) | Lval(Var fvi,NoOffset) -> begin
                    if fvi.vglob && not(isInThreadType fvi.vtype) then begin
                        if !log_change || warnOnChange then
                            E.warn "%s must be annotated SINTHREAD" fvi.vname;
                        fvi.vtype <- addInThreadType fvi.vtype;
                        changed := true
                    end else begin
                        fvi.vtype <- addInThreadType fvi.vtype;
                    end
                end
                | _ -> begin
                    if warnOnChange && not(isInThreadType(typeOf a)) then
                        E.warn "The type of %a must be annotated SINTHREAD"
                            sp_exp a;
                    let fns = getFnPtrAliases (typeOf a) in
                    List.iter (fun fvi ->
                        if not(isInThreadType fvi.vtype) then begin
                            if !log_change then
                                E.log "\nCHANGE: %s is inthread\n" fvi.vname;
                            fvi.vtype <- addInThreadType fvi.vtype;
                            changed := true
                        end)
                        fns
                end
            end) args argtyps

    method private handleReturn lvo rt : unit =
        match lvo with None -> () | Some rlv ->
        if not(isInThreadType rt) then () else
        match rlv with
        | (Var fvi, NoOffset) -> begin
            if fvi.vglob && not(isInThreadType fvi.vtype) then begin
                if !log_change || warnOnChange then 
                    E.warn "%s must be annotated SINTHREAD" fvi.vname;
                fvi.vtype <- addInThreadType fvi.vtype;
                changed := true
            end else begin
                fvi.vtype <- addInThreadType fvi.vtype;
            end
        end
        | _ -> begin
            if warnOnChange && not(isInThreadType(typeOfLval rlv)) then
                E.warn "The type of %a must be annotated SINTHREAD"
                    sp_lval rlv;
            let fns = getFnPtrAliases (typeOfLval rlv) in
            List.iter (fun fvi ->
                if not(isInThreadType fvi.vtype) then begin
                    if !log_change then
                        E.log "\nCHANGE: %s is inthread\n" fvi.vname;
                    fvi.vtype <- addInThreadType fvi.vtype;
                    changed := true
                end) fns
        end

    method vinst (i :instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        match i with
        | Call(_,Lval(Var fvi,NoOffset),[_;_;AddrOf(Var thrfunc,NoOffset);_],loc)
          when fvi.vname = "pthread_create" -> begin
            if isInThreadType thrfunc.vtype then SkipChildren else begin
                if !log_change || warnOnChange then 
                    E.warn "%s must be annotated SINTHREAD" thrfunc.vname;
                thrfunc.vtype <- addInThreadType thrfunc.vtype;
                changed := true;
                SkipChildren
            end
        end
        | Call(_,Lval(Var fvi,NoOffset),[_;_;thrfunc;_],loc)
          when fvi.vname = "pthread_create" -> begin
            let thrfunctyp = typeOf (Lval(Mem thrfunc, NoOffset)) in
            if warnOnChange && not(isInThreadType thrfunctyp) then
                E.warn "The type of %a must be annotated SINTHREAD"
                    sp_exp thrfunc;
            let fns = getFnPtrAliases (typeOf (Lval(Mem thrfunc,NoOffset))) in
            List.iter (fun fvi ->
                if not(isInThreadType fvi.vtype) then begin
                    if !log_change then
                        E.log "\nCHANGE: %s is inthread\n" fvi.vname;
                    fvi.vtype <- addInThreadType fvi.vtype;
                    changed := true
                end)
                fns;
            SkipChildren
        end
        | Call(lvo,Lval(Var fvi,NoOffset),args,_)
          when not(Dattrs.isAllocator fvi.vtype) &&
               not(Dattrs.isDeallocator fvi.vtype) -> begin
            let _ =
                match fvi.vtype with
                | TFun(rt,Some argtyps,_,_) ->
                    self#handleArgs args argtyps;
                    self#handleReturn lvo rt
                | _ -> ()
            in
            if not(isInThreadType fd.svar.vtype) then SkipChildren else
            if isInThreadType fvi.vtype then SkipChildren else begin
                if !log_change || warnOnChange then
                    E.warn "%s must be annotated SINTHREAD" fvi.vname;
                fvi.vtype <- addInThreadType fvi.vtype;
                changed := true;
                SkipChildren
            end
        end
        | Call(lvo,fe,args,_)
          when not(Dattrs.isAllocator (typeOf fe)) &&
               not(Dattrs.isDeallocator (typeOf fe)) -> begin
            let _ =
                match unrollType(typeOf fe) with
                | TFun(rt,Some argtyps,_,_) ->
                    self#handleArgs args argtyps;
                    self#handleReturn lvo rt
                | _ -> ()
            in
            if not(isInThreadType fd.svar.vtype) then SkipChildren else begin
                if warnOnChange && not(isInThreadType(typeOf fe)) then
                    E.warn "The type of %a must be annotated SINTHREAD"
                        sp_exp fe;
                let fns = getFnPtrAliases (typeOf fe) in
                List.iter (fun fvi ->
                    if not(isInThreadType fvi.vtype) then begin
                        if !log_change then
                            E.log "\nCHANGE: %s is inthread\n" fvi.vname;
                        fvi.vtype <- addInThreadType fvi.vtype;
                        changed := true
                    end)
                    fns;
                SkipChildren
            end
        end
        | Set(lv,e,_) when warnOnChange -> begin
            (* when doing the local analysis warn when lhs and rhs don't have same
               inthreadedness *)
            if inThrCompTyps (typeOfLval lv) (typeOf e) then DoChildren
            else begin
                E.warn ("SINTHREAD type mismatch in assignment:\n"^^
                        "\tlhs = %a\n\trhs = %a")
                    sp_type (typeOfLval lv) sp_type (typeOf e);
                DoChildren
            end
        end
        | _ -> SkipChildren


    method vstmt (s : stmt) =
        match s.skind with
        | Return(Some e,_) -> begin
            (* if an inthread function pointer is returned, mark the return
               type as inthread *)
            if isInThreadType (typeOf e) then begin
                match unrollType fd.svar.vtype with
                | TFun(rt,argtyps,va,a) ->
                    if not(isInThreadType rt) then begin
                        let newt = TFun(addInThreadType rt,argtyps,va,a) in
                        if !log_change || warnOnChange then
                            E.warn "return of %s must be annotated SINTHREAD"
                                fd.svar.vname;
                        fd.svar.vtype <- newt;
                        changed := true;
                    end
                | _ -> ()
            end;
            DoChildren
        end
        | _ -> DoChildren

end

let inThreadAnalysis ?(warnOnChange : bool = false) (gl : global list) : unit =
    let change = ref false in
    let vis fd = new inThreadPusherClass ~warnOnChange:warnOnChange change fd in
    let rec helper () =
        change := false;
        List.iter (fun g ->
            match g with
            | GFun(fd, _) ->
                ignore(visitCilFunction (vis fd) fd)
            | _ -> ())
            gl;
        if !change then helper ()
    in
    helper ()

(** 3.) and 4.) *)

type sharingType =
    | Dynamic of varinfo
    | Global of varinfo
    | DependsOn of varinfo
    | NotDynamic

let rec isExpDynamic (e : exp) : sharingType =
    if isNonDynamicType (typeOf e) then NotDynamic else
    match e with
    | Lval lv -> isLvalDynamic lv
    | BinOp(_,e1,e2,t) -> isExpDynamic e1
    | CastE(t,e) -> isExpDynamic e
    | AddrOf lv
    | StartOf lv -> isLvalDynamic lv
    | _ -> NotDynamic

and isLvalDynamic (lv : lval) : sharingType =
    if isNonDynamicType (typeOfLval lv) then NotDynamic else
    match lv with
    | (Var vi, _) ->
        if isDynamicType vi.vtype || isInDynamicType vi.vtype || isOutDynamicType vi.vtype
        then Dynamic vi
        else DependsOn vi
    | (Mem e, _) -> isExpDynamic e

module VS = Set.Make(struct
    type t = varinfo
    let compare vi1 vi2 = Pervasives.compare vi1.vid vi2.vid
end)

(* Union find *)
module VarUf = UF.Make(VS)

let getMergedFnType (ft : typ) : typ * bool =
    let sharingUB (n1,t1,a1) (n2,t2,a2) =
        (* return a type with the ub of sharing attrs on t1 and t2.
           if t2 is above t1 then return true *)
        match getSharingAttr t1, getSharingAttr t2 with
        | SDynamic, _
        | _, SNone -> (n1,t1,a1), false
        | s1, s2 when s1 = s2 -> (n1,t1,a1), false
        | _, SDynamic -> (n1,addDynamicType t1,a1), true
        | SNone, SInDynamic -> (n1,addInDynamicType t1,a1), true
        | SNone, SOutDynamic -> (n1,addOutDynamicType t1,a1), true
        | _, _ -> (n1,addDynamicType t1,a1), true
    in
    let fnTypMerger (typ, change) vi =
        match unrollType typ, unrollType vi.vtype with
        | TFun(rt1,Some argts1,b,a), TFun(rt2,Some argts2,_,_)
            when List.length argts1 = List.length argts2 -> begin
            let (_,rt,_), b = sharingUB ("",rt1,[]) ("",rt2,[]) in
            let argts = List.map2 sharingUB argts1 argts2 in
            if b || List.exists snd argts then
                (TFun(rt,Some(List.map fst argts),b,a), true)
            else typ, change
        end
        | _ -> typ, change
    in
    try
        getFnPtrAliases ft
        |> List.fold_left fnTypMerger (ft, false)
    with Not_found -> ft, false

(* If the type of vi is mapped in fnPtrsHash, make the functions it maps to
   have equivalent sharing annotations *)
let mergeFnTypes  (fvi : varinfo) : unit =
    try
        let (nt,change) =
            if isFnPtrType (unrollType fvi.vtype) then
                getMergedFnType fvi.vtype
            else fvi.vtype, false
        in
        if change then begin
            let fns = getFnPtrAliases fvi.vtype in
            List.iter (fun vi -> vi.vtype <- nt) fns
        end
    with Not_found ->
        E.s(E.error "mergeFnTypes(%s): Not_found should be impossible here"
            fvi.vname)

let returnsDynamic (fd : fundec) : bool =
    match unrollType fd.svar.vtype with
    | TFun(rt,_,_,_) -> isDynamicType rt && isPtrType rt
    | _ -> false

let isFunType (t : typ) : bool =
    match unrollType t with
    | TFun _ -> true
    | _ -> false

let shareThrFuncArg (fvi : varinfo) : unit =
    let ntyp =
        match unrollType fvi.vtype with
        | TFun(rt, Some [(n,t,al)], b, a) ->
            TFun(rt,Some [(n,addDynamicType t,al)], b, a)
        | _ -> fvi.vtype
    in
    fvi.vtype <- ntyp

let isArg (fd : fundec) (vi : varinfo) : bool =
    List.exists (fun vi' -> vi'.vid = vi.vid) fd.sformals

(* After running this visitor over a function the VarUf.t
   pointed to by vufr will contain equivalence classes of
   varinfos that are either dynamic or not dynamic *)
class shareFinderClass ?(warnOnChange : bool = false)
                       (vufr : VarUf.t ref)
                       (retvis : varinfo list ref)
                       (fd : fundec)
                       (change : bool ref)
    = object(self)
    inherit nopCilVisitor

    method vvrbl (vi : varinfo) =
        if isInThreadType fd.svar.vtype &&
            vi.vglob &&
            not(isDynamicType vi.vtype) &&
            not(isNonDynamicType vi.vtype) &&
            (isFunType vi.vtype && isFnPtrType vi.vtype ||
             not(isFunType vi.vtype))
        then begin
            vi.vtype <- addDynamicType vi.vtype;
            if !log_change || warnOnChange then
                E.warn "global %s must be annotated SDYNAMIC. Touched by thread."
                    vi.vname;
            change := true
        end;
        DoChildren

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else

        (* If the type of a formal is dynamic or outdynamic, then
           flow the qualifier to the actual. *) 
        let propDynamicToActuals (args : exp list)
                                (atypso : (string * typ * attributes) list option)
                                : unit
            =
            match atypso with None -> () | Some atyps ->
            let rec handleArgs (args : exp list) atyps : unit =
                match args, atyps with
                | a :: arst, (s,t,at) :: atrst -> begin
                    match isExpDynamic a with
                    | DependsOn vi -> begin
                        (*E.log "Does %s need to be SDYNAMIC? t:%a a:%a vi.vtype:%a\n"
                            vi.vname sp_type t sp_exp a sp_type vi.vtype;*)
                        if (isDynamicType t || isOutDynamicType t) &&
                           isPtrType(typeOf a) &&
                           not(isNonDynamicType vi.vtype) &&
                           not(isReferentNonDynamic (typeOf a))
                        then begin
                            vi.vtype <- addDynamicType vi.vtype;
                            if vi.vglob || isArg fd vi then begin
                                change := true;
                                if !log_change || warnOnChange then
                                    E.warn "%s in %s must be annotated SDYNAMIC."
                                        vi.vname fd.svar.vname
                            end
                        end;
                        handleArgs arst atrst
                    end
                    | _ -> handleArgs arst atrst
                end
                | _, _ -> ()
            in
            handleArgs args atyps
        in

        match i with
        | Set(lv,e,_) when isPtrType (typeOfLval lv) -> begin
            match isLvalDynamic lv, isExpDynamic e with
            | (Dynamic lvvi | DependsOn lvvi | Global lvvi), 
              (Dynamic evi | DependsOn evi | Global evi) -> begin
                (*E.log "%s <- %s\n" lvvi.vname evi.vname;*)
                vufr := VarUf.make_equal (!vufr) lvvi evi Ptrnode.mkRIdent;
                DoChildren
            end
            | _, _ -> DoChildren
        end
        | Call(_,Lval(Var fvi,NoOffset),[_;_;AddrOf(Var thrfunc,NoOffset);arg],loc)
          when fvi.vname = "pthread_create" -> begin
            shareThrFuncArg thrfunc;
            match isExpDynamic arg with
            | DependsOn vi -> begin
                if isPtrType (typeOf arg) then begin
                    vi.vtype <- addDynamicType vi.vtype;
                    if vi.vglob || isArg fd vi then begin
                        change := true;
                        if !log_change || warnOnChange then
                            E.warn "%s in %s must be annotated SDYNAMIC."
                                vi.vname fd.svar.vname
                    end
                end;
                DoChildren
            end
            | _ -> DoChildren
        end
        | Call(_,Lval(Var fvi,NoOffset),[_;_;thrfunc;arg],loc)
          when fvi.vname = "pthread_create" -> begin
            List.iter shareThrFuncArg (getFnPtrAliases (typeOf (Lval(Mem thrfunc,NoOffset))));
            match isExpDynamic arg with
            | DependsOn vi -> begin
                if isPtrType (typeOf arg) then begin
                    vi.vtype <- addDynamicType vi.vtype;
                    if vi.vglob || isArg fd vi then begin
                        change := true;
                        if !log_change || warnOnChange then
                            E.warn "%s in %s must be annotated SDYNAMIC."
                                vi.vname fd.svar.vname
                    end
                end;
                DoChildren
            end
            | _ -> DoChildren
        end
        | Call(lvo,fe,args,_)
          when not(Dattrs.isAllocator (typeOf fe)) &&
               not(Dattrs.isDeallocator (typeOf fe)) -> begin
            (* if the return type is dynamic, then the base vi of the result is
               dynamic, too. If the formals are outdynamic, then make the actuals
               dynamic, too. *)
            match unrollType (typeOf fe) with
            | TFun(rt, argtyps,_,_) -> begin
                propDynamicToActuals args argtyps;
                match lvo with
                | None -> DoChildren
                | Some lv -> begin
                    match isLvalDynamic lv with
                    | DependsOn vi -> begin
                        if isDynamicType rt &&
                           not(isNonDynamicType vi.vtype) &&
                           not(isReferentNonDynamic vi.vtype) &&
                           isPtrType(typeOfLval lv)
                        then begin
                            vi.vtype <- addDynamicType vi.vtype;
                            if vi.vglob || isArg fd vi then begin
                                change := true;
                                if !log_change || warnOnChange then
                                    E.warn "%s in %s must be annotated SDYNAMIC."
                                        vi.vname fd.svar.vname
                            end
                        end;
                        DoChildren
                    end
                    | _ -> DoChildren
                end
            end
            | _ -> DoChildren
        end
        | Asm(_,_,_,_,_,_) -> begin
            DoChildren
        end
        | _ -> DoChildren

    method vstmt (s : stmt) =
        (* Collect the variables that get returned.
           If the return type of the function is dynamic, mark them dynamic *)
        match s.skind with
        | Return(Some e,_) -> begin
            match isExpDynamic e with
            | (Dynamic vi | Global vi | DependsOn vi) -> begin
                if returnsDynamic fd &&
                   not(isDynamicType vi.vtype) &&
                   not(isInDynamicType vi.vtype) &&
                   not(isOutDynamicType vi.vtype) &&
                   not(isNonDynamicType vi.vtype) &&
                   not(isReferentNonDynamic vi.vtype) &&
                   isPtrType(typeOf e)
                then begin
                    vi.vtype <- addDynamicType vi.vtype;
                    if vi.vglob || isArg fd vi then begin
                        E.warn "%s in %s must be annotated SDYNAMIC."
                            vi.vname fd.svar.vname;
                        change := true
                    end
                end;
                retvis := vi :: (!retvis);
                DoChildren
            end
            | _ -> DoChildren
        end
        | _ -> DoChildren
end

let updateFnTypedef (t : typ) (newt : typ) : unit =
    match t with
    | TNamed(ti,a) -> begin
        E.log "updateFnTypedef: %s <- %a\n" ti.tname sp_type newt;
        ti.ttype <- newt
    end
    | _ -> ()

let fixFnPtrArgType (fpt : typ) : typ * bool =
    match unrollType fpt with
    | TPtr(TFun(_,_,_,_) as ft,pa) ->
        let nft, b = getMergedFnType ft in
        (TPtr(nft,pa), b)
    | _ -> fpt, false


(* If the actuals at a call site are dynamic, then change the type
   of the function so that the formals are indynamic *)
class callSiteUpdaterClass ?(warnOnChange : bool = false)
                           (change : bool ref)
    = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        let localchange = ref false in
        let rec handleArgs vi loc args argtyps res =
            match args, argtyps with
            | a :: arst, (s,ot,at) :: atrst -> begin
                let t, b = fixFnPtrArgType ot in
                if b then begin
                    localchange := true;
                    change := true;
                end;
                match isExpDynamic a with
                | Dynamic _ -> begin
                    if not(isDynamicType t) &&
                        not(isInDynamicType t) &&
                        not(isNonDynamicType t) &&
                        not(isReferentNonDynamic t) &&
                        isPtrType t
                    then begin
                        if not(isOutDynamicType t) then begin
                            let newt = addInDynamicType t in
                            localchange := true;
                            change := true;
                            if !log_change || warnOnChange then
                                E.warn "arg %s of %s must be annotated SINDYNAMIC."
                                    s vi.vname;
                            handleArgs vi loc arst atrst ((s,newt,at)::res)
                        end else begin
                            let newt = addDynamicType t in
                            localchange := true;
                            change := true;
                            if !log_change || warnOnChange then
                                E.warn "arg %s of %s must be annotated SDYNAMIC."
                                    s vi.vname;
                            handleArgs vi loc arst atrst ((s,newt,at)::res)
                        end
                    end else handleArgs vi loc arst atrst ((s,t,at)::res)
                end
                | _ -> handleArgs vi loc arst atrst ((s,t,at)::res)
            end
            | _, _ -> List.rev res
        in

        let handleFnVi (loc : location) (lvo : lval option) (args : exp list)
                       (ft : typ) (vi : varinfo) : unit =
            (*if isBuiltin vi then () else
            if Rcutils.isRcFunction vi.vname then () else*)
            match unrollType vi.vtype with
            | TFun(rt,argtypso,b,a) -> begin
                match argtypso with None -> () | Some argtyps -> begin
                localchange := false;
                let newargs = handleArgs vi loc args argtyps [] in
                let nrt =
                    (* If the return is written into a dynamic location, then
                       the return type of the function has to be dynamic *)
                    match lvo with
                    | None -> rt
                    | Some lv -> begin
                        match isLvalDynamic lv with
                        | Dynamic _ ->
                            if not(isDynamicType rt) &&
                               not(isNonDynamicType rt) &&
                               not(isReferentNonDynamic rt) &&
                               isPtrType rt
                            then begin
                                localchange := true;
                                change := true;
                                if !log_change || warnOnChange then
                                    E.warn "return type of %s:%a must be annotated SDYNAMIC. Call site."
                                        vi.vname sp_type vi.vtype;
                                addDynamicType rt
                            end else rt
                        | _ -> rt
                    end
                in
                let newt = TFun(nrt,Some newargs,b,a) in
                if !localchange then begin
                    updateFnTypedef ft newt;
                    vi.vtype <- newt;
                    mergeFnTypes vi
                end
                end
            end
            | _ -> ()
        in

        match i with
        | Call(lvo,Lval(Var vi,NoOffset),args,loc)
          when not(Dattrs.isAllocator vi.vtype) &&
               not(Dattrs.isDeallocator vi.vtype) -> begin
                handleFnVi loc lvo args vi.vtype vi;
                SkipChildren
        end
        | Call(lvo,fe,args,loc)
          when not(Dattrs.isAllocator (typeOf fe)) &&
               not(Dattrs.isDeallocator (typeOf fe)) -> begin
            let fns = getFnPtrAliases (typeOf fe) in
            List.iter (handleFnVi loc lvo args (typeOf fe)) fns;
            SkipChildren
        end
        | _ -> SkipChildren

end

let propDynamicThroughCallSites ?(warnOnChange : bool = false)
                               (fd : fundec)
                               (change : bool ref) : unit
    =
    let vis = new callSiteUpdaterClass ~warnOnChange:warnOnChange change in
    ignore(visitCilFunction vis fd)

class compTypeUpdaterClass ?(warnOnChange : bool = false)
                           (change : bool ref)
    = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        match i with
        | Set((lh,Field(fi,NoOffset)) as lv, e, loc) -> begin
            match unrollType (typeOfLval lv) with
            | TPtr(TFun(_,_,_,_), _) as ft ->
                let t, b = fixFnPtrArgType ft in
                if b then begin
                    fi.ftype <- t;
                    change := true
                end;
                SkipChildren
            | _ -> SkipChildren
        end
        | _ -> SkipChildren

end

let updateCompTypes ?(warnOnChange : bool = false)
                    (fd : fundec)
                    (change : bool ref) : unit
    =
    let vis = new compTypeUpdaterClass ~warnOnChange:warnOnChange change in
    ignore(visitCilFunction vis fd)
    

let testSharing (vi : varinfo) : bool =
     if (isDynamicType vi.vtype || isInDynamicType vi.vtype) then begin
        (*E.log "%s is dynamic\n" vi.vname;*)
        true
     end else begin
        (*E.log "%s is not dynamic\n" vi.vname;*)
        false
     end


class castFixerClass = object(self)
    inherit nopCilVisitor

    method private fixCast (t : typ) (e : exp) : exp =
        let e = self#fixExp e in
        match isExpDynamic e with
        | Dynamic _ ->
            if not(isNonDynamicType t) &&
               not(isReferentNonDynamic t)
            then CastE(addDynamicType t, e)
            else CastE(t,e)
        | _ -> CastE(t,e)

    method private fixOff (off : offset) : offset =
        match off with
        | Field(fi, off) -> Field(fi, self#fixOff off)
        | Index(e, off) -> Index(self#fixExp e, self#fixOff off)
        | _ -> off

    method private fixLval (lv : lval) : lval =
        match lv with
        | (Mem e, off) -> (Mem(self#fixExp e), self#fixOff off)
        | (Var vi, off) -> (Var vi, self#fixOff off)

    method private fixExp (e : exp) =
        match e with
        | Lval lv -> Lval(self#fixLval lv)
        | SizeOfE e -> SizeOfE(self#fixExp e)
        | AlignOfE e -> AlignOfE(self#fixExp e)
        | UnOp(uo,e,t) -> UnOp(uo,self#fixExp e,t)
        | BinOp(bo,e1,e2,t) -> BinOp(bo,self#fixExp e1,self#fixExp e2,t)
        | CastE(t,e) -> self#fixCast t e
        | AddrOf lv -> AddrOf(self#fixLval lv)
        | StartOf lv -> StartOf(self#fixLval lv)
        | _ -> e

    method vexpr (e : exp) = ChangeTo(self#fixExp e)

    method vinst (i : instr) =
        if Dcheckdef.isDeputyFunctionInstr i then SkipChildren else
        if Rcutils.isRcInstr i then SkipChildren else
        DoChildren
        
end


let findDynamicVis ?(warnOnChange : bool = false) (fd : fundec) (change: bool ref) : unit =
    let vufr = ref VarUf.empty in
    let vilr = ref [] in
    setFunctionType fd fd.svar.vtype;
    let vis = new shareFinderClass ~warnOnChange:warnOnChange vufr vilr fd change in
    ignore(visitCilFunction vis fd);
    let vill = VarUf.eq_classes (!vufr) in
    List.iter
        (fun vil ->
            let dynamic =
                List.exists
                testSharing
                vil
            in
            if dynamic then
                List.iter
                (fun vi ->
                    if isArg fd vi && not(isDynamicType vi.vtype) &&
                       not(isNonDynamicType vi.vtype) &&
                       not(isReferentNonDynamic vi.vtype) && isPtrType vi.vtype
                    then begin
                        if isInDynamicType vi.vtype then begin
                            vi.vtype <- addDynamicType vi.vtype;
                            change := true;
                            if !log_change || warnOnChange then
                                E.warn "arg %s of %s must be annotated SDYNAMIC."
                                    vi.vname fd.svar.vname
                        end else if not(isOutDynamicType vi.vtype) then begin
                            vi.vtype <- addOutDynamicType vi.vtype;
                            change := true;
                            if !log_change || warnOnChange then
                                E.warn "arg %s of %s must be annotated SOUTDYNAMIC."
                                    vi.vname fd.svar.vname
                        end
                    end else begin
                        (*E.log "%s is now dynamic\n" vi.vname;*)
                        if not(isNonDynamicType vi.vtype) &&
                           not(isReferentNonDynamic vi.vtype) &&
                           not(isDynamicType vi.vtype) && isPtrType vi.vtype
                        then begin
                            vi.vtype <- addDynamicType vi.vtype;
                            if vi.vglob then begin
                                change := true;
                                if !log_change || warnOnChange then
                                    E.warn "solver: global %s must be annotated SDYNAMIC."
                                        vi.vname
                            end
                        end
                    end)
                vil
            else ())
        vill;
    let dynamic =
        List.exists
        (fun vi -> isDynamicType vi.vtype || isInDynamicType vi.vtype)
        (!vilr)
    in
    if dynamic then begin match unrollType fd.svar.vtype with
    | TFun(rt,s,b,a) -> begin
        if not(isDynamicType rt) && not(isNonDynamicType rt) &&
           not(isReferentNonDynamic rt) && isPtrType rt then begin
            setFunctionType fd (TFun(addDynamicType rt,s,b,a));
            if !log_change || warnOnChange then
                E.warn "return of %s must be annotated SDYNAMIC. Def Site." fd.svar.vname;
            change := true
        end else ()
    end
    | _ -> () end;
    propDynamicThroughCallSites ~warnOnChange:warnOnChange fd change;
    updateCompTypes ~warnOnChange:warnOnChange fd change;
    ignore(visitCilFunction (new castFixerClass) fd)

let getRetType (fd : fundec) : typ option =
    match unrollType fd.svar.vtype with
    | TFun(rt,s,b,a) -> Some rt
    | _ -> None


class sharingAnalysisClass ?(warnOnChange : bool = false)
                            (change : bool ref)
    = object(self)
    inherit nopCilVisitor

    method vglob = function
    | GFun(fd,_) -> begin
        findDynamicVis ~warnOnChange:warnOnChange fd change;
        SkipChildren
    end
    | _ -> SkipChildren

end

(** 5.) *)

let isHasDefType (t : typ) : bool = hasAttribute "shasdef" (typeAttrs t)
let addHasDefType (t : typ) : typ = typeAddAttributes [Attr("shasdef",[])] t

let addHasDef (g : global) : unit =
    match g with
    | GFun(fd,_) -> fd.svar.vtype <- addHasDefType fd.svar.vtype
    | _ -> ()

class undefFuncFinderClass = object(self)
    inherit nopCilVisitor

    val mutable warnedabout = []

    method vvrbl (vi : varinfo) =
        if vi.vname = "SCAST" ||
           isPthreadFnName vi.vname then SkipChildren else
        match unrollType vi.vtype with
        | TFun(_,Some argts,_,_)
          when vi.vglob && not(isHasDefType vi.vtype) &&
               not(Rcutils.isRcFunction vi.vname) &&
               not(Dcheckdef.isDeputyFunctionLval(Lval(Var vi,NoOffset))) ->
            let badargs =
                List.fold_left (fun bas (n,t,_) ->
                    if isInDynamicType t then n::bas else bas)
                    [] argts
            in
            if badargs <> [] && not(List.mem vi.vname warnedabout) then begin
                E.warn "External function %s is passed a dynamic argument at %a: %s"
                    vi.vname d_loc (!currentLoc) (String.concat " " badargs);
                warnedabout <- vi.vname :: warnedabout
            end;
            SkipChildren
        | _ -> SkipChildren
end

(** 6.) *)

class structCastFinderClass = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        match i with
        | Call(reslv, Lval(Var fvi, NoOffset), [e], loc)
          when fvi.vname = "SCAST" -> begin
            ignore(addCastedStructType (unrollType(typeOf e)));
            SkipChildren
        end
        | _ -> SkipChildren

end

let findCastedStructs (gl : global list) : unit =
    let vis = new structCastFinderClass in
    List.iter (fun g -> ignore(visitCilGlobal vis g)) gl

(** Entry point *)
let localSharingAnalysis ?(warnOnChange : bool = false)
                         (gl : global list) : unit
    =
    List.iter fnPtrAnalysis gl;
    findCastedStructs gl;
    inThreadAnalysis gl;
    let change = ref false in
    let vis = new sharingAnalysisClass ~warnOnChange:warnOnChange change in
    let rec helper () =
        change := false;
        List.iter (fun g -> ignore(visitCilGlobal vis g)) gl;
        if !change then
            helper ()
    in
    helper ();
    List.iter addHasDef gl;
    let defvis = new undefFuncFinderClass in
    List.iter (fun g -> ignore(visitCilGlobal defvis g)) gl

(** XXX: Move to ivyglobserver.ml. *)

let sameGlob g1 g2 =
    match g1, g2 with
    | GType(ti1,_), GType(ti2,_) -> ti1.tname = ti2.tname
    | GCompTag(ci1,_) , GCompTag(ci2,_) ->
        ci1.cname = ci2.cname
    | GCompTagDecl(ci1,_), (GCompTag(ci2,_)|GCompTagDecl(ci2,_)) ->
        ci1.cname = ci2.cname
(*
    | (GCompTag(ci1,_)|GCompTagDecl(ci1,_)),
      (GCompTag(ci2,_)|GCompTagDecl(ci2,_)) ->
        ci1.cname = ci2.cname
*)
    | (GEnumTag(ei1,_)|GEnumTagDecl(ei1,_)),
      (GEnumTag(ei2,_)|GEnumTagDecl(ei2,_)) ->
        ei1.ename = ei2.ename
    | (GVar(vi1,_,_)|GVarDecl(vi1,_)),
      (GVar(vi2,_,_)|GVarDecl(vi2,_)) ->
        vi1.vname = vi2.vname
    | GFun(fd1,_), GFun(fd2,_) -> fd1.svar.vname = fd2.svar.vname
    | GVarDecl(vi,_),GFun(fd,_)
    | GFun(fd,_), GVarDecl(vi,_) -> vi.vname = fd.svar.vname
    | GAsm(s1,_), GAsm(s2,_)
    | GText s1, GText s2 -> s1 = s2
    | GPragma(a1,_), GPragma(a2,_) ->
        let s1 = sprint ~width:100 (d_global () g1)
        and s2 = sprint ~width:100 (d_global () g2) in
        s1 = s2
    | _, _ -> false

let globName (g : global) : string =
    match g with
    | GType(ti,_) -> ti.tname
    | GCompTag(ci,_) | GCompTagDecl(ci,_) -> ci.cname
    | GEnumTag(ei,_) | GEnumTagDecl(ei,_) -> ei.ename
    | GVarDecl(vi,_) | GVar(vi,_,_) -> vi.vname
    | GFun(fd,_) -> fd.svar.vname
    | GAsm(s,_) | GText s -> s
    | _ -> sprint ~width:100 (d_global () g)


(* has is set to true if all the globals visited are in gl *)
class dependencyFinderClass (gl : global list) (has : bool ref) = object(self)
    inherit nopCilVisitor

    (* Can't have fields with type of forward declared struct *)
    method vglob (g : global) =
        match g with
        | GCompTag(ci, _) ->
            let hasdeps =
                List.fold_left (fun b fi -> b &&
                    match unrollType fi.ftype with
                    | TComp(ci',_) ->
                        List.exists (sameGlob(GCompTag(ci',locUnknown))) gl
                    | _ -> true) true ci.cfields
            in
            if not hasdeps then begin
                has := false;
                SkipChildren
            end else DoChildren
        | _ -> DoChildren

    method vtype (t : typ) =
        match t with
        | TNamed(ti,_) ->
            if not(List.exists (sameGlob (GType(ti,locUnknown))) gl) then begin
                (*E.log "dependencyFinder: typdef %s not found in:\n" ti.tname;
                List.iter (fun g -> E.log "%s\n" (globName g)) gl;*)
                has := false;
                SkipChildren
            end else DoChildren
        | TComp(ci,_) ->
            if not(List.exists (sameGlob (GCompTagDecl(ci,locUnknown))) gl)
            then begin
                (*E.log "dependencyFinder: struct %s not found\n" ci.cname;
                List.iter (fun g -> E.log "%s\n" (globName g)) gl;*)
                has := false;
                SkipChildren
            end else DoChildren
        | TEnum(ei,_) ->
            if not(List.exists (sameGlob (GEnumTag(ei,locUnknown))) gl)
            then begin
                (*E.log "dependencyFinder: enum %s not found\n" ei.ename;
                List.iter (fun g -> E.log "%s\n" (globName g)) gl;*)
                has := false;
                SkipChildren
            end else DoChildren
        | _ -> DoChildren

    method vvrbl (vi : varinfo) =
        if vi.vglob &&
           not(List.exists (sameGlob (GVarDecl(vi,locUnknown))) gl)
        then begin
            (*E.log "dependencyFinder: var %s not found\n" vi.vname;
            List.iter (fun g -> E.log "%s\n" (globName g)) gl;*)
            has := false;
            SkipChildren
        end else DoChildren

end

let hasDependencies (gl : global list) (g : global) : bool =
    let has = ref true in
    let vis = new dependencyFinderClass gl has in
    ignore(visitCilGlobal vis g);
    !has

(* Assumes things are appropriately forward declared so that
   there won't be any cycles *)
let topoSortGlobs (gl : global list) : global list =
    let rec one_pass sorted globs =
        let (newsorted, newglobs) =
            List.fold_left (fun (sorted, globs) g ->
                (*E.log "topoSortGlobs: trying %s\n" (globName g);*)
                if hasDependencies (g :: sorted) g then begin
                    (*E.log "topoSortGlobs: adding %s\n" (globName g);*)
                    (g :: sorted, globs)
                end else (sorted, g :: globs))
            (sorted,[]) globs
        in
        if newglobs = []
        then List.rev newsorted
        else if List.length newsorted = List.length sorted
        then begin
            E.warn "Couldn't toposort globs:";
            (*List.iter (fun g -> E.log "notsorted: %s\n" (globName g)) globs;*)
            (List.rev sorted) @ globs
        end else one_pass newsorted newglobs
    in
    one_pass [] gl

let dumpGlobals (fname : string) (gl : global list) : unit =
    let outf = open_out fname in
    let printg = dumpGlobal defaultCilPrinter outf in
    let dump_one g =
        begin match g with
        | GVar(vi,_,loc) -> printg (GVarDecl(vi,loc)) (* just need the type *)
        | GFun(fd,loc) -> printg (GVarDecl(fd.svar,loc))
        | _ -> printg g end;
        output_string outf "\n";
    in
    let prevStyle = !lineDirectiveStyle in
    lineDirectiveStyle := None;
    List.iter dump_one gl;
    lineDirectiveStyle := prevStyle;
    close_out outf


(** Entry point for ivyglobserver *)
(* iterate until types converge *)
let globalSharingAnalysis ?(warnOnChange : bool = false)
                          (gl : global list)
    : unit =
    localSharingAnalysis ~warnOnChange:warnOnChange gl;
    dumpGlobals "sharc_sharing.i" (topoSortGlobs gl)

let init () =
    Ivyglobserver.addGlobalProcessor name globalSharingAnalysis
