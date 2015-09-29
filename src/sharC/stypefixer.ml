(*
 * stypefixer.ml
 *
 * Use user annotations and results of the sharing analysis to put an
 * annotation on every type. Also check the well-formedness of types.
 * The actual type checking happens in stypechecker.ml
 *
 *)

open Cil
open Pretty
open Ivyoptions
open Sutil

module E = Errormsg

(* Fix dynamic types *)
class dynamicTypeFixerClass = object(self)
    inherit nopCilVisitor

    (* 1) If it's a local non-pointer whose address hasn't been taken,
        then we make sure that it's pprivate.
        2) If it's a local non-pointer whose address has been taken,
        then we have to leave it as dynamic.
        3) If it's a local pointer whose address has not been taken,
        then change to private, but make the referrent type dynamic unless
        it's already qualified.
        4) If it's a local pointer whose address has been taken,
        then leave as dynamic.
        5) If it's a global, then leave it dynamic *)
    method private fix_type (t : typ) : typ =
        let fixFnPtrType (t : typ) : typ =
            match unrollType t with
            | TPtr(TFun(rt,None,va,a),pa) ->
                TPtr(TFun(self#fix_type rt,None,va,a),pa)
            | TPtr(TFun(rt,Some ntal,va,a),pa) ->
                TPtr(TFun(self#fix_type rt,
                          Some(List.map (fun (n,t,a) -> (n,self#fix_type t,a)) ntal),
                          va,a), pa)
            | _ -> t
        in
        let newt =
        match qualFromAttrs (typeAttrs t) with
        | OneQual(Attr(q,ap))
          when List.mem q sharc_dynamic_attrs -> begin
            match unrollType t with
            | TPtr(rt, a) -> begin
                match qualFromAttrs (typeAttrs rt) with
                | OneQual _ -> begin
                    fixFnPtrType
                        (typeAddAttributes [sprivate]
                            (typeRemoveAttributes sharc_dynamic_attrs
                                t))
                end
                | NoQual -> begin
                    fixFnPtrType
                        (typeAddAttributes [sprivate]
                            (typeRemoveAttributes sharc_dynamic_attrs
                                (TPtr(typeAddAttributes [Attr(q,ap)] rt,a))));
                end
                | MultiQual -> begin
                    E.s(E.bug "dynamicTypeFixer: type %a has more than one qualifer at %a"
                        sp_type rt d_loc (!currentLoc))
                end
            end
            | TArray(rt,e,a) -> begin
                match qualFromAttrs (typeAttrs rt) with
                | OneQual _ -> begin
                    typeAddAttributes [sprivate]
                        (typeRemoveAttributes sharc_dynamic_attrs
                            t)
                end
                | NoQual -> begin
                    typeAddAttributes [sprivate]
                        (typeRemoveAttributes sharc_dynamic_attrs
                            (TArray(typeAddAttributes [Attr(q,ap)] rt,e,a)))
                end
                | MultiQual -> begin
                    E.bug "dynamicTypeFixer: type %a has more than one qualifer at %a"
                        sp_type rt d_loc (!currentLoc);
                    t
                end
            end
            | TFun(rt,None,va,a) -> begin
                TFun(self#fix_type rt,None,va,a)
            end
            | TFun(rt,Some ntal,va,a) -> begin
                TFun(self#fix_type rt,
                     Some(List.map (fun (n,t,a) -> (n,self#fix_type t,a)) ntal),
                     va,a)
            end
            | _ -> begin
                typeAddAttributes [sprivate]
                    (typeRemoveAttributes sharc_dynamic_attrs t)
            end
        end
        | OneQual _ -> begin
            match unrollType t with
            | TFun(rt,None,va,a) -> TFun(self#fix_type rt,None,va,a)
            | TFun(rt,Some ntal,va,a) ->
                TFun(self#fix_type rt,
                    Some(List.map (fun (n,t,a) -> (n,self#fix_type t,a)) ntal),
                    va,a)
            | _ -> fixFnPtrType t
        end
        | MultiQual -> begin
            E.bug "dynamicTypeFixer: type %a has more than one qualifier at %a"
                sp_type t d_loc (!currentLoc);
            t
        end
        | _ -> fixFnPtrType t
        in
        (*E.log "fix_type:\n\tOld: %a\n\tNew: %a\n" sp_type t sp_type newt;*)
        newt

    method private fix_nondynamic_type (t : typ) : typ =
        match qualFromAttrs (typeAttrs t) with
        | OneQual(Attr(q,ap)) -> begin
            match unrollType t with
            | TPtr(rt, a) -> begin
                match qualFromAttrs (typeAttrs rt) with
                | OneQual _ ->
                    typeAddAttributes [sprivate]
                        (typeRemoveAttributes sharc_nonprivate_attrs t)
                | NoQual ->
                    typeAddAttributes [sprivate]
                        (typeRemoveAttributes sharc_nonprivate_attrs
                            (TPtr(typeAddAttributes [Attr(q,ap)] rt,a)))
                | _ -> t (* an error that will get caught elsewhere *)
            end
            | TArray(et,e,a) -> begin
                match qualFromAttrs (typeAttrs et) with
                | OneQual _ ->
                    typeAddAttributes [sprivate]
                        (typeRemoveAttributes sharc_nonprivate_attrs t)
                | NoQual ->
                    typeAddAttributes [sprivate]
                        (typeRemoveAttributes sharc_nonprivate_attrs
                            (TArray(typeAddAttributes [Attr(q,ap)] et,e,a)))
                | _ -> t
            end
            | _ ->
                typeAddAttributes [sprivate]
                    (typeRemoveAttributes sharc_nonprivate_attrs t)
        end
        | _ -> t

    method vvdec (vi : varinfo) =
        (*E.log "dynamicTypeFixer: %s\n" vi.vname;*)
        match qualFromAttrs (typeAttrs vi.vtype) with
        | OneQual(Attr(q,ap))
          when List.mem q sharc_dynamic_attrs -> begin
            if vi.vglob || vi.vaddrof then SkipChildren else begin
                (*E.log "dynamicTypeFixer: %s\n" vi.vname;
                E.log "\tchanging %a to " sp_type vi.vtype;*)
                vi.vtype <- self#fix_type vi.vtype;
                (*E.log "%a\n" sp_type vi.vtype;*)
                SkipChildren
            end
        end
        | OneQual(Attr(q,ap)) -> begin
            if vi.vglob || vi.vaddrof then SkipChildren else begin
                vi.vtype <- self#fix_nondynamic_type vi.vtype;
                SkipChildren
            end
        end
        | NoQual -> begin
            (*E.log "dynamicTypeFixer: %s\n" vi.vname;
            E.log "\tchanging %a to " sp_type vi.vtype;*)
            vi.vtype <- typeAddAttributes [sprivate] vi.vtype;
            (*E.log "%a\n" sp_type vi.vtype;*)
            match unrollType vi.vtype with
            | TFun _ -> DoChildren
            | _ -> SkipChildren
        end
        | MultiQual -> begin
            E.bug "dynamicTypeFixer: %s:%a has too many qualifiers at %a"
                vi.vname sp_type vi.vtype d_loc (!currentLoc);
            SkipChildren
        end

    method vtype (t : typ) =
        let newt = self#fix_type t in
        (*E.log "dynamicTypeFixer:\n\tOld: %a\n\tNew: %a\n"
            sp_type t sp_type newt;*)
        ChangeTo newt

end

let dynamicTypeFixer (f : file) : unit =
    let vis = new dynamicTypeFixerClass in
    visitCilFile vis f

class compTypeFixerClass = object(self)
    inherit nopCilVisitor

    method vtype (t : typ) =
        match unrollType t with
        | TComp(ci,_) ->
            List.iter (fun fi ->
                match qualFromAttrs (typeAttrs fi.ftype) with
                | OneQual _ -> ()
                | NoQual ->
                    fi.ftype <- typeAddAttributes [sctx] (unrollType fi.ftype)
                | MultiQual ->
                    E.bug "compTypeFixer: field %s of %s has too many qualifiers"
                        fi.fname ci.cname)
            ci.cfields;
            DoChildren
        | _ -> DoChildren
end

(* Add pctx qualifier to unqualified structure fields to indicate that
   how they are dynamic depends on the qualification of the instance *)
let compTypeFixer (f : file) : unit =
    let vis = new compTypeFixerClass in
    visitCilFile vis f

(* canonicalize types by putting a qualifier on every type *)
let rec fixTypes ?(comp : bool = false) ?(casted : bool = false)
                  (t : typ) (qc : attribute) : typ =
    (*E.log "fixTypes: %a\n" sp_type t;*)
    let ft t qc =
        match qc, qualFromAttrs (typeAttrs t) with
        | Attr("sctx",_), NoQual -> begin
            (* If a structure is casted, then unannotated types in pointers
               become sdynamic. Otherwise, the qualifier is pushed down *)
            if casted then typeAddAttributes [Attr("sdynamic",[])] t
            else typeAddAttributes [qc] t
        end
        | _, NoQual -> begin
            (*E.log "fixTypes: Adding %a to %a\n" sp_attr qc sp_type t;*)
            typeAddAttributes [qc] t
        end
        | Attr(s,_), OneQual(Attr(q,_)) -> t
        | _, MultiQual -> begin
            E.bug "fixTypes: %a has more than one qualifier"
                sp_type t;
            t
        end
    in
    if Dattrs.isAllocator t || Dattrs.isDeallocator t then ft t qc else
    match t with
    | TPtr(rt,a) -> begin
        (* canonicalize the referrent type in the context of the qualifier
           on the pointer type if there is one. If there isn't one
           canonicalize the referrent type in the current context and put the
           current qualifier on the pointer type. *)
        let attr =
            match qualFromAttrs a with
            | OneQual attr -> attr
            | NoQual -> qc
            | MultiQual -> begin
                E.bug "fixTypes: %a has more than one qualifier"
                    sp_type t;
                qc
            end
        in
        ft (TPtr(fixTypes ~comp:comp ~casted:casted rt attr, a)) qc
    end
    | TArray(et,e,a) -> begin
        (* Same for arrays as for pointers *)
        let attr =
            match qualFromAttrs a with
            | OneQual attr -> attr
            | NoQual -> qc
            | MultiQual -> begin
                E.bug "fixTypes: %a has more than one qualifier"
                    sp_type t;
                qc
            end
        in
        ft (TArray(fixTypes ~comp:comp ~casted:casted et attr,e,a)) qc
    end
    | TComp(ci,a) -> begin
        (* Call fixTypes on field types *)
        if comp then ft (TComp(ci,a)) qc else begin
        let attr =
            match qualFromAttrs a with
            | OneQual attr -> attr
            | NoQual -> qc
            | MultiQual -> begin
                E.bug "fixTypes: %a has more than one qualifier"
                    sp_type t;
                qc
            end
        in
        let casted = isCastedStruct t in
        List.iter (fun fi -> fi.ftype <-
            fixTypes ~comp:true ~casted:casted fi.ftype attr) ci.cfields;
        ft (TComp(ci,a)) qc
        end
    end
    | TFun(rt,ntalo,b,a) ->
        (* Call fixTypes on return and argument types in the context of private *)
        let rt = fixTypes rt sprivate in
        let ntalo =
            match ntalo with
            | None -> None
            | Some ntal ->
                let ntal =
                    List.map (fun (n,t,a) -> (n,fixTypes ~comp:comp t sprivate,a))
                    ntal
                in
                Some ntal
        in
        ft (TFun(rt,ntalo,b,a)) qc
    | TNamed(ti,a) -> begin
        match qualFromAttrs a with
        | NoQual -> fixTypes ~comp:comp ~casted:casted ti.ttype qc
        | OneQual attr -> fixTypes ~comp:comp ~casted:casted ti.ttype attr
        | MultiQual -> begin
            E.bug "fixTypes: %a has more than one qualifier"
                sp_type t;
            t
        end
    end
    | _ -> ft t qc

class typeFixerClass = object(self)
    inherit nopCilVisitor

    method vexpr (e : exp) =
        let fixCast (it : typ) (e : exp) : exp =
            match e with
            | CastE(t, e1) -> begin
                let attrs = typeAttrs (unrollType (sharCTypeOf e1)) in
                match qualFromAttrs attrs with
                | NoQual ->
                    (*E.bug "typeFixerClass: %a has no attributes at %a\n"
                        sp_type it d_loc (!currentLoc);*)
                    CastE(fixTypes it sprivate,e1)
                | OneQual attr ->
                    CastE(fixTypes it attr, e1)
                | MultiQual ->
                    E.bug "Type has more than one qualifier: %a at %a\n"
                        sp_type it d_loc (!currentLoc);
                    CastE(t,e1)
            end
            | _ -> e
        in
        match e with
        | CastE(t,_) -> ChangeDoChildrenPost(e,fixCast t)
        | _ -> DoChildren


    method vtype (t : typ) = ChangeTo(fixTypes t sprivate)

    method vglob (g : global) =
        match g with
        | GType _ -> SkipChildren
        | _ -> DoChildren
end

let rec wfTypes (t : typ) (qc : attribute) (comp : bool) : bool =
    (*E.log "wfTypes: %a\n" sp_type t;*)
    let ctxFill attr qc =
        if attr = sctx then qc else attr
    in
    let localWF t qc =
        match qc, qualFromAttrs (typeAttrs t) with
        | Attr(s,_), NoQual ->
            E.bug "Type has no qualifiers: %a in context %s at %a\n"
                sp_type t s d_loc (!currentLoc);
            false
        | Attr(s,_), OneQual(Attr(q,_)) ->
            if qle s q then true else begin
                E.log "wfTypes: bad ordering %s over %a at %a\n"
                    s sp_type t d_loc (!currentLoc);
                false
            end
        | _, MultiQual -> begin
            E.bug "wfTypes: %a has more than one qualifier" sp_type t;
            false
        end
    in
    if Dattrs.isAllocator t || Dattrs.isDeallocator t then localWF t qc else
    match unrollType t with
    | TPtr(rt, a) -> begin
        match qualFromAttrs a with
        | NoQual ->
            E.bug "Ptr type has no qualifiers: %a at %a\n"
                sp_type t d_loc (!currentLoc);
            false
        | OneQual attr -> begin
            localWF t qc && wfTypes rt (ctxFill attr qc) comp
        end
        | MultiQual -> begin
            E.bug "wfTypes: %a has more than one qualifier" sp_type t;
            false
        end
    end
    | TArray(et,e,a) -> begin
        match qualFromAttrs a with
        | NoQual -> 
            E.bug "Array type has no qualifiers: %a at %a\n"
                sp_type t d_loc (!currentLoc);
            false
        | OneQual attr -> begin
            localWF t qc && wfTypes et (ctxFill attr qc) comp
        end
        | MultiQual -> begin
            E.bug "wfTypes: %a has more than one qualifier" sp_type t;
            false
        end
    end
    | TComp(ci,a) -> begin
        if comp then localWF t qc else
        match qualFromAttrs a with
        | NoQual -> 
            E.bug "Type has no qualifiers: %a in in comp %s at %a\n"
                sp_type t ci.cname d_loc (!currentLoc);
            false
        | OneQual attr -> begin
            (*E.log "wfTypes: Checking compinfo: %a\n" sp_global (GCompTag(ci,locUnknown));*)
            localWF t qc &&
            (* There does not exist a field that is not well formed *)
            not(List.exists (fun b -> not b)
                (List.map (fun fi -> wfTypes fi.ftype (ctxFill attr qc) true)
                    ci.cfields))
        end
        | MultiQual -> begin
            E.bug "wfTypes: %a has more than one qualifier" sp_type t;
            false
        end
    end
    | TFun(rt,ntalo,b,a) ->
        wfTypes rt sprivate comp &&
        (match ntalo with
        | None -> true
        | Some ntal ->
            not(List.exists (fun b -> not b)
               (List.map (fun (_,t,_) -> wfTypes t sprivate comp) ntal))) &&
        localWF t qc
    | _ -> localWF t qc

class wfTypeCheckerClass = object(self)
    inherit nopCilVisitor

    method vtype (t : typ) =
        if not(wfTypes t sprivate false) then
            E.error "Type %a is not well-formed at %a"
                sp_type t d_loc (!currentLoc);
        SkipChildren

    method vvdec (vi : varinfo) =
        if not(wfTypes vi.vtype sprivate false) then
            E.error "Type %a of variable %s is not well-formed at %a"
                sp_type vi.vtype vi.vname d_loc (!currentLoc);
        SkipChildren

    method vglob (g : global) =
        match g with
        | GType _ | GCompTag _ | GCompTagDecl _ -> SkipChildren
        | _ -> DoChildren

end

(* entry point. run after sharing analysis. *)
let fixTypes (f : file) : unit =
    dynamicTypeFixer f;
    compTypeFixer f;
    visitCilFile (new typeFixerClass) f;
    visitCilFile (new wfTypeCheckerClass) f
