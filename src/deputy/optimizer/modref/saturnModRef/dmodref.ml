(*
 * dmodref.ml
 * 
 * Figure out what globals and formals a function may modify and reference.
 * Add Modifies annotations.
 *
 *)
 
open Cil
open Pretty
open Ivyoptions
open Doptimutil
 
(* From Saturn *)
module B = Bdb
module S = Spec
module SIO = Specio
 
module E = Errormsg
module IH = Inthash
module DPF = Dprecfinder
 
let debug = ref false

(* To match the interface *)
let registerIgnoreInst (f : instr -> bool) : unit = ()
let registerIgnoreCall (f : instr -> bool) : unit = ()

let varinfoEqual vi1 vi2 = vi1.vid = vi2.vid

let addGlobalMod (fdat : DPF.functionData)
                 (fvi : varinfo)
                 (gvi : varinfo) :
                 unit
    =
    ignore(E.log "DModRef: %s modifies global %s\n" fvi.vname gvi.vname);
    match IH.tryfind fdat.DPF.fdModHash fvi.vid with
    | Some(gvil,argl) -> begin
        if List.exists (varinfoEqual gvi) gvil then () else begin
            IH.replace fdat.DPF.fdModHash fvi.vid (gvi::gvil,argl);
            match IH.tryfind fdat.DPF.fdFnHash fvi.vid with
            | None -> IH.add fdat.DPF.fdFnHash fvi.vid (fvi, true)
            | Some _ -> ()
        end
    end
    | None -> begin
        IH.add fdat.DPF.fdModHash fvi.vid ([gvi],[]);
        match IH.tryfind fdat.DPF.fdFnHash fvi.vid with
        | None -> IH.add fdat.DPF.fdFnHash fvi.vid (fvi, true)
        | Some _ -> ()
    end

let addArgMod (fdat : DPF.functionData)
              (fvi : varinfo)
              (i : int) :
              unit
    =
    ignore(E.log "DModRef: %s modifies argument %d\n" fvi.vname i);
    match IH.tryfind fdat.DPF.fdModHash fvi.vid with
    | Some(gvil,argl) -> begin
        if List.mem i argl then () else begin
            IH.replace fdat.DPF.fdModHash fvi.vid (gvil,i::argl);
            match IH.tryfind fdat.DPF.fdFnHash fvi.vid with
            | None -> IH.add fdat.DPF.fdFnHash fvi.vid (fvi, true)
            | Some _ ->  ()
        end
    end
    | None -> begin
        IH.add fdat.DPF.fdModHash fvi.vid ([],[i]);
        match IH.tryfind fdat.DPF.fdFnHash fvi.vid with
        | None -> IH.add fdat.DPF.fdFnHash fvi.vid (fvi, true)
        | Some _ ->  ()
    end

type satConst =
    | SatStr of string
    | SatInt of int
(* look inside of v for glob sums and arg sums *)
let extractModsFromVal (fvi : varinfo)
                       (fdat : DPF.functionData)
                       (c : DPF.ctxt)
                       (v : S.t_val) :
                       unit
    =
    (* if it's a sum, unwrap the first val and repeat.
       if it's a constant, then return that *)
    let rec helper (v : S.t_val) : satConst option =
        try
            let (name, vars) = S.val2sum v in
            if name = "arg" then
                Some(SatInt(S.val2sint vars.(0)))
            else if name = "glob" then
                Some(SatStr(S.val2str vars.(0)))
            else helper vars.(0)
        with S.Unexpected s -> begin
            ignore(E.log "DModRef: Expected sum but got %s: %s\n"
                (S.full_string_of_val v) s);
            None
        end
    in
    match helper v with
    | None -> ()
    | Some(SatStr s) -> begin
        try
            (* there might be a colon. we want things to the right of it *)
            if String.contains s ':' then begin
                let ci = String.index s ':' in
                let len = String.length s in
                let s = String.sub s (ci+1) (len - ci - 1) in
                let vi = Hashtbl.find c.DPF.cGlobMap s in
                addGlobalMod fdat fvi vi;
                ()
            end else begin
                let vi = Hashtbl.find c.DPF.cGlobMap s in
                addGlobalMod fdat fvi vi;
                ()
            end
        with Not_found -> begin
            ignore(E.log "DModRef: %s not found in global table\n" s);
            ()
        end
    end
    | Some(SatInt i) ->
        addArgMod fdat fvi i;
        ()

let extractModsFromPred (fvi : varinfo)
                        (fdat : DPF.functionData)
                        (c : DPF.ctxt)
                        (pred : S.t_pred) :
                        unit
    =
    let (name, valarr) = S.pred2rep pred in
    if name <> "stuse" then begin
        if !debug then
            ignore(E.log "DModRef: name %s is not stuse\n" name);
        ()
    end else
        let typ = valarr.(1) in
        try
            let (typstr,_) = S.val2sum typ in
            if typstr <> "write" && typstr <> "deepwrite" then begin
                if !debug then
                    ignore(E.log "DModRef: %s is not write or deepwrite\n"
                        typstr);
                ()
            end else
                let written = valarr.(0) in
                extractModsFromVal fvi fdat c written;
                ()
        with S.Unexpected s -> begin
            ignore(E.log "typ not a string: %s\n" s);
            ()
        end

let dbTryFind (db : B.db) (key : string) : string option =
    try Some(B.find db key)
    with Not_found -> None

let getDbData (db : B.db)
              (fname : string)
              (name : string) :
              string option (* this is really database data. not a real string *)
    =
    let key = "sum_usemod(\""^name^"\",s_func)" in
    match dbTryFind db key with
    | Some s -> Some s
    | None -> begin
        let basename = Filename.basename fname in
        (* force extension to be .c *)
        let basename =
            try (Filename.chop_extension basename)^".c"
            with Invalid_argument _ -> basename^".c"
        in
        let key = "sum_usemod(\""^basename^":"^name^"\",s_func)" in
        match dbTryFind db key with
        | Some s -> Some s
        | None -> begin
            ignore(E.log "DModRef: Neither %s nor %s were in the database\n"
                name (basename^":"^name));
            None
        end
    end
              

let extractModsFromDB (db : B.db)
                      (c : DPF.ctxt)
                      (fdat : DPF.functionData)
                      (f : file) : 
                      unit
    =
    let handleFunVi (vi : varinfo) : unit =
        if not(isFunctionType vi.vtype) then () else
        (* XXX: Also, figure out how to add Modifies(None) annotations! *)
        match getDbData db f.fileName vi.vname with
        | Some data -> begin
            ignore(E.log "DModRef: db found key for %s\n" vi.vname);
            match SIO.load_session_str data with
            | Some sess ->
                S.iter_ext_logic sess (extractModsFromPred vi fdat c)
            | None -> begin
                ignore(E.log "DModRef: SIO.load_session_str returned None\n")
            end
        end
        | None -> begin
            ignore(E.log "DModRef: key for %s was not found in database\n"
                vi.vname);
            match IH.tryfind fdat.DPF.fdModHash vi.vid with
            | Some _ -> begin (* Don't change what's already there *)
                ignore(E.log "DModRef: already data about %s\n"
                    vi.vname);
                ()
            end
            | None -> begin
                (* If we don't already know about it, and Saturn says it
                 * doesn't modify anything, then we'll go with that.
                 * The caveat here is that if Saturn warns us that it
                 * doesn't know about something, then we have to add a stub
                 * for it to analyse *)
                IH.add fdat.DPF.fdModHash vi.vid ([],[]);
                ()
            end;
            ()
        end
    in
    List.iter (fun g -> match g with
        | GVarDecl(vi, _) -> handleFunVi vi
        | GFun(fd, _) -> handleFunVi fd.svar
        | _ -> ()) f.globals


(* Entry point: find Modifications and add them to the prototypes in
   fdat *)
let addAllModifications (fdat : DPF.functionData) (f : file) : unit =
    let sumFile = !saturnLogicPath ^ "/sum_usemod.db" in
    try
        let fd = open_in sumFile in
        close_in fd;
        let db = Bdb.opendbm None sumFile [ Bdb.Dbm_rdonly ] 0o666 in
        let c = DPF.mkGlobalContext f in
        extractModsFromDB db c fdat f;
        ()
    with Sys_error msg -> begin
        ignore(E.log "DModRef: Could not open database file: %s\n" msg);
        ()
    end


(* The functions below are copied from ../zraModRef/dmodref.ml *)
(* helper for modsFromAnnotationsClass *)
let attributeToModVar  (c : DPF.ctxt)
                       (al : attribute list) :
                       (varinfo list * int list) option
    =
    let helper a =
        let attrParamListToModInfo (apl : attrparam list) :
                                   (varinfo list * int list)
            =
            let rec helper apl (viacc,iacc) =
                match apl with
                | [] -> viacc, iacc
                | [ACons("None",[])] -> [], []
                | ap :: rst -> begin
                    match ap with
                    | ACons(s, []) -> begin
                        if String.sub s 0 1 = "$" then
                            let nstr = String.sub s 1 ((String.length s) - 1) in
                            let n = int_of_string nstr in
                            helper rst (viacc, n :: iacc)
                        else try
                            let vi = Hashtbl.find c.DPF.cGlobMap s in
                            helper rst (vi :: viacc, iacc)
                        with Not_found -> begin
                            helper rst (viacc, iacc)
                        end
                    end
                    | _ -> helper rst (viacc, iacc)
                end
            in
            helper apl ([],[])
        in
        match a with
        | Attr("Modifies",apl) -> begin
            try
                if not c.DPF.cInited then
                    ignore(visitCilFile
                            (new DPF.globalMapMakerClass c.DPF.cGlobMap)
                            c.DPF.cFile);
                Some(attrParamListToModInfo apl)
            with DPF.NotAnExp ap -> begin
                ignore(E.log "DModRef: Not an Exp %a\n" d_attrparam ap);
                None
            end
        end
        | Attr(s, _) -> begin
            None
        end
    in
    (*if al = [] then ignore(E.log "DModRef: No Attributes at all!\n");*)
    List.fold_left (fun r a ->
        match helper a with
        | None -> r
        | Some(vilst, ilst) -> Some(vilst, ilst))
        None al

(* helper for extractModAnnotations *)
class modsFromAnnotationsClass (c : DPF.ctxt)
                               (fdat : DPF.functionData) = object(self)
    inherit nopCilVisitor

    method vvdec (vi : varinfo) =
        if isFunctionType vi.vtype then
        try
            let attrs = typeAttrs vi.vtype in
            let modso = attributeToModVar c attrs in
            (match modso with
             | None -> begin
                if !debug then
                    ignore(E.log "DModRef: no annotations for %s:%d\n"
                        vi.vname vi.vid);
             end
             | Some(vilst,ilst) -> begin
                if !debug then
                    ignore(E.log "DModRef: found annotations for %s:%d\n"
                        vi.vname vi.vid);
                (* strip annotation to avoid type errors *)
                vi.vtype <- setTypeAttrs vi.vtype (dropAttribute "Modifies" attrs);
                IH.replace fdat.DPF.fdModHash vi.vid (vilst,ilst)
            end);
            SkipChildren
        with Not_found -> DoChildren
        else DoChildren
end

(* Entry point: take info from Modifies annotations and add to fdat *)
let extractModAnnotations (fdat : DPF.functionData)
                          (f : file) :
                          unit
    =
    let c = DPF.mkGlobalContext f in
    let vis = new modsFromAnnotationsClass c fdat in
    ignore(visitCilFile vis f)
