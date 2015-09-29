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
 
 module E = Errormsg
 module IH = Inthash
 
 module P = Dptranal
 module DPF = Dprecfinder
 
(*
 * When ignore_inst returns true, then
 * the instruction in question has no
 * effects on the abstract state.
 * When ignore_call returns true, then
 * the instruction only has side-effects
 * from the assignment if there is one.
 *)
let ignore_inst = ref (fun i -> false)
let ignore_call = ref (fun i -> false)

let registerIgnoreInst (f : instr -> bool) : unit =
  let f' = !ignore_inst in
  ignore_inst := (fun i -> (f i) || (f' i))

let registerIgnoreCall (f : instr -> bool) : unit =
  let f' = !ignore_call in
  ignore_call := (fun i -> (f i) || (f' i))


let varinfoEqual vi1 vi2 = vi1.vid = vi2.vid


(* helper for modFinderVisitor *)
let addViToGlobMod (globmod : varinfo list ref)
                   (vi : varinfo) :
                   unit
    =
    if vi.vglob then
       if not(List.exists (varinfoEqual vi) (!globmod)) then
          globmod := vi :: (!globmod)

(* helper for modFinderVisitor *)
let addViToArgMod (argmod : int list ref)
                  (f : fundec)
                  (vi : varinfo) :
                  unit
    =
    if List.exists (varinfoEqual vi) f.sformals then
        if not(List.mem vi.vid (!argmod)) then
            match DPF.argToNumber vi f.svar with
            | Some i -> argmod := i :: (!argmod)
            | None -> ()

let kill (globmod : varinfo list ref)
         (argmod : int list ref)
         (error : bool ref) :
         unit
    =
    globmod := [];
    argmod := [];
    error := true

(* helper for modFinderVisitor *)
let memWrite (globmod : varinfo list ref)
             (argmod : int list ref)
             (error : bool ref)
             (f : fundec)
             (ptre : exp) :
             bool
    =
    if not(!doPtrAnalysis) then begin
        ignore(E.log "DModRef: Pointer Analysis is off\n");
        kill globmod argmod error;
        false
    end else begin
        match P.try_resolve_exp ptre with
        | Some dests -> begin
            if dests = [] then
                ignore(E.log "DModRef: pt-set for %a was empty\n" d_exp ptre);
            List.iter (fun vi ->
                ignore(E.log "DModRef: %s is a dest of %a\n"
                    vi.vname d_exp ptre);
                addViToGlobMod globmod vi;
                addViToArgMod argmod f vi)
                dests;
            true
        end
        | None -> begin
            kill globmod argmod error;
            false
        end
    end

(* helper for modFinderVisitor *)
let funCall (fdat : DPF.functionData)
            (globmod : varinfo list ref)
            (argmod : int list ref)
            (error : bool ref)
            (f : fundec)
            (vf : varinfo)
            (args : exp list) :
            bool
    =
    if vf.vname = "__deputy_memset" then begin
        match P.try_resolve_exp (List.hd args) with
        | Some dests -> begin
            List.iter (fun vi ->
                addViToGlobMod globmod vi;
                addViToArgMod argmod f vi)
                dests;
            true
        end
        | None -> begin
            kill globmod argmod error;
            false
        end
    end else match IH.tryfind fdat.DPF.fdModHash vf.vid with
    | None -> begin
        ignore(E.log "DModRef: No data for %s:%d\n" vf.vname vf.vid);
        kill globmod argmod error;
        false
    end
    | Some(gm, am) -> begin
        List.iter (addViToGlobMod globmod) gm;
        List.fold_left (fun b i ->
            let ae = List.nth args i in
            if not(!doPtrAnalysis) then begin
                ignore(E.log "DModRef: Pointer Analysis is off\n");
                kill globmod argmod error;
                false
            end else
                match P.try_resolve_exp ae with
                | Some dests -> begin
                    List.iter (fun vi ->
                        addViToGlobMod globmod vi;
                        addViToArgMod argmod f vi)
                        dests;
                    b
                end
                | None -> begin
                    kill globmod argmod error;
                    false
                end)
        true am
    end

(* accumulate globals and arguments modified by f in globmod and argmod.
   if error is true after the visitor is run, then this information could not
   be determined. If error is false but the lists are empty, then the function
   is pure. fdat gives info about other functions. *)
(* helper for funcModificationFinder *)
class modFinderVisitor (fdat : DPF.functionData)
                       (f : fundec) 
                       (globmod : varinfo list ref)
                       (argmod : int list ref) 
                       (error : bool ref) = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        (* If the function writes memory, but no pointer analysis has been done
         * then give up. *)
        if (!error) && not(!doPtrAnalysis) then SkipChildren else
        match i with
        | Set((Var vi, _), _, _) -> begin
            addViToGlobMod globmod vi;
            DoChildren
        end
        | Set((Mem e, _), _, _) -> begin
            if memWrite globmod argmod error f e then
                DoChildren
            else
                SkipChildren
        end
        | Call(Some(Var vi,_), fe, args, _) -> begin
            addViToGlobMod globmod vi;
            if (!ignore_call) i then DoChildren else
            match fe with
            | Lval(Var vf, NoOffset) -> begin
                if funCall fdat globmod argmod error f vf args then
                    DoChildren
                else SkipChildren
            end
            | _ -> begin
                if not(!doPtrAnalysis) then begin
                    ignore(E.log "DModRef: Pointer Analysis is off\n");
                    kill globmod argmod error;
                    SkipChildren
                end else begin
                    match P.try_resolve_funptr fe with
                    | None -> begin
                        kill globmod argmod error;
                        SkipChildren
                    end
                    | Some fds ->
                        let b = List.fold_left (fun b fd ->
                            b && (funCall fdat globmod argmod error f fd.svar args))
                            true fds
                        in
                        if b then DoChildren else SkipChildren
                end
            end
        end
        | Call(Some(Mem e, off), fe, args, _) -> begin
            if memWrite globmod argmod error f e then
                if (!ignore_call) i then DoChildren else
                match fe with
                | Lval(Var vf, NoOffset) -> begin
                    if funCall fdat globmod argmod error f vf args then
                        DoChildren
                    else
                        SkipChildren
                end
                | _ -> begin
                    if not(!doPtrAnalysis) then begin
                        ignore(E.log "DModRef: Pointer Analysis is off\n");
                        kill globmod argmod error;
                        SkipChildren
                    end else begin
                        match P.try_resolve_funptr fe with
                        | None -> begin
                            kill globmod argmod error;
                            SkipChildren
                        end
                        | Some fds ->
                            let b = List.fold_left (fun b fd ->
                                b && (funCall fdat globmod argmod error f fd.svar args))
                                true fds
                            in
                            if b then DoChildren else SkipChildren
                    end
                end
            else
                SkipChildren
        end
        | Call(None, fe, args, _) -> begin
            if (!ignore_call) i then DoChildren else
            match fe with
            | Lval(Var vf, NoOffset) -> begin
                if funCall fdat globmod argmod error f vf args then
                    DoChildren
                else
                    SkipChildren
            end
            | _ -> begin
                if not(!doPtrAnalysis) then begin
                    ignore(E.log "DModRef: Pointer Analysis is off\n");
                    kill globmod argmod error;
                    SkipChildren
                end else begin
                    match P.try_resolve_funptr fe with
                    | None -> begin
                        kill globmod argmod error;
                        SkipChildren
                    end
                    | Some fds ->
                        let b = List.fold_left (fun b fd ->
                            b && (funCall fdat globmod argmod error f fd.svar args))
                            true fds
                        in
                        if b then DoChildren else SkipChildren
                end
            end
        end
        | Asm(_,_,writes,_,_,_) -> begin
            (* XXX: fix me! *)
            DoChildren
        end
end

(* helper for modificationFinder *)
let funcModificationFinder (fdat : DPF.functionData) (f : fundec) : unit =
    let globmod = ref [] in
    let argmod = ref [] in
    let error = ref false in
    let vis = new modFinderVisitor fdat f globmod argmod error in
    ignore(visitCilFunction vis f);
    if not(!error) then begin
        ignore(E.log "DModRef: found some Modifies stuff! %s\n" f.svar.vname);
        IH.replace fdat.DPF.fdModHash f.svar.vid (!globmod,!argmod);
        match IH.tryfind fdat.DPF.fdFnHash f.svar.vid with
        | None -> IH.add fdat.DPF.fdFnHash f.svar.vid (f.svar, true)
        | Some _ -> ()
    end else
        ignore(E.log "DModRef: problem with %s\n" f.svar.vname)

(* helper for addAllModifications. finds Modifications and adds them to
   fdat.fdModHash *)
let modificationFinder (fdat : DPF.functionData) (f : file) : unit =
    List.iter (fun g -> match g with
        | GFun(fd, _ ) -> funcModificationFinder fdat fd
        | _ -> ()) f.globals


(* Entry point: find Modifications and add them to the prototypes in
   fdat *)
let addAllModifications (fdat : DPF.functionData) (f : file) : unit =
    modificationFinder fdat f
    (*;addModificationAttributes fdat*)

(* The functions below are also in ../saturnModRef/dmodref.ml *)
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
                ignore(E.log "DModRef: no annotations for %s:%d\n"
                    vi.vname vi.vid);
             end
             | Some(vilst,ilst) -> begin
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
