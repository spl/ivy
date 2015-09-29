
(** Process the global initializer *)
open Cil
open Pretty
open Dattrs
open Ivyoptions
open Dutil
open Dcheckdef

module E = Errormsg
module IH = Inthash

(*** PREPROCESSING **)

(* Make a function that contains all the assignments that would be needed to 
 * initialize the globals. We expect the checker to add the necessary checks, 
 * and the optimizers to remove ALL of them. We'll check this later. Call 
 * this then the global initializers have been finished, but before inserting 
 * checks. *)
let prepareGlobalInitializers (f: file) : fundec = 
  (* Create a function at the end of the file *)
  let fd = emptyFunction "__deputy_global_initializers" in
  fd.svar.vstorage <- Static;
  setFunctionType fd (TFun(voidType, Some [], false, []));
  (* We do not insert it in the file *)

  (* Now scan all global data defined in this file. *)
  let instrs : instr list ref = ref [] in

  let rec doInit (lv: lval) (i: init) : unit = 
    let addi (lv': lval) (e': exp) : unit = 
      instrs := (Set(lv', e', !currentLoc)) :: !instrs
    in
    let doSubInit () : unit = 
      match i with 
        CompoundInit (ct, initl) -> 
          foldLeftCompound ~implicit:true
            ~doinit:(fun off' i' t' acc ->
                       if not (isOpenArray t') then
                         doInit (addOffsetLval off' lv) i')
            ~ct:ct
            ~initl:initl
            ~acc:()

      | _ -> ()
    in
    match unrollType (typeOfLval lv), i with
    | TPtr _, SingleInit e -> (* All pointers are checked *)
        addi lv e
       
      (* For arrays whose base type contains pointers or null-term, we 
       * check the whole array *)
    | TArray(bt, _, a), _  when typeContainsPtrOrNullterm bt -> 
        doSubInit ()

      (* For arrays whose base type does not contain pointers or nullterm, 
       * but are nullterm themselves, we check the last element only *)
    | (TArray(_, _, a) as arrt), 
      CompoundInit (_, initl) when hasAttribute "nullterm" a ->
        begin
          (* Scan all (including implicit initializers) and remember the last*)
          let last : (offset * init) option ref = ref None in 
          foldLeftCompound
            ~implicit:true
            ~doinit:(fun off' i' t acc -> last := Some (off', i'))
            ~ct:arrt
            ~initl:initl
            ~acc:();
          match !last with 
          | Some (off', SingleInit e') -> 
              addi (addOffsetLval off' lv) e'
          | Some (_, CompoundInit _) -> 
              unimp ("Cannot initialize a global nullterm " ^^
                     "array of arrays or structs.")
          | None -> E.s (bug "Missing implicit initializer for %a." d_lval lv)
        end

        (* For structs that contain pointers of null-term we check the whole 
         * thing *)
      | TComp _ as t, _ when typeContainsPtrOrNullterm t -> doSubInit ()
            
        (* For other things we do not need to check anything *)
      | _, _ -> ()
  in

  iterGlobals f
    (function
        GVar(gvi, {init = inito}, l)
            when not (isTrustedAttr (typeAttrs gvi.vtype)) ->
          let init' = 
            match inito with 
              None -> makeZeroInit gvi.vtype
            | Some init' -> init'
          in
          doInit (var gvi) init' 
      | _ -> ());

  fd.sbody <- mkBlock [mkStmt (Instr (List.rev !instrs))];
     
  
  fd


(** Call this function after you inserted the checks, to perform the 
 * optimization of the global initializer. Return true if we still have 
 * residual checks. *)
let checkGlobinit (f: file) 
               (gi: fundec) 
               (check: fundec -> unit) 
               (optim: fundec -> location -> unit) : bool =
  (* Before optimization we replace all the references to global data with the 
   * actual data in the initializer. *)
  if !verbose then 
    log "checkGlobinit\n";

  (* insert the checks *)
  check gi;

  if !verbose then 
    log "prepare global initializer for optimizations\n";

  (* First, create a hash-table with the initializers for each global, 
   * indexed by the vid *)
  let globinits : init IH.t = IH.create 13 in 
  iterGlobals f
    (function 
        GVar(gvi, { init = Some i }, _) -> IH.add globinits gvi.vid i
      | _ -> ());
          
  let replaceGlobalsVisitor =  object (self) 
    inherit nopCilVisitor
    method vtype (t: typ) = SkipChildren

    method vexpr (e: exp) = 
      match e with 
      | Lval (Var g, off) when g.vglob && not (isFunctionType g.vtype) &&
                               g.vname <> "__LOCATION__" -> begin
          let off' = visitCilOffset (self :> cilVisitor) off in 
          (* Now fetch the value of this lval from the globinits *)
          let i: init = 
            try IH.find globinits g.vid
            with Not_found -> makeZeroInit g.vtype
          in
          (*
          ignore (log "Find init for %a in %a\n" 
                    d_lval (Var g, off) 
                    d_init i);
          *)
          let rec findInit (i: init) (off: offset) : exp = 
            match off, i with 
              NoOffset, SingleInit e -> e (* We found it *)
            | Index(idx, off'), CompoundInit (ct, inits) -> begin
                let expToInt (e: exp) : int = 
                  match isInteger (constFold true e) with 
                    Some i -> to_int i
                  | None -> E.s (unimp "Integer index %a not a constant"
                                   d_exp e)
                in
                let idxi : int = expToInt idx in 
                (* Find the field in the inits *)
                let found : init option ref = ref None in
                (try
                  foldLeftCompound
                    ~implicit:true
                    ~doinit:(fun off i t () -> 
                      match off with 
                        Index(thisidx, _) -> 
                          let thisi = expToInt thisidx in
                          if thisi = idxi then begin
                            found := Some i;
                            raise Not_found (* Skip the rest *)
                          end
                      | _ -> assert false)
                    ~ct:ct
                    ~initl:inits
                    ~acc:()
                with Not_found ->());

                match !found with 
                  Some i -> findInit i off'
                | None -> 
                    E.s (unimp "Cannot find initializer for %a" 
                           d_lval (Var g, off))
            end

            | Field(fld, off'), CompoundInit (ct, inits) -> begin
                (* Find the field in the inits *)
                try
                  match List.find (function (Field(fld', _), _) -> fld' == fld
                                      | _ -> assert false) 
                        inits with 
                    Field(_, _), fi -> findInit fi off'
                  | _ -> assert false
                with Not_found -> 
                  E.s (unimp "Cannot find initializer for field %s" fld.fname)
            end
            | _, SingleInit _ -> 
                E.s (unimp "SingleInit for compound value (%a)" 
                       (d_offset (text g.vname)) off)
            | NoOffset, CompoundInit _ -> 
                E.s (unimp "global initializer reads CompoundInit")
          in
          ChangeTo (findInit i off')
        end
      | SizeOfE _ | AlignOfE _ ->
          (* Skip size/align because these may contain large array values.
           * See small/global8. *)
          SkipChildren
      | _ -> DoChildren

    method vinst (i: instr) = 
      (* Drop the instructions that initialize the initializers. Hopefully we 
       * do not drop other instructios too *)
      match i with 
        Set _ -> ChangeTo []
      | _ -> DoChildren

  end in
  gi.sbody <- visitCilBlock replaceGlobalsVisitor gi.sbody;
  
  if !verbose then 
    log "optimize the global initializer\n";

  (* Now we optimize *)
  optim gi locUnknown;

  let suppressGlobalInitWarnings = ref false in

  (** Now check the global initializers, after the optimizations. Return true 
   * if we have residual checks for global initializer. *)
  (* The global initializer function must be empty. Give an error message for 
   * each check in the file *)
  let hadErrors = ref false in
  let reportChecksVisitor =  object (self) 
    inherit nopCilVisitor

    method vexpr (e: exp) = SkipChildren

    method vinst (i: instr) = 
      if (instrToCheck i) <> None then begin
        hadErrors := true;
        if not !suppressGlobalInitWarnings then begin
          (* Ivyoptions.strictGlobInit chooses whether this should be an
             error or a warning.  FIXME: always make it an error (bug?)
             once we're sure we've covered all of the cases. *)
          if !Ivyoptions.strictGlobInit then
            error "Undischarged check for global initializer:\n%a"
                    dn_instr i
          else
            ignore (warn "Undischarged check for global initializer:\n%a"
                      dn_instr i);
          (* suppressGlobalInitWarnings := true; *)
        end;
      end;
      SkipChildren

  end in 
  suppressGlobalInitWarnings := false; (* We give one warning for each file *)
  ignore (visitCilBlock (reportChecksVisitor :> cilVisitor) gi.sbody);

  !hadErrors
