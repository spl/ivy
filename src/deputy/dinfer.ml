(*
 *
 * Copyright (c) 2004, 
 *  Jeremy Condit       <jcondit@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

open Cil
open Expcompare
open Pretty
open Dattrs
open Ivyoptions
open Dutil
open Dcheckdef
open Dcheck

module E = Errormsg
module DC = Dcheck
module DO = Doptimmain
module DT = Dtinyos
module S = Stats
module N = Ptrnode
module H = Hashtbl

(**************************************************************************)


(* Get the base type and attributes of a pointer type.  
 * If this is a void* type, see if we've inferred a better type for it. *)
let getPointerType (t: typ) (where: string) : typ * attributes =
  match unrollType t with
  | TPtr (bt, a) when isVoidType bt -> begin
      (* This is a void*.  Have we inferred a better type for it?*)
      match N.nodeOfAttrlist a with
        Some n when not (isVoidType (N.get_rep n).N.btype) -> 
          (* we have a better type *)
          let rep = N.get_rep n in
          if hasAttribute "trusted" a || hasAttribute "ntexpand" a then begin
            (* Don't replace *)
            bt, a
          end
          else if (hasAttribute "bounds" a || hasAttribute "size" a)
                  && not (hasDefaultAnnot a) then 
            begin
              (* Don't replace if this void* has an explicit annotation. *)
              if !verbose then
                log ("Not replacing %a in %s with a true type because "^^ 
                     "it has an annotation.\n")
                  dx_type t where;
              bt, a
            end
          else begin 
            if !verbose then
              log "Replacing %a in %s with %a." 
                dx_type t where dx_type (TPtr(rep.N.btype,a));
            rep.N.btype, a
          end
      | _ -> (* No better type, so keep the void* *)
          bt, a
    end
  | TPtr (bt, a) ->
      bt, a
  | _ -> E.s (error "Expected pointer type in %s" where)
    

(**************************************************************************)

let debugAuto = false


let findnull = mkFun "deputy_findnull" intType
           [typeAddAttributes [count0Attr; trustedAttr] voidPtrType; intType] Rcutils.nofreeAttr

let hasBoundsAttr (t: typ) : bool =
  hasAttribute "bounds" (typeAttrs t)

let getBoundsAttr (t: typ) : attrparam list =
  match filterAttributes "bounds" (typeAttrs t) with
  | [Attr ("bounds", aps)] -> aps
  | [] -> E.s (bug "Expected bound attribute")
  | _ -> E.s (error "Type has more than one bound attribute: \"%a\""
                dx_type t)

let setBoundsAttr (t: typ) (aps: attrparam list) : typ =
  typeAddAttributes [Attr ("bounds", aps)] (typeRemoveAttributes ["bounds"] t)

let hasAutoBounds (t: typ) : bool =
  isPointerType t &&
  hasBoundsAttr t &&
  match getBoundsAttr t with
  | [ACons (n, []); _] when n = autoKeyword -> true
  | [_; ACons (n, [])] when n = autoKeyword -> true
  | [_; _] -> false
  | _ -> E.s (bug "Bounds attribute does not have two arguments")

let mapBounds (fn: attrparam -> string -> attrparam) (aps: attrparam list)
    : attrparam list =
  match aps with
  | [b; e] -> [fn b "b"; fn e "e"]
  | _ -> E.s (bug "Bounds attribute does not have two arguments")

(* The name of a fat structure, based on base type and the meta fields. We 
 * must differentiate in the name all attributes of types that we do not want 
 * to conflate. *)
let fatStructName (bt: typ) (metafields: (string * typ) list) = 
  let rec btname = function
    | TNamed (t, _) -> t.tname
    | TBuiltin_va_list _ -> "va_list"
    | TVoid(_) -> "void"
    | TInt(IInt,_) -> "int"
    | TInt(IUInt,_) -> "uint"
    | TInt(IShort,_) -> "short"
    | TInt(IUShort,_) -> "ushort"
    | TInt(IChar,_) -> "char"
    | TInt(IUChar,_) -> "uchar"
    | TInt(ISChar,_) -> "schar"
    | TInt(ILong,_) -> "long"
    | TInt(IULong,_) -> "ulong"
    | TInt(ILongLong,_) -> "llong"
    | TInt(IULongLong,_) -> "ullong"
    | TFloat(FFloat,_) -> "float"
    | TFloat(FDouble,_) -> "double"
    | TFloat(FLongDouble,_) -> "ldouble"
    | TEnum (enum, _) -> "e_" ^ enum.ename
    | TComp (comp, _) -> 
        let su = if comp.cstruct then "s_" else "u_" in
        su ^ comp.cname
    | TFun _ -> "fun"
    | TPtr(t, a) -> 
        let atn = 
          if hasAttribute "nullterm" a then 
            "n"
          else
            ""
        in
        "p" ^ atn ^ "_" ^ btname t
    | TArray(t, sz, _) -> "a_" ^ btname t
  in
  List.fold_left 
     (fun acc (s, _) -> 
       (* We assume that s starts with __ *)
       acc ^ 
       (if String.length s > 2 then 
         String.sub s 2 (String.length s - 2) else s))
     ((btname bt) ^ "_")
    metafields

(** Keep a list of the fat structs, indexed by their name *)
let fatStructs: (string, typ) H.t = H.create 13

(** Keep a list of global declarations that we must add, in reverse order *)
let preAutoDecls: global list ref = ref []

(** Make a fat struct. Each field is described with a name and type. We 
 * assume that the names are of the form "__x", where "x" a suffix (either 
 * "b" or "e" for now). The main field is called __p and is always the first 
 * one. *)
let makeFatStruct (dt: typ) (* type of the data field *)
                  (metafields: (string * typ) list) : typ = 
  (* Get the name of the fat struct, based on base type and suffixes *)
  let fn = fatStructName dt metafields in
  try H.find fatStructs fn 
  with Not_found -> begin
    let fatci = 
      mkCompInfo true fn
        (fun ci -> 
          (* Prepend the data field *)
          ("__p", dt, None, [], !currentLoc) :: 
          List.map (fun (fn, ft) -> (fn, ft, None, [], !currentLoc)) 
            metafields)
        []
    in
    preAutoDecls := GCompTag(fatci, !currentLoc) :: !preAutoDecls;
    let tfat = TComp(fatci, []) in
    H.add fatStructs fn tfat;
    tfat
  end
        
(** Test if a type is a fat structure *)
let isFatStructType (t: typ) = 
  match unrollType t with 
    TComp(ci, _) when H.mem fatStructs ci.cname -> true
  | _ -> false

(** Get the data and meta fields of a fat compinfo. For each meta field we 
 * also have the suffix. *)
let getFieldsOfFatComp (ci: compinfo) : fieldinfo * (string * fieldinfo) list = 
  match ci.cfields with 
    fdata :: fmetas when fdata.fname = "__p" -> 
      let metas: (string * fieldinfo) list = 
        List.map
          (fun fm -> 
            (* We assume that the field name is __e, etc *)
            let suff = 
              if String.length fm.fname > 2 then 
                String.sub fm.fname 2 (String.length fm.fname - 2)
              else
                fm.fname
            in
            (suff, fm))
          fmetas
      in
      fdata, metas

  | _ -> E.s (bug "The data field is not the first one in %s\n" ci.cname)

(** Get the data and meta fields of a fat compinfo.  *)
let getFieldsOfFat (t: typ) : (fieldinfo * (string * fieldinfo) list) option = 
  match unrollType t with 
    TComp(ci, _) when H.mem fatStructs ci.cname -> 
      Some (getFieldsOfFatComp ci)

  | _ -> None


(* Split a fat lval into the data one and the meta lvals, each one with the 
 * suffix. Return None if not a fat struct lval. *)
let splitFatLval (lv: lval) : (lval * (string * lval) list) option = 
  let lvt = typeOfLval lv in 
  let lvbase, lvoff = lv in
  match unrollType lvt with 
    TComp(ci, _) when H.mem fatStructs ci.cname -> begin
      let fdata, fmeta = getFieldsOfFatComp ci in
      Some ((lvbase, addOffset (Field(fdata, NoOffset)) lvoff),
            List.map (fun (suff, fm) -> 
              (suff, (lvbase, addOffset (Field(fm, NoOffset)) lvoff))) fmeta)

    end
  | _ -> None
  

(** Get the data field, if any, from a fat struct lval *)
let getDataFromFatLval (lv: lval) : lval = 
  match getFieldsOfFat (typeOfLval lv) with 
    None -> lv
  | Some (fdata, _) -> begin
      let reslv = addOffsetLval (Field(fdata, NoOffset)) lv in
      reslv
    end


(** Get an lval denoting the whole fat value, from a data value. Return 
 * the input lval if not a data lval *)
let getFatFromDataLval (lv: lval) : lval = 
  match removeOffsetLval lv with 
    lv', Field(fdata, NoOffset) -> begin
      try
        if H.mem fatStructs fdata.fcomp.cname &&
          fdata == List.nth fdata.fcomp.cfields 0 then 
          lv'
        else
          lv
      with _ -> lv
    end
            
  | _ -> lv


(** Get an expression denoting the whole fat value, from a data value. Return 
 * the input expression if not a data expression *)
let getFatFromDataExp (e: exp) : exp = 
  match e with 
    Lval lv -> begin
      let lv' = getFatFromDataLval lv in 
      if lv' != lv then 
        Lval lv'
          else
        e
    end
  | _ -> e    


let makeHiddenVar (fdec: fundec) (name: string) (t: typ) : varinfo =
  let vi = makeLocalVar fdec name t in
  vi.vattr <- addAttribute hiddenAttr vi.vattr;
  vi

(* This visitor is responsible for converting "__auto" in bounds annotation 
 * into fresh variables and fat structures that have properly-assigned 
 * bounds. *)
let autoVisitor = object (self)
  inherit nopCilVisitor

  (** Map a variable name to a list of new bound variables added for it, each 
   * with the suffix "b" or "e" and the variable name. Use find_all to get 
   * all the bounds. *)    
  val varBounds : (string, (string * varinfo)) Hashtbl.t =
    Hashtbl.create 7

  (** The current return type of the function, already processed *)
  val mutable currentReturnType = intType

  (** Indicates whether we are currently processing trusted code. *)
  val mutable trustedCode = false

  val mutable curIndex = 0
  method private makeName (base: string) =
    curIndex <- curIndex + 1;
    base ^ (string_of_int curIndex)

  (* Get the fancybounds of this expression, for the purposes of 
   * setting automatic bound variables. *)
  method private getPointerBounds (toType: typ) (fromType: typ) (e: exp) =
    let lo, hi =
      if hasAttribute "fancysize" (typeAttrs fromType) then
        fancyBoundsOfSizeType toType fromType e
      else
        fancyBoundsOfType fromType
    in
    (* We expand the range of nullterms with deputy_findnull (like strlen)
     * when NTEXPAND is used, or when we cast from something with
     * fixed bounds to a local/cast with automatic bounds. *)
    let doExpandNullterm: bool = 
      isNulltermExpand toType ||
      (isNullterm fromType && not (isNullterm toType))
    in
    if doExpandNullterm then
      let tmp = makeHiddenVar !curFunc (self#makeName "deplength") intType in
      let sz =
        match unrollType fromType with
        | TPtr (bt, _) -> bitsSizeOf bt / 8
        | _ -> E.s (error "Expected pointer type")
      in
      let instrs =
        [Call (Some (var tmp), findnull, [hi; integer sz], !currentLoc)]
      in
      let hi' = BinOp (PlusPI, hi, Lval (var tmp), typeOf hi) in
      instrs, lo, hi'
    else
      [], lo, hi

  (* Get the upper and lower bounds for an expression e when assigning to
   * a variable of type toType.  Also two lists of instructions that
   * must be inserted into the program before and after using the
   * expressions. *)
  method private getBounds (instr: instr) (toType: typ)
      : instr list * exp * exp * exp * instr list =
    DC.startExtraInstrs ();
    let e, t, endInstrs = DC.checkInstrRhs instr in
    let beginInstrs = DC.endExtraInstrs () in
    if isPointerType t then
      let instrs', lo, hi = self#getPointerBounds toType t e in
      beginInstrs @ instrs', e, lo, hi, endInstrs
    else
      beginInstrs, e, e, e, endInstrs

  (* Given a type t whose bounds contain the "__auto" keyword, create
   * fresh variables with the given base name.  The global flag indicates
   * whether the new variables should be globals.  Returns the new type
   * with the fresh variables substituted, along with a list of the new
   * variables for each bound (given as strings "b" and "e"). *)
  method private makeNewVars (t: typ) (baseName: string)
      : typ * (string * string * typ) list =
    let addedVars : (string * string * typ) list ref = ref [] in
    let bounds = getBoundsAttr t in
    let bounds' =
      mapBounds
        (fun ap suffix ->
           match ap with
           | ACons (n, []) when n = autoKeyword ->
               let name = baseName ^ "__" ^ suffix in
               let t' =
                 typeAddAttributes sentinelAttrs
                   (typeRemoveAttributes ["bounds"] t)
               in
               addedVars := (suffix, name, t') :: !addedVars;
               ACons (name, [])
           | _ -> ap)
        bounds
    in
    setBoundsAttr t bounds', !addedVars


  (* Given a list of suffix/type pairs, where the suffix "b" or "e"
   * indicates the purpose of the type, create a list of expressions that
   * can be used to set these variables of this type to the given low and
   * high bounds appropriately. *)
  method private makeSetExps (addedTypes: (string * typ) list)
                             (lo: exp) (hi: exp) : exp list =
    List.fold_right
      (fun (suffix, rhs) acc ->
         if List.mem_assoc suffix addedTypes then
           (stripNopCasts rhs) :: acc
         else
           acc)
      [("b", lo); ("e", hi)]
      []

  (* Given a list of suffix/lval pairs, where the suffix "b" or "e"
   * indicates the purpose of the lval, create a list of instructions that
   * set these variables to the given low and high bounds appropriately. *)
  method private makeSetInstrs (addedLvals: (string * lval) list)
                               (lo: exp) (hi: exp) : instr list =
    List.fold_right
      (fun (suffix, rhs) acc ->
         try
           let lv = List.assoc suffix addedLvals in
           Set (lv, (stripNopCasts rhs), !currentLoc) :: acc
         with Not_found ->
           acc)
      [("b", lo); ("e", hi)]
      []


  (** Process a type. This is done w.r.t a function that can process new 
   * names. If the function is not given then we use fat pointers (the 
   * default case) *)
  val mutable typeProcessMeta : 
      (string (* base name for makeVars *) *
       (string * string * typ -> unit) (* function to process a meta, with 
                                        * suffix, name, and type. *)
      ) option = None
  method vtype (t: typ) = 
    (* Save the processor as we see this type *)
    let savedProcessor = typeProcessMeta in 
    (* Turn off the processor for nested types, always *)
    typeProcessMeta <- None;

    match unrollType t with 
      TPtr(bt, a) as t' -> begin
        let bt' = visitCilType (self :> cilVisitor) bt in 
        if not (hasAutoBounds t') then 
          if bt' == bt then SkipChildren else ChangeTo (TPtr(bt', a))
        else
          match savedProcessor with 
            None -> 
              (* We just generate the names for the fields *)
              let t'', addedNames = self#makeNewVars (TPtr(bt', a)) "" in
              (* make the structure *)
              let fat : typ = makeFatStruct t'' 
                  (List.map (fun (_, n, t) -> (n, t)) addedNames) in 
              ChangeTo fat
                
          | Some (basename, process) -> 
              let t'', addedNames = self#makeNewVars t' basename in 
              (* process them *)
              List.iter process addedNames;
              ChangeTo t''
      end

    | TArray (bt, leno, a) -> 
        let bt' = visitCilType (self :> cilVisitor) bt in 
        let leno' = 
          match leno with 
            None -> None
          | Some len -> Some (visitCilExpr (self :> cilVisitor) len) 
        in 
        if bt == bt' && leno == leno' then 
          SkipChildren 
        else
          ChangeTo (TArray(bt', leno', a))

      (* Process the function type. This is only invoked for prototypes and 
       * pointers to functions. For function definitions we do the same thing 
       * indirectly by processing the formals *)
    | TFun (rt, formals, isva, a) -> begin
        (* Do the return type *)
        let rt' = visitCilType (self :> cilVisitor) rt in 
        (* Do the formals in expanded form *)

        let formals' = 
          match formals with 
            None -> None
          | Some formals -> begin
              (* Add the formals in the right order, first the data and then 
               * the meta fields. *)
              let formals' : (string * typ * attributes) list ref = ref [] in 
              (* Specify after how many to add. Use negative number for end *)
              let addFormal (after: int) f = 
                let rec loop after = function
                  | rest when after = 0 -> f :: rest
                  | [] -> [f]
                  | f1 :: rest -> f1 :: loop (after - 1) rest
                in
                formals' := loop after !formals'
              in
              
              List.iter
                (fun (fName, fType, fAttrs) -> 
                  (* We never leave the formals in fat form *)
                  let formalMetaProcessor (suff, mname, mtype) = 
                    (* We get here because we have a formal *)
                    (* We better have a name for this formal *)
                    if fName = "" then 
                      E.s (error "Formal with auto-bounds must have name");
                    (* Always add meta formals at end of list *)
                    addFormal (-1) (mname, mtype, []);
                  in
                  typeProcessMeta <- Some (fName, formalMetaProcessor);
                  (* Process the type and add the meta formals *)
                  let placeForDataFormal = List.length !formals' in
                  let fType' = visitCilType (self :> cilVisitor) fType in 
                  typeProcessMeta <- None;
                  (* Add the data formal *)
                  addFormal placeForDataFormal (fName, fType', []);
                )
                
                formals;

              Some !formals'
          end
        in

        ChangeTo (TFun(rt', formals', isva, a))
    end
    | _ -> DoChildren


  (* Process expressions. Normally all expressions that would end up as fat, 
   * are transformed to refer to the data element. This is mostly achieved by 
   * vlval, but we need some special cases done here. *)
  method vexpr e =
    let ve e = visitCilExpr (self :> cilVisitor) e in 
    let vt t = visitCilType (self :> cilVisitor) t in 
    let vl l = visitCilLval (self :> cilVisitor) l in 

    let te e =
      let saveTrustedCode = trustedCode in
      trustedCode <- true;
      let e' = ve e in
      trustedCode <- saveTrustedCode;
      e'
    in
    
    match e with 
    | SizeOfE e' ->
        (* We process sizeof in fat mode, since we want the size of the
         * actual structure, if relevant.  We use 'te' in order to turn
         * on the trusted flag--this code will not actually be executed! *)
        let e2 = getFatFromDataExp (te e') in
        if e2 != e' then ChangeTo (SizeOfE e2) else SkipChildren

    | AlignOfE e' ->
        (* Same as sizeof. *)
        let e2 = getFatFromDataExp (te e') in
        if e2 != e' then ChangeTo (AlignOfE e2) else SkipChildren

    | BinOp ((PlusPI | IndexPI | MinusPI) as bop, e1, e2, t) ->
        (* We must not do the t, or else vtype will change it. *)
        let e1' = ve e1 in 
        let e2' = ve e2 in
        if e1' != e1 || e2' != e2 then 
          ChangeTo (BinOp (bop, e1', e2', typeOf e1'))
        else
          SkipChildren

    | BinOp (bop, e1, e2, t) ->
        if isPointerType t then
          E.s (bug "Unexpected pointer type in non-pointer binop");
        DoChildren

     (* When we take the address of, we take the address of the fat thing *)
    | StartOf lv
    | AddrOf lv -> 
        let lv' = vl lv in
        let lvFat = getFatFromDataLval lv' in 
        if lvFat != lv' && trustedCode then
          E.s (error ("In trusted code, you may not take the address of "
                      ^^"%a, which has auto bounds.") dx_lval lv);
        if lvFat != lv then
          ChangeTo (mkAddrOrStartOf lvFat)
        else 
          SkipChildren

    | CastE (t, e') when trustedCode ->
        (* In trusted code, we make no changes to casts. We still need to
         * process the expression in case reads of auto globals need
         * expansion. *)
        ChangeTo (CastE (t, ve e'))

      (* Handle automatic bounds in casts. We create fresh variables and 
       * assign them based on the expression to be cast. *)
    | CastE (t, e') when hasAutoBounds t -> begin 
        if !curFunc == dummyFunDec then
          E.s (error "Casts in global initializers may not have auto bounds");
        let t = (* FIXME: NTEXPAND macro should set the type *)
          if isNulltermExpand t then
            setTypeAttrs (typeOf e') (nulltermAttr :: typeAttrs t)
          else
            t
        in
        (* Do the type. If it has auto bounds, we make new local variables 
         * for them *)
        let boundLocals: (string * lval) list ref = ref [] in
        let castTypeProcessor (suff, mname, mtype) = 
          let lv = makeHiddenVar !curFunc mname mtype in
          boundLocals := (suff, var lv) :: !boundLocals
        in
        typeProcessMeta <- Some ((self#makeName "cbound"), castTypeProcessor);
        let t' = vt t in 
        typeProcessMeta <- None;
        let e2 = ve e' in
        (* We must create assignments *)
        (* make an instruction, to get the bounds *)
        let instr = Set ((Mem zero, NoOffset), e2, !currentLoc) in 
        let begini, e3, lo, hi, endi = self#getBounds instr t' in
        if endi <> [] then
          E.s (unimp "Post-instructions when processing cast");
        let boundType =
          typeAddAttributes sentinelAttrs (typeRemoveAttributes ["bounds"] t')
	in
	let il =
          self#makeSetInstrs !boundLocals
            (mkCast lo boundType) (mkCast hi boundType)
        in
        self#queueInstr (begini @ il);
        ChangeTo (CastE (t', e3))
    end
        
    | _ -> DoChildren (* The rest are known to be non fat already, because 
                       * all fat have been taken care by vlval *)

  (* Get the data field of lvals *)
  method vlval (lv: lval)  =
    ChangeDoChildrenPost (lv, getDataFromFatLval)



  method vinst i =
    (* We first process the children and then we cleanup, first the calls, 
     * then the Set instructions *)

    
    let processCall (instr: instr) : instr list (* some preamble, already 
                                                 * processed *)
                                   * instr (* replacement instruction *)
                                   = 
      match instr with 
        Call(retlv, func, args, l) -> begin
          let rett, formals =
            match typeOf func with
            | TFun (rett, argInfo, _, _) -> rett, (argsToList argInfo)
            | _ -> E.s (bug "Expected function type")
          in
          (* Deal with the arguments *)
          let (beginInstrs: instr list), (args': exp list) =
            let rec loopArgs (formals: (string * typ * attributes) list)
                             (actuals: exp list) : instr list * exp list = 
              if formals = [] then 
                (* We ran out of formals, a vararg *)
                [], actuals
              else if actuals = [] then 
                (* We ran out of actuals *)
                E.s (error "Function call has too few arguments")
              else begin 
                let (fn: string), (ft: typ), restformals = 
                  match formals with 
                    (fn, ft, _) :: restformals -> fn, ft, restformals
                  | _ -> assert false
                in
                (** See if we have some meta formals that follow *)
                let (metaFormals: (string * typ) list), restformals' = 
                  let rec loopFormals = function
                      [] -> [], []
                    | ((fn1, ft1, _) :: rest) as formals -> 
                        let meta', rest' = loopFormals rest in 
                        (* If fn1 is fn__b or fn__e then it is ours *)
                        if fn1 = fn ^ "__b" then 
                          (("b", ft1) :: meta'), rest'
                        else if fn1 = fn ^ "__e" then 
                          (("e", ft1) :: meta'), rest'
                        else
                          [], formals
                  in
                  loopFormals restformals
                in
                let arg, restactuals' = 
                  match actuals with 
                    arg :: restactuals -> arg, restactuals
                  | _ -> assert false
                in

                (* Process the rest now *)
                let instrs', actuals'' = loopArgs restformals' restactuals' in

                if metaFormals = [] then begin
                  (* Not an auto formal *)
                  instrs', arg :: actuals''
                end else if trustedCode then begin
                  error ("Calling function %a from trusted code.  Trusted code"
                         ^^" is not modified by Deputy, so it may not use"
                         ^^" functions that have auto bounds.") dx_exp func;
                  instrs', arg :: actuals''
                end else begin 
                  (* It was an auto formal. Get the bounds *)
                  (* Dummy instr; the bogus lval will be ignored. *)
                  let instr = Set ((Mem zero, NoOffset), arg, !currentLoc) in
                  let beginInstrs, arg', lo, hi, endInstrs =
                    self#getBounds instr ft
                  in
                  if endInstrs <> [] then
                    E.s (bug "Expected empty endInstrs");
                  beginInstrs @ instrs', 
                  arg' :: self#makeSetExps metaFormals lo hi @ actuals''
                end
              end
            in
            loopArgs formals args
          in
          (* If the return type of the function is fat, then we introduce a 
           * temporary variable *)
          if isFatStructType rett && retlv != None then begin
            let tmp = makeHiddenVar !curFunc (self#makeName "ret") rett in 
            let retlv: lval = 
              match retlv with Some retlv -> retlv | _ -> assert false 
            in
            beginInstrs @ [Call(Some (var tmp), func, args', l)],
            (* Turn the instruction into something that you would get from 
             * preprocessing a set instruction *)
            Set (getDataFromFatLval retlv, 
                 Lval (getDataFromFatLval (var tmp)), l)
          end else
            beginInstrs, Call (retlv, func, args', l)
          end
      | _ -> [], instr
    in

    (* Helpers for processLhs, below. *)
    let makeInstrs ~(isALocal:bool)
                   (addedLvals: (string * lval) list)
                   (instr: instr) (lv: lval) : instr list =
      assert (not trustedCode);  (* Don't modify trusted blocks *)
      let lvType = typeOfLval lv in
      let beginInstrs, e, lo, hi, endInstrs = self#getBounds instr lvType in
      (* We don't need to zero locals; liveness handles this issue for us *)
      let zeroInstrs =
        if isALocal then [] else [Set (lv, zero, !currentLoc)] in
      let setInstrs = self#makeSetInstrs addedLvals lo hi in
      let instr' = Set (lv, e, !currentLoc) in
      beginInstrs @ zeroInstrs @ setInstrs @ [instr'] @ endInstrs
    in

    (* If we're setting a variable with automatic bounds, get the bounds
     * from the RHS and assign the automatic bounds variables. *)
    let processLhs (instr: instr) : instr list =
      (* If lv is a local split variable *)
      let getSplitMetas lv: (string * varinfo) list =  
        match lv with 
          (Var vi, NoOffset) when not vi.vglob -> 
            H.find_all varBounds vi.vname
        | _ -> []
      in
      let lvHasAuto lv: bool =
        ((getSplitMetas lv) <> []) 
        || ((splitFatLval (getFatFromDataLval lv)) <> None)
      in
      match instr with 
      | Set (lv, _, _)
      | Call (Some lv, _, _, _) -> begin
          (* If lv is a local split variable *)
          let splitMetas = getSplitMetas lv in
          if splitMetas <> [] then begin 
            if trustedCode then
              E.s (error ("Trusted block assigns to \"%a\", which has auto"
                     ^^" bounds.  Trusted blocks are not modified by Deputy,"
                     ^^" so they may not use variables that have auto bounds.")
                dx_lval lv);
            makeInstrs ~isALocal:true 
              (List.map (fun (suff, vil) -> (suff, var vil)) splitMetas) 
              instr 
              lv
          end else begin 
            (* See if it this is the data of a fat type *)
            let lvfat = getFatFromDataLval lv in 
            match splitFatLval lvfat with 
              None -> (* Not a fat lval, must be regular lval *)
                [instr]
            | Some (lvdata, lvmeta) -> 
                if trustedCode then
                  E.s (error 
                         ("Trusted code assigns to \"%a\", which has auto "
                          ^^"bounds.  Trusted code is not modified by Deputy, "
                          ^^"so it may not use lvalues that have auto bounds.")
                       dx_lval lv);
                (* Change the instruction to use lvdata instead *)
                let instr' = 
                  match instr with 
                    Set (lv, e, l) -> Set (lvdata, e, l)
                  | Call (Some lv, func, args, l) -> 
                      Call (Some lvdata, func, args, l)
                  | _ -> assert false
                in
                makeInstrs ~isALocal:false lvmeta instr' lvdata
          end
        end
      | Call(None, _, _, _) -> 
          [instr]
      | Asm(_,_,outputs,_,_,_) ->
          List.iter
            (fun (_,_,lv) -> 
               if lvHasAuto lv then begin
                 (* Inline asm modifies something with Deputy-controlled 
                    metadata.  This will cause runtime problems.*)
                 error 
                   "Inline assembly modifies \"%a\", which has auto bounds." 
                   dx_lval lv
               end)
          outputs;
          [instr]
    in

    (* Process the LHS and the RHS separately.  For the RHS, we need to
     * adjust calls whose arguments involve automatic bounds.  For the
     * LHS, we need to handle cases where the LHS of a call or set has
     * automatic bounds. *)
    let postProcessInstrs (instrs: instr list) : instr list =
      match instrs with 
      | [] -> []
      | [instr] ->
          let beginInstrs, instr' = processCall instr in
          beginInstrs @ processLhs instr'
      | _ -> E.s (bug "Expected at most one instruction")
    in
    ChangeDoChildrenPost([i], postProcessInstrs)

  method vstmt (s: stmt) = 
    match s.skind with 
      Return (Some rv, l) -> 
        (* If the return type is fat, then create a new fat local and we copy 
         * the return value in there before we return *)
        if trustedCode then begin
          if isFatStructType currentReturnType then
            E.s (error "Trusted block contains return of fat type");
          DoChildren
        end else if isFatStructType currentReturnType then begin
          (* If the type is fat then we make a new local with the fat type *)
          let newl = makeHiddenVar !curFunc (self#makeName "ret") 
                                   currentReturnType in 
          let newlv = (Var newl, NoOffset) in
          (* make an instruction to assign to the new local *)
          let instr = Set (newlv, rv, !currentLoc) in
          (* process the instruction *)
          let il = visitCilInstr (self :> cilVisitor) instr in 
          self#queueInstr il;
          (* Now we want to return the whole fat thing *)
          s.skind <- Return (Some (Lval (getFatFromDataLval newlv)), l);
          SkipChildren
        end else
          DoChildren

    | _ -> DoChildren

  method vblock (b: block) =
    let saveTrustedCode = trustedCode in
    trustedCode <- saveTrustedCode || isTrustedAttr b.battrs;
    let postProcessBlock (b: block) =
      trustedCode <- saveTrustedCode;
      b
    in
    ChangeDoChildrenPost (b, postProcessBlock)

  (* Handle locals with automatic bounds.  Here we create the new
   * variables and update the type of the corresponding local variable. *)
  method vfunc fd =
    Hashtbl.clear varBounds;
    curFunc := fd;
    trustedCode <- isTrustedType fd.svar.vtype;

      (* We process the formals first. This will fix the type of the function 
       * also. *)    
    let where : string ref = ref "" in (* Where to add the formal *)
    List.iter (fun vi -> 
      let metaForFormal (suff, varName, varType) =
        if vi.vaddrof then 
          E.s (unimp "You cannot take the address of a formal (%s) with auto-bounds. Use a copy\n" vi.vname);

        (* We make the formal, and we put it in all places *)
        let vif = makeFormalVar !curFunc ~where:!where varName varType in
        H.add varBounds vi.vname (suff, vif);
        where := vif.vname
      in
      typeProcessMeta <- Some (vi.vname, metaForFormal);
      where := vi.vname; (* Add the first one right after this one *)
      vi.vtype <- visitCilType (self :> cilVisitor) vi.vtype;
      typeProcessMeta <- None)

      fd.sformals;
    
    if not trustedCode then begin
      (* Now take care of the locals *)
      List.iter
        (fun vi ->
           (* If we take the address of this one, or involved in return, we 
            * leave if fat *)
           let metaForLocal: (string * (string * string * typ -> unit)) option=
             if vi.vaddrof then
               None
             else
               Some (vi.vname, 
                     fun (vSuff, vName, vType) ->
                       let vil = makeHiddenVar !curFunc vName vType in
                       H.add varBounds vi.vname (vSuff, vil))
           in
           typeProcessMeta <- metaForLocal;
           let t' = visitCilType (self :> cilVisitor) vi.vtype in 
           typeProcessMeta <- None;
           vi.vtype <- t')
        fd.slocals;
      
      (* Process the return type *)
      (match fd.svar.vtype with
         TFun(rt, args, isva, l) -> 
           typeProcessMeta <- None;
           let rt' = visitCilType (self :> cilVisitor) rt in
           currentReturnType <- rt';
           fd.svar.vtype <- TFun(rt', args, isva, l)
       | _ -> assert false);
    end;
    

    let cleanup x =
      Hashtbl.clear varBounds;
      curFunc := dummyFunDec;
      trustedCode <- false;
      x
    in
    ChangeDoChildrenPost (fd, cleanup)


  (** process the initializers *)
  method vinit (forg: varinfo) (off: offset) (i: init) = 
    (* The initializers have already been processed. We must turn SingleInit 
     * for fat into CompoundInit *)
    let postInit (i: init) = 
      match i with 
        SingleInit e -> begin 
          let expected_t = typeOffset forg.vtype off in 
          match getFieldsOfFat expected_t with 
            None -> (* Not a fat type *) i
          | Some (fdata, fmetas) -> 
              (* Dummy instr; the bogus lval will be ignored. *)
              let instr = Set ((Mem zero, NoOffset), e, !currentLoc) in
              let beginInstrs, arg', lo, hi, endInstrs =
                self#getBounds instr fdata.ftype
              in
              if beginInstrs <> [] || endInstrs <> [] then 
                E.s (unimp "Processing initializer %a (for %s) requires instructions" d_exp e forg.vname);
              (* Prepare the fmetas for makeSetExps *)
              let addedTypes : (string * typ) list = 
                List.map (fun (suff, f) -> (suff, f.ftype)) fmetas in
              let addedInits: exp list = self#makeSetExps addedTypes lo hi in
              (* Now package the list of initializers *)
              CompoundInit (expected_t, 
                            (Field(fdata, NoOffset), SingleInit e) ::
                            (List.map2
                               (fun (_, fm) i -> 
                                 (Field(fm, NoOffset), SingleInit i))
                               fmetas  
                               addedInits))
        end
      | CompoundInit _ -> i
    in
    ChangeDoChildrenPost (i, postInit)

  method vvdec (vi: varinfo) = 
    (* We preprocess first, to get the new type *)
    let postVar (vi: varinfo) : varinfo = 
      (* see if a type contains or refers to fat pointers *)
      let containsAutoType (t: typ) : bool = 
        existsType 
          (function 
              TComp (ci, _) when H.mem fatStructs ci.cname -> ExistsTrue
            | _ -> ExistsMaybe)
          t
      in
      if vi.vglob && vi.vstorage <> Static then begin
        (* Perhaps the name is already changed *)
        let vil = String.length vi.vname in
        if vil > 7 && String.sub vi.vname (vil - 8) 8 = "__deputy" then 
          (* We already have the mangled name *)
          ()
        else if containsAutoType vi.vtype then 
          vi.vname <- vi.vname ^ "__deputy"
      end;
      vi
    in
    ChangeDoChildrenPost(vi, postVar)

  (* Handle functions, globals, and structures with automatic bounds. *)
  method vglob g =
    preAutoDecls := [];
    ChangeDoChildrenPost([g], 
                         (fun x -> (List.rev !preAutoDecls) @ x))
end


(**************************************************************************)


let needsAnnot (t: typ) : bool =
  isPointerType t &&
  let attrs = typeAttrs t in
  not (hasAttribute "bounds" attrs) &&
  not (hasAttribute "size" attrs)

let isCharPtr (t: typ) : bool =
  match unrollTypeDeep t with
  | TPtr (TInt ((IChar | ISChar | IUChar), _), _) -> true
  | _ -> false

let isCharArray (t: typ) : bool =
  match unrollTypeDeep t with
  | TArray (TInt ((IChar | ISChar | IUChar), _), _, _) -> true
  | _ -> false

(* This visitor is responsible for inferring bound and nullterm
 * annotations when not otherwise provided by the programmer.  We use the
 * results from CCured's inference for locals, and we guess annotations
 * for globals, function parameters, and structure fields. *)
let inferVisitor = object (self)
  inherit nopCilVisitor

  (* Keep track of vars that didn't have a programmer-supplied anntoation. *)
  val mutable unannotatedVars : varinfo list = []

  (* Builtins can appear in the code without a preceding declaration,
   * so we make sure to check out their types too. *)
  method vvrbl v =
    v.vtype <- visitCilType self v.vtype;
    DoChildren

  (* This is the catchall case.  If a type has not otherwise been assigned
   * a type (e.g., by CCured inference), then guess. *)
  method vtype t =
    let postProcessType (t: typ) =
      if needsAnnot t then
        let newAnnots =
          if !assumeString && isCharPtr t then
            stringAttrs
          else
            [safeAttr]
        in
        typeAddAttributes (missingAnnotAttr :: newAnnots) t
      else if isArrayType t then
        match unrollType t with
        | TArray (_, Some e, a) ->
            let n =
              match isInteger (constFold true e) with
              | Some n -> to_int n
              | None -> E.s (bug "Array length could not be determined")
            in
            let n' =
              if isNullterm t then 
                if n = 0 then begin
                  error "Cannot have nullterm array with zero length.";
                  0
                end else
                  n - 1
              else
                n
            in
            if not (hasAttribute "bounds" a) || n' > 0 then
              typeAddAttributes [countAttr (AInt n')]
                (typeRemoveAttributes ["bounds"] t)
            else
              t
        | TArray (_, None, a) ->
	    if not (hasAttribute "bounds" a) then
              typeAddAttributes [count0Attr] t
            else
              t
        | _ -> E.s (bug "Expected array type")
      else
        t
    in
    ChangeDoChildrenPost (t, postProcessType)

  (* Infer annotations for types in casts. *)
  method vexpr e =
    (* Assign string constants to a temporary variable that is exempt from
     * Deputy checks.  The reason is that two identical string constants
     * may not always evaluate to the same address; thus, when adding
     * checks on such variables, we need to make sure that we refer to the
     * same address in all parts of the check. *)
    let fixStr (t: typ) (length: int) : exp =
      (* Add a temp with annotation NT COUNT(stringlen) *)
      let lengthAttr = countAttr (AInt length) in
      let t = typeAddAttributes [lengthAttr; nulltermAttr] t in
      let tmp = makeTempVar !curFunc ~name:"__fixstr_tmp" t in
      addTempInfoSet tmp e;
      DC.exemptLocalVars := tmp :: !DC.exemptLocalVars;
      self#queueInstr [Set (var tmp, e, locUnknown)];
      Lval (var tmp)
    in
    let e' =
      match e with
      | Const (CStr str) when !curFunc != dummyFunDec ->
          (* JC: We use charPtrType instead of (typeOf e) because the
           * latter results in lots of warnings relating to const casts. *)
          fixStr charPtrType (String.length str)
      | Const (CWStr wchars) when !curFunc != dummyFunDec ->
          fixStr (TPtr (!wcharType, [])) (List.length wchars)

        (* All trusted types are converted to auto types.  This change is
         * necessary because the TC macro uses typeof(), which can
         * otherwise introduce invalid annotations. *)
      | CastE (t, e') when isPointerType t && isTrustedType t &&
                           !curFunc != dummyFunDec ->
          let t' =
            typeAddAttributes [autoAttr] (typeRemoveAttributes ["bounds"] t)
          in
          CastE (t', e')

      | CastE (t, e') when isNulltermExpand t && !curFunc != dummyFunDec ->
          let bt, a = getPointerType t "the cast" in
          let a = dropAttribute "bounds" a in
          mkCast e' (TPtr (bt, addAttribute autoEndAttr a))
      | CastE (t, e') when needsAnnot t && !curFunc != dummyFunDec ->
          (* Make sure we're not casting from a trusted pointer. *)
          if isTrustedType (typeOf e') then
            error ("Target of trusted cast must have user-supplied bounds:\n" ^^
                   "  from: %a\n" ^^
                   "    to: %a\n" ^^
                   "   exp: %a")
                   dt_type (typeOf e') dt_type t dx_exp e';
          (* First adjust the type for void* polymorphism. *)
          let bt, a = getPointerType t "the cast" in
          let a = dropAttribute "bounds" a in
          (* Now see if we need to add an annotation. *)
          let kind, _ = N.inferredKindOf a in
          let a =
            if N.kindIsNullterm kind && not (hasAttribute "nullterm" a) then
              addAttribute nulltermAttr a
            else 
              a
          in
          begin
            match kind with 
            | N.Safe when not (isVoidPtrType (typeOf e')) &&
                          not (isTrustedType t) -> 
                mkCast e' (TPtr (bt, addAttribute safeAttr a))

            | N.Sentinel ->
                mkCast e' (TPtr (bt, addAttribute count0Attr a))
            | N.String when not (isNulltermExpand t) ->
                mkCast e' (TPtr (bt, addAttribute count0Attr a))
            | N.FSeq | N.FSeqN ->
                mkCast e' (TPtr (bt, addAttribute autoEndAttr a))
            | _ ->
                mkCast e' (TPtr (bt, addAttribute autoAttr a))
          end
      | _ -> e
    in
    ChangeDoChildrenPost (e', (fun e -> e))

  (* Make sure the left-hand side of a TC is fully annotated. *)
  method vinst i =
    let check (vi: varinfo) (t: typ) : unit =
      if List.memq vi unannotatedVars && isTrustedType t then
        error "Target \"%s\" of trusted cast must have user-supplied bounds" 
          vi.vname
    in
    begin
      match i with
      | Set ((Var vi, NoOffset), e, _) -> check vi (typeOf e)
      | Call (Some (Var vi, NoOffset), fn, _, _) ->
          begin
            match typeOf fn with
            | TFun (t, _, _, _) -> check vi t
            | _ -> E.s (bug "Expected function with non-void return value")
          end
      | _ -> ()
    end;
    DoChildren

  (* Infer annotations for local variables. *)
  method vfunc fd =
    assert (unannotatedVars = []);
    if isTrustedType fd.svar.vtype then begin
      (* Visit the return type and formals.  This is mostly just to get SAFE
         added in the right places. *)
      fd.svar.vtype <- visitCilType self fd.svar.vtype;

      let newformals = mapNoCopy (visitCilVarDecl self) fd.sformals in
      (* Make sure the type reflects the formals *)
      setFormals fd newformals;

      SkipChildren
    end
    else begin
    curFunc := fd;
    List.iter
      (fun vi ->
         if isPointerType vi.vtype then begin
           (* First adjust the type for void* polymorphism. *)
           let bt, a = getPointerType vi.vtype vi.vname in
           vi.vtype <- TPtr (bt, a);
           (* Now see if we need to add an annotation. *)
           let kind, _ = N.inferredKindOf a in
           if hasAttribute "bounds" a || hasAttribute "size" a then begin
             if N.kindIsNullterm kind &&
                not (hasAttribute "nullterm" a) &&
                not (hasAttribute "sentinel" a) then begin
               warn "Marking variable %s as null-terminated" vi.vname;
               vi.vtype <- TPtr (bt, addAttribute nulltermAttr a)
             end
           end else begin
             if not (isTrustedType vi.vtype) then
               unannotatedVars <- vi :: unannotatedVars;
             let a =
               if N.kindIsNullterm kind && not (hasAttribute "nullterm" a) then
                 addAttribute nulltermAttr a
               else 
                 a
             in
             match kind with 
             | N.Safe -> (* No bound vars needed. *)
                 vi.vtype <- TPtr (bt, addAttribute safeAttr a)
             | N.String | N.Sentinel -> (* No bound vars needed. *)
                 vi.vtype <- TPtr (bt, addAttribute count0Attr a)
             | N.FSeq | N.FSeqN -> (* Automatic bounds for end only. *)
                 vi.vtype <- TPtr (bt, addAttribute autoEndAttr a)
             | N.Seq | N.SeqN -> (* Automatic bounds for base and end. *)
                 vi.vtype <- TPtr (bt, addAttribute autoAttr a)
             | N.Unknown | N.UnknownN -> 
                 (bug "bad kind returned by inferredKindOf for %a"
                    dx_type vi.vtype);
                 ()
           end
         end else if isArrayType vi.vtype then begin
           (* For arrays, we infer nullterm if one of two conditions holds:
            * 1. It's a char array and we're assuming all such arrays are
            *    null-terminated, or
            * 2. It was inferred nullterm by the inference engine *)
           let a = typeAttrs vi.vtype in
           if ((!assumeString && isCharArray vi.vtype) ||
               N.kindIsNullterm (fst (N.inferredKindOf a))) &&
              not (hasAttribute "nullterm" a) then
             vi.vtype <- typeAddAttributes [nulltermAttr] vi.vtype
         end)
      fd.slocals;
    List.iter
      (fun vi ->
         if isPointerType vi.vtype &&
            not (hasAttribute "bounds" (typeAttrs vi.vtype)) then begin
           match getZeroOneAttr ["arraylen"] (typeAttrs vi.vtype) with
           | Some (Attr (_, [a])) ->
               vi.vtype <- typeAddAttributes [countAttr a] vi.vtype
           | Some _ -> errorwarn "Malformed arraylen attribute."
           | None -> ()
         end)
      fd.sformals;
    let cleanup fd =
      curFunc := dummyFunDec;
      unannotatedVars <- [];
      fd
    in
    ChangeDoChildrenPost (fd, cleanup)
    end
end


(**************************************************************************)

let strncpy_proto: varinfo option ref = ref None

(* This visitor does some simple pre-processing prior to inference and
 * type checking. *)
let preProcessVisitor = object (self)
  inherit nopCilVisitor

  method vglob g =
    (* Look for a strncpy prototype *)
    (match g with
       GVarDecl(vi, _)
     | GFun({svar = vi}, _) when vi.vname = "strncpy" ->
         strncpy_proto := Some vi
     | _ -> ()
    );
    DoChildren

  method vtype t =
    let t' = unrollType t in
    let attrs = typeAttrs t' in
    if (hasAttribute "bound" attrs || hasAttribute "nullterm" attrs) &&
       not (isPointerType t') && not (isArrayType t') then
      E.s (error "Deputy annotations cannot be placed on this type");
    match t with
    | TNamed (ti, a) ->
        (* Unroll unannotated typedefs. *)
        if hasAttribute "bounds" (typeAttrs ti.ttype) then
          DoChildren
        else
          ChangeTo t'
    | _ -> DoChildren

  method vexpr e =
    let post e : exp =
      match e with
      | AddrOf lv ->
          (* Change AddrOf of an array to a StartOf,
             and optimize &*e to e. *)
          mkAddrOrStartOf lv
      | _ -> e
    in
    ChangeDoChildrenPost(e, post)

  (* If the RHS of an instruction refers to a variable that is modified in
   * the LHS, introduce a temporary.  Later, autoVisitor will assume that
   * a variable appearing on the LHS does not also appear on the RHS.
   * We also spread the trusted attribute to CIL-introduced temporaries
   * on the LHS of a call (see trusted12.c). *)
  method vinst i = 
    let postProcessInstr (instrs: instr list) : instr list =
      List.fold_right
        (fun instr acc ->
           let needsTemp (instr: instr) : bool =
             match instr with
             | Call _ ->
                 (* Processing the call will introduce a temporary, so an
                  * additional one is not needed. *)
                 false
             | Set ((Var vi, NoOffset), e, _) ->
                 (* We only need a temp if we might have automatic bounds
                  * and if the RHS refers to the variable. *)
                 isPointerType vi.vtype && expRefersToVar vi.vname e
             | Set (lv, _, _) ->
                 (* For an LHS other than a variable, automatic bounds
                  * must already be indicated by the programmer. *)
                 let t = typeOfLval lv in
                 hasAttribute "bounds" (typeAttrs t) && hasAutoBounds t
             | Asm _ ->
                 false
           in
           let needsTrusted (instr: instr) : bool =
             match instr with
             | Call (Some (Var vi, NoOffset), fn, _, _) ->
                 let rtype =
                   match unrollType (typeOf fn) with
                   | TFun (rtype, _, _, _) -> rtype
                   | _ -> E.s (bug "Expected function type.")
                 in
                 vi.vdescr <> nil && isTrustedType rtype
             | _ -> false
           in
           let getLhs (instr: instr) : lval =
             match instr with
             | Set (lv, _, _) -> lv
             | Call (Some lv, _, _, _) -> lv
             | Call (None, _, _, _) -> E.s (bug "Expected return for call")
             | Asm _ -> E.s (bug "Unexpected asm instruction")
           in
           let setLhs (instr: instr) (lv: lval) : instr =
             match instr with
             | Set (_, e, l) -> Set (lv, e, l)
             | Call (Some _, fn, args, l) -> Call (Some lv, fn, args, l)
             | Call (None, _, _, _) -> E.s (bug "Expected return for call")
             | Asm _ -> E.s (bug "Unexpected asm instruction")
           in
           let getRhsType (instr: instr) : typ =
             match instr with
             | Set (_, e, _) -> typeOf e
             | Call (_, fn, _, _) ->
                 begin
                   match typeOf fn with
                   | TFun (t, _, _, _) -> t
                   | _ -> E.s (bug "Expected function type")
                 end
             | Asm _ -> E.s (bug "Unexpected asm instruction")
           in
           if needsTemp instr then
             let lv = getLhs instr in
             let t = typeRemoveAttributes
	               ["bounds"; "nonnull"; "warn_unused_result"]
                       (typeOfLval lv) in
             let t' =
               if isTrustedType (getRhsType instr) then
                 typeAddAttributes [Attr ("trusted", [])] t
               else
                 t
             in
             let tmp = makeTempVar !curFunc ~name:"__bnd_tmp" t' in
             begin
               match instr with
               | Set (_, e, _) -> addTempInfoSet tmp e
               | Call (_, fn, args, _) -> addTempInfoCall tmp fn args
               | Asm _ -> E.s (bug "Unexpected asm instruction")
             end;
             (setLhs instr (var tmp)) ::
               Set (lv, Lval (var tmp), !currentLoc) ::
               Set (var tmp, zero, !currentLoc) ::
               acc
           else begin
             if needsTrusted instr then begin
               match getLhs instr with
               | Var vi, NoOffset ->
                   vi.vtype <- typeAddAttributes [trustedAttr] vi.vtype
               | _ -> E.s (bug "Unexpected LHS.")
             end;
             instr :: acc
           end)
        instrs
        []
    in
    let i' : instr list = 
      match i with
        (* strcpy is not permitted in Deputy programs.
         * Here, we transform strcpy(dest, "literal")  into
         *
         *              strncpy(dest, "literal", len);
         *              dest[len] = 0;
         *                     where len = (sizeof("literal")-1)
         * TODO: Maybe we should do this for non-literals as well?  But
         * there's a perf cost to calling strlen.  For now, we'll only do it
         * for literals. *)
      | Call (lvo, Lval (Var vf, NoOffset), [dest; src], loc) 
          when vf.vname = "strcpy" -> begin
            match stripNopCasts src with
              Const(CStr s) -> begin
                let len = integer(String.length s) in
                let last_ptr = BinOp (PlusPI, 
                                      mkCast dest charPtrType,
                                      len,
                                      charPtrType) in
                let last_lv = (Mem last_ptr), NoOffset in
                match !strncpy_proto with
                  Some strncpy -> 
                    [Call(lvo, Lval(var strncpy), [dest; src; len], loc);
                     Set(last_lv, zero, loc)
                    ]
                | None -> 
                    warn ("Could not transform strcpy() to strncpy() " ^^
                          "because strncpy() declaration was not found.");
                    [i]
              end
            | _ -> 
                (* The source is not a literal.  Leave it alone;
                   this is reported as an error later. *) 
                [i];
          end
      | _ -> [i]
    in
    match i with
      Call(_, f, _, _) when isVarargOperator f -> 
          (* Don't mess with the arguments to e.g.  __builtin_va_arg *)
          SkipChildren
    | _ -> 
        ChangeDoChildrenPost (i', postProcessInstr)

  method vfunc fd =
    curFunc := fd;
    let cleanup fd =
      curFunc := dummyFunDec;
      fd
    in
    ChangeDoChildrenPost (fd, cleanup)
end


(***************************************************************)


(* This visitor makes array type declarations consistent.  Empty array
 * bounds in extern globals are converted to zeros.  Zero array bounds at
 * the end of a structure are converted to empty bounds.  All other
 * appearances of empty array bounds are illegal.
 *
 * From this point forward, the only empty array bounds should be an
 * indication of an open array at the end of a structure. *)
let flexibleArrayVisitor = object (self)
  inherit nopCilVisitor

  method vtype t =
    match t with
    | TArray (_, None, _) -> E.s (error "Illegal use of flexible array")
    | _ -> DoChildren

  method vglob g =
    match g with
    (* Rewrite bounds for structures ending in a zero-length array. *)
    | GVarDecl (vi, _) when vi.vstorage = Extern ->
        begin
          match unrollType vi.vtype with
          | TArray (bt, None, a) ->
              (* This is always an error; if the array were unused then
               * Rmtmps would have deleted it.
               * Without this, we get unhelpful errors about 
               * arrays with length 0 or -1. *)
              if not (hasBoundsAttr vi.vtype) 
                && not (isTrustedType vi.vtype) then
                error ("Global array %s needs a length annotation "
                       ^^"(e.g. COUNT or NTS)") vi.vname;
              let e = if isNullterm vi.vtype then one else zero in
              vi.vtype <- TArray (bt, Some e, a);
              DoChildren
          | _ -> DoChildren
        end
    (* Rewrite bounds for extern globals with emtpy bounds. *)
    | GCompTag (ci, _) when List.length ci.cfields > 1 ->
        let _, fi = remove_last ci.cfields in
        let fixup bt a g = fi.ftype <- TArray (bt, None, a); g in
        begin
          match unrollType fi.ftype with
          | TArray (bt, Some z, a) when isZero z ->
              (* Fix the type on the way up so as not to trigger the
               * "illegal use" warning above. *)
              ChangeDoChildrenPost ([g], fixup bt a)
          | TArray (bt, None, a) ->
              (* Change the type temporarily so as not to trigger the
               * "illegal use" warning above. Fix it on the way up. *)
              fi.ftype <- TArray (bt, Some zero, a);
              ChangeDoChildrenPost ([g], fixup bt a)
          | _ -> DoChildren
        end
    | _ -> DoChildren
end


(***************************************************************)


(* This visitor handles the copytype attribute, which says that the
 * associated void* should be changed to hold the type of the source
 * for this cast expression.  This feature is used to implement the
 * TC, NTDROP, and NTEXPAND macros. *)
let copyTypeVisitor = object (self)
  inherit nopCilVisitor

  method vexpr e =
    let postProcessExpr e =
      match e with
      | CastE (TPtr (TVoid [], a), e') when hasAttribute "copytype" a ->
          let bt =
            match unrollType (typeOf e') with
            | TPtr (bt, _) -> bt
            | _ -> TVoid []
          in
          CastE (TPtr (bt, dropAttribute "copyType" a), e')
      | _ -> e
    in
    ChangeDoChildrenPost (e, postProcessExpr)
end


(***************************************************************)
(*   Combine the prepasses                                     *)
(***************************************************************)


let preProcessFile (f : file) =
  let doPreprocess () = 
    if !verbose then
      log "preprocess file (dinfer)";

    (* Create a decl for "__deputy_memset". *)
    f.globals <- GVarDecl(memset, locUnknown) :: f.globals;

    List.iter
      (fun global ->
         match global with
           | GVar (vi, _, _)
           | GVarDecl (vi, _) when not (isFunctionType vi.vtype)->
               if not (List.memq vi !allGlobalVars) then begin
                 registerGlobal vi
               end
           | _ -> ())
      f.globals;
    if !verbose then
      log "preprocess visitor (dinfer)";
    visitCilFileSameGlobals copyTypeVisitor f;
    visitCilFileSameGlobals flexibleArrayVisitor f;
    visitCilFileSameGlobals preProcessVisitor f;
  in
  Stats.time "preprocessing" doPreprocess ()

let preProcessFileAfterMarking (f : file) =
  let doPreprocess () = 
    if !verbose then
      log "infer visitor (dinfer)";
    visitCilFileSameGlobals inferVisitor f;

    H.clear fatStructs;
    if !verbose then
      log "auto visitor (dinfer)";
    visitCilFile autoVisitor f;
    H.clear fatStructs;

    if !verbose then
      log "finished preprocessing (dinfer)";
  in
  Stats.time "preprocessing" doPreprocess ()


(**************************************************************************)
(*   Post pass                                                            *)
(**************************************************************************)

let numChecksAdded: int ref = ref 0
let numChecksAddedVar: varinfo option ref = ref None

let postPassVisitor = object (self)
  inherit nopCilVisitor
    
  method vinst i =
    (match instrToCheck i with
       Some _ -> incr numChecksAdded
     | None -> ());
    DoChildren
      
  method vglob g =
    match g with
      GVarDecl(vi, _) when vi.vname = "DEPUTY_NUM_CHECKS_ADDED" ->
        numChecksAddedVar := Some vi;
        DoChildren
    | GVarDecl(vi, _) when vi == memset ->
        (* Filter out the decl of __deputy_memset.  This is declared in
           checks.h *)
        ChangeTo []
    | _ -> DoChildren

  
  (* Remove any "bounds" or "fancybounds" annotations. *)
(*
  method vattr a =
    if isDeputyAttr a then
      ChangeTo []
    else
      DoChildren
*)

  (* Replace gratuitous blocks and instruction sequences *)
  (* matth: only move statements with no labels.  If you want to clean up blocks
     with labels, you must patch up goto statements.  See r9295 and earlier
     for the version of this code that moved labels around correctly but
     did not patch gotos. *)
  method vblock (b: block) : block visitAction =
    (* See if there are nested Blocks *)
    let postProcessBlock b =
      let rec loop (bl: stmt list) : stmt list =
        match bl with
        | [] -> []
        | {skind=Block b';labels=[]} :: brest when b'.battrs == [] -> begin
            (* Move the labels from the statement into the first statement *)
            loop (Util.list_append b'.bstmts brest)
	end
        | {skind=Instr [];labels=[]} :: brest ->
            loop brest

	| ({skind=Switch(e,b,sl,loc); labels=[]} as s) :: brest -> begin
	    let slp = loop b.bstmts in
	    b.bstmts <- slp;
	    s.skind <- Switch(e,b,sl,loc);
	    
	    (s :: (loop brest))
	end

        | s :: brest ->
            let brest' = loop brest in
            if brest' == brest then
              bl
            else
              (s :: brest')
      in
      b.bstmts <- loop b.bstmts;
      b
    in
    ChangeDoChildrenPost (b, postProcessBlock)

end

class deputyAttrRemoverClass = object(self)
    inherit nopCilVisitor

  (* Remove any "bounds" or "fancybounds" annotations. *)
  method vattr a =
    if isDeputyAttr a then
      ChangeTo []
    else
      DoChildren
end

let removeDeputyAttributes (f : file) : unit =
    visitCilFile (new deputyAttrRemoverClass) f

(**************************************************************************)



let postProcessFile (f : file) =
  (* Turn the check datastructure into explicit checks, so that they show up
     in the output. *)
  if !verbose then
    log "postprocess file (dinfer)";
  (*if !optLevel >= 3 then
    S.time "deadcode-elim" DO.deadCodeElim f;*)
  visitCilFile postPassVisitor f;
  let numChecksAddedGlobal = match !numChecksAddedVar with
      (* Was DEPUTY_NUM_CHECKS_ADDED declared in this file?  If so, replace
         the declaration with a definition.  (If the var is missing, that's
         because it was unused and CIL deleted it.) *)
      Some vi -> 
        vi.vstorage <- Static;
        GVar(vi, {init = Some (SingleInit(integer !numChecksAdded))}, vi.vdecl)
    | None -> GText ""
  in
  f.globals <- (GText ((if !alwaysStopOnError then "#define" else "#undef") ^ 
                       " DEPUTY_ALWAYS_STOP_ON_ERROR")) ::
               (GText ((if !fastChecks then "#define" else "#undef") ^ 
                       " DEPUTY_FAST_CHECKS")) ::
               numChecksAddedGlobal ::
               (GText ("#include <" ^ !deputyChecksFile ^ ">\n\n"))::f.globals;
  if !insertFLIDs <> "" then DT.insert_flids f;
  (*if not(Check.checkFile [] f) then
    E.s(error "Check.checkFile failed!");*)
  (* this is done in main.ml:
     if !Ivyoptions.stats then S.print stdout "optimizer-stats:" *)
  ()
