(*
 *
 * Copyright (c) 2001-2006, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
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
open Pretty

module H = Hashtbl
module IH = Inthash
module E = Errormsg

module N = Ptrnode

(* We will accumulate the marked globals in here *)
let theFile: global list ref = ref []

let lu = locUnknown
let verbose = Ivyoptions.verbose

let currentFile = ref dummyFile
let currentFunction: fundec ref = ref dummyFunDec
let currentResultType = ref voidType

let noStackOverflowChecks = ref false

(* Remember the structures we have marked already. This way we detect forward 
 * references *)
let markedCompInfos: unit IH.t = IH.create 17

(* Remember the nodes for which the PointsTo information is unreliable 
 * because they point to forward-declared structures *)
let mustRecomputePointsTo: N.node IH.t = IH.create 17

let callId = ref (-1)  (* Each call site gets a new ID *)

let allocFunctions: (string, unit) H.t = H.create 17

(* weimer: utility function to ease the transition between our flag formats *)
let setPosArith n why = N.setFlag n N.pkPosArith why
let setArith n why = N.setFlag n N.pkArith why 
let setUpdated n why = N.setFlag n N.pkUpdated why
let setIntCast n why = N.setFlag n N.pkIntCast why
let setInterface n why = N.setFlag n N.pkInterface why
let setNoProto n why = N.setFlag n N.pkNoPrototype why
let setString n why = N.setFlag n N.pkString why 
let setReferenced n why = N.setFlag n N.pkReferenced why
let setEscape n why = N.setFlag n N.pkEscape why
let setStack n why = N.setFlag n N.pkStack why
let default_why () = N.ProgramSyntax(!currentLoc) 

(* We keep track of a number of type that we should not unroll *)
let dontUnrollTypes : (string, bool) H.t = H.create 19

let rec mustUnrollTypeInfo (ti: typeinfo) : bool = 
  (not (H.mem dontUnrollTypes ti.tname)) &&
  (match ti.ttype with 
  | TPtr _ -> true
  | TArray _ -> true
  | TFun _ -> true
  | TNamed (ti', _) -> mustUnrollTypeInfo ti'
  | _ -> false)


(* if some enclosing context [like the attributes for a field] says that
 * this array should be sized ... we do not want to forget it! *)
let addArraySizedAttribute arrayType enclosingAttr =
  if filterAttributes "sized" enclosingAttr <> [] then
    typeAddAttributes [Attr("sized",[])] arrayType
  else
    if hasAttribute "safeunion" enclosingAttr then
      typeAddAttributes [Attr("safeunion",[])] arrayType
    else
      arrayType

(* Grab the node from the attributs of a type. Returns dummyNode if no such 
 * node *)
let nodeOfType : typ -> N.node =
    (fun t ->
       match unrollType t with 
         TPtr(_, a) -> begin
           match N.nodeOfAttrlist a with
             Some n -> n
           | None -> N.dummyNode
         end
       | _ -> N.dummyNode)

(* Pass also the place and the next index within the place. Returns the 
 * modified type and the next ununsed index *)
let rec doType (t: typ) (p: N.place) 
               (nextidx: int) : typ * int = 
  match t with 
    (TVoid _ | TInt _ | TFloat _ | TEnum _ ) -> t, nextidx
  | TBuiltin_va_list _ -> t,nextidx
  | TPtr (bt, a) -> begin
      match N.nodeOfAttrlist a with
        Some n -> TPtr (bt, a), nextidx (* Already done *)
      | None -> 
          let bt', i' = doType bt p (nextidx + 1) in
          let n = N.getNode p nextidx bt' a in
          (* See if the bt is a forward referenced TComp *)
          (match unrollType bt with 
            TComp(ci, _) when not (IH.mem markedCompInfos ci.ckey) -> 
              IH.add mustRecomputePointsTo n.N.id n

          | _ -> ());
          TPtr (bt', n.N.attr), i'
  end
  | TArray (bt, len, a) -> begin
      (* wes: we want a node for the array, just like we have a node for
       * each pointer *)
      match N.nodeOfAttrlist a with
        Some n -> TArray (bt, len, a), nextidx (* Already done *)
      | None -> 
          let bt', i' = doType bt p (nextidx + 1) in
          let n = N.getNode p nextidx bt' a in
          n.N.is_array <- true;
          TArray (bt', len, n.N.attr), i'
  end
          
  | TComp (c, at) ->
      t, nextidx (* A reference to a regular composite type, leave alone *)

    (* Strip the type names so that we have less sharing of nodes. However, 
     * we do not need to do it if the named type is a structure, and we get 
     * nicer looking programs. We also don't do it for base types *)
  | TNamed (bt, a) -> 
      if mustUnrollTypeInfo bt then begin
        let t = typeAddAttributes a bt.ttype in
        let t', nextidx' = doType t p nextidx in
        t', nextidx'
      end else
        (* A type reference. Leave alone. We'll handle the type inside when 
         * we do the GType *)
        t, nextidx
        
  | TFun (restyp, args, isva, a) -> 
      let noproto = hasAttribute "missingproto" a in
      let restyp = 
        if noproto && not (isPointerType restyp) then 
          voidPtrType
        else restyp 
      in
      let restyp', i0 = doType restyp p nextidx in
      let args', i' = match args with 
        None -> None, i0
      | Some argl -> 
          let argl', i' =  
            List.fold_left 
              (fun (args', nidx) (an, at, aa) -> 
                let t', i' = doType at p nidx in
                ((an,t',aa) :: args', i')) ([], i0) argl 
          in
          Some (List.rev argl'), i'
      in
      let newtp = TFun(restyp', args', isva, a) in
      let newtp' = Dvararg.processFormatAttribute newtp in 
      newtp', i'

and doField (f: fieldinfo) : N.node = 
  let fftype = addArraySizedAttribute f.ftype f.fattr in 
  let t', i' = doType fftype (N.PField f) 1 in
  (* Now create the node corresponding to the address of the field *)
  let nd = N.newNode (N.PField f) 0 t' f.fattr in
  f.fattr <- addAttributes f.fattr nd.N.attr ; 
  f.ftype <- t';
  nd
  
    
(** This is called once for each compinfo DEFINITION. Do not call for 
 * declarations. It will process the fields and will add the nodes 
 * corresponding to the address of the fields. *)
and markCompInfo (comp: compinfo) (comptagloc: location) : unit = 
  (* We must do its fields *)
  List.iter (fun f -> ignore (doField f)) comp.cfields;
  (* Keep track of the compinfo we have done. We do this after we have done 
   * the fields, just in case some of the fields refer to the whole structure.
   *)
  IH.add markedCompInfos comp.ckey ()

(* Create a field successor. Just get the node from the field attributes. 
 * Also add an EOFFSET edge from the pointer to struct to pointer to field. *)
let fieldOfNode (n: N.node) (fi: fieldinfo) : N.node =
  if N.useOffsetNodes then begin
    (* Make a new node *)
    let fieldn = N.getNode (N.POffset (n.N.id, fi.fname)) 0 fi.ftype [] in
    (* And add the ESafe edge *)
    let _ = N.addEdge n fieldn N.EOffset (Some !currentLoc) in 
    fieldn
  end else begin
    (* In the original scheme we have one node for the address of a field. 
     * The problem with this is that it is shared to much and contributes to 
     * the spreading of WILDness *)
    match N.nodeOfAttrlist fi.fattr with
      Some fieldn -> 
        (* Add an EOffset edge from n to fieldn *)
        let _ = N.addEdge n fieldn N.EOffset (Some !currentLoc) in 
        fieldn
          
    | None -> 
        (* We should have created nodes for all fieldinfo *)
        E.s (bug "Field %s.%s does not have a node"
               (compFullName fi.fcomp) fi.fname)
  end

let startOfNode (n: N.node) : N.node =
  match unrollType n.N.btype with
    TArray (bt, len, a) -> 
      let next = 
        match N.nodeOfAttrlist a with
          Some oldn -> oldn
        | _ -> E.s (bug "Array type does not have a node")
      in              
      let _ = N.addEdge n next N.EIndex (Some !currentLoc) in 
      next

  | _ -> n (* It is a function *)



(* Compute the sign of an expression. Extend this to a real constant folding 
 * + the sign rule  *)
type sign = SPos | SNeg | SAny | SLiteral of int64

let rec signOf = function
    Const(CInt64(n, _, _)) -> SLiteral n
  | Const(CChr c) -> signOf (Const (charConstToInt c))
  | SizeOf _ -> SPos (* We do not compute it now *)
  | UnOp (Neg, e, _) -> begin
      match signOf e with
        SPos -> SNeg
      | SLiteral n -> SLiteral (Int64.neg n)
      | SNeg -> SNeg
      | _ -> SAny
  end
  | UnOp (LNot, e, _) -> SPos
  | BinOp (PlusA, e1, e2, _) -> begin
      match signOf e1, signOf e2 with
        SPos, SPos -> SPos
      | SLiteral n, SPos when n >= Int64.zero -> SPos
      | SPos, SLiteral n when n >= Int64.zero -> SPos
      | SLiteral n1, SLiteral n2 -> SLiteral (Int64.add n1 n2)
      | SNeg, SNeg -> SNeg
      | SLiteral n, SNeg when n <= Int64.zero -> SNeg
      | SNeg, SLiteral n when n <= Int64.zero -> SNeg
      | _ -> SAny
  end
  | BinOp (MinusA, e1, e2, _) -> begin
      match signOf e1, signOf e2 with
        SPos, SNeg -> SPos
      | SLiteral n, SNeg when n >= Int64.zero -> SPos
      | SPos, SLiteral n when n <= Int64.zero -> SPos
      | SLiteral n1, SLiteral n2 -> SLiteral (Int64.sub n1 n2)
      | SNeg, SPos -> SNeg
      | SLiteral n, SPos when n <= Int64.zero -> SNeg
      | SNeg, SLiteral n when n >= Int64.zero -> SNeg
      | _ -> SAny
  end
  | _ -> SAny


(* Handle Deputy's allocator annotation. *)
let doAlloc (vi : varinfo) : unit =
  let attrs = typeAttrs vi.vtype in
  if hasAttribute "dalloc" attrs || hasAttribute "drealloc" attrs then
    H.add allocFunctions vi.vname ()

(* Handle Deputy's memcpy, memset, and memcmp annotations. We need to add
 * appropriate kinds for these for the inference to work properly. *)
let doMemcpy (varAttrs : attributes) (varType : typ) : unit =
  match unrollType varType with
  | TFun (_, Some args, _, attrs) ->
      if hasAttribute "dmemcpy" attrs ||
         hasAttribute "dmemcmp" attrs ||
         hasAttribute "dmemset" attrs then
        List.iter
          (fun (_, argType, _) ->
             match N.nodeOfAttrlist (typeAttrs argType) with
             | Some n ->
                 n.N.kind <- N.FSeq;
                 n.N.why_kind <- N.UserSpec
             | None -> ())
          args
  | _ -> ()

(* Do varinfo. We do the type and for all variables we also generate a node 
 * that will be used when we take the address of the variable (or if the 
 * variable contains an array) *)
let doVarinfo (vi: varinfo) : unit = 
  (* Compute a place for it *)
  let original_location = !currentLoc in (* weimer: better places *)
  if vi.vdecl != locUnknown then 
    currentLoc := vi.vdecl; 
  let place = 
    if vi.vglob then
      if vi.vstorage = Static then 
        N.PStatic (!currentFile.fileName, vi.vname)
      else
        N.PGlob vi.vname
    else
      N.PLocal (!currentFile.fileName, !currentFunction.svar.vname, vi.vname)
  in
  let vi_vtype = addArraySizedAttribute vi.vtype vi.vattr in 
  (* Do the type of the variable. Start the index at 1 *)
  let t', _ = doType vi_vtype place 1 in
  vi.vtype <- t';
  (* Associate a node with the variable itself. Use index = 0 *)
  let n = N.getNode place 0 vi.vtype vi.vattr in

  (* Add this to the variable attributes. Note that this node might have been 
   * created earlier. Merge the attributes and make sure we get the _ptrnode 
   * attribute  *)
  vi.vattr <- addAttributes vi.vattr n.N.attr;

  (* Add appropriate kinds for arguments of memcpy and friends. *)
  doAlloc vi;
  doMemcpy vi.vattr vi.vtype;

  currentLoc := original_location

(* Do an expression. Return an expression, a type and a node. The node is 
 * only meaningful if the type is a TPtr _. In that case the node is also 
 * refered to from the attributes of TPtr. Otherwise the node is N.dummyNode *)
let rec doExp ?(inSizeof:bool = false) (e: exp): exp * typ * N.node = 
  let markAddrOfLocal lv lvn : unit =
    (* when taking the address of an lvalue, check whether we're taking the
       address of a local var. *)
    let locals = (!currentFunction).slocals in
    let formals = (!currentFunction).sformals in
    (match lv with 
      Var vi, _ when List.mem vi locals || List.mem vi formals ->
        (* Taking the address of a local variable*)
        setStack lvn (default_why ())
    | _ -> ())
  in
  match e with 
    Lval lv -> 
      let lv', lvn = doLvalue lv false in
      (* We are reading from it, so mark it as referenced *)
      setReferenced lvn (default_why ());
      Lval lv', lvn.N.btype, nodeOfType lvn.N.btype

  | AddrOf lv -> 
      let lv', lvn = doLvalue lv false in
      markAddrOfLocal lv lvn;
      AddrOf lv', TPtr(lvn.N.btype, lvn.N.attr), lvn

  | StartOf lv -> 
      let lv', lvn = doLvalue lv false in
      let next = startOfNode lvn in
      markAddrOfLocal lv next;
      StartOf lv', TPtr(next.N.btype, next.N.attr), next

  | UnOp (uo, e, tres) -> (* tres is an arithmetic type *)
      UnOp(uo, doExpAndCast e tres, tres), tres, N.dummyNode

  | SizeOf (t) ->
      let t', _ = doType t (N.anonPlace()) 1 in
      SizeOf (t'), !typeOfSizeOf, N.dummyNode

  | SizeOfE (e) -> 
      let e', et', en' = doExp ~inSizeof:true e in
      SizeOfE(e'), !typeOfSizeOf , N.dummyNode

  | SizeOfStr (s) -> 
      e, !typeOfSizeOf, N.dummyNode

  | AlignOf (t) ->
      let t', _ = doType t (N.anonPlace()) 1 in
      AlignOf (t'), !typeOfSizeOf, N.dummyNode

  | AlignOfE (e) -> 
      let e', et', en' = doExp ~inSizeof:true e in
      AlignOfE(e'), !typeOfSizeOf , N.dummyNode

    (* pointer subtraction. do the subexpressions *)
  | BinOp (MinusPP, e1, e2, tres) -> 
      let e1', _, _ = doExp e1 in
      let e2', _, _ = doExp e2 in
      BinOp(MinusPP, e1', e2', tres), tres, N.dummyNode

    (* non-pointer arithmetic *)
  | BinOp (((PlusA|MinusA|Mult|Div|Mod|Shiftlt|Shiftrt|
             Lt|Gt|Le|Ge|Eq|Ne|BAnd|BXor|BOr|LAnd|LOr) as bop), 
           e1, e2, tres) -> 
             BinOp(bop, doExpAndCast e1 tres,
                   doExpAndCast e2 tres, tres), tres, N.dummyNode

    (* pointer arithmetic *)
  | BinOp (((PlusPI|MinusPI|IndexPI) as bop), e1, e2, tres) -> 
      let e1', e1t, e1n = doExp e1 in
      let sign = 
        signOf 
          (match bop with PlusPI|IndexPI -> e2 | _ -> UnOp(Neg, e2, intType)) 
      in
      (match sign with
        SLiteral z -> 
          if z < Int64.zero then setArith e1n (default_why ()) else
          if z > Int64.zero then setPosArith e1n (default_why ()) else
          ()

      | SPos -> setPosArith e1n (default_why ())

      | _ -> 
          if bop = IndexPI then (*  Was created from p[e] *)
             setPosArith e1n (default_why ())
          else 
             setArith e1n (default_why ()) );
      if sign = SLiteral Int64.zero then
        e1', e1t, e1n
      else
        BinOp (bop, e1', doExpAndCast e2 intType, e1t), e1t, e1n
      
      
  | CastE (newt, e) -> 
      let newt', _ = doType newt (N.anonPlace ()) 1 in
      let e' = 
        if Dattrs.isTrustedType newt then begin
          (* Trusted Cast.  Do not insert an edge. *)
          let e', _, _ = doExp e in
          e'
        end else if Dattrs.isNulltermDrop newt then begin
          (* An NTDROP.  Don't propagate pkString across the edge. *)
          doExpAndCast ~castKind:N.EEK_stringdrop e newt'
        end else
          (* Ordinary cast *)
          doExpAndCast e newt'
      in
      CastE (newt', e'), newt', nodeOfType newt'

  | Const (CStr s) as e ->
      let n = N.getNode N.PStr 1 charType Dattrs.stringAttrs in
      (e, typeOf e, n)
  | Const (CWStr s) as e ->
      let n = N.getNode N.PWStr 1 !wcharType Dattrs.stringAttrs in
      (e, typeOf e, n)

  | Const _ -> (e, typeOf e, N.dummyNode)



(* Do initializers. *)
and doInit (vi: varinfo) (i: init) (l: location) : init * typ = 

  (* Baseoff is the offset to the current compound *)
  let rec doOne (baseoff: offset) off (what: init) : init * typ = 
    let off' = addOffset off baseoff in
    match what with 
    | SingleInit ei -> begin
        (* Fake an assignment *)
        let lv', ei' = doSet (Var vi, off') ei l in
        SingleInit ei', typeOfLval lv'
    end
    | CompoundInit (t, initl) -> 
        let t', _ = doType t (N.anonPlace ()) 1 in
        let initl' = 
          foldLeftCompound 
            ~implicit:false
            ~doinit:(fun newoff what t acc -> 
                        let what', _ = doOne off' newoff what in
                        (newoff, what') :: acc)
            ~ct:t' ~initl:initl ~acc:[] in
        CompoundInit (t', List.rev initl'), t'

  in
  doOne NoOffset NoOffset i


and doSet (lv: lval) (e: exp) (l: location) : lval * exp = 
  let lv', lvn = doLvalue lv true in
  (* We are writing to it, so mark it as referenced *)
  setReferenced lvn (N.ProgramSyntax(l)) ; 
  let e' = doExpAndCast e lvn.N.btype in
  (* sg: If assigning thru a pointer or to a global, mark adresses in e' 
   * as pkEscape. The former is a conservative approximation since 
   * depending on where lv can point, the value may probably not escape *)
  (match lv' with
    Mem _, _ -> expMarkEscape e' (* thru a pointer *)
  | Var vi, _ -> 
      if vi.vglob then expMarkEscape e' else () ); (* to a global *)
  lv', e'

and expMarkEscape (e: exp) : unit = 
  match e with 
    
    Lval lv -> 	
      let lvnode = nodeOfType (typeOfLval lv) in
      setEscape lvnode (default_why ())
        
  | StartOf lv -> 
      let lvnode = (* like typeOf, but keeps attrs of arrays *)
	    match unrollType (typeOfLval lv) with
	      TArray (t,_,al) -> nodeOfType (TPtr(t, al))
	    | _ -> E.s (E.bug "expMarkEscape: StartOf on a non-array")
      in
      setEscape lvnode(default_why ())
        
  | AddrOf lv  -> 
      let _, alvnode = doLvalue lv false (* gets node for &lv *)
      in setEscape alvnode(default_why ())
        
  | CastE(_, e1)   -> expMarkEscape e1
  | UnOp((Neg|BNot), e1, _) -> expMarkEscape e1 
        
  | BinOp( (Lt|Gt|Le|Ge|Eq|Ne(*|LtP|GtP|LeP|GeP|EqP|NeP*)), _, _, _) -> ()
  | BinOp(_, e1, e2, _) -> expMarkEscape e1; expMarkEscape e2 
  | _ -> ()
    

(* Do an lvalue. We assume conservatively that this is for the purpose of 
 * taking its address. Return a modifed lvalue and a node that stands for & 
 * lval. Just ignore the node and get its base type if you do not want to 
 * take the address of. *)
and doLvalue ((base, off) : lval) (iswrite: bool) : lval * N.node = 
  let base', startNode = 
    match base with 
      Var vi -> begin 
        let vn = 
          match N.nodeOfAttrlist vi.vattr with
            Some n -> n
          | _ -> N.dummyNode
        in
        (* Now grab the node for it *)
        base, vn
      end
    | Mem e -> 
        let e', et, ne = doExp e in
        if iswrite then
          setUpdated ne (default_why ());
        Mem e', ne
  in
  let newoff, newn = doOffset off startNode in
  (base', newoff), newn
        
(* Now do the offset. Base types are included in nodes. *)
and doOffset (off: offset) (n: N.node) : offset * N.node = 
  match off with 
    NoOffset -> off, n

  | Field(fi, resto) -> 
      let nextn = fieldOfNode n fi in
      let newo, newn = doOffset resto nextn in
      Field(fi, newo), newn

  | Index(e, resto) -> begin
      let nextn = startOfNode n in
      setPosArith nextn (default_why ()) ;
      let newo, newn = doOffset resto nextn in
      let e', et, _ = doExp e in
      Index(e', newo), newn
  end


(* Now model an assignment of a processed expression into a type *)
and expToType ?(castKind=N.EEK_cast) (e,et,en) t (callid: int) : exp = 
  let debugExpToType = false in
  if not (Dattrs.isTrustedType et) && not (Dattrs.isTrustedType t) then begin
    let destn = nodeOfType t in
    if debugExpToType then 
      ignore (E.log "expToType e=%a (NS=%d) -> TD=%a (ND=%d)\n"
                d_plainexp e en.N.id d_plaintype t destn.N.id); 
    match en == N.dummyNode, destn == N.dummyNode with
      true, true -> e (* scalar -> scalar *)
    | false, true -> e (* Ignore casts of pointer to non-pointer *)
    | false, false -> (* pointer to pointer *)
        if debugExpToType then
          ignore (E.log "Setting %a : %a (%d -> %d)\n"
                    d_plainexp e d_plaintype et en.N.id destn.N.id); 
        ignore (N.addEdge en destn (N.ECast castKind) (Some !currentLoc));
        e

    | true, false -> (* scalar -> pointer *)
        (* Check for zero *)
        if isZero e then
          () (* setNull destn *)
        else begin
          if isPointerType et then
            E.s (Dutil.bug "Casting %a to pointer type %a, but it has no node."
                           Dutil.dx_exp e Dutil.dx_type t);
          setIntCast destn (default_why ())
        end;
        e
  end else
    e

    
and doExpAndCast ?(castKind: N.extra_edge_kind option) e t = 
  expToType ?castKind (doExp e) t (-1)

and doExpAndCastCall e t callid = 
  expToType (doExp e) t callid





(*****************************************************************)


let rec doBlock blk = 
  if not (hasAttribute "trusted" blk.battrs) then
    List.iter doStmt blk.bstmts;
  blk

and doStmt (s: stmt) : unit = 
  match s.skind with 
    Goto _ | Break _ | Continue _ -> ()
  | Return (None, _) -> ()
  | Return (Some e, l) -> 
      currentLoc := l;
      let e' = doExpAndCast e !currentResultType in
      expMarkEscape e';
      s.skind <- Return (Some e', l)
  | Instr il -> 
      s.skind <- Instr (mapNoCopyList doInstr il)
  | Loop (b, l, lb1, lb2) -> 
      currentLoc := l;
      s.skind <- Loop (doBlock b, l, lb1, lb2)
  | Block b -> s.skind <- Block (doBlock b)
  | If(e, b1, b2, l) -> 
      currentLoc := l;
      s.skind <- If (doExpAndCast e intType, doBlock b1, doBlock b2, l)
  | Switch (e, b, cases, l) -> 
      currentLoc := l;
      s.skind <- Switch(doExpAndCast e intType, doBlock b, cases, l)
  | TryFinally (b, h, l) -> 
      currentLoc := l;
      s.skind <- TryFinally(doBlock b, doBlock h, l)
  | TryExcept (b, (il, e), h, l) -> 
      currentLoc := l;
      s.skind <- TryExcept(doBlock b, (mapNoCopyList doInstr il, 
                                       doExpAndCast e intType), 
                           doBlock h, l)

and doInstr (i:instr) : instr list = 
  match i with
  | Asm (attrs, tmpls, outs, ins, clob, l) -> 
      currentLoc := l;
      let outs' = 
        List.map
          (fun (i,n, o) -> 
            let o', lvn = doLvalue o true in
            setReferenced lvn (default_why ()); 
            (i,n, o'))
          outs 
      in
      let ins' = 
        List.map
          (fun (i,n, e) -> 
            let e', _, _ = doExp e in
            (i,n, e'))
          ins
      in
      [Asm(attrs, tmpls, outs', ins', clob, l)]

  | Set (lv, e,l) -> 
      currentLoc := l;
      let lv', e' = doSet lv e l in
      [Set(lv', e',l)]
        
  | Call (reso, orig_func, args, l) -> begin
      currentLoc := l;
      Stats.time "doFunctionCall" (doFunctionCall reso orig_func args) l
  end

and doFunctionCall 
    (reso: lval option)
    (func: exp)
    (args: exp list) 
    (l: location) = 
  incr callId; (* A new call id *)

  (* Do the function itself *)
  let func', pfuncn =
    match func with 
      Lval lv ->
        let lv', lvn = doLvalue lv false in
        setReferenced lvn (default_why ());
        Lval lv', lvn
    | _ -> E.s (Dutil.bug "Called function is not an lvalue")
  in
  let (rt, formals, isva, attrs) = 
    match unrollType (typeOf func') with
      TFun(rt, formals, isva, attrs) -> 
        rt, argsToList formals, isva, attrs
    | _ -> E.s (Dutil.bug "Call to a non-function")
  in
  let args' =  
    if isva then  
      (* This might add prototypes to theFile *)
      Dvararg.prepareVarargArguments  
        (fun t ->  
          let vi = makeTempVar !currentFunction t in  
          doVarinfo vi; 
          vi)  
        func' (List.length formals) args
    else 
      args 
  in
  let freeArg =
    match Dattrs.getZeroOneAttr ["dfree"; "drealloc"] attrs with
    | Some (Attr ("dfree", [ACons (name, [])]))
    | Some (Attr ("drealloc", [ACons (name, []); _])) -> Some name
    | _ -> None
  in
  (* Now check the arguments *)
  let rec loopArgs formals args = 
    match formals, args with
      [], [] -> []
    | [], a :: args -> 
        (* We ran out of formals. This is either in a vararg functions or 
         * else this is bad, so we make sure to mark that the argument is 
         * used in a function without prototypes *)
        (* Do the arguments because they might contain pointer types *)
        let a', _, an = doExp a in
        if an != N.dummyNode && not isva then
          Dutil.warn "Calling function %a with too many args."
                     d_exp func;
        a' :: loopArgs [] args
                
    | (fn, ft, _) :: formals, a :: args -> 
        let a' =
          if Some fn <> freeArg then
            doExpAndCastCall a ft !callId
          else
            let a', _, _ = doExp a in a'
        in
        a' :: loopArgs formals args
                
    | _ :: _, [] ->
        E.s (Dutil.error "Calling function %a with too few args."
                         d_exp func)
  in  
  (* Now scan the arguments again and add EArgs edges *)
  let args'' = loopArgs formals args' in
  List.iter (fun a' -> 
    let a'n = nodeOfType (typeOf a') in
    if a'n != N.dummyNode then 
      ignore (N.addEdge pfuncn a'n N.EArgs (Some l))) args'';

  let reso' = 
    (* Now check the return value *)
    match reso, unrollType rt with
      None, TVoid _ -> None
    | Some _, TVoid _ -> 
        ignore (warn "void value is assigned.");
        None

    | None, _ -> None (* "Call of function is not assigned" *)
    | Some dest, _ -> begin
        (* Do the lvalue, just so that the type is done *)
        let dest', destn = doLvalue dest true in
        (* We are using the pointer, so mark it referenced. *)
        setReferenced destn (default_why ());
        (* Add the cast from the return type to the destination of the call. 
         * Make up a phony expression and a node so that we can call 
         * expToType. *)
        let dest't = typeOfLval dest' in
        (* Also add an EArgs edge *)
        let dest'n = nodeOfType dest't in
        if dest'n != N.dummyNode then 
          ignore (N.addEdge pfuncn dest'n N.EArgs (Some l));
        (* For allocation functions do not connect the returned value to the 
         * result because the returned value is an integer *)
        (match func' with 
          Lval(Var f, NoOffset) when H.mem allocFunctions f.vname -> ()
        | _ -> 
            ignore (expToType (CastE(rt, mkString ("<a call return>")),
                               rt, nodeOfType rt) dest't 
                      !callId));
        Some dest'
    end 
  in
  [Call(reso', func', args'', l)]


let doFormals (fdec: fundec) = 
  currentFunction := fdec;
  (* Go through the formals and copy their type and attributes from 
   * the type of the function. Then add the nodes for the address of the 
   * formals. Then restore the sharing with the function type. *)
  let rt, targs, isva, fa = splitFunctionTypeVI fdec.svar in
  let rec scanFormals targs sformals = 
    match targs, sformals with
      [], [] -> ()
    | (tan, tat, taa) :: targs, sf :: sformals -> 
        sf.vtype <- tat;
        let n = 
          N.getNode (N.PLocal(!currentFile.fileName, 
                              !currentFunction.svar.vname, tan))
            0 tat taa in
        sf.vattr <- addAttributes taa n.N.attr;
        scanFormals targs sformals
    | _ -> E.s (bug "scanFormals(%s) non-matching formal lists"
                  fdec.svar.vname)
  in
  scanFormals (argsToList targs) fdec.sformals;
  (* Restore the sharing by writing the type *)
  setFormals fdec fdec.sformals;
  ()
  
let doFunctionBody (fdec: fundec) = 
  currentFunction := fdec;
  let rt,_,_,_ = splitFunctionTypeVI fdec.svar in
  currentResultType := rt;
  (* Do the other locals *)
  List.iter doVarinfo fdec.slocals;
  (* Do the body *)
  fdec.sbody <- doBlock fdec.sbody


  
(* Now do the globals *)
let doGlobal (g: global) : global = 
  match g with
  | GPragma _ | GText _ | GAsm _
  | GEnumTag _ | GCompTagDecl _ | GEnumTagDecl _ -> g
            
    (* We process here only those types that we must not unroll. 
     * The others we'll process as we see them used.*)
  | GType (t, l) ->
      currentLoc := l;
      (* See if we have the "nounroll" attribute *)
      if hasAttribute "nounroll" (typeAttrs t.ttype) then 
        H.add dontUnrollTypes t.tname true;
      if not (mustUnrollTypeInfo t) then begin
        let t', _ = doType t.ttype (N.PType t.tname) 1 in
        t.ttype <- t';
        g
      end else 
        if !N.printVerboseOutput then 
          GText ("// Definition of unrolled type "^t.tname^" was removed")
        else
          GText ("//")
            
  | GCompTag (comp, l) -> 
      currentLoc := l;
      markCompInfo comp l;
      g

  | GVarDecl (vi, l) -> 
      currentLoc := l;
      Stats.time "global doVarinfo" doVarinfo vi;
      g
            
  | GVar (vi, init, l) -> 
      currentLoc := l;
      Stats.time "global doVarinfo" doVarinfo vi; 
      (match init.init with
        None -> ()
      | Some i -> 
          let i', _ = Stats.time "doInit" (doInit vi i) l in
          init.init <- Some i');
      g
            
  | GFun (fdec, l) ->
      currentLoc := l;
      Stats.time "global doVarinfo" doVarinfo fdec.svar;
      Stats.time "doFormals" doFormals fdec;
      let dobox = not (Dattrs.isTrustedType fdec.svar.vtype) in
      if dobox then
        Stats.time "doFunctionBody" doFunctionBody fdec;
      g


(********************************************************)

      
(* Now do the file *)      
let markFile fl = 
  currentFile := fl;
  
  N.initialize ();
  IH.clear mustRecomputePointsTo;
  IH.clear markedCompInfos;
  H.clear dontUnrollTypes;
  H.clear allocFunctions;

  (* This is where we process all the functions. *)
  theFile := [];
  Stats.time "doGlobal"
    (List.iter (fun g -> let g' = doGlobal g in 
                      theFile := g' :: !theFile)) fl.globals;

  (* Now we have to scan the nodes again. There might be some nodes whose 
   * type is pointer to TComp and which do not have any EPointsTo edges 
   * because the TComp was a forward reference. Now that should have been 
   * fixed, so try to regenerate the EPoints to edges *)
  IH.iter (fun _ n -> N.setNodePointsTo n) mustRecomputePointsTo;

  (* Now do the globinit *)
  let newglobinit = 
    match fl.globinit with
      None -> None
    | Some g -> begin
        match doGlobal (GFun(g, locUnknown)) with
          GFun (g', _) -> Some g'
        | _ -> E.s (bug "markptr: globinit")
    end
  in
  if !verbose then
    ignore (E.log "after markptr\n");

  let newglobals = List.rev !theFile in

  let newfile = {fl with globals = newglobals; globinit = newglobinit} in

  H.clear dontUnrollTypes;
  H.clear allocFunctions;
  IH.clear mustRecomputePointsTo;
  IH.clear markedCompInfos;
  theFile := [];
  currentFile := dummyFile;

  newfile
