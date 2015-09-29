(*
 *
 * Copyright (c) 2001-2006, 
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
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

(* Weimer
 *
 * CCured pointer kind inference using an extension of the algorithm
 * described in the paper submitted to PLDI'02. 
 *
 * INPUT ASSUMPTIONS: 
 *
 * The node hashtable includes the following edges:
 *      n1 ECAST n2     for the top-level nodes of casts
 *      n1 EOFFSET n2     from the top of a struct to its non-array fields
 *      n1 EINDEX n2    from the top of a struct to array fields
 *
 * Nodes have the following bits set iff the corresponding fact actually
 * originate at that node: 
 *      pkPosArith
 *      pkArith
 *      pkNull
 *      pkUpdated
 *      pkIntCast
 *      pkInterface
 *      pkSized
 *      pkNoPrototype (makes a function node wild)
 *
 * The "is_p x y" function returns true if x--cast-->y is from a polymorphic
 * function and should not be considered. 
 *
 * Returns "true" if we should typecheck the result because we let some
 * user-annotated qualifier stand. 
 *)
(*
 * How does the solver work? 
 *
 * We treat every "void *" as a separate type variable and we keep
 * equivalence classes of void* nodes that are connected by ECast or
 * ECompat edges. ECast edges come from Markptr as part of our
 * precondition. We create ECompat edges. 
 *
 * (1) We examine every CAST in the program. While scanning the
 *      types to see if the cast is valid we add ECompat edges between
 *      inner types that must be equal and mark as Wild types that
 *      do not match up. We also mark nodes as Not Safe in casts where
 *      the sizes are wrong. 
 * (2) Check equivalence classes. All nodes joined by ECompat edges must
 *      have equal types. Make sure all nodes in all equiv classes have
 *      the same flags. 
 * (3) We assign base-case flags. For example, we assign
 *      "pkString" to nodes that are of type string.
 * (4) We push those flags around using standard data-flow tricks. Nodes
 *      connected by ECompat edges have identical flags. 
 * (5) Once we have all the flags in place we distinguish between all
 *      the kinds of sequences. For example, a node that cannot be safe
 *      and has an integer cast into it but does not reach a string becomes 
 *      FSEQ. 
 * (6) We turn all string-like nodes that lead only into ROString nodes 
 *      into ROString nodes themselves. Note all nodes connected by ECompat
 *      edges must have the same kind. 
 * (7) We push WILD as far as it can go. Generally WILD contaminates all
 *      outgoing edges and all points-to targets, however an edge from
 *      WILD to ROString is allowed. 
 * (8) All otherwise unconstrainted nodes become SAFE. 
 *
 * Compared to previous solvers, this solver is much stricter about
 * strings. No "safe -> string" or "safe -> rostring" casts should remain. 
 *)

open Cil
open Ptrnode
open Pretty
open Trace
module E = Errormsg
module IH = Inthash

let verbose = Ivyoptions.verbose

(* Added for compatibility with Deputy's warnings. *)
let warnLoc (loc : location) (fmt : ('a,unit,doc) format) : 'a = 
  let f d =
    let saveLoc = !currentLoc in
    currentLoc := loc;
    Dutil.warn "%a" insert d;
    currentLoc := saveLoc;
    nil
  in
  Pretty.gprintf f fmt

let bitsSizeOfOpt tau =
  try Some(bitsSizeOf tau)
  with SizeOfError _ -> None

(* Euclid's algorithm for the GCD *)
let rec gcd a b = 
  if a = 0 || b = 0 then 1
  else if b > a then gcd b a 
  else match a mod b with
    0 -> b
  | r -> gcd b r 

(* go through the source code and find where tau was declared *)
class findTypeVisitor tau = object
  inherit nopCilVisitor
  val tau_sig = typeSig tau 
  method vtype some_type = 
    if tau_sig = typeSig some_type then 
      ignore (warn "type %a was not given a node by markptr" d_type tau) ;
    DoChildren
end

(* equiv classes of nodes connected by ECompat edges. *)
module OrderedNode = 
  struct 
    type t = node 
    let compare n1 n2 = n1.id - n2.id 
    (* Avoid using Pervasives.compare, which is the same as "=", which may
     * loop forever because nodes contain "Cil.typ"s. *)
  end
module NodeSet = Set.Make(OrderedNode)
module NodeUF = Unionfind.Make(NodeSet)


(*
 **
 *** The Solver!
 ** 
 *)
let solve (the_file : Cil.file) (node_ht : node Inthash.t) : unit = begin
  let node_eq = ref (NodeUF.empty) in (* ECompat equivalence classes *)

  let existsECompatEdge ~(start : node) ~(dest : node) = 
    List.fold_left (fun acc e -> acc ||
     (e.eto.id = dest.id && match e.ekind with ECompat _ -> true | _ ->
     false)) false start.succ
  in 

  (* Spread a flag from one node to another one *)
  let spreadFlag (f: int) (from: node) (why_from_to: chain) (nto: node) = 
    if not (hasFlag nto f) then begin
      let orig, _, _ = trueSourceOfFlag from f in
      setFlag nto f (FlagSpreadFromNode(from, why_from_to, orig))
    end
  in


  (* Say that n1 and n2 (which are usually matching inner pointers) must
   * really be equal. This adds an ECompat edge between them and places
   * them in the same equivalence class. We avoid making duplicate edges.
   * We know if this edge is for inner pointers. Otherwise it is for void* 
   * equivalence classes *)
  let rec addECompatEdge (isinner: bool) n1 n2 why_n1_n2 location =
    if existsECompatEdge n1 n2 || 
       existsECompatEdge n2 n1 || 
       n1.id = n2.id then
      ()
    else begin
      (* Sometimes it might be convenient to swap the nodes in order to keep 
       * the explanations shorter. *)
      let n1, n2, why_n1_n2 = 
        match isSym why_n1_n2 with
          Some why_n2_n1 -> n2, n1, why_n2_n1
        | _ -> n1, n2, why_n1_n2
      in

      if doCheckChains then 
        checkChainEnds n1 n2 why_n1_n2;

      (* matth: I had originally removed this line from Deputy. 
         Does it break anything? *)
      ignore(addEdge n1 n2 (ECompat why_n1_n2) (Some(location)));

      (* We only join in the equivalence classes (maintained through the .rep 
       * fields) if at least one is TPtr(void). OTherwise we use the NodeUF 
       * equivalence classes  *)
      if (isVoidType n1.btype || isVoidType n2.btype) then begin
        join n1 n2 why_n1_n2
      end else 
        node_eq := NodeUF.make_equal (!node_eq) n1 n2 why_n1_n2 ;
    end
  in 
  
  (* whenever we have to "loop until things settle", we used
   * finished to keep track of our status *)
  let finished = ref false in 

  (* update changes node "n"'s kind to "k" because of "w" and sets
   * finished to false. It also does logging and sanity checking. *)
  let update n k w = begin
    if (k <> n.kind) then begin
      (* Check if the new kind is stronger than the old one *)
      let shouldUpdate: bool = 
        match k, n.kind with 
          _, Unknown -> true (* Unknown is weakest *)
        | Unknown, _ -> false
        | _, Sentinel -> true (* Sentinel is next *)
        | Safe, _ -> false (* this means Safe can only replace Unknown or 
                              Sentinel *)
        (* Strings replace non-strings *)
        | String, (UnknownN|Safe) -> true
        | FSeqN, (Seq|FSeq|Safe) -> true
        | SeqN, (Seq|FSeq|Safe) -> true

        (* Seq replaces FSeq, which in turn replaces SAFE,
           unless the user specified otherwise *)
        | (Seq|SeqN), (FSeq|FSeqN|Safe|String|UnknownN) -> 
            n.why_kind <> UserSpec
        | (FSeq|FSeqN), (Safe|String|UnknownN) -> 
            n.why_kind <> UserSpec

        | _, _ -> false
      in
      if shouldUpdate then begin
        (* The new kind is stronger. We must update. *)
        let trulyUpdate = 
          if n.why_kind = UserSpec then 
            if !allowOverride then begin
	      (* matth:  If the user annotates a node as __RTTI
	       * and we infer it to be FSeqR or SeqR, assume that that's what
	       * the user intended, and don't print a warning. *)
	      (match n.kind, k with
              | FSeq, FSeqN
              | Seq, SeqN -> ()
	      | _ -> ignore (warnLoc n.loc
                        "Solver: Changing User Specified %a node %d (%a) to %a."
                        d_opointerkind n.kind n.id 
                        d_place_nice n.where
                        d_opointerkind k));
              true
            end else begin
              (* Use "ignore" so that we do not stop here. But we'll stop 
               * after solving *)
              E.hadErrors := true;
              ignore (errorLoc n.loc
                        "Solver: Should change User Specified %a node %d (%a) to %a."
                        d_opointerkind n.kind n.id 
                        d_place_nice n.where
                        d_opointerkind k);
              false
            end
          else
            true (* If it is not User_Spec then always update *)
        in
        if trulyUpdate then begin
          n.kind <- k ; 
          n.why_kind <- w ;
          finished := false 
        end
      end
    end else (* Already have the same kind *)
      ()
  end
  in          

  (* Help Function: find the attributes of a type *)
  let node_of_type tau = 
    nodeOfAttrlist (typeAttrs tau)
  in

  (* Step 0
   * ~~~~~~
   * Our first pass over the set of nodes. 
   * Set all of the flag starting conditions that we know about.  
   *)
  if !verbose then ignore (E.log "Solver: Step 0  (Base Case)\n") ;


  (* loop over all the nodes ... *)
  IH.iter (fun id n -> 
    (* calling a function without a prototype makes it wild *)
    if hasFlag n pkNoPrototype then begin
      Dutil.errorwarn "You passed too many arguments to a function (see above).  We should make the function WILD.";
    end ;

    begin
    match n.kind with
    | String when !useStrings -> 
        setFlag n pkString (RequiredByPointerKind n.kind);
        setFlag n pkOneWord (FlUserSpec n.loc)

    | FSeq
    | Seq -> ()

    | FSeqN
    | SeqN
    | UnknownN when !useStrings -> 
        setFlag n pkString (RequiredByPointerKind n.kind) 

    | Safe -> setFlag n pkOneWord (FlUserSpec n.loc)

    | _ -> () 
    end ;

    if hasAttribute "size" n.attr || hasAttribute "count" n.attr then 
      setFlag n pkOneWord (FlUserSpec n.loc);

  ) node_ht ; 

  (* Step 1
   * ~~~~~~
   * Consider every cast.
   *
   * Generate ECOMPAT edges between aligned sub-pointers.
   * Generate BADCAST constaints on failed pointers (make 'em WILD)
   * Generate ARITH constaints on upcasts (make 'em not SAFE). 
   *)
  if !verbose then ignore (E.log "Solver: Step 1  (Casts)\n") ;

  let the_edge = ref None in 

  (* Whenever we compare two types for equality we should mark all
   * matching inner pointers with ECOMPAT edges. This function is called
   * by the type-scanning phase on all pairs of pointers that should
   * match up. *)
  let handle_inner_pointers loc explanation tau1 tau2 = 
    try begin
      match (node_of_type tau1),(node_of_type tau2) with
      | Some(n1),Some(n2) -> 
          addECompatEdge true n1 n2 explanation loc;

      | Some(n),None 
      | None,Some(n) when (isVoidType n.btype) -> begin
          (* Link a "void*" equivalence class with the scalars. *)
          setFlag n pkCompatWithScalars (FlagSpreadFromNode(n,explanation,n)) ;
          let (nr,why_n_nr) = get_rep_why n in
          setFlag nr pkCompatWithScalars (FlagSpreadFromNode(n,why_n_nr,n)) 
          end

      | _,_ -> (* in this unfortunate case, we don't know how to get
                * to the nodes of these types. Try to print a useful error 
                * message  *)
        begin 
        if node_of_type tau1 = None then 
          ignore (visitCilFile (new findTypeVisitor tau1) the_file) ;
        if node_of_type tau2 = None then 
          ignore (visitCilFile (new findTypeVisitor tau2) the_file) ;
        
        E.s (E.bug "Solver: cannot link inner pointers:@!%a@!%a@!%a\n"
          d_type tau1 d_type tau2 
          (docOpt (fun e -> 
            dprintf "%d->%d" e.efrom.id e.eto.id)) !the_edge)
        end 
    end with e -> begin
      ignore (E.warn "handle_inner_pointers raises %s"
                (Printexc.to_string e))
    end
  in 
  (* This function is called by type comparison functions in Type.ml when the 
   * base types of two pointer types fails to compare properly. This function 
   * should be called on representatives only. *)
  let handle_failure n1 why_n1_n2 n2 =
    if n1.rep != None then 
      E.s (E.bug "handle_failure called on node %d which is not a representative"
             n1.id);
    if n2.rep != None then 
      E.s (E.bug "handle_failure called on node %d which is not a representative"
             n2.id);
  in
  (* 
   * Step 1 Loop : examine every cast
   *)
  (* Sometimes we might need to create new ECast edges for auto RTTI. 
   * Remember them here *)
  let step1_oneEdge e = (* look at every forward edge *)
    the_edge := Some(e) ; 
    if isECast e then begin
      if Type.debugType then 
         ignore (E.log "Considering Edge %d->%d\n" e.efrom.id e.eto.id);

      let from_rep, why_efrom_frep = get_rep_why e.efrom in
      let to_rep, why_eto_trep = get_rep_why e.eto in 
      let from_rep_t = from_rep.btype in
      let to_rep_t = to_rep.btype in 
      (* explanation: from_rep -> e.efrom -> e.eto -> to_rep *)
      let why_frep_trep = 
        mkRTrans (mkRSym why_efrom_frep) 
          (mkRTrans (mkRSingle e) why_eto_trep) in

      (* Deal with void* casts. *)
      if (isVoidType from_rep_t || isVoidType to_rep_t) then begin
        let from_rep_is_void = isVoidType from_rep_t in
        let to_rep_is_void = isVoidType to_rep_t in

        (* If one of the representatives types is void_ptr,
         * and we are doing void* inferrence on this node, 
         * then we just add an ECompat edge and join the classes.
         * If BOTH nodes are void*, only add the ECompat if we're doing
         * inference on both of them. *)
        if ( (from_rep_is_void || to_rep_is_void) 
             && (e.eto.shouldInfer || not to_rep_is_void)
             && (e.efrom.shouldInfer || not from_rep_is_void)) then
          addECompatEdge false from_rep to_rep why_frep_trep e.eloc
      end else begin
        (* Not a cast involving void*. Just go ahead and check the types *)
        let from_size = try bitsSizeOf(from_rep_t) with SizeOfError _ -> 1 in
        let to_size = try bitsSizeOf(to_rep_t) with SizeOfError _ -> 1 in
        if from_size < to_size then begin
          setFlag e.efrom pkNotSafe (DownCast e.eto); (* ARITH constraint *)
        end ;
        
        Stats.time "subtype" (fun () -> 
          if not (Type.subtype
              ~compat:(handle_inner_pointers e.eloc)
              ~failure:(handle_failure)
              ~why_small_big:(mkRSym why_frep_trep)
              ~small:to_rep_t 
              ~big:from_rep_t)
            then begin (* they are not subtypes *)
              (* We do *NOT* pass polymorphic_replace to Type.all_scalars
               * because we have already replaced the top-level void*s
               * (with to_rep and from_rep). p_r would just replace any
               * void*s in to_rep_type and from_rep_type -- but if there
               * are any void*s in to_rep_type or from_rep_type then we
               * don't want to say that it was "all scalars" here. In
               * particular, this could happen in a case like:
               *   int i = 5 __1 ; 
               *   void *__2 *__3 v = ( void *__4 *__5 )&i;
               * Between 3 and 5. 4 will have the pkCompatWithScalars flag,
               * but we don't to make 2 and 4 FSEQ here. *)
              if (Type.all_scalars to_rep_t) && (Type.all_scalars from_rep_t)
                 (* if it must be compatible with scalars and we failed the
                  * subtyping then it must be WILD! *)
              then begin
                (* ARITH constraint *)
                (* GN: Subtyping failed but they are all scalars. In that 
                 * case all we need is the the origin node is not SAFE. I 
                 * commented out the next line. *)
                (* setFlag e.eto pkNotSafe (SubtypeFailed e.efrom) ; *)
                setFlag e.efrom pkNotSafe (SubtypeFailed e.eto) ;
                (* In this one special case, we'll infer that the two
                 * types should be SEQ *)
              end else begin
                handle_failure from_rep why_frep_trep to_rep
              end
            end 
            ) ()
      end
    end else if e.ekind = EIndex then begin
      (* while we're here, these arrays cannot be safe *)
      setFlag e.eto pkNotSafe (RequiredByEdge e);
    end
  in
  IH.iter (fun id cur ->
    List.iter step1_oneEdge cur.succ ; (* look at every forward edge *)
    the_edge := None ; 
    (* Set user-specified flags *)
    match cur.kind with
      Seq | SeqN ->
        setFlag cur pkArith (RequiredByPointerKind cur.kind) ; 
        setFlag cur pkReferenced (RequiredByPointerKind cur.kind) ; 
    | FSeq | FSeqN ->
        setFlag cur pkPosArith (RequiredByPointerKind cur.kind) ; 
        setFlag cur pkReferenced (RequiredByPointerKind cur.kind) ; 
    | Safe | String | UnknownN ->
        setFlag cur pkReferenced (RequiredByPointerKind cur.kind) ; 
    | Unknown | Sentinel -> ()
  ) node_ht ; 


  (* Step 2
   * ~~~~~~
   * Skipped in Deputy!
   *)


  (* Step 3
   * ~~~~~~
   * Check our equivalence classes for consistency.
   *
   * All "void *" equivalence class nodes should have an ECompat edge to
   * their rep. The rep has the flags for the whole class. 
   *
   * All nodes in "void*" equivalence classes should link up everything
   * they point to in "void*" equivalence classes as well. 
   *
   * All nodes in equiv classes should have the same flags. 
   *)
  (* First we add transitive closure of the ECast edges on "void *" *)
  if !verbose then ignore (E.log "Solver: Step 3  (equiv)\n") ;

  let check_compat_fun e =
    match e.ekind with 
      ECompat r -> 
        let to_t = e.eto.btype in
        let from_t = e.efrom.btype in 
        (* Leave alone the edges that have a void-ptr !! *)
        if isVoidType to_t || isVoidType from_t then 
          ()
        else begin
          the_edge := Some(e) ; 
          if (not (Stats.time "subtype" 
                     (fun () -> Type.equal 
                             ~compat:(fun _ _ _ -> ()) (* gn: why ? *)
                             ~failure:(handle_failure) 
                             ~why_t1_t2: r
                             ~t1:from_t 
                             ~t2:to_t) ())) then  
            handle_failure e.eto r e.efrom;

          the_edge := None ; 
        end;
    | _ -> ()

  in 

  Stats.time "equiv-check" 
  (IH.iter (fun id cur ->
    let rep, why_cur_rep = get_rep_why cur in

    (* Check to see if any equivalence classes must be compatible with
     * scalars AND ALSO with some non-void type. If so, that class becomes
     * WILD. *)
    if (     hasFlag cur pkCompatWithScalars && 
        not (hasFlag rep pkCompatWithScalars)) then begin
        E.s (E.bug "Solver: node %d has pkCompatWithScalars flag but its rep %d does not" cur.id rep.id)
    end ; 

    if hasFlag rep pkCompatWithScalars && not (isVoidType rep.btype) then begin
      ignore (warnLoc rep.loc "Solver: BAD CAST / EQ-SCALAR@!%a"
        d_type rep.btype)
    end ;

    if doCheckChains then 
      checkChainEnds cur rep why_cur_rep;
    if rep != cur then begin
      for i = 0 to pkLastFlag do
        (* The RTTI flag is spread while the edges are being created *)
        if i <> pkRtti && hasFlag cur i then 
          spreadFlag i cur why_cur_rep rep
      done ;
    end; 
    (* Once for each edge *)
    List.iter check_compat_fun cur.succ ;
    (* List.iter check_compat_fun cur.pred ; *)
  )) node_ht ;

  (* Now we have equivalence classes of ECompat-joined nodes *)
  let compat_eq_classes = NodeUF.eq_classes !node_eq in 

  (* 
   * Step 3 Loop #2 : examine each "void *" equiv class 
   *)

  (* share all flags within equivalence classes *)
  List.iter (fun eq_class ->
    List.iter (fun from_elt ->
      List.iter (fun to_elt ->
        for i = 0 to pkLastFlag do
          (* The RTTI flag is spread while the edges are being created *)
          if i <> pkRtti && hasFlag from_elt i then 
            if not (hasFlag to_elt i) then 
              let why_from_to = NodeUF.why_equal !node_eq from_elt to_elt in
              if doCheckChains then 
                checkChainEnds from_elt to_elt why_from_to;
              spreadFlag i from_elt why_from_to to_elt
        done ;
        if (to_elt.why_kind = UserSpec) then begin
           from_elt.kind <- to_elt.kind ; 
           from_elt.why_kind <- to_elt.why_kind  
        end ;
        if (from_elt.why_kind = UserSpec) then begin
           to_elt.kind <- from_elt.kind ; 
           to_elt.why_kind <- from_elt.why_kind
        end ;
        if (to_elt.why_kind = Default && from_elt.why_kind <> Default) then
          to_elt.why_kind <- from_elt.why_kind 
      ) eq_class
    ) eq_class
  ) compat_eq_classes ;


  (* Step 4
   * ~~~~~~
   * Push all of the boolean flags around. 
   *)
  if !verbose then ignore (E.log "Solver: Step 4  (Data-Flow)\n") ;
  (* loop over all the nodes ... *)
  finished := false ; 

  let worklist = Queue.create () in

  (* Find edge chain *)
  let findEdgeChain (src: node) (e: edge) = 
    (* Find the chain src -> dst *)
    let r1 = 
      match e.ekind with 
        ECompat r' -> r'
      | _ -> mkRSingle e
    in
    (* Check that this edge has src as one of its ends *)
    if doCheckChains && src.id <> e.efrom.id && src.id <> e.eto.id then 
      ignore (E.warn "findEdgeChain for src=%d and edge %d->%d"
                src.id e.efrom.id e.eto.id);
    (* See if the edge is going in the right direction *)
    if e.efrom.id = src.id then r1 else mkRSym r1
  in


  let setFlagsFromListChain dst src r_src_dst lst =
    if doCheckChains then 
      checkChainEnds src dst r_src_dst;
    List.iter (fun i ->
      (* The RTTI flag is spread while the edges are being created *)
      if i <> pkRtti && hasFlag src i && not (hasFlag dst i) 
         (* Do not spread the intCast flag to RTTI pointer *)
         && (i <> pkIntCast || not (hasFlag dst pkRtti)) then begin
        Queue.add dst worklist ;
        spreadFlag i src r_src_dst dst
      end 
    ) lst 
  in 

  let setFlagsFromList dst src e lst =
    let r_src_dst = findEdgeChain src e in
    setFlagsFromListChain dst src r_src_dst lst 
  in 

  let processDataFlow cur = begin
    (* First consider all ECompat edges:
     * flags should be equal across them. This is motivated by
     * test/small1/apachebuf.c. Merely making ECompat-linked nodes have
     * the same kind does not suffice: a pred of an ecompat-linked node
     * may need to be made FSEQ because of a posarith on the other side
     * of the ecompat link. *)
    let inner_fun e = 
      if isECompat e || isESameKind e then begin
        setFlagsFromList e.efrom e.eto e allFlags ;
        setFlagsFromList e.eto e.efrom e allFlags ;
      end
    in 
    List.iter inner_fun cur.pred ;
    List.iter inner_fun cur.succ ;

    (* Consider all Successor Edges, do data-flow *)
    List.iter (fun e ->
      (match e.ekind with
      | ECast extra_kind ->
          (* We do not propagate the pkString flag in the following cases:
           * 1. The user explicitly dropped the NT flag.
           * 2. The target is user-specified, in which case we do not want
           *    to override the user's choice.
           * 3. The source is a non-local and non-cast (e.g., an argument)
           *    and it was not specified NT by the user.  This check
           *    prevents NT from flowing into a function without the
           *    user's permission. *)
          if extra_kind = EEK_stringdrop || e.eto.why_kind = UserSpec ||
             (e.efrom.why_kind <> UserSpec && not e.efrom.shouldInfer) then
            setFlagsFromList e.eto cur e pkCastSuccFlagsNoString
          else
            setFlagsFromList e.eto cur e pkCastSuccFlags;
         
          (* If the successor node is referenced and we have the pkString 
           * flag, we propagate pkPosArith and pkArith flag to successor. We 
           * want to make sure that the accesses to these pointers will be 
           * checked against the bound, not using the NULLTERM functions *)
          if hasFlag cur pkString && not (hasFlag e.eto pkOneWord) then 
            setFlagsFromList e.eto cur e [ pkPosArith; pkArith ]

      | EOffset ->
          setFlagsFromList e.eto cur e pkOffsetSuccFlags ;
      | _ -> ()) ;
    ) cur.succ ;

    (* Consider all Predecessor Edges, do data-flow *)
    List.iter (fun e ->
      (match e.ekind with
         ECast extra_kind ->  (* track [F]SEQ information *) 
           setFlagsFromList e.efrom cur e pkCastPredFlags ;

           (* See comment above for explanation. *)
           if e.efrom.why_kind = UserSpec ||
              (e.eto.why_kind <> UserSpec && not e.eto.shouldInfer) then
             setFlagsFromList e.efrom cur e pkCNIPredFlagsNoString
           else
             setFlagsFromList e.efrom cur e pkCNIPredFlags;
       | EIndex -> setFlagsFromList e.efrom cur e pkCNIPredFlagsNoString ;
       | EOffset ->
                   setFlagsFromList e.efrom cur e pkOffsetPredFlags ;
       | _ -> ()) ;
    ) cur.pred ;

  end 
  in 

  Stats.time "data-flow" (fun () ->
    (* data-flow can actually take some time, so we'll use a work-list *)
    IH.iter (fun id cur -> processDataFlow cur) node_ht;
    while (Queue.length worklist > 0) do 
      (* first, run normal data-flow *) 
      while (Queue.length worklist > 0) do
        let cur = Queue.take worklist in
        processDataFlow cur 
      done ; 
      (* If one array has been compared against another, they must share
       * the same flags. Notably, if you have:
       *   struct { int __INDEX a[8]; } *p;
       *   struct { int         b[8]; } *q = p;
       * we want b to end up being INDEX as well. *)
      Hashtbl.iter (fun (t1,t2) why ->
        let n1 = node_of_type t1 in
        let n2 = node_of_type t2 in 
        match n1,n2 with
        | Some(n1),Some(n2) -> 
          setFlagsFromListChain n1 n2 why [pkReachIndex] ;
          setFlagsFromListChain n2 n1 (mkRSym why) [pkReachIndex] 
        | _ -> 
          ignore (E.warn "solver: cannot set flags equal for arrays %a and %a"
          d_type t1 d_type t2)
      ) Type.arraysThatHaveBeenComparedWithArrays ; 
      (* If this array step didn't update anything, we'll fall out of the
       * outer loop and be done with data-flow. Otherwise we do it all
       * again.  *)
    done 
  ) () ; 


  (* Step 5
   * ~~~~~~
   * Distinguish between sequences. We must do this after boolean flags
   * (otherwise we cannot tell what reaches what, etc.) but before we do
   * WILDs (because they interact with read-only strings). 
   *
   * Also generate ARITH constraints: q != SAFE. 
   *)
  if !verbose then ignore (E.log "Solver: Step 5  (sequences)\n") ;

  (* n is a polymorphic "void *" node if it points to void* and its
   * representative points to void* as well. *)
  let is_polymorphic_voidstar n =
    match n.btype, (get_rep n).btype with
      TVoid _ , TVoid _->  true
    | _ -> false
  in 

  IH.iter (fun id cur -> 
    (* Generate "ARITH" style constraints: q != SAFE *)
    List.iter (fun f -> 
      if hasFlag cur f then setFlag cur pkNotSafe (RequiredByFlag f)
    ) [pkArith ; pkPosArith ] ;

    if hasFlag cur pkIntCast then
      setFlag cur pkNotSafe (RequiredByFlag pkIntCast) ;

    if hasFlag cur pkString && not !useStrings then 
      E.s (bug "we are not using strings but node %d has the pkString flag"
             cur.id);
    
    if hasFlag cur pkNotSafe || 
       hasFlag cur pkString ||
       hasFlag cur pkReachIndex then
    begin
      let new_kind,why = 
        if (hasFlag cur pkReachIndex)   then 
          E.s (bug "no Index in Deputy")
        else if hasFlag cur pkArith then 
          (if hasFlag cur pkString then SeqN else Seq),BoolFlag pkArith
            
        else if hasFlag cur pkPosArith then 
          (if  hasFlag cur pkString then 
            (if !useFSEQ then FSeqN else SeqN) 
          else 
            (if !useFSEQ then FSeq else Seq)), BoolFlag pkPosArith
            
        (* NOT: pkReachIndex, pkReachSeq, pkPosArith, pkArith *)
        else if hasFlag cur pkIntCast then
          begin
            if is_polymorphic_voidstar cur then
              Safe, PolyInt
            else
              (if hasFlag cur pkString then FSeqN else FSeq),
              BoolFlag pkIntCast
          end
        else if hasFlag cur pkString then 
          String, BoolFlag pkString

        (* NOT: pkString *)
        else if hasFlag cur pkNotSafe then 
          (if !useFSEQ then FSeq else Seq), BoolFlag pkNotSafe

        else begin
          E.s (bug "Unexpected combination of flags for node %d: %a\n"
                 cur.id
                 (docArray ~sep:nil
                    (fun idx elm -> 
                      match elm with 
                        None -> nil
                      | Some _ -> text ("\n\t" ^ pkFlagName.(idx)))) cur.flags)
        end
      in 
      update cur new_kind why
    end
  ) node_ht ; 

  (* Step 7  
   * ~~~~~~
   * Verify that SEQ-SEQ casts have the correct tiling. For example:
   *  struct A { int f1; } * __SEQ p1; 
   *  struct B { int f2; int *f3; } * __SEQ p2;
   *  p1 = p2 ;
   * This must result in WILD pointers, otherwise (p1++)->f1=5, *p2->f3 = 6
   * causes a crash. 
   *)
  if !verbose then ignore (E.log "Solver: Step 7  (SEQ-SEQ Tiling)\n") ;
  let isSeqish n = match n.kind with
    Seq | SeqN | FSeq | FSeqN -> true
  | _ -> false
  in 
  Stats.time "seq-seq checking" (fun () -> 
  IH.iter (fun id cur ->
    List.iter (fun e -> 
      if isECast e && isSeqish cur && isSeqish e.eto then begin
        let from_target = (get_rep cur).btype in
        let to_target = (get_rep e.eto).btype in 
        if isVoidType from_target || isVoidType to_target then
          ()
        else begin
          (* check for tiling! *)
          let okay = 
            match bitsSizeOfOpt from_target, bitsSizeOfOpt to_target with
              Some(from_size)  ,Some(to_size) -> 
                let the_gcd = gcd from_size to_size in 
                let from_factor = to_size / the_gcd in 
                let to_factor = from_size / the_gcd in 
                Type.equal 
                  ~compat:(fun _ _ _ -> ())
                  ~failure:(fun _ _ _ -> ())
                  ~why_t1_t2: mkRIdent
                  ~t1:(TArray(from_target, Some(integer from_factor), []))
                  ~t2:(TArray(to_target, Some(integer to_factor), [])) 
            | _ -> 
                Type.equal 
                  ~compat:(fun _ _ _ -> ())
                  ~failure: (fun _ _ _ -> ())
                  ~why_t1_t2: mkRIdent
                  ~t1:from_target 
                  ~t2:to_target
          in 
          if not okay then begin
            ignore (warnLoc e.eloc "Solver: BAD CAST / SEQ-SEQ@!   %a@!<- %a"
              d_type to_target d_type from_target)
          end 
        end
      end 
    ) cur.succ 
  ) node_ht) () ; 

  (* Step 8
   * ~~~~~~~
   * All other nodes are Safe, String, or Sentinel. 
   *)
  if !verbose then ignore (E.log "Solver: Step 8  (Safe)\n") ;
  IH.iter (fun id n -> 
     (* Replace Unknown/referenced with Safe, 
        Unknown/unreferenced with Sentinel,
        and UnknownN with String *)
    if n.kind = Unknown then begin
      if hasFlag n pkReferenced then
        update n Safe Unconstrained
      else
        update n Sentinel Unconstrained        
    end else if n.kind = UnknownN then begin
      update n String Unconstrained
    end ;

    (* Sanity Check! Typecheck.ml does much more than this. *)
    if n.kind = Safe &&
      (hasFlag n pkNotSafe || 
       hasFlag n pkString ||
       hasFlag n pkReachIndex || 
       hasFlag n pkIntCast) && 
      not (n.why_kind = UserSpec) &&
      not (is_polymorphic_voidstar n) then begin
      E.s (E.bug "Solver: botched node (left/made it safe) %d (%a)"
             n.id d_place_nice n.where)
    end ;

  ) node_ht
end 
