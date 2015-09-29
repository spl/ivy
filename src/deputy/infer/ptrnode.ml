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


(* Implements nodes in a graph representing the pointer locations in a 
 * program *)
open Cil
open Pretty
open Trace

module H = Hashtbl
module IH = Inthash
module E = Errormsg

(* Deputy uses separate compilation, so just about anything can
   escape.  So far, we only use this for pkReferenced  *)
let separateCompilation = true

(* If defaultIsNotWild then pointers without a qualifier are SAFE and only 
 * the arrays that are specfically SIZED contain a size field and only the 
 * variables that are specifically TAGGED contain tags *)
let defaultIsWild  = ref false


let useFSEQ = ref true
let useStrings = ref true
let extendStringBuffers = ref false

let allowOverride = ref true

let useOffsetNodes = true

let printVerboseOutput = ref false

(* Whether to check the chains *)
let doCheckChains = false


(* This function will be set by the Type module *)
let isSubtype: (typ -> typ -> bool) ref = ref (fun _ _ -> false)
let origSubtype = !isSubtype

(* flag to force functions to never be tagged *)
let wild_solve_untagged_functions = ref false

(* force functions to always be tagged *)
let wild_solve_tag_all_functions = ref false
    
(* True if the wild solver is used. *)
let use_wild_solver = ref false

(** How much detail to print.  -1 means do not print the graph *)
let emitGraphDetailLevel : int ref = Ivyoptions.emitGraphDetailLevel

let graphDetailLevelLegend =
"the level of detail in the .infer files:\n" ^
"\t 0 - just the nodes, kind and the chains\n" ^ 
"\t 1 - also the types, location, name and flags\n" ^ 
"\t 2 - also the edges (without) justification\n" ^ 
"\t 3 - everything"

let keepDetails () =
  !emitGraphDetailLevel > 0

(* A marker that the solver places, if we use lean fats *)
let useLeanFats = ref false

let allowPartialElementsInSequence = ref false
        
let hasPrefix p s = 
  let pl = String.length p in
  (String.length s >= pl) && String.sub s 0 pl = p
 
let hasSuffix suff s = 
  let ls = String.length s in
  let lsuff = String.length suff in
  ls >= lsuff && suff = String.sub s (ls - lsuff) lsuff

(* A place where a pointer type can occur *)
type place = 
    PGlob of string  (* A global variable or a global function *)
  | PType of string  (* A global typedef *)
  | PStatic of string * string (* A static variable or function. First is  
                                * the filename in which it occurs *)
  | PLocal of string * string * string (* A local varialbe. The name of the 
                                        * file, the function and the name of 
                                        * the local itself *)
  | POffset of int * string             (* An offset node, give the host node 
                                         * id and a field name *)
  | PField of fieldinfo                 (* A field of a composite type *)

  | PAnon of int                        (* Anonymous. This one must use a 
                                         * fresh int every time. Use 
                                         * anonPlace() to create one of these 
                                         * *)
  | PStr                                (* The global node for all string
                                         * literals. They all have the same
                                         * kind, so we don't need separate
                                         * nodes.*)
  | PWStr                               (* The global node for all wide string
                                         * literals. *)

let anonId = ref (-1) 
let anonPlace () : place = 
  incr anonId;
  PAnon !anonId

(* Each node corresponds to a place in the program where a qualifier for a 
 * pointer type could occur. As a special case we also add qualifiers for 
 * variables in expectation that their address might be taken *)
type node = 
    {         id: int;                  (* A program-wide unique identifier *)
              where: place * int;       (* A way to identify where is this 
                                         * coming from. We use this to make 
                                         * sure we do not create duplicate 
                                         * nodes. The integer is an index 
                                         * within a place, such as if the 
                                         * type of a global contains several 
                                         * pointer types (nested) *)

              btype: typ;               (* The base type of this pointer *)
      mutable attr: attributes;         (* The attributes of this pointer 
                                         * type *)
      mutable is_array: bool;           (* This node is associated with an
                                         * array, not with a pointer. *)

      mutable flags: (whyflag option) array; 

      mutable succ: edge list;          (* All edges with "from" = this node *)
      mutable pred: edge list;          (* All edges with "to" = this node *)

      
      (* The rest are the computed results of constraint resolution *)
      mutable kind: opointerkind;
      mutable why_kind: whykind;
      mutable sized: bool ;            (* An array may be SIZED at which
                                         * point it has a length field
                                         * stored right before it. This
                                         * leads to INDEX pointers. *)
      
      mutable locked: bool;            (* do not change this kind later *)
      mutable mark: bool;               (* For mark-and-sweep GC of nodes. 
                                         * Most of the time is false *)
      mutable rep : (node * chain ) option;
        (* the next node in the chain to the representative of this class. 
         * use get_rep to get the final representative *)
      mutable loc : Cil.location;       (* where did this node come from? *)
      
              shouldInfer: bool;        (* True if this is a local or a cast
                                           and we can do more aggressive
                                           inference. *)
    }       
   
and opointerkind = 
    Safe     (* a COUNT(1) pointer *)
  | Sentinel (* a COUNT(0) pointer.  If a pointer is not referenced,
                not NT, is not annotated SAFE, and does not use
                arithmetic, it gets this kind.*)
      
  | Seq    (* Needs lower and upper bounds *)
  | FSeq   (* Needs upper bound *)

  | SeqN 
  | FSeqN
  | String (* An NT COUNT(0) pointer *)

  | UnknownN (* An NT pointer with no annotated bounds.
                Inference turns this into String, FSeqN, or SeqN.
                If no pkArith flag is present after solving, this
                will default to String.*)

  | Unknown  (*  If no pkArith or pkString flag is present after solving,
                 this will default to Safe.*)

and whyflag = (* why is this flag set for this node? *)
  | ProgramSyntax of Cil.location

  (* This flag is set because it is set on some other node (node1 + the 
   * chain:node1->this). We also give the original source of the flag.  *)
  | FlagSpreadFromNode of node * chain * node

  | DownCast of node
  | SubtypeFailed of node
  | RequiredByEdge of edge
  | RequiredByPointerKind of opointerkind
  | RequiredByFlag of int
  | FlUserSpec of Cil.location  (* Annotated by a user *) 
  | MayEscape of Cil.location (* We are using separate compilation,
                                 and this node is not a local.
                                 Therefore, we assume it can be used
                                 by anybody. *)

and whykind = (* why did we give it this kind? *)
    BadCast of edge (* always attach to ECast edges *)
  | BadSequenceCast of edge
  | Incompat of node * chain * node (* Two nodes that should be in the same 
                                     * equivalence class are incompatible *)

  | BoolFlag of int
  | PolyInt (* This is a void* connected only to scalars *)
  | Default
  | UserSpec
  | Unconstrained
  | PrintfArg (* printf inference *)
  | Special of string * location

  (* This kind is set because it is set on some other node (node1 + the 
   * chain:node1->this). We also give the original source of the kind.  *)
  | SpreadFromNode of node * chain * node


and edge = 
    {         eid:      int;
      mutable efrom:    node;
      mutable eto:      node;
      mutable ekind:    edgekind;
      mutable eloc:     location;
    } 
      

and edgekind = 
    ECast of extra_edge_kind (* T_from ref q_from <= T_to ref q_to. We also 
                              * cary some additional explanation for this 
                              * edge. *)
  | EOffset                  (* From a pointer to struct to a pointer to 
                              * field *)
  | EIndex                   (* q_to = if q_from = wild then wild else index *)

  | ECompat                  (* the kinds of these two nodes must be
                              * compatible: either both wild, index or
                              * safe. This edge type is added by the solver
                              * for its convenience. In cases like
                              * int * 1 * 2 x; 
                              * int * 3 * 4 y;
                              * We will connect 1 and 3 with ECompat. *)
    of chain                (* An ECompat edge can always be explained
                              * using a list of ECast edges *)
  | ESameKind                (* Special edge that does not require
                              * compatibility of the types involved, but does
                              * require that they be of the same KIND. *)
     of extra_edge_kind_sk   (* See below for uses of ESameKind *)
  | EPointsTo                (* from's base type included to *)
  | EArgs                    (* From the pointer to the function to the 
                              * actual arguments and result values. Before we 
                              * added this edge we relied on WILDness to 
                              * spread from the function pointer to the 
                              * actual argument by means of EPoints to edge 
                              * to the formals and then ECast edges. But that 
                              * did not work when there were no formals 
                              * declared ! *)

(* More info about ECast edges *)
and extra_edge_kind = 
    EEK_cast                 (* A true cast *)
  | EEK_stringdrop           (* An NTDROP cast in deputy.  We do not push
                                pkString forwards across this edge.
                                (pkString flows backwards as usual) *)
  | EEK_cxxOverride          (* Due to the Cxx inheritance. See markcxx *)
  | EEK_extends              (* Due to an extends relationship *)
  | EEK_mkptr                (* Due to a mkptr or alignseq *)
  | EEK_union                (* Edges added between union fields *)
  | EEK_rtti                 (* Edges due to auto RTTI *)

(* More info about ESameKind edges *)
and extra_edge_kind_sk = 
  | EEK_trustedCast          (* This edge is added between the formal 
                              * argument and the result value in an instance 
                              * of trusted_cast function. This does not 
                              * require compatibility of the types involved 
                              * but does require that the two types be of the 
                              * same KIND *)
  | EEK_taggedUnion          (* Behaves like an trustedCast, but is sound.
                              * We use this to connect union fields that must
                              * have the same kind in case we cast from one to
                              * another, but we can ignore types on these edges
                              * since those are checked dynamically. *)


(************** CHAINS ********************)

(** An implementation of chains using constructors for sym and trans *)
and chain = 
        (* The chain why a node has a certain representative or why a 
         * ECompat edge exists *)
    RIdent          (* Identity: a relationship between identical nodes *)

  | RSingle of edge   
        (* This is an ECast edge. This chain is used for 
         * ECompat edges that arise "below" a ECast edge. *)

  | RSym of chain  (* If "chain" explains ECompat(n1-n2) then, 
        * "RSym(chain)" explains ECompat(n2-n1). *)

         (* Transitivity *)
  | RTrans of node * chain * chain * node * int
          (* Remember the first and the last nodes, and the length *)


  | RList of node * (bool * edge) list * node * int
        (* A list of elements along with the information whether they are 
         * reversed. Remember the first and the last node and the length. *)

(** Keep a table with the shortest path *)
type pathEntry = 
    { mutable peLen: int; (* Nr of RSingle *)
      mutable peChain: chain
    } 

let inftyLen = 1000000 (* A very large length *)
let idPathEntry = { peLen = 0; peChain = RIdent }

(* matth: unused in Deputy *)
let shortestPath: (int * int,  pathEntry) H.t = H.create 11111

let getShortestChain (nfrom: node) (nto: node) : pathEntry * bool = 
  if nfrom.id = nto.id then 
    idPathEntry, false
  else 
    let from', to', sym = 
      if nfrom.id < nto.id then 
        nfrom.id, nto.id, false
      else
        nto.id, nfrom.id, true
    in
    let pe = 
      Util.findOrAdd shortestPath (from', to')
        (fun _ -> { peLen = inftyLen; peChain = RIdent }) in
    pe, sym

let d_edge (e: edge) =  dprintf "%d->%d" e.efrom.id e.eto.id

let rec d_chain () (r: chain) =
  match r with 
    RIdent -> nil
  | RSingle e -> d_edge e (* dprintf "%d->%d" e.efrom.id e.eto.id *)
  | RSym r -> text "sym(" ++ d_chain () r ++ text ")"
  | RTrans (_, r1, r2, _, _) -> 
      if !emitGraphDetailLevel > 2 then 
        d_chain () r1 ++ text "," ++ d_chain () r2
      else text "..."
  | RList (_, l, _, _) -> 
      dprintf "list(%a)"
        (docList 
           (fun (isrev, a) -> 
             if isrev then text "sym(" ++ d_edge a ++ text ")" 
             else d_edge a))
           l
          
let rec dumpChain = function
    RIdent -> ignore (E.log "RID\n")
  | RSingle e -> ignore (E.log "Edge %a\n" insert (d_edge e))
  | RSym r ->
      ignore (E.log "(RSym \n");
      dumpChain r;
      ignore (E.log ")\n")
        
  | RTrans (_, r1, r2, _, _) -> 
      ignore (E.log "(RTrans \n");
      dumpChain r1;
      ignore (E.log ") and (\n");
      dumpChain r2;
      ignore (E.log ")\n")
  | RList (_, l, _, _) -> 
      ignore (E.log "list(\n");
      List.iter 
        (fun (isrev, a) -> 
          if isrev then 
            ignore (E.log "sym(%a)" insert (d_edge a))
          else
            ignore (E.log "Edge %a," insert (d_edge a)))
        l

let debugChains = false

let mkRIdent = RIdent
let mkRSingle e = RSingle e
    
    (* A few helper functions for manipulating chains *)
let mkRSym (r: chain) = 
  match r with 
    RIdent -> RIdent
  | RSym r1 -> r1
  | _ -> RSym r
        
let isSym (r: chain) = 
  match r with
    RSym r1 -> Some r1
  | _ -> None
        
(* Get one edge from the chain *)
let rec getOneEdge (r: chain) : edge option =
  match r with 
    RSingle e' -> Some e'
  | RSym r -> getOneEdge r
  | RTrans (_, r1, r2, _, _) -> getOneEdge r1
  | RList (_, ((_, h) :: _), _, _) -> Some h
  | RIdent -> None
  | RList _ -> None

let rec isOneEdge (r: chain) : edge option =
  match r with 
    RSingle e' -> Some e'
  | RSym r -> isOneEdge r
  | RList (_, [(_, e)], _, _) -> Some e
  | _ -> None

        (* Return a list of elements in a chain. The boolean value says 
         * whether the edge is reversed *)
let rec chainToList (c: chain) : (bool * edge) list = 
  (* We have the tail already. We have to cons on the beginning of it the 
   * argument, possibly symmetric *)

  (* Remember all the tails, indexed by the node number *)
  let tails: (int, (bool * edge) list) H.t = H.create 19 in
  let rec loop (sym: bool) (c: chain) 
               (tail: (bool * edge) list) =
    match c with 
      RIdent -> tail
    | RSingle e -> begin
        (* Maybe this cancels out with something in the tail *)
        match tail with 
          (sym', e') :: tail' when e == e' ->
            if sym <> sym' then 
              tail'
            else begin
              ignore (E.warn "duplicate edge in chain");
              (* (sym, e) :: *) tail
            end
        | _ -> begin
            (* This is the place where we extend the tail. Check if we can 
             * use a shorter tail *)
            let f = if sym then e.eto.id else e.efrom.id in
            let res = (sym, e) :: tail in
            Util.findOrAdd tails f (fun _ -> res)
        end
    end
    | RSym c -> loop (not sym) c tail
    | RTrans (_, r1, r2, _, _) -> 
        (* ignore (E.log "chainToList(%x)\n" (Obj.magic c)); *)
        if sym then
          loop sym r2 (loop sym r1 tail) 
        else
          loop sym r1 (loop sym r2 tail) 
    | RList (_, l, _, _) -> 
        if sym then (* Must reverse the list as well *)
          List.fold_left
            (fun acc (isrev, h) -> 
              loop (sym <> isrev) (RSingle h) acc)
            tail
            l
        else if tail = [] then 
          l (* since sym = false && tail = [] *)
        else
        ( try 
          List.fold_right
            (fun (isrev, h) acc -> 
              loop (sym <> isrev) (RSingle h) acc)
            l
            tail
          with e -> 
            (ignore (E.warn "List.fold_right raises %s"
              (Printexc.to_string e)) ; raise e)
        ) 
  in
  loop false c []

  
let rec getFirstAndLastNode (sym: bool) (c: chain) : node * node * int = 
  match c with 
    RSingle e -> 
      let fn, ln = if sym then e.eto, e.efrom else e.efrom, e.eto in
      fn, ln, 1

  | RSym c -> getFirstAndLastNode (not sym) c
  | RTrans (fn, _, _, ln, len)
  | RList (fn, _, ln, len) -> 
      if sym then ln,fn,len else fn,ln,len
  | _ -> E.s (E.bug "getFirstAndLastEdge: %a" d_chain c)

      
(* A helper function for concatenating chains. Call when both of the chains 
 * are non-empty. *)
let mkRTransHelper (r1: chain) (r2: chain) : chain = 
  let fn1, ln1, len1 = getFirstAndLastNode false r1 in
  let fn2, ln2, len2 = getFirstAndLastNode false r2 in
  (* Get the data about this whole path *)
  let pe, sym = getShortestChain fn1 ln2 in
  (* See if the new one has any chance of being better *)
  if pe.peLen <= len1 + len2 then 
    if sym then mkRSym pe.peChain else pe.peChain (* Keep the old one *)
  else begin
    (* Prepare the possible result *)
    let res = RTrans(fn1, r1, r2, ln2, len1 + len2) in
    (* The new one is better. See how small it can get *)
    if debugChains then 
      ignore (E.log "Finding best chain from %d->%d. Right now %d->%d(%d) + %d->%d(%d)\n"
                fn1.id ln2.id fn1.id ln1.id len1 fn2.id ln2.id len2);
    let l = chainToList res in
    let l_len = List.length l in
    if debugChains && l_len > 40 then begin
      ignore (E.log "  res=%a@!"
                (docList
                   (fun (sym, e) -> 
                     if sym then dprintf "<-%d" e.efrom.id
                     else dprintf "->%d" e.eto.id))
                l);
    end;
    let bestLen, bestChain =
      if l_len < len1 + len2 then 
        l_len, (if l_len = 0 then RIdent else RList (fn1, l, ln2, l_len))
      else
        len1+len2, res
    in
    (* Update the entry *)
    if debugChains then 
      ignore (E.log "Setting best chain from %d->%d of length %d %s\n"
                fn1.id ln2.id bestLen
                (if bestLen < len1 + len2 then "(compressed)" else ""));
    pe.peLen <- bestLen;
    pe.peChain <- if sym then mkRSym bestChain else bestChain;
    bestChain
  end

let mkRTransChain (r1: chain) (r2: chain) = 
  let isSymOf (r1: chain) (r2: chain) = 
    match r1, r2 with 
    | r1, RSym r1' when r1 == r1' -> true
    | RSym r2', r2 when r2 == r2' -> true
    | _, _ -> false
  in
  begin
    match r1, r2 with 
      RIdent, r2 -> r2
    | r1, RIdent -> r1
          (* It is important to recognize some special cases that lead to 
          * exponential explosion *)
    | r1, r2 when isSymOf r1 r2 -> RIdent
    | r1, RTrans (_, r1', r2, _, _) when isSymOf r1 r1' -> r2
    | RTrans (_, r1, r2, _, _), r2' when isSymOf r2 r2' -> r1
    | _, _ -> mkRTransHelper r1 r2
  end
          
     


(* A mapping from place , index to ids. This will help us avoid creating 
 * duplicate nodes *)
let placeId: (place * int, node) H.t = H.create 1111

(* A mapping from ids to nodes. Rarely we need to find a node based on its 
 * index. *)
let idNode: node IH.t = IH.create 1111

(* Next identifier *)
let lastNodeId = ref (-1)



let pkInterface = 0          (* this is an interface node *)
let pkUpdated = 1            (* we write through this pointer *)
let pkIntCast = 2           (* can contain an integer *)
let pkPosArith = 3          (* subject to positive pointer arithmetic *)
let pkArith = 4             (* subject to arbitrary pointer arithmetic *)
let pkString = 5            (* A String node. The value at the end of the
                               buffer is a nul.  matth, sept05: This
                               flows forwards and backwards now.*)
let pkReachIndex = 6       (* can reach an Index node *)
let pkNoPrototype = 7     (* Used as actual argument in a function without 
                              * prototype *)
let pkEscape = 8          (* value may be assigned thru a pointer and
                           * escape  to the heap *)
let pkNotSafe = 9    (* constraint used by solvers: node must not be Safe *)

let pkReferenced = 10 (* might be eventually referenced *)

let pkRtti = 11

let pkCompatWithScalars = 12
  (* This flag means that a void* node (or its equivalence class) must be
   * compatible with a scalar. Example:
   *   void *1 *2 v;
   *   int *3 x;
   *   v = x; 
   * In this case, node 1 should have this flag. 
   * (1) This flag is only valid on "void*" nodes. If a non-"void*" node
   * has this flag, that node should be WILD by the end of solving. 
   * (2) This flag will always be present on the rep of a class if any node
   * in that class has it.
   * (3) If a node (or its rep) has this flag, then polymorphic_replace
   * will return Int for the type of that node. 
   * (4) This flag is propagated whenever new reps are created.
   *)

(* Could point to the stack; CHECK_STORE_PTR and CHECK_RETURN needed. 
 * This is too conservative, since we flow this flag through globals and the
 * heap, even though we know the checks will prevent that at runtime.  But
 * it's good enough for now. *)
let pkStack = 13

let pkOneWord = 14 (** Specified by user to be one word *)

let pkFlagName = (* should match up with the order above *)
  [| "Interface Node" ;
     "Updated" ;
     "Contains an Integer" ;
     "Positive Arithmetic" ;
     "Arithmetic" ;
     "Reaches String" ;
     "Reaches Index" ;
     "No Prototype" ;
     "Value Escapes to the Heap" ;
     "Cannot be SAFE" ;
     "Referenced"; 
     "Has RTTI" ;
     "Compatible with Scalars";
     "Might Point To Stack";
     "One Word" |]

let pkNumberOfFlags = Array.length pkFlagName
let pkLastFlag = pkNumberOfFlags - 1

(* These are bitmasks of flags. *) 
let pkCastPredFlags = [pkUpdated ; pkPosArith ; pkArith ; pkEscape ;
                       pkReferenced]
let pkCNIPredFlagsNoString =  (* for ECast EEK_stringdrop *)
  [pkReachIndex ; pkReferenced ]
let pkCNIPredFlags =          (* all ECasts except stringdrop *)
  pkString :: pkCNIPredFlagsNoString
let pkCastSuccFlagsNoString = (* for ECast EEK_stringdrop *)
  [pkIntCast ; pkStack]
let pkCastSuccFlags =         (* all ECasts except stringdrop *)
  pkString :: pkCastSuccFlagsNoString 
let pkOffsetSuccFlags = [pkEscape]
let pkOffsetPredFlags = [pkReferenced]

(* A list of all indices into the array *)
let allFlags = 
  let rec allIndices (n: int) : int list = 
    if n > pkLastFlag then [] else n :: allIndices (n + 1)
  in
  allIndices 0

let emptyFlags () = Array.make pkNumberOfFlags None 

(* set a boolean bitflag *)
let setFlag n f why = 
  if n.flags.(f) = None then n.flags.(f) <- Some(why)
(* check a boolean bitflag *)
let hasFlag n f = n.flags.(f) <> None 


let canHaveRtti (t: typ) : bool = isVoidType t

let allKinds = 
    [ Safe; Sentinel; Seq;
      FSeq; SeqN; FSeqN;
      String; UnknownN;
      Unknown ]

(* Just some code to check that we have added all pointer kinds to allKinds. 
 * If the compiler complains about an inexhaustive pattern then you have 
 * probalby added new pointer kinds. Add them to the pattern AND TO allKinds 
 * above. *)
let _ = 
  List.iter 
    (function 
      | Safe | Sentinel
      | String | UnknownN
      | Seq | SeqN 
      | FSeq | FSeqN 
      | Unknown -> ())
    allKinds

(* Print the graph *)
let d_place () = function
    PGlob s -> dprintf "Glob(%s)" s
  | PType s -> dprintf "Type(%s)" s
  | PStatic (f, s) -> dprintf "Static(%s.%s)" f s
  | PLocal (f, func, s) -> dprintf "Local(%s.%s.%s)" f func s
  | POffset (nid, fld) -> dprintf "Offset(%d, %s)" nid fld
  | PField(fi) -> dprintf "Field(%s.%s)" fi.fcomp.cname fi.fname
  | PAnon id -> dprintf "Anon(%d)" id
  | PStr -> text "Str"
  | PWStr -> text "WStr"

(* Print the place "nicely", in a human-readable format *)
let d_place_nice () (p,i) = match p with 
    PGlob s -> dprintf "the global %s" s
  | PType s -> dprintf "the type %s" s
  | PStatic (f, s) -> dprintf "the static variable %s" s
  | PLocal (f, func, s) -> dprintf "the local variable %s" s
  | POffset (nid, fld) -> dprintf "the field %s of node %d" fld nid
  | PField(fi) -> dprintf "the field %s" fi.fname
  | PAnon id -> text "an unnamed location (often an inserted cast)" 
  | PStr -> text "global string literal node."
  | PWStr -> text "global wide-string literal node."

let d_placeidx () (p, idx) = 
  dprintf "%a.%d" d_place p idx

let d_opointerkind () = function
    Safe -> text "SAFE"
  | Sentinel -> text "SNT"
  | FSeq -> text "FSEQ" 
  | FSeqN -> text "FSEQN" 
  | UnknownN -> text "UNKNOWN_NT" 
  | String -> text "STRING"
  | Seq -> text "SEQ"
  | SeqN -> text "SEQN"
  | Unknown -> text "UNKNOWN" 

let d_eekind () = function
    EEK_cast -> nil
  | EEK_stringdrop -> text "(ntdrop)"
  | EEK_cxxOverride -> text "(cxx_override)"
  | EEK_extends -> text "(extends)"
  | EEK_mkptr -> text "(mkptr)"
  | EEK_union -> text "(union)"
  | EEK_rtti -> text "(rtti)"

let d_ekind () = function
    ECast eek -> text "Cast" ++ d_eekind () eek
  | EOffset -> text "Offset"
  | EIndex -> text "Index"
  | ECompat(r) -> dprintf "Compat(%a)" d_chain r
  | ESameKind EEK_trustedCast -> text "TCast"
  | ESameKind EEK_taggedUnion -> text "Union"
  | EPointsTo -> text "Points"
  | EArgs -> text "Args"

let d_whyflag (n: node) () = function 
  | ProgramSyntax(l) -> dprintf "Syntax at %a" d_loc l 
  | DownCast(n) -> dprintf "Downcast With Node %d" n.id
  | SubtypeFailed(n) -> dprintf "Subtyping Failed With Node %d" n.id
  | RequiredByEdge(e) -> dprintf "Required By %a Edge %d->%d"
      d_ekind e.ekind e.efrom.id e.eto.id 
  | RequiredByPointerKind(o) -> dprintf "Required For %a Nodes"
      d_opointerkind o 
  | RequiredByFlag(i) -> dprintf "Required By Flag [%s]"
      pkFlagName.(i) 
  | FlagSpreadFromNode(near,r_near_this,orig) -> 
      dprintf "Spread from %d (%a). Transitive from %d"
        near.id d_chain r_near_this orig.id
  | FlUserSpec l -> text "User-specified at " ++ d_loc () l
  | MayEscape l -> text "May escape this file at " ++ d_loc () l
    

let ptrAttrCustom = 
  (* Define a hash table for printing the attributes *)
  let ptrAttrCustomTable: (string, string * (attrparam list -> doc)) H.t = 
    let h: (string, string * (attrparam list -> doc)) H.t  = H.create 31 in
    let noArgs (al: attrparam list) : doc = 
      match al with 
        [] -> nil
      | _ -> raise Not_found
    in
    let doArgs (al: attrparam list) : doc = 
      dprintf "(@[%a@])" 
        (docList (d_attrparam ())) al
    in
    let addSimple (n: string) = 
      H.add h n ("__" ^ String.uppercase n, noArgs)
    in
    List.iter addSimple 
      ["ronly"; "seq"; "fseq"; "seqn"; "fseqn" ];
    H.add h "selector" ("__SELECTOR", doArgs);
    H.add h "selectedwhen" ("__SELECTEDWHEN", doArgs);
    H.add h "size" ("__SIZE", doArgs);
    H.add h "count" ("__COUNT", doArgs);
    h
  in
  fun ~(printnode: bool) (a: attribute) ->
    match a with 
      Attr("_ptrnode", [AInt n]) -> 
        if printnode then
          Some (dprintf "__NODE(%d)" n)
        else begin
          Some nil
        end
    | Attr("safe", []) -> 
        if printnode then Some (text "__SAFE") else Some nil
    | Attr("discriminated_union", []) -> Some nil
    | Attr("stack", []) -> Some (text "__STACK")
    | Attr("trustedunion", []) -> Some (text "__TRUSTEDUNION")
    | Attr("safeunion", []) -> Some (text "__SAFEUNION")
    | Attr("heapify", []) -> Some (text "__HEAPIFY")
    | Attr("nocure", []) -> Some (text "__NOCURE")
    | Attr("nounroll",[]) -> Some (text "__NOUNROLL")
    | Attr("noescape", []) -> Some (text "__NOESCAPE")
    | Attr("ccuredvararg", [ASizeOf t]) -> Some (text "__CCUREDVARARG(" ++ 
                                                d_type () t ++ text ")")
    | Attr("ccuredformat", [AInt fidx]) -> Some (text "__CCUREDFORMAT(" ++
                                                num fidx ++ text ")")
    | Attr("override", [AStr s]) -> Some (text ("__OVERRIDE(\"" ^ s ^ "\")"))
    | Attr("main_input", []) -> Some (text (""))
    | Attr("metacomp", []) -> Some (text "")
    | Attr("mergecomp", []) -> Some (text "")
    | Attr("mdsize", _) -> Some (text "")
    | Attr("annotated", _) -> Some (text "")
    | Attr (n, args) -> begin
        try 
          let n', args' = H.find ptrAttrCustomTable n in
          Some (text n' ++ (args' args))
        with Not_found -> None
    end

(* Now define a special way of printing the infer file *)
class ccuredInferPrinterClass = object 
  inherit defaultCilPrinterClass as super

  method pAttr (a: attribute) : doc * bool = 
    match ptrAttrCustom ~printnode:true a with 
      Some d -> d, false
    | None -> super#pAttr a

  (* We do not print some pragmas *)
  method dGlobal (out: out_channel) (g: global) : unit = 
    match g with
    | GPragma(Attr(n, _), _) -> 
        if hasPrefix "ccured" n || hasPrefix "cil" n then
          if !printVerboseOutput then begin
            fprint out 80 (text "// ");
            super#dGlobal out g
          end else
            ()
        else
          ()

    | GText t -> 
        if !printVerboseOutput || not (t = "//\n") then
          super#dGlobal out g

    | g -> super#dGlobal out g
    
end
let ccuredInferPrinter = new ccuredInferPrinterClass

let d_type = printType ccuredInferPrinter

let d_whykind (n: node) () = function
  | BadCast e -> 
      dprintf "cast(%a(%d) <= %a(%d)) at %a" 
        d_type e.eto.btype e.eto.id d_type e.efrom.btype e.efrom.id 
        d_loc e.eloc
  | BadSequenceCast e -> 
      dprintf "cast(%a(%d) <= %a(%d)) at %a (and cannot be sequence)" 
        d_type e.eto.btype e.eto.id d_type e.efrom.btype e.efrom.id 
        d_loc e.eloc
  | Incompat (n1, why_n1_n2, n2) -> 
      dprintf "Incompat %d and %d (%a)"
        n1.id n2.id d_chain why_n1_n2
  | BoolFlag(i) -> dprintf "from_flag(%s)" pkFlagName.(i)
  | PolyInt -> dprintf "void* equivalent to scalar"
  | Default -> text "by_default"
  | UserSpec -> text "user_spec"
  | Unconstrained -> text "unconstrained"
  | PrintfArg -> text "printf_arg"
  | Special (s, l) -> text (s ^ " at ") ++ d_loc () l
  | SpreadFromNode(near,r_near_this,orig) -> 
      dprintf "Spread from %d (%a). Transitive from %d\n"
        near.id d_chain r_near_this orig.id

let d_node () n = 
    num n.id 
     ++ text " : " 
     ++ (match n.rep with 
          None -> nil 
        | Some (nrep, _) -> dprintf "(rep is %d) " nrep.id)
     ++ (if !emitGraphDetailLevel > 1 then d_placeidx () n.where  else nil)
     ++ (if !emitGraphDetailLevel > 1 then text " L=" ++ Cil.d_loc () n.loc else nil) 
     ++ line
     ++ text " K="  ++ d_opointerkind () n.kind
     ++ text "/"  ++ (d_whykind n) () n.why_kind
     ++ (if !emitGraphDetailLevel > 0 then text " T="  ++ d_type () n.btype else nil) 
     ++
     (if !emitGraphDetailLevel > 0 &&
       (Array.fold_left (fun acc elt -> acc || elt <> None) false n.flags) 
     then begin
       line ++ text "Flags: "
         ++ (align
               ++ (docArray ~sep:(text "")
                     (fun i flag_opt -> match flag_opt with
                       (* Do not print the pkNotSafe flag. It is for internal 
                        * use and in the case of polymorphic_void* we 
                        * actuallly may make such nodes SAFE, creating 
                        * confusion *)
                     | Some(why) when i <> pkNotSafe -> 
                         dprintf "@![%s]: %a" pkFlagName.(i) (d_whyflag n) why 
                     | _ -> nil
                           ) () n.flags)
               ++ unalign ++ line)
     end else begin
       nil
     end)
    ++ 
    (if !emitGraphDetailLevel > 1 then 
      line 
        ++ text "  S="
        ++ (align 
              ++ (docList ~sep:(chr ',' ++ break)
                    (fun e ->
                      num e.eto.id
                        ++ text ":"
                        ++ d_ekind () e.ekind
                        ++ text "@" ++ d_loc () e.eloc)
                    ()
                    n.succ)
              ++ unalign)
        ++ line
        ++ text "  P="
        ++ (align 
              ++ (docList ~sep:(chr ',' ++ break)
                    (fun e ->
                      num e.efrom.id
                        ++ text ":"
                        ++ d_ekind () e.ekind)
                    ()
                    n.pred)
              ++ unalign)
     else nil)

    ++ line
        
let nodeOfAttrlist al = 
  let findnode n =
    try Some (IH.find idNode n)
    with Not_found -> E.s (E.bug "Cannot find node with id = %d\n" n)
  in
  match filterAttributes "_ptrnode" al with
    [] -> None
  | [Attr(_, [AInt n])] -> findnode n
  | (Attr(_, [AInt n]) :: _) as filtered -> 
      ignore (E.warn "nodeOfAttrlist(%a)" d_attrlist filtered);
      findnode n
  | _ -> E.s (E.bug "nodeOfAttrlist")

let nodeOfType (t: typ) : node option =  nodeOfAttrlist (typeAttrs t)

(* weimer: find the node that points to this one *)
let nodeThatPointsTo (child : node) = 
  try
    let e = List.find (fun e -> e.ekind = EPointsTo) child.pred in
    Some e.efrom
  with Not_found -> None

let k2attr = function
    Safe -> Attr("safe", [])
  | Seq -> Attr("seq", [])
  | FSeq -> Attr("fseq", [])
  | SeqN -> Attr("seqn", [])
  | FSeqN -> Attr("fseqn", [])
  | String -> Attr("string", [])
  | k -> E.s (E.unimp "k2attr:%a" d_opointerkind k)

let nullterm_kind     =  64
let rec k2number = function
  | Sentinel -> 0
  | Safe -> 1
  | Seq ->  2
  | FSeq -> 3
  | String ->  6
  | SeqN -> nullterm_kind + k2number Seq
  | FSeqN -> nullterm_kind + k2number FSeq
  | k -> E.s (E.unimp "k2number:%a" d_opointerkind k)



(* The inferred kind for this node. Optionally, do it only for inferrable 
 * nodes. *)
let inferredKindOf ?(localOnly=false) 
                   (allAttributes: attributes) : opointerkind * whykind =
  let default = 
    if hasAttribute "nullterm" allAttributes then
      UnknownN, Default
    else
      Unknown, Default
  in
  let rec loop al =
    (* If there's no UserSpec kind, look at the node *)
    match al with
      Attr ("_ptrnode", [AInt n])::_ -> begin
        let nd = IH.find idNode n in
        (* If local only is set, then we look at the place for this node *)
        if not localOnly || 
          (match nd.where with 
              (PLocal _ | PAnon _), 1 -> true
              | _ -> false) then 
          nd.kind, nd.why_kind
        else
          default
      end
    | _::rest -> loop rest
    | [] -> (* No NODE() attribute *)
        default
  in
  loop allAttributes


(* The kind of this pointer.  If there is no BND attribute,
   defaults to inferredKind *)
let kindOfAttrlist allAttributes: opointerkind * whykind = 
  let isNullterm = hasAttribute "nullterm" allAttributes in
  let rec loop al =
    match al with
      Attr("bounds", [a1;a2])::rest -> begin
        match Dutil.checkParam a1, Dutil.checkParam a2 with
        | Dutil.PKThis, Dutil.PKThis ->
            if isNullterm then 
              String, UserSpec
            else
              (* Sentinel, UserSpec *)
              inferredKindOf allAttributes
        | Dutil.PKThis, Dutil.PKOffset (AInt 1) -> (* SAFE -> SAFE*)
            (if isNullterm then FSeqN else Safe),
            UserSpec
        | Dutil.PKThis, Dutil.PKOffset a ->        (* COUNT -> FSEQ *)
            (if isNullterm then FSeqN else FSeq),
            UserSpec
        | _ ->                                       (* BND -> SEQ *)
            (if isNullterm then SeqN else Seq),
            UserSpec
      end
    | Attr("size", _)::rest ->
        (if isNullterm then FSeqN else FSeq),
        UserSpec
    | _::rest -> loop rest
    | [] -> (* No BND annotation *)
        inferredKindOf allAttributes
  in
  loop allAttributes

let kindIsNullterm (k:opointerkind) : bool =
  match k with
  | Safe | Sentinel | Seq | FSeq | Unknown -> false
  | String | SeqN | FSeqN | UnknownN -> true

let kindNeedsBounds (k:opointerkind) : bool =
  match k with
  | Safe | Sentinel | String | Unknown | UnknownN -> false
  | Seq | FSeq | SeqN | FSeqN -> true

    

(* Replace the ptrnode attribute with the actual qualifier attribute *)
type whichAttr = 
    AtPtr  (* In a pointer type *)
  | AtArray  (* In an array type *)
  | AtOpenArray (* In an array type without a size *)
  | AtVar (* For a variable *)
  | AtOther (* Anything else *)


let replacePtrNodeAttrList ~(which:whichAttr) al = 
(*  ignore (E.log "replacePtrNode: %a\n"
            (d_attrlist true) al); *)
  let foundKind : string ref = ref "" in
  let foundInNode : bool ref = ref false in
  let foundAnother (innode: bool) (s: string) = 
    if innode then begin
      foundInNode := true;
      foundKind := s (* Discard all others *)
    end else
      (* Look at non-node ones only if we haven't found a node *)
      if not !foundInNode then foundKind := s
  in
  (* Scan the attributes and look at pointer kind attributes and at node 
   * attributes. Remove all pointer-kind attributes and set foundKind and 
   * foundInNode if it was found in a node. *)
  let rec loop = function
      [] -> []
    | a :: al -> begin
        match a with
          Attr("_ptrnode", [AInt n]) -> begin
            try 
              let nd = IH.find idNode n in
              let found = 
                if nd.kind = Unknown then begin
                  ignore (E.warn "Found node %d with kind Unknown" n);
                  ""
                end else 
                  match k2attr nd.kind with
                    Attr(s, _)  -> s
              in
              foundAnother true found;
              a :: loop al
            with Not_found -> begin
              ignore (E.warn "Cannot find node %d" n);
              a :: loop al
            end
          end
        | Attr("safe", []) -> foundAnother false "safe"; loop al
        | Attr("seq", []) -> foundAnother false "seq"; loop al
        | Attr("fseq", []) -> 
            foundAnother false (if !useFSEQ then "fseq" else "seq"); loop al
        | Attr("seqn", []) -> 
            foundAnother false (if !useStrings then "seqn" else "seq"); loop al
        | Attr("fseqn", []) -> 
            foundAnother false 
              (if !useFSEQ then 
                (if !useStrings then "fseqn" else "fseq")
              else (if !useStrings then "seqn" else "seq")); loop al
        | Attr("string", []) when !useStrings -> 
            foundAnother false "string"; loop al
        | Attr("rostring", []) when !useStrings -> 
            foundAnother false "rostring"; loop al
        | _ -> a :: loop al
    end
  in 
  let al' = loop al in (* Get the filtered attributes *)
  let kres = 
    match which with
      AtPtr -> 
        if !foundKind <> "" then !foundKind 
        else if !defaultIsWild then "wild" else "safe" 
    | (AtArray | AtOpenArray) -> 
        if !foundKind = "seqn" then "nullterm" 
        else if !foundKind = "fseqn" then "nullterm" 
        else if !foundKind = "string" then "nullterm" 
        else if !foundKind = "rostring" then "nullterm" 
        else !foundKind
    | (AtVar | AtOther) -> !foundKind
  in
  if kres <> "" then 
    addAttribute (Attr(kres,[])) al' 
  else 
    al'

let nodeExists (p: place) (idx: int) = 
  H.mem placeId (p, idx)

let existsEdge ~(start : node) ~(dest : node) ~(kind : edgekind) =
  List.fold_left (fun acc e -> acc ||
   (e.eto.id = dest.id && e.ekind = kind)) false start.succ

let isECompat e =
  match e.ekind with
    ECompat _ -> true
  | _ -> false 

let isECast e = 
  match e.ekind with
    ECast _ -> true
  | _ -> false

let isESameKind e = 
  match e.ekind with
    ESameKind _ -> true
  | _ -> false

let lastEdgeIdx = ref 0 (* 0 is reserved for the union edge *)
let addEdge ~(start: node) ~(dest: node) ~(kind: edgekind)
            ~(eloc : Cil.location option) =

  incr lastEdgeIdx;
  let nedge = 
    { eid = !lastEdgeIdx;
      efrom = start; eto= dest; ekind = kind;
      eloc = match eloc with 
              Some(loc) -> loc
            | None -> !currentLoc } in
  start.succ <- nedge :: start.succ;
  dest.pred <- nedge :: dest.pred ;
  nedge

let removeSucc n sid = 
  n.succ <- List.filter (fun e -> e.eto.id <> sid) n.succ

let removePred n pid = 
  n.pred <- List.filter (fun e -> e.efrom.id <> pid) n.pred

(* Delete an edge from the graph *)
let removeEdge e =
  if not (List.memq e e.efrom.succ) then 
    E.s (bug "edge not in e.efrom.succ");
  if not (List.memq e e.eto.pred) then
    E.s (bug "edge not in e.eto.pred");
  e.efrom.succ <- List.filter ((!=) e) e.efrom.succ;
  e.eto.pred <- List.filter ((!=) e) e.eto.pred

(** Set the EPointsTo edges for a node. *)
let setNodePointsTo (n: node) =        
  let doOneType = function
      (* This will add points to to pointers embedded in structures or in 
      * functions (function return or arguments) *)
      TPtr (bt, a) -> begin
        (match nodeOfAttrlist a with
        | Some n' -> ignore (addEdge n n' EPointsTo (Some n.loc))
        | _ -> (*
           ignore 
              (warn "Node %d points to a pointer of type %a without a node" 
                 n.id d_type bt); *)
            ());
        ExistsFalse
      end
    | _ -> ExistsMaybe
  in
  ignore (existsType doOneType n.btype);


  (* If a structure contains an array, a pointer to that structure also 
  * contains a pointer to the array. We need this information to
  * properly handle wild pointers. *)
  let lookForInternalArrays = function
      TArray(bt,len,al) -> begin
        (match nodeOfAttrlist al with
        | Some n' -> ignore (addEdge n n' EPointsTo (Some !currentLoc))
        | _ -> ());
        ExistsFalse
      end
          
    | _ -> ExistsMaybe
  in 
  ignore (existsType lookForInternalArrays n.btype)
  
(* Make a new node *)
let newNode ~(p: place) ~(idx: int) ~(bt: typ) ~(al: attributes) : node =
  let where = p, idx in
  incr lastNodeId;
  (* Maybe it has a kind specified by the user *)
  let kind,why_kind = kindOfAttrlist al in
  let shouldInfer = match p with
      PLocal _ | PAnon _ -> true
    | _ -> false
  in
(*  if !lastNodeId = 1 then 
    ignore (E.log "newNode: %a\n" d_opointerkind kind); *)
(*   E.log "%a: new node %d has attrs %a, kind %a\n" d_loc !currentLoc *)
(*     !lastNodeId d_attrlist al d_opointerkind kind; *)
  let n = { id = !lastNodeId;
            btype   = bt;
            attr    = addAttribute (Attr("_ptrnode", [AInt !lastNodeId])) al;
            is_array = false;
            where   = where;
            flags   = emptyFlags () ;
            locked = false;
            succ = [];
            kind = kind;
            why_kind = why_kind; 
            sized = false ;
            mark = false;
            pred = []; 
            rep = None;
            loc = !Cil.currentLoc;
            shouldInfer = shouldInfer; } 
  in
  if hasAttribute "noescape" al then
    setFlag n pkStack (FlUserSpec !Cil.currentLoc);
  if separateCompilation && not shouldInfer then
    (* Not a local or cast.  Therefore, assume it's referenced somewhere. *)
    setFlag n pkReferenced (MayEscape !Cil.currentLoc);

(*  ignore (E.log "Created new node(%d) at %a\n" n.id d_placeidx where); *)
  H.add placeId where n;
  IH.add idNode n.id n;
  (* We do not yet set the EPointsTo edges because we might have forward 
   * references. But once we have created all the nodes, we should call the 
   * setNodePointsTo *)
  setNodePointsTo n;
  n
    

(** Dummy node is a node with the ID=0 *)
let dummyNode = newNode (PGlob "@dummy") 0 voidType []


(* Get a node for a place and an index. Give also the base type and the 
 * attributes *)
let getNode ~(p: place) ~(idx: int) ~(bt: typ) ~(al: attributes) : node = 
  (* See if exists already *)
  let where = (p, idx) in
  try
    H.find placeId where
  with Not_found -> newNode p idx bt al


            (** Check that a node points to another node *)
let rec checkPointsTo (seen: int list) (* To prevent recursion *)
    (nstart: node) 
    (nend_id: int) : bool = 
  (* Scan all EPoints successors of nstart *)
  if nstart.id = nend_id then true
  else begin
    if List.exists (fun s -> s = nstart.id) seen then begin
      ignore (E.log "checkPointsTo: circularity at %d\n" nstart.id);
      false
    end else begin
      let seen' = nstart.id :: seen in
      List.exists (fun e -> 
        e.ekind = EPointsTo && 
        checkPointsTo seen' e.eto nend_id) nstart.succ
    end
  end


            (* Check that a node does not occur twice in a chain. We use 
             * this function to debug circular chains *)
let rec checkChain 
        (start: node) (* The node that we think the edge should 
                       * be starting from *)
        (r: chain) : node * int list = 
  if not (keepDetails ()) then 
    E.s (bug "checkChains but not keeping details");
  let edges = chainToList r in
  let rec loop (start: node) (* The next expected node *)
               (seen: int list) (* Nodes we've seen already *) = function
      [] -> start, seen
    | (sym, e) :: rest -> 
        (* Orient the edge appropriately *)
        let estart, eend = if sym then e.eto, e.efrom else e.efrom, e.eto in
        (* Check that we start at the right points. estart must be pointing to 
        * start or viceversa *)
        if start.id <> 0 &&
          not (checkPointsTo [] start estart.id) &&
          not (checkPointsTo [] estart start.id) then begin
            ignore (E.warn 
                      "Disconnected chain: start=%d, edge %d->%d\n seen = %a\n" 
                      start.id e.efrom.id e.eto.id
                      (docList num) (List.rev seen));
            raise (Failure "bad chain: disconnected")
          end;
        (* Complain if we've seen eend.id already *)
        if List.exists (fun s -> s = eend.id) seen then begin
          ignore (E.warn 
                    "Circular chain: start=%d, edge %d->%d\n seen = %a\n" 
                    start.id e.efrom.id e.eto.id
                    (docList num) (List.rev seen));
          raise (Failure "bad chain: circular")
        end;
        loop eend (eend.id :: (if start.id = 0 then [estart.id] else seen)) 
          rest
  in
  loop start [] edges

let checkChainEnds (nstart: node) (nend: node) (r: chain) : unit = 
  try
    let end', seen'  = checkChain nstart r in
    if not (checkPointsTo [] end' nend.id) &&
       not (checkPointsTo [] nend end'.id) then begin
        ignore (E.warn "checkChainEnds. Ends at %d and expected %d" 
                  end'.id nend.id);
        raise (Failure "bad chain: misoriented edge")
      end
  with e -> begin
    ignore (E.log "Failed the check that chain starts at %d and ends at %d\n"
              nstart.id nend.id);
    ();
  end


(* Override mkRTrans to do some checking *)
let mkRTrans (r1: chain) (r2: chain) = 
  let res = mkRTransChain r1 r2 in
  if doCheckChains && res != r1 && res != r2 then begin
    try 
      ignore (checkChain dummyNode res);
    with e -> begin
      ignore (E.warn "Trying to mkRTrans of");
      dumpChain r1;
      ignore (E.log "  and \n");
      dumpChain r2;
      raise e
    end
  end;
  res




(* Given a flag for a node, produce the original node where the flag 
 * originates, the true chain why it originates, and the chain:orig->this *)
let rec trueSourceOfFlag (n: node) (f:int) : node * whyflag * chain = 
  match n.flags.(f) with
  | Some(FlagSpreadFromNode(near,r_near_n,source)) when near.id <> n.id -> 
      let orig, why, r_orig_near = trueSourceOfFlag near f in
      orig, why, mkRTrans r_orig_near r_near_n
  | Some w -> n, w, mkRIdent
  | None -> E.s (bug "trueSourceOfFlag(%d, %d)" n.id f) 




(* obtain the representative of this equivalence class. Also return the 
 * reaons n -> representative *)
let rec get_rep_why (n: node) : node * chain =
  match n.rep with
    Some(nr,why_n_nr) -> 
      let final_result, why_nr_final_result = get_rep_why nr in
      if final_result == nr then 
        nr, why_n_nr
      else begin
        (* Do path compression *)
        let why_n_final_result = mkRTrans why_n_nr why_nr_final_result in
        if not (hasFlag n pkRtti) then begin
          (if hasFlag n pkCompatWithScalars then
            let orig,_,_ = trueSourceOfFlag n pkCompatWithScalars in
            setFlag final_result pkCompatWithScalars 
              (FlagSpreadFromNode(n,why_n_final_result,orig)));
          n.rep <- Some(final_result, why_n_final_result) ;
        end ; 
        final_result, why_n_final_result
      end
  | None -> n, mkRIdent

let rec get_rep n = fst (get_rep_why n)

let rec join n1 n2 (why_n1_n2: chain) (* The chain goes n1 -> n2 *) =
  (if doCheckChains then checkChainEnds n1 n2 why_n1_n2);
  let n1r, why_n1_n1r = get_rep_why n1 in
  let n2r, why_n2_n2r = get_rep_why n2 in
  if n1r.id = n2r.id then begin
    () (* only join if they are distinct *)
  end else begin
    if isVoidType n1r.btype then begin (* n2r becomes the new rep *)
      if not (hasFlag n1r pkRtti) then begin
        (* chain: n1r -> n1 -> n2 -> n2r *)
        let why_n1r_n2r = 
          mkRTrans (mkRSym why_n1_n1r) (mkRTrans why_n1_n2 why_n2_n2r)
        in
        n1r.rep <- Some(n2r, why_n1r_n2r);
        if hasFlag n1r pkCompatWithScalars then begin
          let res,_,_ = trueSourceOfFlag n1r pkCompatWithScalars in
          setFlag n2r pkCompatWithScalars 
            (FlagSpreadFromNode(n1r, why_n1r_n2r, res))
        end
      end 
    end else if isVoidType n2r.btype then begin (* n1r becomes the new rep *)
      if not (hasFlag n2r pkRtti) then begin
        let why_n2r_n1r = 
          mkRTrans (mkRSym why_n2_n2r) (mkRTrans (mkRSym why_n1_n2) why_n1_n1r)
        in
        n2r.rep <- Some(n1r, why_n2r_n1r);
        if hasFlag n2r pkCompatWithScalars then 
          let res,_,_ = trueSourceOfFlag n2r pkCompatWithScalars in
          setFlag n1r pkCompatWithScalars 
            (FlagSpreadFromNode(n2r, why_n2r_n1r, res))
      end
    end else
      (* Do not join nodes whose representatives are not void-ptr *)
      ()
  end 
(*
  ignore (E.warn "join %d(%b) %d(%b) -> %d(%b)" 
    n1.id (hasFlag n1 pkCompatWithScalars)
    n2.id (hasFlag n2 pkCompatWithScalars)
    (get_rep n1).id (hasFlag (get_rep n1) pkCompatWithScalars)
    )  *)

(* Given a kind for a node, produce the original node where the kind
 * originates, the true chain why it originates, and the chain:orig->this *)
let rec trueSourceOfKind (n: node) : node * whykind * chain = 
  match n.why_kind with
  | SpreadFromNode(near,r_near_n,source) -> 
      let orig, why, r_orig_near = trueSourceOfKind near in
      orig, why, mkRTrans r_orig_near r_near_n
  | w -> n, w, mkRIdent


(* Type names, computed in such a way that compatible types have the same id, 
 * even if they are syntactically different. Right now we flatten structures 
 * but we do not pull common subcomponents out of unions and we do not unroll 
 * arrays. *)


(* Some structs (those involved in recursive types) are named. This hash maps 
 * their name to the ID *)
let namedStructs : (string, string) H.t = H.create 110


(* Keep track of the structs in which we are (to detect loops). When we 
 * detect a loop we remember that *)
let inStruct : (string, bool ref) H.t = H.create 110


let rec typeIdentifier (t: typ) : string = 
  let res = typeId t in
  H.clear inStruct;  (* Start afresh next time *)
  res

and typeId = function
    TInt(ik, a) -> ikId ik ^ attrsId a
  | TVoid a -> "V" ^ attrsId a
  | TFloat (fk, a) -> fkId fk ^ attrsId a
  | TEnum _ -> ikId IInt (* !!! *)
  | TNamed (t, a) -> typeId (typeAddAttributes a t.ttype)
  | TComp (comp, a) when comp.cstruct -> begin
      (* See if we are in a loop *)
      try
        let inloop = H.find inStruct comp.cname in
        inloop := true; (* Part of a recursive type *)
        "t" ^ prependLength comp.cname (* ^ attrsId comp.cattr *)
      with Not_found -> 
        let inloop = ref false in
        let isanon = hasPrefix "__anon" comp.cname  in
        if not isanon then H.add inStruct comp.cname inloop;
        let fieldsids = 
          List.fold_left (fun acc f -> acc ^ typeId f.ftype) "" comp.cfields in
        (* If it is in a loop then keep its name *)
        let res = fieldsids (* ^ attrsId comp.cattr *) in
        if not isanon then H.remove inStruct comp.cname;
        if !inloop && not (H.mem namedStructs comp.cname) then begin
          H.add namedStructs comp.cname res;
          "t" ^ prependLength comp.cname (* ^ attrsId comp.cattr *)
        end else
          res
  end
  | TComp (comp, a) when not comp.cstruct -> 
      "N" ^ (string_of_int (List.length comp.cfields)) ^
      (List.fold_left (fun acc f -> acc ^ typeId f.ftype ^ "n") 
         "" comp.cfields) ^
      attrsId (addAttributes comp.cattr  a)
  | TPtr (t, a) -> "P" ^ typeId t ^ "p" ^ attrsId a
  | TArray (t, lo, a) -> 
      let thelen = "len" in
      "A" ^ typeId t ^ "a" ^ prependLength thelen ^ attrsId a
  | TFun (tres, args, va, a) -> 
      "F" ^ typeId tres ^ "f" ^ 
      (string_of_int (List.length (argsToList args))) ^ 
      (List.fold_left (fun acc (_, at, _) -> acc ^ typeId at ^ "f") 
         "" (argsToList args)) ^ (if va then "V" else "v") ^ attrsId a
  | _ -> E.s (E.bug "typeId")
      
and ikId = function
    IChar -> "C"
  | ISChar -> "c"
  | IUChar -> "b"
  | IInt -> "I"
  | IUInt -> "U"
  | IShort -> "S"
  | IUShort -> "s"
  | ILong -> "L"
  | IULong -> "l"
  | ILongLong -> "W"
  | IULongLong -> "w"

and fkId = function
    FFloat -> "O"
  | FDouble -> "D"
  | FLongDouble -> "T"

and prependLength s = 
  let l = String.length s in
  if s = "" || (s >= "0" && s <= "9") then
    E.s (E.unimp "String %s starts with a digit\n" s);
  string_of_int l ^ s

and attrsId al = 
  match al with
    [] -> "_"
  | _ -> "r" ^ List.fold_left (fun acc (Attr(an,_)) -> acc ^ an) "" al ^ "r"



(************ Print statistics about the graph ******************)
let addToHisto (histo: ('a, int ref) H.t) (much: int) (which: 'a) : unit = 
  let r = Util.findOrAdd histo which (fun _ -> ref 0) in
  r := !r + much

let getHisto (histo: ('a, int ref) H.t) (which: 'a) : int = 
  try let r = H.find histo which in !r with Not_found -> 0

let sortHisto (histo: ('a, int ref) H.t) : ('a * int) list = 
  let theList : ('a * int) list ref = ref [] in
  H.iter (fun k r -> theList := (k, !r) :: !theList) histo;
  List.sort (fun (_,v1) (_,v2) -> - (compare v1 v2)) !theList 

let showFirst (showone: 'a -> int -> unit)
              (many: int) (lst: ('a * int) list) =    
  let rec loop i = function
      (n, s) :: rest when i >= 0 && s > 0 -> 
        showone n s;
        loop (i - 1) rest
    | _ -> ()
  in
  loop many lst
    
(*** Statistics ***)


type incompat = node * chain * node

type incompatClass = 
    { 
              icId: int;
      mutable icCompats: incompat list; (* A list of incompats in this class *)
      mutable icNodes: (int, node * int ref) H.t; (* A hashtable indexed by 
                                  * node id; for each node also keep a count 
                                  * of how many incompats it is part of *) 
    } 

  
(* Create a list of equivalence classes *)
let incompatEquivalence: (node * (node * edge) list) list ref = ref []
let nrIncompatClasses = ref 0
let nrIncompatCasts = ref 0

let reportIncompats (incompats: (int * int, incompat) H.t) = 
  incompatEquivalence := [];
  nrIncompatClasses := 0;
  nrIncompatCasts := 0;
  let debugIncompat = false in
  let icLastId = ref (-1) in (* A counter for incompat classes *)
  (* Scan all incompats and construct the list of equivalence classes *)
  let nodeClass: (int, incompatClass) H.t = H.create 11 in
  let allClasses: (int, incompatClass) H.t = H.create 11 in
  H.iter (fun _ ((n1, why_n1_n2, n2) as inc) -> 
    let c = chainToList why_n1_n2 in
    if debugIncompat then 
      ignore (E.log "Processing incompat %d and %d\n" n1.id n2.id);
    let theReprClass = 
      (* Scan first and find out the equivalence classes in which this chain 
       * should go (indexed by class id). This could be empty if all nodes 
       * are new. *)
      let classes: (int, incompatClass) H.t = H.create 7 in
      let markClassNode (n: node) = 
        (* Omit the extreme nodes *)
        if n.id <> n1.id && n.id <> n2.id then begin
          try
            let cls = H.find nodeClass n.id in
            ignore (Util.findOrAdd classes cls.icId (fun _ -> cls))
          with Not_found -> 
            ()
        end
      in
      List.iter 
        (fun (_, e) -> 
          markClassNode e.efrom; markClassNode e.eto) c;
      let theRepr = ref None in
      (* Now we must union all the classes *)
      H.iter (fun _ cls -> 
        if debugIncompat then 
          ignore (E.log "  already in class %d\n" cls.icId);
        match !theRepr with 
          None -> theRepr := Some cls
        | Some cls' -> 
            (**** UNION ****)
            if debugIncompat then
              ignore (E.log " unioning class %d to %d\n" cls.icId cls'.icId);
            cls'.icCompats <- cls'.icCompats @ cls.icCompats;
            H.remove allClasses cls.icId;
            H.iter 
              (fun nid (nd, pCount) -> 
                let _, pCount' = 
                  Util.findOrAdd cls'.icNodes nid (fun _ -> (nd, ref 0)) in
                H.replace nodeClass nid cls';
                pCount' := !pCount' + !pCount) 
              cls.icNodes) 
        classes;
      (* Maybe we need to create a new class *)
      (match !theRepr with
        None -> 
          incr icLastId;
          if debugIncompat then 
            ignore (E.log "create a new class %d\n" !icLastId);
          let cls = 
            { icId = !icLastId; icCompats = []; icNodes = H.create 5 } in
          H.add allClasses !icLastId cls;
          cls

      | Some cls -> cls)
    in
    if debugIncompat then 
      ignore (E.log "Found the representative class %d\n" theReprClass.icId);
    (* Now add this chain to the class *)
    theReprClass.icCompats <- inc :: theReprClass.icCompats;
    let addIncToNode (n: node) = 
      if n.id <> n1.id && n.id <> n2.id then begin
        H.replace nodeClass n.id theReprClass;
        let _, pCount = 
          Util.findOrAdd theReprClass.icNodes n.id (fun _ -> (n, ref 0)) in
        incr pCount
      end
    in
    
    List.iter (fun (_, e) -> addIncToNode e.efrom; addIncToNode e.eto) c;
    
    ) incompats;
  if debugIncompat then 
    ignore (E.log "printing classes\n");
  (* Now we have a list of classes of incompats *)
  H.iter 
    (fun _ cls -> 
      (* Find the node with maximum count, and which is not Anon *)
      incr nrIncompatClasses;
      let maxNode = ref None in
      let maxCount = ref 0 in
      H.iter (fun nid (nd, pCount) -> 
        if !pCount > !maxCount 
           && (match nd.where with PAnon _, _ -> false | _ -> true) then begin
          maxNode := Some nd;
          maxCount := !pCount
        end) cls.icNodes;
      let reprNode = 
        match !maxNode with 
          None -> dummyNode
        | Some nd -> nd
      in
      (* Now for each incompat we collect the extreme nodes along with the 
       * extreme edges *)
      let extremes: (int * int, node * edge) H.t = H.create 7 in
      List.iter
        (fun (n1, why_n1_n2, n2) -> 
          let c = chainToList why_n1_n2 in
          if List.length c = 0 then begin
            if keepDetails() then 
              ignore (E.warn "Chain for incompat %d and %d is empty"
                        n1.id n2.id)
          end else begin
            let _, e1 = List.nth c 0 in
            let _, e2 = List.nth (List.rev c) 0 in
            ignore (Util.findOrAdd extremes (n1.id, e1.eid) 
                      (fun _ -> (n1, e1)));
            ignore (Util.findOrAdd extremes (n2.id, e2.eid) 
                      (fun _ -> (n2, e2)))
          end)
        cls.icCompats;
      (* Now print them *)
      let extremesList = ref [] in
      H.iter
        (fun _ (n, e) -> 
          incr nrIncompatCasts;
          extremesList := (n, e) :: !extremesList)
        extremes;
      incompatEquivalence := 
         (reprNode, !extremesList) :: !incompatEquivalence;)
    allClasses;
  if !nrIncompatClasses > 0 && not (keepDetails()) then begin
    ignore (E.warn "Cannot print details for the equivalence classes because you turned off the generation of the browser info")
  end


let printGraphStats () =     
  (* Keep a histograph per kind *)
  if !isSubtype == origSubtype then 
    E.s (bug "printGraphStats: isSubtype is not set\n");
  let totKind : (opointerkind, int ref) H.t = H.create 17 in 
  let totalNodes = ref 0 in
  let unusedNodes = ref 0 in 
  let voidStarNodes = ref 0 in
  let splitNodes = ref 0 in
  let metaPtrNodes = ref 0 in
  (* The number of bad casts *)
  let badCastsCount = ref 0 in
  let downCastCount = ref 0 in
  (* All the incompats *)
  let incompats: (int * int, node * chain * node) H.t = H.create 113 in
  (* A list of the edges involved in bad casts, and whether or not each is
   * a sequence cast.  Will be sorted and printed *)
  let badCastsList: (edge * bool) list ref = ref [] in
  (* Index the bad casts by location because one bad bad cast can be counted 
   * many times (if it is in a macro).  Use a separate hashtable,
   * rather than badCastsList, for performance.  *)
  (* let badCastsLoc: (location, unit) H.t = H.create 113 in *)
  let badCastsVoid = ref 0 in
  let badCastsFPtr = ref 0 in
  (* Keep track of spread_from_edge. For each node how many other nodes have 
   * WILD/spread_from_edge(n).  *)
  let spreadTo : (int, int ref) H.t = H.create 117 in
  let examine_node id n =
    incr totalNodes;
    (match unrollType n.btype with 
      TVoid _ -> incr voidStarNodes
    | _ -> ());
    (* See if it is not-used. We check that it does not have ECompat, ECast 
     * or ESameKind edges *)
    if n.kind = Safe then begin
      let isUsedEdge e = 
        match e.ekind with
          ECast _ | ECompat _ | ESameKind _ -> true
        | _ -> false
      in
      if not (List.exists isUsedEdge n.succ ||
              List.exists isUsedEdge n.pred) then 
        incr unusedNodes;
    end;
    addToHisto totKind 1 n.kind;
  in
  IH.iter examine_node idNode;
  badCastsList := List.sort 
      (fun (e1, _) (e2, _) -> compareLoc e1.eloc e2.eloc) 
      !badCastsList;
  List.iter 
    (fun (e, isseq) ->
      incr badCastsCount;
      ignore (E.log "** %d: Bad cast %sat %a (%a *%d ->%a *%d)\n"
                !badCastsCount
                (if isseq then "(seq) " else "")
		d_loc e.eloc d_type e.efrom.btype e.efrom.id
                d_type e.eto.btype e.eto.id))
    !badCastsList;
  (* sm: prepend string 'ptrkinds:' so I can easily grep for this info *)
  ignore (E.log "ptrkinds: Graph contains %d nodes (%d are used)\n" 
            !totalNodes (!totalNodes - !unusedNodes));
  (* Now subtract the unused ones *)
  totalNodes := !totalNodes - !unusedNodes;
  (try 
    let rsafe = H.find totKind Safe in
    rsafe := !rsafe - !unusedNodes
  with Not_found -> ());
  let percent (n: int) : float = 
    if !totalNodes = 0 then begin
      if n <> 0 then 
        ignore (E.warn "Ptrnode.percent: divide by 0");
      100.0
    end else
      (float_of_int n)
         /. float_of_int (!totalNodes) *. 100.0 
  in 
  H.iter
    (fun k r -> ignore (E.log "ptrkinds:   %a - %d (%3.0f%%)\n"
                          d_opointerkind k !r (percent !r)))
    totKind;
  ignore (E.log "%d pointers are void*\n" !voidStarNodes);
  ignore (E.log "%d bad casts of which %d involved void* and %d involved function pointers\n"
            !badCastsCount !badCastsVoid !badCastsFPtr);
  if !badCastsCount = 0 then 
    ignore (E.log "No bad casts, so no downcasts\n") 
  else begin
    ignore (E.log "%d (%d%%) of the bad casts are downcasts\n"
    !downCastCount (100 * !downCastCount / !badCastsCount));
  end ;
  ignore (E.log "%d (%d%%) of the nodes are split\n"
                !splitNodes (int_of_float (percent !splitNodes)));
  ignore (E.log "%d (%d%%) of the nodes are have a metadata pointer\n"
                !metaPtrNodes (int_of_float (percent !metaPtrNodes)));
  reportIncompats incompats;
  let incompatCount = ref 0 in
  List.iter
    (fun (n, extremes) -> 
      let nrExtremes = List.length extremes in
      if nrExtremes > 0 then begin
        ignore (E.log "%d incompatible types flow into node %a *%d\n"
                  nrExtremes
                  d_type n.btype n.id);
        List.iter
          (fun (n, e) -> 
            incr incompatCount;
            ignore (E.log "  Type %a *%d at %a\n" 
                      d_type n.btype n.id d_loc e.eloc)) extremes
      end)
    !incompatEquivalence;
  ignore (E.log "%d incompatible equivalence classes\n" !incompatCount);
  H.clear totKind;
  H.clear spreadTo;
  ()




let printInferGraph (c: out_channel) =
  output_string c "#if 0\n/* Now the graph */\n";
  output_string c "/* Now the solved graph (simplesolve) */\n";
  
  (* Get the nodes ordered by ID *)
  let allsorted =
    Stats.time "sortgraph"
      (fun () ->
        let all : node list ref = ref [] in
        IH.iter (fun id n -> all := n :: !all) idNode;
        List.sort (fun n1 n2 -> compare n1.id n2.id) !all) ()
  in
  Stats.time "printnodes"
    (List.iter (fun n -> (
      fprint c 80 (d_node () n)
        )))
    allsorted;
  output_string c "/* End of solved graph*/\n#endif\n";
  ()


let printInfer (f: string) (file: Cil.file) = 
  begin
    let c = 
      try open_out f  (* Might throw an exception *)
      with e -> E.s (E.error "Cannot open infer output file %s" f)
    in
    Util.tryFinally
      (fun _ -> 
         dumpFile ccuredInferPrinter c f file;
         Stats.time "printgraph" printInferGraph c)
      (fun _ -> 
         close_out c)
      ()
  end

let initialize () = 
  H.clear placeId;
  IH.clear idNode;
  H.clear namedStructs;
  H.clear inStruct;
  lastEdgeIdx := 0;
  lastNodeId := 0; (* We reserve the ID=0 to the dummyNode *)
  if dummyNode.id <> 0 then 
    E.s (E.bug "Ptrnode:dummyNode does not have ID=0");
  (* And add the dummyNode in the graph *)
  IH.add idNode dummyNode.id dummyNode;
  if not !useStrings && !use_wild_solver then begin
    useStrings := true;
    ignore (E.warn "You must use strings when using the WILD solver! I turned them back on!");
  end;
    
  ()
