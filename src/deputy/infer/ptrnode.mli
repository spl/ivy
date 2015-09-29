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

(* Initialize the pointer graph *)
val initialize: unit -> unit

(* If defaultIsNotWild then pointers without a qualifier are SAFE and only 
 * the arrays that are specfically SIZED contain a size field and only the 
 * variables that are specifically TAGGED contain tags *)
val defaultIsWild: bool ref

(* flag to force all functions to be untagged, in the WILD solver *)
val wild_solve_untagged_functions: bool ref

(* flag to force all functions to be tagged, in the WILD solver *)
val wild_solve_tag_all_functions: bool ref

(* True if the wild solver is used. *)
val use_wild_solver: bool ref


(** Whether we use Offset nodes. If false then we use the node stored with 
 * the address of a fieldinfo *)
val useOffsetNodes: bool

(** Whether to print verbose curing output source file *)
val printVerboseOutput: bool ref

(* Turn on/off the use of FSEQ *)
val useFSEQ: bool ref

(** Turn on/off the use of RWSTRING, ROSTRING and NULLTERM *)
val useStrings: bool ref

(** Whether to extend the strign buffers with the null character. If false, 
 * then we use the last character for the null *)
val extendStringBuffers: bool ref 

(** Whether to override user-specified annotations *)
val allowOverride: bool ref

(** Allow partial elements in sequences *)
val allowPartialElementsInSequence: bool ref

(** Whether to emit more details in the .infer file. *)
val emitGraphDetailLevel: int ref
val graphDetailLevelLegend: string (* The meaning of different values *)

(* A marker that the solver places, if we use lean fats *)
val useLeanFats: bool ref


(* A place where a pointer type can occur *)
type place = 
    PGlob of string  (* A global variable or a global function *)
  | PType of string  (* A global typedef *)
  | PStatic of string * string (* A static variable or function. First is  
                                * the filename in which it occurs *)
  | PLocal of string * string * string (* A local variable. The name of the 
                                        * file, the function and the name of 
                                        * the local itself *)
  | POffset of int * string             (* An offset node, give the host node 
                                         * id and a field name *)
  | PField of Cil.fieldinfo             (* A field of a composite type *)

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

type chain (* A chain of edges *)

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

              btype: Cil.typ;           (* The base type of this pointer *)
      mutable attr: Cil.attribute list; (* The attributes of this pointer 
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
                                         
      mutable rep : ((node * chain) option);
        (* a representative pointer in this node's equivalence class. use 
         * this only for nodes whose btype is void. use get_rep to get the 
         * final representative. The chain is always from the node to the 
         * representative. *)
      mutable loc : Cil.location;       (* where did this node come from? *)
         
              shouldInfer: bool;        (* True if this is a local or a cast
                                           and we can do more aggressive
                                           inference. *)
    }       

(*** If you add pointer kinds, make sure you extend the definition of 
 * allKinds *)
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

and whykind = (* why did we give it this kind? *)

    (* Give the edge of a bad cast. *)
    BadCast of edge

  | BadSequenceCast of edge

  | Incompat of node * chain * node (* Two nodes that should be in the same 
                                     * equivalence class are incompatible *)

  | BoolFlag of int (* Due to a flag *)
  | PolyInt (* This is a void* connected only to scalars *)
  | Default
  | UserSpec
  | Unconstrained
  | PrintfArg (* printf inference *)
  | Special of string * Cil.location
  (* This kind is set because it is set on some other node (node1 + the 
   * chain:node1->this). We also give the original source of the kind.  *)
  | SpreadFromNode of node * chain * node

and edge = 
    {         eid:      int;
      mutable efrom:    node;
      mutable eto:      node;
      mutable ekind:    edgekind;
      mutable eloc: Cil.location;
    } 

and whyflag = (* why is this flag set for this node? *)
  | ProgramSyntax of Cil.location (* This flag was set because of the usage 
                                   * of this node in the program *)

  (* This flag is set because it is set on some other node (node1 + the 
   * chain:node1->this). We also give the original source of the flag. *)
  | FlagSpreadFromNode of node * chain * node

  | DownCast of node

  | SubtypeFailed of node

  | RequiredByEdge of edge 

  | RequiredByPointerKind of opointerkind

  | RequiredByFlag of int (* This flag is required by another flag *)

  | FlUserSpec of Cil.location

  | MayEscape of Cil.location (* We are using separate compilation,
                                 and this node is not a local.
                                 Therefore, we assume it can be used
                                 by anybody. *)
 

and edgekind = 
    ECast of extra_edge_kind (* T_from ref q_from <= T_to ref q_to. We also 
                              * cary some additional explanation for this 
                              * edge. *)
  | EOffset                  (* This is an edge added from a pointer to a 
                              * structure to a pointer to a field. The 
                              * destination of this edge should be either a 
                              * POffset node or the node associated with the 
                              * address of a field. WILDness spreads in both 
                              * directions across this edge. *)
  | EIndex                   (* q_to = if q_from = wild then wild else index *)
(*  | ENull *)                   (* a NULL flows in the direction of the edge *)
  | ECompat                  (* the kinds of these two nodes must be
                              * compatible: either both wild, index or
                              * safe. This edge type is added by the solver
                              * for its convenience. In cases like
                              * int * 1 * 2 x; 
                              * int * 3 * 4 y;
                              * We will connect 1 and 3 with ECompat. *)
    of chain                (* the two types we were comparing when we
                              * decided that these had to be equal *)
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

val mkRIdent: chain

val mkRSingle: edge -> chain
val mkRSym: chain -> chain
val mkRTrans: chain -> chain -> chain

val isSym: chain -> chain option

val getOneEdge: chain -> edge option

val isOneEdge: chain -> edge option

val get_rep : node -> node   (* find the representative of this node's
                              * equivalence class *)

val join : node -> node -> chain -> unit  
  (* join these two nodes into the same equivalence class because of
   * the given edge. *)

val doCheckChains: bool (* Whether to check the chains *)
val checkChainEnds: node -> node -> chain -> unit

val get_rep_why : node -> node * chain
  (* given a node, return the list of edges that join'd it to its
   * representative *)

val setFlag : node -> int -> whyflag -> unit
val hasFlag : node -> int -> bool

(* Given a flag for a node, produce the original node where the flag 
 * originates, the true chain why it originates, and the chain:orig->this *)
val trueSourceOfFlag: node -> int -> node * whyflag * chain

(* Given a flag for a node, produce the original node where the flag 
 * originates, the true chain why it originates, and the chain:orig->this *)
val trueSourceOfKind: node -> node * whykind * chain

val pkInterface: int (* this is an interface node *)
val pkUpdated: int (* we write through this pointer *)
val pkIntCast: int (* can contain an integer *)
val pkPosArith: int (* subject to positive pointer arithmetic *)
val pkArith: int    (* subject to arbitrary pointer arithmetic *)
val pkString: int   (* A String node *)
val pkReachIndex: int (* can reach an Index node *)
val pkNoPrototype: int (* Used as actual argument in a function without 
                              * prototype *)
val pkEscape: int (* can "escape" i.e. be assigned to a global or through a 
                    * pointer *)
val pkNotSafe: int (* constraint used by solvers: node must not be Safe *)

val pkReferenced: int (* might be eventually referenced *)

val pkRtti: int (* has run-time type information *)
val pkCompatWithScalars: int (* void* node is compat with scalars *)
val pkStack: int (* Could point to the stack; CHECK_STORE_PTR needed. *)

val pkOneWord: int (* This is specified by the user to be one word *)

val pkLastFlag: int 
val pkNumberOfFlags: int

(* The names for the flags *)
val pkFlagName: string array

(* One certain types can have RTTI *)
val canHaveRtti: Cil.typ -> bool


(** All the pointer kinds *)
val allKinds: opointerkind list

(* The main graph *)
val idNode: node Inthash.t

val dummyNode: node (* A node with ID=0. Use when you don't have one *)

(* Get a node for a place and an index. Give also the base type and the 
 * attributes *)
val getNode: p:place -> idx:int -> bt:Cil.typ -> al:Cil.attribute list -> node

(* Make a new node *)
val newNode: p:place -> idx:int -> bt:Cil.typ -> al:Cil.attribute list -> node

(** Recompute the EPointsTo information for a node *)
val setNodePointsTo: node -> unit

(* Make a new anonymous place *)
val anonPlace: unit -> place

(** A bitwise-or of the flags that are pushed to the predecessor of a node 
  * (backward) and always through the ECompat edges *)
val pkCastPredFlags: int list

(** A bitwise-or of the flags that are pushed to the successor of a node 
  * (forward) and always through the ECompat edges *)
val pkCastSuccFlags: int list
val pkCastSuccFlagsNoString: int list
val pkCNIPredFlags: int list
val pkCNIPredFlagsNoString: int list
val pkOffsetSuccFlags: int list
val pkOffsetPredFlags: int list
val allFlags: int list

val d_opointerkind: unit -> opointerkind -> Pretty.doc
val d_whykind: node -> unit -> whykind -> Pretty.doc
val d_whyflag: node -> unit -> whyflag -> Pretty.doc
val d_node: unit -> node -> Pretty.doc
val d_place: unit -> place -> Pretty.doc
val d_place_nice: unit -> (place * int) -> Pretty.doc
val d_chain: unit -> chain -> Pretty.doc

val ccuredInferPrinter: Cil.cilPrinter

(*val printBrowser: string -> Cil.file -> unit*)
val printInfer: string -> Cil.file -> unit
val printInferGraph: out_channel -> unit

val printGraphStats: unit -> unit

(* Helpers for printGraphStats *)
val addToHisto: ('a, int ref) Hashtbl.t -> int -> 'a -> unit
val getHisto: ('a, int ref) Hashtbl.t -> 'a -> int

val existsEdge: start:node -> dest:node -> kind:edgekind -> bool

(* Add an edge to the graph *)
val addEdge: start:node -> dest:node -> kind:edgekind ->
             eloc:Cil.location option -> edge

val removeEdge: edge -> unit

val isECompat: edge -> bool 
val isECast: edge -> bool 
val isESameKind: edge -> bool 


val nodeOfAttrlist: Cil.attribute list -> node option

(* The inferred kind for this node. If localOnly is true and the node is not 
 * local, then return Unknown *)
val inferredKindOf: ?localOnly:bool -> 
                    Cil.attribute list -> opointerkind * whykind


(* The kind of this pointer.  If there is no BND attribute,
   defaults to inferredKind *)
val kindOfAttrlist: Cil.attribute list -> opointerkind * whykind

val kindIsNullterm: opointerkind -> bool
val kindNeedsBounds: opointerkind -> bool

(* Replace the ptrnode attribute with the actual qualifier attribute *)
type whichAttr = 
    AtPtr  (* In a pointer type *)
  | AtArray  (* In an array type *)
  | AtOpenArray (* In an array type without a size *)
  | AtVar (* For a variable *)
  | AtOther (* Anything else *)

val replacePtrNodeAttrList: which:whichAttr 
                           ->  Cil.attribute list -> Cil.attribute list

val k2attr: opointerkind -> Cil.attribute

(** Return the numeric identifier of the kind *)
val k2number: opointerkind -> int

(** The parent in the points-to relationship *)
val nodeThatPointsTo: node -> node option


(** A function pointer that can be used to compare two types *)
val isSubtype: (Cil.typ -> Cil.typ -> bool) ref

