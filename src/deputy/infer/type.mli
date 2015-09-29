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

(*
 * C Structural Type Equality
 *)
val debugType: bool


(* Initialize the type module *)
val init: unit -> unit

(* A failure handler is called on two nodes whose base types fail to match 
 * up. This should make those nodes have WILD types (and thus force them to 
 * match up) *)
type failureHandler = Ptrnode.node -> Ptrnode.chain -> Ptrnode.node -> unit

(* A compatHandler is called on two nodes that must have an equal
 * representation. This should put an ECompat edge between those two nodes. 
 *)
type compatHandler = Ptrnode.chain -> Cil.typ -> Cil.typ -> unit


(** Use this function to replace a void-ptr with its representative. The 
 * resulting chain is always orig_type -> type. *)
val polymorphic_replace: Cil.typ -> Cil.typ * Ptrnode.chain

(* This is the main (conceptual) entry point for this file.
 *
 * These remarks apply to "subtype" and "equal", both of which are
 * implemented using an underlying function called "compare". 
 * 
 * Use physical subtyping (a la Reps, etc.) to determine the relationship
 * between t1 and t2. In general, this is similar to width subtyping (like
 * in object oriented languages) with the following exceptions:
 *
 * (1) "void*" is treated as a type variable and special handling exists
 *     to replace a "void*" with its representative type. Any direct
 *     comparison with a representative-less "void*" type succeeds. 
 * (2) A special "compat" function is called on all pointers that must have
 *     the same physical representation and on all pointers that area
 *     compared against a representative-less "void*" type. 
 * (3) A special "failure" function is called on all internal pointers that
 *     "fail to match up correctly" and must thus have their types checked
 *     at run-time (e.g., by making them WILD in CCured). "compare" can
 *     return true even if some lower-level pointers fail to match up,
 *     provided that it calls "failure" on them. 
 *
 * Because memoization is used to prevent this from taking too much time
 * over the course of the analysis, "compat" and "failure" are only
 * guaranteed to be called once per pair of types, even across many
 * invocations of "compare". 
 *)
val subtype:  compat:compatHandler -> 
              (* Failure is invoked with the two types involved and the chain 
               * between them *)
              failure:failureHandler ->
              why_small_big: Ptrnode.chain  -> (* Goes small -> big *)
              small:Cil.typ ->
              big:Cil.typ -> bool


val equal:    compat:compatHandler -> 
              (* Failure is invoked with the two types involved and the chain 
               * between them *)
              failure: failureHandler -> 
              why_t1_t2: Ptrnode.chain  ->
              t1:Cil.typ -> 
              t2:Cil.typ -> bool

val all_scalars: ?replace: (Cil.typ -> Cil.typ * Ptrnode.chain) ->
                 Cil.typ -> bool

val arraysThatHaveBeenComparedWithNonArrays: (Cil.typ, Ptrnode.chain) Hashtbl.t

val arraysThatHaveBeenComparedWithArrays: (Cil.typ * Cil.typ, Ptrnode.chain) Hashtbl.t
