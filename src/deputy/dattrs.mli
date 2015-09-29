(*
 *
 * Copyright (c) 2006, 
 *  Jeremy Condit       <jcondit@cs.berkeley.edu>
 *  Matthew Harren      <matth@cs.berkeley.edu>
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

val getZeroOneAttr : string list -> Cil.attributes -> Cil.attribute option
val getOneAttr : string list -> Cil.attributes -> Cil.attribute
val isNullterm : Cil.typ -> bool
val isNulltermDrop : Cil.typ -> bool
val isNulltermExpand : Cil.typ -> bool
val isSizePtr : Cil.typ -> bool
val isTrustedAttr : Cil.attributes -> bool
val isTrustedType : Cil.typ -> bool
val isTrustedComp : Cil.compinfo -> bool
val isNonnullType : Cil.typ -> bool
val isHiddenVar : Cil.varinfo -> bool
val typeContainsNonnull : Cil.typ -> bool
val countAttr : Cil.attrparam -> Cil.attribute
val count0Attr : Cil.attribute
val sizeAttr : Cil.attrparam -> Cil.attribute
val safeAttr : Cil.attribute
val nulltermAttr : Cil.attribute
val autoAttr : Cil.attribute
val autoEndAttr : Cil.attribute
val stringAttrs : Cil.attributes
val trustedAttr : Cil.attribute
val sentinelAttrs : Cil.attributes
val hiddenAttr : Cil.attribute
val isSentinelType : Cil.typ -> bool
val isConstType : Cil.typ -> bool
val missingAnnotAttr : Cil.attribute
val hasDefaultAnnot : Cil.attributes -> bool
val isAllocator : Cil.typ -> bool
val isDeallocator : Cil.typ -> bool
val isMemset : Cil.typ -> bool
val isMemcpy : Cil.typ -> bool
val isMemcmp : Cil.typ -> bool
val isSpecialFunction : Cil.typ -> bool
val allGlobalVars : Cil.varinfo list ref
val registerGlobal : Cil.varinfo -> unit
val globalsEnv : Cil.varinfo -> Cil.varinfo list

type whenMap = (Cil.fieldinfo * Cil.exp) list
val getSelectedField : whenMap -> Cil.fieldinfo option
val depsOfWhenAttrs : Cil.attributes -> string list
val depsOfType : ?missingBoundsOkay:bool -> Cil.typ -> string list
val hasExternalDeps : Cil.lval -> bool
type context = (string * bool * Cil.exp) list
val d_ctx : unit -> context -> Pretty.doc
val d_ctx_simple : unit -> context -> Pretty.doc
val formalsContext : Cil.fundec -> context
val localsContext : Cil.fundec -> context
val liveLocalsContext : Usedef.VS.t -> context
val globalsContext : Cil.varinfo -> context
val structContext : Cil.lval -> Cil.compinfo -> context
val allContext : unit -> context
val compileAttribute : ?deputyAttrsOnly:bool -> context -> Cil.attrparam -> string list * Cil.exp
type bounds =
    BSimple of Cil.attrparam * Cil.attrparam
  | BFancy of Cil.exp * Cil.exp
val getBounds : Cil.attributes -> bounds
val boundsOfAttrs : context -> Cil.attributes -> Cil.exp * Cil.exp
val fancyBoundsOfType : Cil.typ -> Cil.exp * Cil.exp
val makeFancyPtrType :
  ?nullterm: bool -> Cil.typ -> Cil.exp -> Cil.exp -> Cil.typ
type size =
    SSimple of Cil.attrparam
  | SFancy of Cil.exp
val fancySizeOfType : Cil.typ -> Cil.exp
val fancyBoundsOfSizeType : Cil.typ -> Cil.typ -> Cil.exp -> Cil.exp * Cil.exp
val fancyWhenOfType : Cil.typ -> whenMap
val substType : context -> Cil.typ -> Cil.typ
val emptyContext : context
val addThisBinding : context -> Cil.typ -> Cil.exp -> context
val addTypeBinding : context -> string -> Cil.typ -> context
val addBinding : context -> string -> Cil.exp -> context
val hasBinding : context -> string -> bool
val hasBindings : context -> string list -> bool
val substTypeName : (string * string) list -> Cil.typ -> Cil.typ
val normalizeTypeNames : Cil.typ -> Cil.typ
val getOpenArrayLength : Cil.typ -> (Cil.fieldinfo * Cil.typ) option


(* For Rmtmps *)
val treatAsRoot: Cil.file -> Cil.global -> bool
