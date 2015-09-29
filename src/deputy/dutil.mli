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

val curFunc : Cil.fundec ref
val curStmt : int ref
val memset : Cil.varinfo
val outputAll : unit -> unit
val bug : ('a, unit, Pretty.doc, unit) format4 -> 'a
val error : ('a, unit, Pretty.doc, unit) format4 -> 'a
val unimp : ('a, unit, Pretty.doc, unit) format4 -> 'a
val warn : ('a, unit, Pretty.doc, unit) format4 -> 'a
val log : ('a, unit, Pretty.doc, unit) format4 -> 'a
val errorwarn : ('a, unit, Pretty.doc, unit) format4 -> 'a
val isPointer : Cil.exp -> bool
val isPtrOrArray: Cil.typ -> bool
val isUnionType : Cil.typ -> bool
val isOpenArray : Cil.typ -> bool
val isOpenArrayComp : Cil.typ -> bool
val typeContainsPointers : Cil.typ -> bool
val typeContainsPtrOrNullterm : Cil.typ -> bool
val isAbstractType : Cil.typ -> bool
val isAbstractPtr : Cil.typ -> bool
val baseType : string -> Cil.typ -> Cil.typ
val baseSize : Cil.typ -> int
val to_int : int64 -> int
val to_signedint : Int64.t -> int
val iter_index : ('a -> int -> unit) -> 'a list -> unit
val iter2_index : ('a -> 'b -> int -> unit) -> 'a list -> 'b list -> unit
val remove_last : 'a list -> 'a list * 'a
val split : 'a list -> int -> 'a list * 'a list
type referenced = { varsRead : Cil.varinfo list; memRead : bool }
val varsOfExp : Cil.exp -> referenced
val d_referenced : unit -> referenced -> Pretty.doc
val expRefersToVar : string -> Cil.exp -> bool
val lvalRefersToVar : string -> Cil.lval -> bool
val isVarargOperator : Cil.exp -> bool
val isCorrectSizeOf : Cil.exp -> Cil.lval -> bool

val isSignedType : Cil.typ -> bool
val isDeputyAttr : Cil.attribute -> bool
val hasDeputyAttr : Cil.typ -> bool
val stripDepsFromType: Cil.typ -> Cil.typ
val deputyCompareTypes: Cil.typ -> Cil.typ -> bool
val deputyCompareExp: Cil.exp -> Cil.exp -> bool
val deputyCompareLval: Cil.lval -> Cil.lval -> bool
val deputyStripCastsForPtrArith : Cil.exp -> Cil.exp
val deputyStripAndCompareExp : Cil.exp -> Cil.exp -> bool

val markLocationChecked: unit -> unit
val markLocationTrusted: unit -> unit
val markTrustedBlock: Cil.block -> unit
val reportTrustedLines: unit -> unit

val thisKeyword : string
val autoKeyword : string
val clearBoundsTable : unit -> unit
val getBoundsExp : int -> Cil.exp
val addBoundsExp : expectedType:Cil.typ -> Cil.exp -> int
type paramkind =
    PKNone
  | PKThis
  | PKOffset of Cil.attrparam
val checkParam : Cil.attrparam -> paramkind
class deputyPrinterClass : showBounds:bool -> enable:bool -> Cil.descriptiveCilPrinter
val deputyFilePrinter : deputyPrinterClass
val deputyPrinter : deputyPrinterClass
val dx_type : unit -> Cil.typ -> Pretty.doc
val dx_exp : unit -> Cil.exp -> Pretty.doc
val dx_lval : unit -> Cil.lval -> Pretty.doc
val dx_instr : unit -> Cil.instr -> Pretty.doc
val dx_global : unit -> Cil.global -> Pretty.doc
val dx_temps : unit -> Pretty.doc
val dc_exp : unit -> Cil.exp -> Pretty.doc
val startTemps : unit -> unit
val stopTemps : unit -> unit
val dt_type : unit -> Cil.typ -> Pretty.doc
val dt_exp : unit -> Cil.exp -> Pretty.doc
val dt_lval : unit -> Cil.lval -> Pretty.doc
val dt_instr : unit -> Cil.instr -> Pretty.doc
class deputyPatchPrinterClass : Cil.cilPrinter
val deputyPatchPrinter : deputyPatchPrinterClass
val dp_global : unit -> Cil.global -> Pretty.doc
val addTempInfoSet : Cil.varinfo -> Cil.exp -> unit
val addTempInfoCall : Cil.varinfo -> Cil.exp -> Cil.exp list -> unit
