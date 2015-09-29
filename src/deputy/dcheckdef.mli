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

type check =
    CNonNull of Cil.exp
  | CEq of Cil.exp * Cil.exp * string * Pretty.doc list
  | CMult of Cil.exp * Cil.exp
  | CPtrArith of Cil.exp * Cil.exp * Cil.exp * Cil.exp * int
  | CPtrArithNT of Cil.exp * Cil.exp * Cil.exp * Cil.exp * int
  | CPtrArithAccess of Cil.exp * Cil.exp * Cil.exp * Cil.exp * int
  | CLeqInt of Cil.exp * Cil.exp * string
  | CLeq of Cil.exp * Cil.exp * string
  | CLeqNT of Cil.exp * Cil.exp * int * string
  | CNullOrLeq of Cil.exp * Cil.exp * Cil.exp * string
  | CNullOrLeqNT of Cil.exp * Cil.exp * Cil.exp * int * string
  | CWriteNT of Cil.exp * Cil.exp * Cil.exp * int
  | CNullUnionOrSelected of Cil.lval * Cil.exp
  | CSelected of Cil.exp
  | CNotSelected of Cil.exp
val checks_equal : check -> check -> bool
val mkFun : string -> Cil.typ -> Cil.typ list -> Cil.attributes -> Cil.exp
val checkWhy : check -> string
val checkText : check -> Pretty.doc list
val instrToCheck : Cil.instr -> check option
val checkToInstr : check -> Cil.instr
val isDeputyFunctionLval : Cil.exp -> bool
val isDeputyFunctionInstr : Cil.instr -> bool
val is_check_instr : Cil.instr -> bool
val is_deputy_instr : Cil.instr -> bool
val is_deputy_fun : Cil.instr -> bool
val is_alloc_fun : Cil.instr -> bool
val isLibcNoSideEffects : Cil.instr -> bool
val lvNoSideEffects : Cil.exp -> bool
