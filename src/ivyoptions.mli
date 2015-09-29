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

val outFile : string ref
val debug : bool ref
val verbose : bool ref
val trustAll : bool ref
val stats : bool ref
val optLevel : int ref
val parseFile : string ref
val inferFile : string ref
val assumeString : bool ref
val alwaysStopOnError : bool ref
val fastChecks : bool ref
val insertFLIDs : string ref
val multipleErrors : bool ref
val inferKinds : bool ref
val saturnLogicPath : string ref
val findNonNull : bool ref
val findPreconditions : bool ref
val propPreconditions : bool ref
val htmlOutDir : string ref
val instrument : bool ref
val taintflow : bool ref
val doPtrAnalysis : bool ref
val warnAsm : bool ref
val warnVararg : bool ref
val strictGlobInit : bool ref
val countTrustedLines: bool ref
val emitGraphDetailLevel : int ref
val patches : string list ref
val checkCilInvariants : bool ref
val noDeputy : bool ref
val deputyChecksFile : string ref

val options : (string * Arg.spec * string) list
val align : (string * Arg.spec * string) list -> (string * Arg.spec * string) list

val size_t: string ref
val home : string ref
val hsdebug : bool ref
val warnTypeofChar: bool ref
val opsFile : string ref
val noRc: bool ref
val concRc : bool ref
val noDefer: bool ref
val noLocals: bool ref
val typeDebug: bool ref
val fakeAdjust: bool ref
val saveAdjust: bool ref
val adjustDir: string ref
val noHoist: bool ref
val noMerge: bool ref

val sharcOpsFile : string ref
val noSharC : bool ref

val globalAnalysis : string ref
val globServer : bool ref
val buildRoot : string ref
