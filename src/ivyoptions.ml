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

module C = Cil
module RD = Reachingdefs
module AE = Availexps
module Z = Zrapp

open Printf

(* General settings *)
let size_t: string ref = ref ""
let home : string ref = ref "/usr/local/lib/heapsafe"
let outFile : string ref = ref ""
let debug : bool ref = ref false
let verbose : bool ref = ref false
let stats: bool ref = ref false
let parseFile : string ref = ref ""
let warnAsm: bool ref = ref false
let warnVararg: bool ref = ref false

(* Deputy-specific settings *)
let trustAll : bool ref = ref false
let optLevel : int ref = ref 3
let inferFile : string ref = ref ""
let assumeString : bool ref = ref false
let alwaysStopOnError : bool ref = ref false
let fastChecks : bool ref = ref false
let insertFLIDs : string ref = ref ""
let multipleErrors : bool ref = ref false
let inferKinds: bool ref = ref true
let saturnLogicPath : string ref = ref ""
let findNonNull: bool ref = ref false
let findPreconditions : bool ref = ref false
let propPreconditions : bool ref = ref false
let htmlOutDir : string ref = ref ""
let instrument : bool ref = ref false
let taintflow : bool ref = ref false
let doPtrAnalysis : bool ref = ref false
let strictGlobInit: bool ref = ref false
let countTrustedLines: bool ref = ref false
let patches = ref []
let checkCilInvariants = ref false
let noDeputy : bool ref = ref false
let deputyChecksFile : string ref = ref "deputy/checks.h"

(* HeapSafe-specific settings *)
let hsdebug : bool ref = ref false
let warnTypeofChar: bool ref = ref false
let opsFile : string ref = ref "heapsafe/rcops.h"
let noRc: bool ref = ref false
let concRc : bool ref = ref false
let noDefer: bool ref = ref false
let noLocals: bool ref = ref false
let typeDebug: bool ref = ref false
let fakeAdjust: bool ref = ref false
let saveAdjust: bool ref = ref false
let adjustDir: string ref = ref ""
let noHoist: bool ref = ref false
let noMerge: bool ref = ref false

(* SharC options *)
let sharcOpsFile : string ref = ref "sharc/sharCops.h"
let noSharC : bool ref = ref false

(* experimental *)
let globalAnalysis = ref ""
let globServer = ref false
let buildRoot = ref ""

(** How much detail to print.  -1 means do not print the graph *)
let emitGraphDetailLevel : int ref = ref (-1)

let publicOption (_, _, x) = 
  String.get x 0 <> '_'

let rec options = [
  (* General *)
  "", Arg.Unit (fun () -> ()), "General:";
  "--verbose", Arg.Set verbose,
    "Enable verbose output";
  "--stats", Arg.Set stats,
    "Output optimizer execution time stats";
  "--help", Arg.Unit (fun () -> Arg.usage (align options) ""; exit 0),
    "Show this help message";
  "-help", Arg.Unit (fun () -> Arg.usage (align (List.filter publicOption options)) ""; exit 0),
    "Show this help message";
   "--envmachine",
   Arg.Unit (fun _ ->
     try
       let machineModel = Sys.getenv "CIL_MACHINE" in
       Cil.envMachine := Some (Machdepenv.modelParse machineModel);
     with 
       Not_found ->
	 ignore (Errormsg.error "CIL_MACHINE environment variable is not set")
     | Failure msg ->
	 ignore (Errormsg.error "CIL_MACHINE machine model is invalid: %s" msg)),
   "Use machine model specified in CIL_MACHINE environment variable";
  "--multiple-errors", Arg.Set multipleErrors,
    "Attempt to continue processing on error";
  "--patch", Arg.String (fun s -> patches := s :: !patches),
    "Specify a patch file containing extra annotations";

  (* Deputy options *)
  "", Arg.Unit (fun () -> ()), "Deputy:";
  "--dp-warn-asm", Arg.Set warnAsm,
    "Show warnings when assembly is ignored";
  "--dp-warn-vararg", Arg.Set warnVararg,
    "Show warnings when vararg operators are ignored";
  "--dp-trust", Arg.Set trustAll,
    "Trust all bad casts by default";
  (* FIXME: make this the default *)
  "--dp-strict-global-init", Arg.Set strictGlobInit,
    ("Report an error, instead of a warning, if global initializer code " ^
     "can't be proved statically safe.");
  "--dp-assume-string", Arg.Set assumeString,
    ("Assume all char arrays, and all unannotated char*s in function " ^
     "types, are NT.");
  "--dp-no-infer", Arg.Clear inferKinds,
    ("Don't use CCured-style interprocedural analysis to determine kinds " ^
     "for unannotated pointers.");
  "--dp-count-trusted-lines", Arg.Set countTrustedLines,
     "Report how many source lines contain an operation that is TRUSTED.";
  "--dp-flids", Arg.Set_string insertFLIDs,
    ("Store verbose failure information in file and replace with fault " ^
     "location identifier (FLID) (use this with a custom version of deputy checks)");
  "--dp-ops", Arg.Set_string deputyChecksFile,
    "Specify a custom file defining the deputy runtime checks";


  (* Code gen and optimizations *)
  "", Arg.Unit (fun () -> ()), "Deputy Optimizations:";
  "--dp-opt", Arg.Set_int optLevel,
    ("Control deputy optimizations:\n" ^
     "  0: no optimization\n" ^
     "  1: flow-insensitive optimization\n" ^
     "  2: some flow-sensitive optimization\n"^
     "  3: all optimizations (default)\n"^
     "  4: use Mine's octagon analysis");
  "--dp-fail-stop", Arg.Set alwaysStopOnError,
    "Optimize checks assuming that we stop on error";
  "--dp-fast-checks", Arg.Set fastChecks,
    ("Optimize checks assuming that we stop on error without printing " ^
     "specifics about the failure");

  (* Heapsafe options *)
  "", Arg.Unit (fun () -> ()), "HeapSafe:";
  "--hs-debug", Arg.Set hsdebug,
    "Track pointers precisely for debugging";
  "--hs-norc", Arg.Set noRc,
    "Disable reference counting";
  "--hs-concrc", Arg.Set concRc,
    "Enable concurrent reference counting";
  "--hs-saveadjust", Arg.String (fun dir -> adjustDir := dir; saveAdjust := true),
    "Save generated adjust functions in the specified directory";
  "--hs-fakeadjust", Arg.String (fun dir -> adjustDir := dir; fakeAdjust := true; saveAdjust := true),
    "Create, and save in the specified directory, adjust functions for all types";
  "--hs-warn-typeof-char", Arg.Set warnTypeofChar,
    "Warn when hs_typeof(char) is used - can help detect casts that fool HS_FREE/etc";
  "--hs-ops", Arg.Set_string opsFile,
    "Specify a custom header file";

  "", Arg.Unit (fun () -> ()), "HeapSafe Optimizations";
  "--hs-no-hoist", Arg.Set noHoist,
    "Disable hoisting of push/pop operations out of loops";
  "--hs-no-merge", Arg.Set noMerge,
    "Disable removal of redundant pop/push operations";
  "--hs-no-defer", Arg.Set noDefer,
    "Disable deferred reference counting";
  "--hs-no-locals", Arg.Set noLocals,
    "Disable reference counting on local variables (when possible)";


  (* SharC options *)
  "", Arg.Unit (fun () -> ()), "SharC:";
  "--sc-ops", Arg.Set_string sharcOpsFile,
    "Specify custom operations for the sharC instrumentation";
  "--sc-infer-sharing", 
    Arg.String (fun root -> buildRoot := Realpath.realpath root; 
                            globalAnalysis := "sharing"),
    "Perform global SPRIVATE and SDYNAMIC inference. The argument must be the root of your build tree";

  (* Options used by, or described in, ivycc driver *)
  "", Arg.Unit (fun () -> ()), "_Internal options:";
  "--nodeputy", Arg.Set noDeputy,
    "_Disable Deputy";
  "--nosharc", Arg.Unit (fun () -> noSharC := true),
    "_Disable SharC";
  "--home", Arg.Set_string home,
    "_Ivy home";
  "--out", Arg.Set_string outFile,
    "_Output file";
  "--in-size_t", Arg.Set_string size_t,
    "_Explicit specification of size_t type";
  "--warnall", Arg.Unit (fun _ -> Errormsg.warnFlag := true),
    "_Show all warnings";

  (* Things end users usually won't need *)
  "", Arg.Unit (fun () -> ()), "_Advanced (for debugging Ivy, etc):";
  "--a-zrapp",
    Arg.Unit (fun n -> C.lineDirectiveStyle := None;
                       C.printerForMaincil := Z.zraCilPrinter;
                       Z.doElimTemps := true),
    "_Use Zach Anderson's pretty printer";
  "--a-dp-ptr-analysis", Arg.Set doPtrAnalysis,
    ("_Use the results of a pointer analysis during optimization");
  "--a-dp-find-nonnull", Arg.Set findNonNull,
    ("_Find parameters to functions that should be annotated as NONNULL");
  "--a-dp-find-preconditions", Arg.Set findPreconditions,
    ("_Find function preconditions, and add them to the patch file");
  "--a-dp-prop-preconditions", Arg.Set propPreconditions,
    ("_Make use of Precondition attributes");
  "--a-dp-html-out-dir", Arg.String (fun s -> htmlOutDir := s),
    ("_Directory in which to put html files");
  "--a-saturn-logic-path", Arg.String (fun s -> saturnLogicPath := s),
    ("_Specify where to look for the results of Saturn analysis");
  "--a-parse-out", Arg.Set_string parseFile,
    "_File in which to place Deputy parsing results, before preprocessing";
  "--a-infer-out", Arg.Set_string inferFile,
    ("_File in which to place the results of Deputy's preprocessing, " ^
     "including inference results.");
  "--a-infer-out-detail", Arg.Set_int emitGraphDetailLevel,
    ("_Dump the inference graph with the specified level " ^
     "of detail, with n=0 being the most terse and n=3 the most " ^
     "verbose.  Has no effect unless --a-infer-out " ^
     "and the interprocedural inference are both used.");
  "--a-debug-optim", Arg.Unit (fun n -> Z.debug := true; RD.debug := true;
                                      AE.debug := true; debug := true),
    "_Have the optimizer output lots of debugging info";
  "--a-internal-line-nums",
    Arg.Unit (fun _ -> Cil.lineDirectiveStyle := Some Cil.LineComment;
                       Cprint.printLnComment := true),
    "_Do not map line numbers back to the original source file";
  "--a-check-cil-invariants",  Arg.Set checkCilInvariants,
    "_Ensure Deputy generates well-formed CIL code.";
  "--a-glob-server", Arg.Set globServer,
    "_(for internal use only)";
  "--a-global-analysis", Arg.Set_string globalAnalysis,
    "_Bypass Ivy, and do some global analysis instead.";
  "--a-build-root", Arg.String (fun s -> buildRoot := Realpath.realpath s),
    "_The root directory of the current build";
  "--a-instrument", Arg.Set instrument,
    ("_Add instrumentation suitable for runtime analysis");
  "--a-taintflow", Arg.Set taintflow,
    ("_Perform a static taint analysis");
]

and align (options: (string * Arg.spec * string) list) =
  (* Get the width of the left column, which contains argument names. *)
  let left =
    try
      List.hd (List.sort (fun a b -> - (compare a b))
                 (List.map (fun (arg, _, _) -> String.length arg) options))
    with Not_found ->
      0
  in
  (* Add extra for left and right margin. *)
  let left = left + 4 in
  (* Now get the width of the description column. *)
  let width = 78 - left in
  (* Helper function to wrap strings. *)
  let rec wrap str =
    if String.length str <= width then
      str
    else
      (* Find the point to break the string--first newline or last space. *)
      let break, skip =
        try
          let break = String.rindex_from str width ' ' in
          try
            String.index (String.sub str 0 break) '\n', 1
          with Not_found ->
            break, 1
        with Not_found ->
          width, 0
      in
      (* Split the string and keep wrapping. *)
      let lstr, rstr =
        String.sub str 0 break,
        String.sub str (break + skip) (String.length str - break - skip)
      in
      lstr ^ "\n" ^ String.make left ' ' ^ wrap rstr
  in
  (* Now update all the descriptions. *)
  List.map
    (fun (arg, action, str) ->
       if arg = "" then
         arg, action, "\n" ^ str ^ "\n"
       else
         let pre = String.make (left - String.length arg - 3) ' ' in
         arg, action, pre ^ wrap str)
    options
