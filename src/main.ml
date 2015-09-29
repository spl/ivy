(*
 *
 * Copyright (c) 2006,
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


module F = Frontc
module C = Cil
module E = Errormsg

let ivyRoot (f:C.file) : C.global -> bool =
  let deputyRoot = Deputy.root f
  and heapsafeRoot = Heapsafe.root f in
  (fun (g:C.global) -> (deputyRoot g) or (heapsafeRoot g))

let parseOneFile (fname: string) : C.file =
  let cabs, cil = F.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps ~isRoot:(ivyRoot cil) cil;
  cil

let outputFile (f : C.file) : unit =
  if !Ivyoptions.outFile <> "" then
    try
      let c = open_out !Ivyoptions.outFile in
      (* Tell CIL to put comments around the bounds attributes. *)
      C.print_CIL_Input := false;
      Stats.time "printCIL" 
        (C.dumpFile (!C.printerForMaincil) c !Ivyoptions.outFile) f;
      close_out c
    with _ ->
      E.s (E.error "Couldn't open file %s" !Ivyoptions.outFile)

let processOneFile (cil: C.file) =

    Ivypreprocess.preprocess cil;

    Deputy.preprocess cil;
    Heapsafe.preprocess cil;
    SharC.preprocess cil;

    if !Ivyoptions.globalAnalysis <> "" then
        Ivyglobclient.putGlob cil.C.globals;

    let cil1 = Deputy.process cil in
    SharC.post_deputy cil1;
    let cil2 = Heapsafe.process cil1 in
    let cil3 = SharC.process cil2 in

    Deputy.postprocess cil3;

    outputFile cil3
;;

let main () =
  (* Setup CIL for use w/ Ivy. Only settings with "global" effects
     should be here, things that are specific to a particular
     extension (e.g. attributes) should be in that extension's init
     function *)

  (* sm: enabling this by default, since I think usually we
   * want 'cilly' transformations to preserve annotations; I
   * can easily add a command-line flag if someone sometimes
   * wants these suppressed *)
  C.print_CIL_Input := true;

  (* Turn off the implicit casts *)
  C.insertImplicitCasts := false;

  (* Turn off line wrapping. *)
  C.lineLength := 100000;

  (* Suppress truncate warnings. *)
  C.warnTruncate := false;

  (* Don't make the cast between a function call and its destination
     explicit.  We need to set this so that polymorphic functions
     are handled correctly. *)
  Cabs2cil.doCollapseCallCast := true;

  let usageMsg = "Usage: ivycc [options] source-files" in
  Arg.parse (Ivyoptions.align Ivyoptions.options) Ciloptions.recordFile usageMsg;
  if !Ivyoptions.stats then
    Stats.reset Stats.SoftwareTimer; (* no performance counters *)
  (* else leave Stats disabled *)

  (* Use our special printer that prints adjust functions where necessary *)
  if !Ivyoptions.concRc then
      C.printerForMaincil := new Rcprint.cRcPrinter
  else
      C.printerForMaincil := new Rcprint.rcPrinter;

  Cil.initCIL ();
  Deputy.init ();
  Heapsafe.init ();

  if !Ivyoptions.globServer then begin
      Ivymerger.init();
      Ssharinganalysis.init();
      Ivyglobserver.globServer !Ivyoptions.globalAnalysis
  end else begin

      (* Fires off ivycc with --globserver so that the above test succeeds *)
      if !Ivyoptions.globalAnalysis <> "" then begin
          ignore(Ivyglobserver.startServer !Ivyoptions.globalAnalysis);
      end;

      Ciloptions.fileNames := List.rev !Ciloptions.fileNames;
      let fileName =
        match !Ciloptions.fileNames with
        | [name] -> name
        | [] -> E.s (E.error "No file names provided")
        | _ -> E.s (E.error "Too many file names provided (%a)"
                   (Pretty.docList Pretty.text) !Ciloptions.fileNames)
      in

      let file = parseOneFile fileName in
      processOneFile file;

      if !Ivyoptions.globalAnalysis <> "" then
          Ivyglobclient.clientClose()
  end
;;  

let cleanup () = 
  Deputy.cleanup ();
  Heapsafe.cleanup ();
  if !E.verboseFlag || !Ivyoptions.stats then
    Stats.print !E.logChannel "Timings:\n";
  if !E.logChannel != stderr then 
    close_out (! E.logChannel);  
;;

begin 
  try 
    main () 
  with
  | F.CabsOnly -> (* this is OK *) ()
  | E.Error -> ()
  (*| exn -> E.log "%s was uncaught\n" (Printexc.to_string exn); raise exn*)
end;
cleanup ();
exit (if !E.hadErrors then 1 else 0)
