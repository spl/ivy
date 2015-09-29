open Cil
open Pretty
open Ivyoptions

module E = Errormsg

let name = "merger"

let func (gl : global list) : unit =
    let outf = open_out "ivymerger.dump.c" in
    List.iter (dumpGlobal defaultCilPrinter outf) (List.rev gl);
    close_out outf;
    ()

let init () =
    Ivyglobserver.addGlobalProcessor name func
