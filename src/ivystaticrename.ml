(*
 * Rename static functions to something globally unique.
 *
 *)

open Cil
open Pretty
open Ivyutil

module E = Errormsg

let alreadyRenamed (name : string) : bool =
    let len = String.length "__ivy_static_" in
    String.length name >= len &&
    (String.sub name 0 len) = "__ivy_static_"


let fnameToCIdent (fname : string) : string =
    let cident = ref "" in
    String.iter (fun c ->
        match c with
        | '/' -> cident := (!cident)^"_"
        | '.' -> ()
        | '-' -> cident := (!cident)^"_"
        | c -> cident := (!cident)^(String.make 1 c))
        fname;
    !cident

let buildNewPrefix (f : file) : string =
    let prootbuild = validateRootBuildDir () in
    let prblen = String.length prootbuild in
    let localDir = Realpath.realpath (Filename.dirname f.fileName) in
    if String.length localDir < prblen ||
       String.sub localDir 0 prblen <> prootbuild
    then E.s(E.error "%s does not have %s as a prefix" localDir prootbuild);
    let suff = String.sub localDir prblen (String.length localDir - prblen)
        |> fnameToCIdent
    in
    let fname = Filename.chop_extension (Filename.basename f.fileName)
        |> fnameToCIdent
    in
    "__ivy_static_"^suff^fname^"_"

let matchesRenamed (f : file) (s : string) (renamed: string) : bool =
    !Ivyoptions.buildRoot <> "" &&
    let prefix = buildNewPrefix f in
    (prefix^s) = renamed
(*
    let re = Str.regexp("__ivy_static_\(.*\)"^s) in
    Str.string_match re renamed 0
*)

class staticRenamerClass (newprefix : string) = object(self)
    inherit nopCilVisitor

    method vvrbl (vi : varinfo) =
        (*if Rcutils.isRcFunction vi.vname then SkipChildren else*)
        if alreadyRenamed vi.vname then DoChildren else begin
            if vi.vglob && vi.vstorage = Static then
                vi.vname <- newprefix^vi.vname;
            DoChildren
        end

end

let renameStatics (f : file) : unit =
    let newprefix = buildNewPrefix f in
    let vis = new staticRenamerClass newprefix in
    visitCilFile vis f
