(*
 * ivypreprocess.ml
 *
 * If we find a sharc_sharing.i file, or if we're doing a global analysis,
 * then make sure the ivy build root is set, and rename the static globals.
 *
 *)

open Cil
open Pretty
open Ivyutil
open Ivyoptions

(* Start in the working directory, and go up the tree looking for
   sharc_sharing.i *)
let findSharcSharing () : string option =
    if !buildRoot <> "" &&
       Sys.file_exists (!buildRoot^"/sharc_sharing.i")
    then Some(!buildRoot^"/sharc_sharing.i") else
    let rec finder (dir : string) : string option =
        let shfname = dir ^ "/sharc_sharing.i" in
        if Sys.file_exists shfname then Some shfname else
        let pdir = Filename.dirname dir in
        if pdir = dir then None else
        finder pdir
    in
    finder (Sys.getcwd ())

let preprocess (f : file) : unit =
    if !globalAnalysis <> "" then
        Ivystaticrename.renameStatics f
    else if not(!Ivyoptions.noSharC) then begin
        match findSharcSharing () with
        | None -> ()
        | Some shdir -> begin
            E.log "Found sharing patch: %s\n" shdir;
            if !buildRoot = "" then
                buildRoot := (Filename.dirname shdir);
            if not(List.mem "sharc_sharing.i" !patches) then
                patches := shdir :: !patches;
            Ivystaticrename.renameStatics f
        end
    end
