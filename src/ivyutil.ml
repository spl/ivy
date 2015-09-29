(* Misc. useful things. *)

open Cil
open Pretty

module E = Errormsg

let printFile ~(extraPrinting:(out_channel->unit) option) 
              ~(globinit:fundec option)
             ?(printer : cilPrinter = defaultCilPrinter)
             (f: file) (name: string) : unit
  =
  if name <> "" then begin
    try
      let channel = open_out name in
      dumpFile printer channel name f;
      (match globinit with 
        Some g -> dumpGlobal printer channel (GFun(g, locUnknown))
      | None -> ()); 
      (match extraPrinting with
         Some doit -> doit channel
       | None -> ());
      close_out channel
    with Sys_error _ ->
      E.s (E.error "Error dumping inference results to %s" name)
  end

(* This and globServRes are used by ivyglobserver and ivyglobclient *)
type globServReq =
    | GSPutGlob of global list
    | GSGetGlob of string
    | GSPutClose
    | GSError

type globServRes =
    | GSGlob of global list
    | GSClose

(* For reading and writing objects from a file descriptor *)
let write (fd : Unix.file_descr) thing : unit =
    let str = Marshal.to_string thing [] in
    if Unix.write fd str 0 (String.length str) <> String.length str then
        E.s(E.error "write failed")

let read (fd : Unix.file_descr) (buf : string) (sz : int) : unit =
    let rec loop off size =
        let numread = Unix.read fd buf off size in
        if numread <> size then
            loop (off + numread) (size - numread)
    in
    loop 0 sz

(* Handy for composing functions on lists *)
let (|>) (a : 'a) (f : 'a -> 'b) : 'b = f a

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thd3 (_,_,c) = c

(* The is_directory function seems to be absent from the standard library *)
let is_directory (fname : string) : bool =
    let s = Unix.stat fname in
    match s.Unix.st_kind with
    | Unix.S_DIR -> true
    | _ -> false

(* Find the root of the build specified by --build-root, or in the
   environment variable IVY_ROOT_BUILD_DIR *)
let validateRootBuildDir () : string =
    try let prootbuild =
        if !Ivyoptions.buildRoot <> "" then
            !Ivyoptions.buildRoot
        else
            Sys.getenv "IVY_ROOT_BUILD_DIR"
    in
    if not(Sys.file_exists prootbuild) then
        E.s(E.error "Root build directroy\n%s\ndoes not exist" prootbuild)
    else
    if not(is_directory prootbuild) then
        E.s(E.error "%s is not a directory" prootbuild)
    else prootbuild
    with Not_found ->
        raise(Failure "set --a-build-root")
        (*E.s(E.error "set arg --a-build-root to root of build.")*)

(* Find the .ppatches dir under the root build dir *)
(* XXX: create it if it doesn't exist? *)
let validateRootPatchesDir () : string =
    try let prootbuild = validateRootBuildDir () in
    let rootPatchesDir = prootbuild^"/.ppatches" in
    if not(Sys.file_exists rootPatchesDir) then
        Unix.mkdir rootPatchesDir 0o755;
    if not(is_directory rootPatchesDir) then
        E.s(E.error "%s is not a directory" rootPatchesDir)
    else rootPatchesDir
    with Not_found ->
        E.s(E.error "set arg --a-build-root to root of build.")

let isIvyAttr (a : attribute) : bool =
    (Dutil.isDeputyAttr a) ||
    (Rcutils.isHeapsafeAttr a) ||
    (Sutil.isSharCAttr a)

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thd3 (_,_,c) = c
