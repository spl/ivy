(* Set up a named pipe, and build a hash table of globals that we get sent.
   Run the function referred to by processGlobals when SIGTERM is recieved.
   Then, exit.
 *)

open Cil
open Pretty
open Ivyutil
open Dpatch

module E = Errormsg

let waitTimeout = 120.0

let globServHash : (string, global list) Hashtbl.t = Hashtbl.create 500

let processGlobals : (global list -> unit) ref =
    ref (fun gl -> ())

let global_processors : (string * (global list -> unit)) list ref = ref []

let addGlobalProcessor (name : string) (func : global list -> unit) : unit =
    if List.exists (fun (s,_) -> s = name) (!global_processors) then () else
    global_processors := (name, func) :: (!global_processors)

let setGlobalProcessor (name : string) : unit =
    try
        let (_,f) = List.find (fun (n,f) -> n = name) (!global_processors) in
        processGlobals := f
    with Not_found -> ()

let s_to_c_out : Unix.file_descr option ref = ref None
let c_to_s_in  : Unix.file_descr option ref = ref None

let getSToCOutPipe () : Unix.file_descr =
    match !s_to_c_out with
    | Some p -> p
    | None ->
        let ppdir = validateRootPatchesDir () in
        let pipename = ppdir^"/stocpipe" in
        let pipe = Unix.openfile pipename [Unix.O_WRONLY] 0o000 in
        s_to_c_out := Some pipe;
        pipe

let getCToSInPipe () : Unix.file_descr =
    match !c_to_s_in with
    | Some p -> p
    | None ->
        let ppdir = validateRootPatchesDir () in
        let pipename = ppdir^"/ctospipe" in
        let pipe = Unix.openfile pipename [Unix.O_RDONLY] 0o000 in
        c_to_s_in := Some pipe;
        pipe

let recvReq (fd : Unix.file_descr) : globServReq =
    let hdr = String.create (Marshal.header_size) in
    let hdr_rdsz = Unix.read fd hdr 0 Marshal.header_size in
    if hdr_rdsz <> Marshal.header_size then
        E.s(E.error "server: recvReq header failed: %d" hdr_rdsz);
    let datasz = Marshal.data_size hdr 0 in
    let data = String.create datasz in
    read fd data datasz;
    Marshal.from_string (hdr^data) 0

(* anonymous comps are given names like __anonstruct_name_number.
   this function strips off the number part *)
let anonCompNumStrip (name : string) : string =
    try
        if String.sub name 0 6 = "__anon" then
            let ridx = String.rindex name '_' in
            String.sub name 0 ridx
        else name
    with Invalid_argument _ -> name
    | Not_found -> name


(* Add globals to the hash, merging annotations where necessary. *)
let addGlobals (gl : global list) : unit =
    let globName (g : global) : string =
        match g with
        | GType(ti,_) -> ti.tname
        | GCompTag(ci,_) | GCompTagDecl(ci,_) -> 
            ci.cname <- anonCompNumStrip ci.cname;
            ci.cname
        | GEnumTag(ei,_) | GEnumTagDecl(ei,_) -> ei.ename
        | GVarDecl(vi,_) | GVar(vi,_,_) -> vi.vname
        | GFun(fd,_) -> fd.svar.vname
        | GAsm(s,_) | GText s -> s
        | _ -> sprint ~width:100 (d_global () g)
    in
    let mergeGlob (newg : global) (oldg : global) : global =
        match newg, oldg with
        | GType(nti,_), GType(oti,l) ->
            begin try
                oti.ttype <- patchType oti.ttype nti.ttype oti.tname
            with PatchFailed -> () end;
            GType(oti,l)
        | (GCompTag(nci,_)|GCompTagDecl(nci,_)) , GCompTag(oci,l) ->
            begin try patchComp oci nci;
                      patchComp nci oci
            with PatchFailed -> () end;
            GCompTag(oci,l)
        | (GCompTag(nci,_)|GCompTagDecl(nci,_)) , GCompTagDecl(oci,l) ->
            begin try patchComp oci nci;
                      patchComp nci oci
            with PatchFailed -> () end;
            GCompTagDecl(oci,l)
        (* | Enums don't need to be merged *)
        | (GVarDecl(nvi,_)|GVar(nvi,_,_)), GVar(ovi,i,l) ->
            begin try
                ovi.vtype <- patchType ovi.vtype nvi.vtype ovi.vname;
                nvi.vtype <- patchType nvi.vtype ovi.vtype nvi.vname
            with PatchFailed -> () end;
            ovi.vattr <- patchAttrs ovi.vattr nvi.vattr;
            nvi.vattr <- patchAttrs nvi.vattr ovi.vattr;
            GVar(ovi,i,l)
        | (GVarDecl(nvi,_) | GVar(nvi,_,_)), GVarDecl(ovi,l) ->
            begin try
                ovi.vtype <- patchType ovi.vtype nvi.vtype ovi.vname;
                nvi.vtype <- patchType nvi.vtype ovi.vtype nvi.vname
            with PatchFailed -> () end;
            ovi.vattr <- patchAttrs ovi.vattr nvi.vattr;
            nvi.vattr <- patchAttrs nvi.vattr ovi.vattr;
            GVarDecl(ovi,l)
        | GFun(nfd,_), GFun(ofd,l) ->
            begin try
                ofd.svar.vtype <- patchType ofd.svar.vtype nfd.svar.vtype ofd.svar.vname;
            with PatchFailed -> () end;
            ofd.svar.vattr <- patchAttrs ofd.svar.vattr nfd.svar.vattr;
            GFun(ofd,l)
        | GFun(nfd,_), GVarDecl(ovi, l) ->
            begin try
                ovi.vtype <- patchType ovi.vtype nfd.svar.vtype ovi.vname;
                nfd.svar.vtype <- patchType nfd.svar.vtype ovi.vtype nfd.svar.vname
            with PatchFailed -> () end;
            ovi.vattr <- patchAttrs ovi.vattr nfd.svar.vattr;
            nfd.svar.vattr <- patchAttrs nfd.svar.vattr ovi.vattr;
            GVarDecl(ovi,l)
        | GVarDecl(nvi, _), GFun(ofd,l) ->
            begin try
                ofd.svar.vtype <- patchType ofd.svar.vtype nvi.vtype ofd.svar.vname;
                nvi.vtype <- patchType nvi.vtype ofd.svar.vtype nvi.vname
            with PatchFailed -> () end;
            ofd.svar.vattr <- patchAttrs ofd.svar.vattr nvi.vattr;
            nvi.vattr <- patchAttrs nvi.vattr ofd.svar.vattr;
            GFun(ofd,l)
        | _ -> oldg
    in
    let sameGlob (newg : global) (oldg : global) : bool =
        match newg, oldg with
        | GType _, GType _
        | GCompTag _, GCompTag _
        | GCompTagDecl _, GCompTagDecl _
        | GEnumTag _, GEnumTag _
        | GEnumTagDecl _, GEnumTagDecl _
        | GVarDecl _, GVarDecl _
        | GVar _, GVar _
        | GFun _, GFun _
        | GAsm _, GAsm _
        | GText _, GText _
        | GPragma _, GPragma _ -> true
        | _ -> false
    in
    let addOne (g : global) =
        let gname = globName g in
        try let gl = Hashtbl.find globServHash gname in
        let ngl = List.map (mergeGlob g) gl in
        Hashtbl.replace globServHash gname ngl;
        if not(List.exists (sameGlob g) ngl) then
            Hashtbl.replace globServHash gname (g :: ngl)
        with Not_found -> Hashtbl.add globServHash gname [g]
    in
    List.iter addOne gl

let getGlobal (s : string) : globServRes =
    try GSGlob(Hashtbl.find globServHash s)
    with Not_found -> GSGlob []

class globalVarStdClass = object(self)
    inherit nopCilVisitor

    method vvrbl (vi : varinfo) =
        let rec findVi (gl : global list) : varinfo =
            match gl with
            | [] -> E.s(E.error "globalStdClass: no global vi for %s" vi.vname)
            | (GVarDecl(vi,_)|GVar(vi,_,_)) :: _ -> vi
            | (GFun(fd,_)) :: _ -> fd.svar
            | _ :: rst -> findVi rst
        in
        if not vi.vglob then DoChildren else
        try let gl = Hashtbl.find globServHash vi.vname in
            let realvi = findVi gl in
            ChangeTo realvi
        with Not_found ->
            E.s(E.error "globalStdClass: glob not in globServHash: %s" vi.vname)

end

class globalCompStdClass = object(self)
    inherit nopCilVisitor

    method vtype (t : typ) =
        match t with
        | TComp(ci, a) -> begin
            let rec findComp (gl : global list) : compinfo =
                match gl with
                | [] -> E.s (E.error "globalCompStdClass: no global for %s" ci.cname)
                | (GCompTag(ci,_) | GCompTagDecl(ci,_)) :: _ -> ci
                | _ :: rst -> findComp rst
            in
            try let gl = Hashtbl.find globServHash ci.cname in
                let ncomp = findComp gl in
                ChangeTo(TComp(ncomp, a))
            with Not_found ->
                E.s(E.error "globalCompStdClass: ci not in globServHash: %s" ci.cname)
        end
        | _ -> DoChildren


end

let standardizeGlobals (g : global) : global =
    let vis1 = new globalVarStdClass in
    let vis2 = new globalCompStdClass in
    ignore(visitCilGlobal vis1 g);
    ignore(visitCilGlobal vis2 g);
    g

let analyzeAndExit () =
    let rpd = validateRootPatchesDir () in
    Sys.remove (rpd^"/serverRunning");
    Hashtbl.fold (fun n gl ggl -> gl @ ggl) globServHash []
        |> List.map standardizeGlobals
        |> (!processGlobals);
    exit 1

(* must wait for client to die and then the next one start back up *)
let serverWait () : unit =
    let rpd = validateRootPatchesDir () in
    let start = Unix.time () in
    let rec loop () =
        E.log ""; (* user supplied signal handlers don't work unless this is here *)
        if (Unix.time()) -. start > waitTimeout then
            analyzeAndExit();
        if not(Sys.file_exists (rpd^"/clientRunning")) then
            begin Unix.sleep 1; loop(); end
    in
    loop ()

(* must wait for server to start up *)
let clientWait () : unit =
    let rpd = validateRootPatchesDir () in
    let rec loop () =
        E.log ""; (* user supplied signal handlers don't work unless this is here *)
        if not(Sys.file_exists (rpd^"/serverRunning")) then
            begin Unix.sleep 1; loop(); end
    in
    loop ()

let handleRequest (r : globServReq)
                  (outpipe : Unix.file_descr)
                  (inpipe : Unix.file_descr)
                  : unit
    =
    match r with
    | GSPutGlob gl ->
        addGlobals gl
    | GSGetGlob s -> write outpipe (getGlobal s)
    | GSPutClose ->
        write outpipe GSClose;
        Unix.close inpipe;
        c_to_s_in := None;
        serverWait()
    | GSError -> ()

let rec handleTermSignal (sn : int) : unit =
    Sys.set_signal Sys.sigterm (Sys.Signal_handle handleTermSignal);
    analyzeAndExit()

(* server entry point *)
let globServer (func : string) : unit =
    let rpd = validateRootPatchesDir () in
    let sr = rpd^"/serverRunning" in
    let outf = open_out sr in
    output_string outf (string_of_int (Unix.getpid()));
    close_out outf;
    setGlobalProcessor func;
    Sys.set_signal Sys.sigterm (Sys.Signal_handle handleTermSignal);
    let rec loop () =
        let inpipe = getCToSInPipe () in
        let outpipe = getSToCOutPipe () in
        handleRequest (recvReq inpipe) outpipe inpipe;
        loop();
    in
    loop ()

(* Starts the global server. Returns global server's pid *)
let startServer (s : string) : int =
    let rpd = validateRootPatchesDir () in
    let sr = rpd^"/serverRunning" in
    if Sys.file_exists sr then begin
        let inf = open_in sr in
        let pids = input_line inf in
        let pid = int_of_string pids in
        close_in inf;
        pid
    end else begin
        let ctos = rpd^"/ctospipe"
        and stoc = rpd^"/stocpipe" in
        if not(Sys.file_exists ctos) then
            Unix.mkfifo ctos 0o644;
        if not(Sys.file_exists stoc) then
            Unix.mkfifo stoc 0o644;
        let pid = Unix.fork () in
        if pid <> 0 then (clientWait(); pid) else
        Unix.execv (Sys.argv.(0)) [|Sys.argv.(0);
                                    "--a-glob-server";
                                    "--a-global-analysis";s;
                                    "--a-build-root";!Ivyoptions.buildRoot|]
    end



