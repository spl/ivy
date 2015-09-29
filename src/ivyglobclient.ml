(* Write lists of globals to a named pipe *)

open Cil
open Pretty
open Ivyutil

module E = Errormsg

let s_to_c_in  : Unix.file_descr option ref = ref None
let c_to_s_out : Unix.file_descr option ref = ref None

let getSToCInPipe () : Unix.file_descr =
    match !s_to_c_in with
    | Some p -> p
    | None ->
        let ppdir = validateRootPatchesDir () in
        let pipename = ppdir^"/stocpipe" in
        let pipe = Unix.openfile pipename [Unix.O_RDONLY] 0o000 in
        s_to_c_in := Some pipe;
        pipe

let getCToSOutPipe () : Unix.file_descr =
    match !c_to_s_out with
    | Some p -> p
    | None ->
        let ppdir = validateRootPatchesDir () in
        let dummy = open_out (ppdir^"/clientRunning") in
        close_out dummy;
        let pipename = ppdir^"/ctospipe" in
        let pipe = Unix.openfile pipename [Unix.O_WRONLY] 0o000 in
        c_to_s_out := Some pipe;
        pipe

let recvRes (fd : Unix.file_descr) : globServRes =
    let hdr = String.create (Marshal.header_size) in
    let hdr_rdsz = Unix.read fd hdr 0 Marshal.header_size in
    if hdr_rdsz <> Marshal.header_size then
        E.s(E.error "client: recvRes header failed: %d" hdr_rdsz);
    let datasz = Marshal.data_size hdr 0 in
    let data = String.create datasz in
    read fd data datasz;
    Marshal.from_string (hdr^data) 0

let putGlob (gl : global list) : unit =
    let outpipe = getCToSOutPipe () in
    let _ = getSToCInPipe () in
    write outpipe (GSPutGlob gl)

let getGlobs (name : string) : global list =
    let outpipe = getCToSOutPipe () in
    let inpipe = getSToCInPipe () in
    write outpipe (GSGetGlob name);
    match recvRes inpipe with
    | GSGlob gl -> gl
    | _ -> E.s(E.error "Expected GSGlob but got GSClose for %s" name)

let clientClose () : unit =
    E.log "Closing glob client\n";
    let outpipe = getCToSOutPipe () in
    let inpipe = getSToCInPipe () in
    let rpd = validateRootPatchesDir () in
    Sys.remove (rpd^"/clientRunning");
    write outpipe GSPutClose;
    Unix.close outpipe;
    match recvRes inpipe with
    | GSClose -> begin
        Unix.close inpipe
    end
    | _ -> E.s(E.error "clientClose: expected PSClose")

