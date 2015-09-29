(*
 * dfdatbrowser.ml
 *
 * This module generates an html file for a source file.
 * The html file has links to an html file for each function mentioned in
 * the functionData structure that is also defined in the source file.
 *
 *)


open Cil
open Pretty
open Ivyoptions
open Dutil
open Dattrs
open Dcheckdef

module E = Errormsg
module IH = Inthash

module DPF = Dprecfinder
module DCE = Dcanonexp

module X = XHTML.M


let tmToStr (t : Unix.tm) : string =
    (string_of_int (t.Unix.tm_hour))^":"^
    (string_of_int (t.Unix.tm_min))^" GMT "^
    (string_of_int (t.Unix.tm_mon+1))^"/"^
    (string_of_int (t.Unix.tm_mday))^"/"^
    (string_of_int (t.Unix.tm_year + 1900))

let href url elts =
    X.a ~a:[X.a_href url] elts


let rec gcd a b = if b = Int64.zero then a else gcd b (Int64.rem a b)

let ceGCD (ce : DCE.Can.t) : int64 =
    List.fold_left (fun g (f, _) ->
        if f = Int64.zero then g else
        if g = Int64.zero then (Int64.abs f)
        else gcd g (Int64.abs f)) Int64.zero ce.DCE.Can.cf

let divByGCD (ce : DCE.Can.t) : DCE.Can.t =
    let g = ceGCD ce in
    let newcf = List.map (fun (f, e) -> (Int64.div f g, e)) ce.DCE.Can.cf in
    {DCE.Can.ct = Int64.div ce.DCE.Can.ct g;
     DCE.Can.cf = newcf;
     DCE.Can.ck = ce.DCE.Can.ck}

let partConExp (ce : DCE.Can.t) : DCE.Can.t * DCE.Can.t =
    let ce = divByGCD ce in
    let pos, neg = List.partition (fun (c, _) -> c > Int64.zero) ce.DCE.Can.cf in
    let neg = List.map (fun (c, e) -> (Int64.neg c, e)) neg in
    if ce.DCE.Can.ct > Int64.zero then
        {DCE.Can.ct = ce.DCE.Can.ct; DCE.Can.cf = pos;DCE.Can.ck=ce.DCE.Can.ck},
        {DCE.Can.ct = Int64.zero; DCE.Can.cf = neg;DCE.Can.ck=ce.DCE.Can.ck}
    else if ce.DCE.Can.ct < Int64.zero then
        {DCE.Can.ct = Int64.zero; DCE.Can.cf = pos;DCE.Can.ck=ce.DCE.Can.ck},
        {DCE.Can.ct = Int64.neg ce.DCE.Can.ct; DCE.Can.cf = neg;DCE.Can.ck=ce.DCE.Can.ck}
    else
        {DCE.Can.ct = Int64.zero; DCE.Can.cf = pos;DCE.Can.ck=ce.DCE.Can.ck},
        {DCE.Can.ct = Int64.zero; DCE.Can.cf = neg;DCE.Can.ck=ce.DCE.Can.ck}
        
let printConLeq (e1 : exp) (e2 : exp) : doc =
    let ce1 = DCE.canonExp Int64.one e1 in
    let ce2 = DCE.canonExp Int64.one e2 in
    let cdiff = DCE.Can.sub ce2 ce1 ILong in
    let greater, lesser = partConExp cdiff in
    (DCE.Can.d_t () lesser) ++ text " <= " ++
    (DCE.Can.d_t () greater)

let d_checkinstr () (i : instr) : doc =
    match instrToCheck i with
    | None -> nil
    | Some c -> begin
        match c with
        | CNonNull e ->
            dprintf "%a != NULL" dc_exp e
        | CEq(e1, e2, _, _) ->
            dprintf "%a == %a" dc_exp e1 dc_exp e2
        | CMult(e1,e2) ->
            dprintf "%a %% %a == 0" dc_exp e2 dc_exp e1
        | CPtrArithAccess(lo,hi,p,e,_) ->
            let e' = BinOp(PlusPI,p,e,typeOf p) in
            let e'' = BinOp(PlusPI,p,BinOp(PlusA,e,one,typeOf e),typeOf p) in
            (printConLeq lo e') ++ text " /\\ " ++
            (printConLeq e'' hi)
        | CPtrArith(lo,hi,p,e,_) ->
            let e' = BinOp(PlusPI,p,e,typeOf p) in
            (printConLeq lo e') ++ text " /\\ " ++
            (printConLeq e' hi)
        | CPtrArithNT(lo,hi,p,e,_) ->
            let e' = BinOp(PlusPI,p,e,typeOf p) in
            (printConLeq lo e') ++ text " /\\ " ++
            (dprintf "%a <= %a + len(%a)"
                dc_exp e' dc_exp hi dc_exp hi)
        | CLeqInt(e1,e2,_) ->
            printConLeq e1 e2
        | CLeq(e1, e2, _) ->
            printConLeq e1 e2
        | CLeqNT(e1,e2,_,_) ->
            dprintf "%a <= %a + len(%a)" dc_exp e1 dc_exp e2 dc_exp e2
        | CNullOrLeq(e1,e2,e3,_) ->
            (dprintf "%a == NULL \\/ " dc_exp e1) ++
            (printConLeq e2 e3)
        | CNullOrLeqNT(e1,e2,e3,_,_) ->
            (dprintf "%a == NULL \\/ %a <= %a + len(%a)"
                dc_exp e1 dc_exp e2 dc_exp e3 dc_exp e3)
        | CWriteNT(p,hi,what,sz) ->
            (dprintf "%a != %a \\/ *(%a) != 0 \\/ %a == 0"
                dc_exp p dc_exp hi dc_exp p dc_exp what)
        | CNullUnionOrSelected(lv, sfs) ->
            (dprintf "%a || iszero(%a)" dc_exp sfs dx_lval lv)
        | CSelected e ->
            (dprintf "%a" dc_exp e)
        | CNotSelected e ->
            (dprintf "! %a" dc_exp e)
    end


(* TODO : 1. clean up and canonicalize the checks.
          2. refer to globals as filename:varname. *)
let genPrecsForHtml (il : instr list) =
    List.fold_left
        (fun el i ->
            (*let d = sprint ~width:80 (d_instr () i) in*)
            let p = sprint ~width:80 (d_checkinstr () i) in
            (*(X.p [X.pcdata d]) ::*)
            (X.p [X.pcdata p]) :: el)
        []
        il

let declToHtml (vi : varinfo) =
    let p = sprint ~width:80 (d_global () (GVarDecl(vi, locUnknown))) in
    (X.p [X.pcdata p])

(* Take the fundec, the list of preconditions and a base name, and write
   the prototype and preconditions to an html file with base name name *)
let genPageForFunction (fd : fundec) (il : instr list) (name : string) : unit =
    let precs = genPrecsForHtml il in
    if precs = [] then () else
    let time = Unix.gmtime (Unix.time()) in
    let locstr = sprint ~width:80 (d_loc () fd.svar.vdecl) in
    let titlestr = locstr^" - "^fd.svar.vname in
    let html = X.html (*~a:[X.a_xmlns X.W3_org_1999_xhtml; X.a_xml_lang "en"]*)
        (X.head
            (X.title (X.pcdata titlestr))
            [X.style ~contenttype:"text/css" [X.pcdata "H1 {color: back}"]])
        (X.body
            ([X.h1 [X.pcdata titlestr];
              X.hr()] @
              [X.h2 [X.pcdata "Function Prototype"];
               declToHtml fd.svar;
               X.h2 [X.pcdata "Preconditions"]] @
              precs @
             [X.hr();
              X.p [X.pcdata ("Last update - "^(tmToStr time))]]))
    in try
        let outf = open_out (!htmlOutDir^"/"^name^".html") in
        X.pretty_print ~width:80 (output_string outf) html;
        close_out outf
    with Sys_error msg -> begin
        ignore(E.log "Dfdatbrowser: error writing file: %s" msg)
    end


(* Take in a file and the function data and generate the files
   for functions, and a list of links to those files *)
let genLinksForFile (f : file) (fdat : DPF.functionData) =
    (* For each function defined in the file:
        1. If it's mentioned in fdat, write to file.html.
        2. Call genPageForFunction on the function. *)
    foldGlobals f
        (fun l g -> match g with
        | GFun(fd, loc) -> begin
            match IH.tryfind fdat.DPF.fdPCHash fd.svar.vid with
            | (Some il) when il <> [] -> begin
                let name = fd.svar.vname in
                genPageForFunction fd il name;
                (X.p [href (name^".html") [X.pcdata name]]) ::
                l
            end
            | _ -> l
        end
        | _ -> l) []

let genSourceFileLinks () =
    try
        let dirhand = Unix.opendir (!htmlOutDir) in
        let rec loop acc =
            try
                let fname = Unix.readdir dirhand in
                if Filename.check_suffix fname "i.html" then
                    loop ((X.p [href fname [X.pcdata fname]]) :: acc)
                else loop acc
            with End_of_file -> acc
        in
        loop []
    with Sys_error msg -> begin
        ignore(E.log "Dfdatbrowser: error writing index: %s" msg);
        []
    end

let rewriteIndex () : unit =
    let links = genSourceFileLinks () in
    if links = [] then () else
    let time = Unix.gmtime (Unix.time()) in
    let html = X.html (*~a:[X.a_xmlns X.W3_org_1999_xhtml; X.a_xml_lang "en"]*)
        (X.head
            (X.title (X.pcdata "File Information"))
            [X.style ~contenttype:"text/css" [X.pcdata "H1 {color: back}"]])
        (X.body
            ([X.h1 [X.pcdata "File Information"];
              X.hr()] @
              links @
              [X.hr();
              X.p [X.pcdata ("Last update - "^(tmToStr time))]]))
    in try
        let outf = open_out (!htmlOutDir^"/index.html") in
        X.pretty_print ~width:80 (output_string outf) html;
        close_out outf
    with Sys_error msg -> begin
        ignore(E.log "Dfdatbrowser: error writing file: %s" msg)
    end

(* Take in a file and the function data and generate the html file
   for it *)
(* TODO: This should be made more robust. I.e. if htmlOutDir doesn't exist,
   then create it. Also, if htmlOutDir/index.html doesn't exist, then create it.
   If it does exist then concat the link to this file. *)
let genPageForFile (f : file) (fdat : DPF.functionData) =
    let links = genLinksForFile f fdat in
    if links = [] then () else
    let time = Unix.gmtime (Unix.time()) in
    let html = X.html (*~a:[X.a_xmlns X.W3_org_1999_xhtml; X.a_xml_lang "en"]*)
        (X.head
            (X.title (X.pcdata f.fileName))
            [X.style ~contenttype:"text/css" [X.pcdata "H1 {color: back}"]])
        (X.body
            ([X.h1 [X.pcdata f.fileName];
              X.hr()] @
              links @
              [X.hr();
              X.p [X.pcdata ("Last update - "^(tmToStr time))]]))
    in try
        let outf = open_out (!htmlOutDir^"/"^f.fileName^".html") in
        X.pretty_print ~width:80 (output_string outf) html;
        close_out outf;
        rewriteIndex ()
    with Sys_error msg -> begin
        ignore(E.log "Dfdatbrowser: error writing file: %s" msg)
    end
