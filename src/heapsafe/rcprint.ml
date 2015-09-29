(* Copyright (c) 2007 Intel Corporation 
 * All rights reserved. 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 	Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 	Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *     Neither the name of the Intel Corporation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE INTEL OR ITS
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)
(* The 'rcPrinter' class  filters out our attributes, and prints adjust 
   functions *)
open Cil
open Rcutils
open Rc
open Pretty
module L = List
module E = Errormsg
module H = Hashtbl

(* Wrap some code in a C block *)
let wrapInBlock (body:doc) : doc = 
  (text "{\n") ++ (indent 2 body) ++ (text "}\n")

(* RCHACK: typedebug code doesn't deal with floats yet *)

(* Generate the calls to RC_ADJUST for all pointers in a variabled called
  'name' whose type is 't' 
*)
let adjustVariable (name:string) (t:typ) : doc =
  let nextTemp = ref 0 in (* For generating unique index variables *)

  (* accessor is a doc value (thunk because that's what dprintf's %t
     wants) that corresponds to the part of the value being adjusted.
     't' is the type of 'accessor'. *)
  let rec adjustByType t accessor = 
    match t with
    | TPtr _ when not (isNorc t) -> dprintf "RC_ADJUST(%t, by);\n" accessor
    | TNamed (ti, _) -> adjustByType ti.ttype accessor
    | TArray (ta, size, _) when typeContainsCountedPointers ta -> 
	(* Generate a loop over the array elements *)
	nextTemp := !nextTemp + 1;
	let name = dprintf "index%d" !nextTemp in
	let namet = fun () -> name in
	let decl = dprintf "unsigned long %t;\n" namet
	and loop = if isOpenArraySize size then
                dprintf "for (%t = 0; &((%t)[%t]) < (char*)x + size; %t++)" namet accessor namet namet
                else            
                dprintf "for (%t = 0; %t < sizeof %t / sizeof *%t; %t++)" namet namet accessor accessor namet
	and element = dprintf "%t[%t]" accessor namet in
	let elementt = fun () -> element in
	let elementBody = adjustByType ta elementt in
	let body = decl ++ line ++ loop ++ line ++ elementBody in
	wrapInBlock body
    | TComp (ci, _) ->
	(* Generate code for all structure fields *)
	let adjustField fi = 
	  if fi.fbitfield = None then
                let fOffset = dprintf "%t.%s" accessor fi.fname in
	        adjustByType fi.ftype (fun () -> fOffset)
          else nil
	in
	let body = L.fold_left concat nil (L.map adjustField ci.cfields) in
	wrapInBlock body
    | TInt(_, _) | TEnum(_, _) when !Ivyoptions.typeDebug ->
        dprintf "RC_CHECKPTR(%t);\n" accessor
    | _ -> nil
  in
  adjustByType t (fun () -> text ("(*" ^ name ^ ")"))


(* Printer that filters out our attributes, and prints adjust functions *)
class rcPrinter : cilPrinter = object (self)
  inherit defaultCilPrinterClass as super

  (* Print an adjust function called 'name' for type 't' *)
  method private pAdjustFn (name, t) : doc = 
    let linedir = text ("#line 1 \"" ^ name ^ ".c\"") in
    let header = dprintf "static inline void %s(void *x, int by, %a size)" 
			 name d_type !typeOfSizeOf in
    let decl = dprintf "%a = x;\n" (self#pType (Some (text "p"))) (TPtr(t, []))
    and adjustments = adjustVariable "p" t in
    let body = if isOpenStruct t then
            decl ++ line ++ adjustments
        else 
            decl ++ line ++ 
	    (text "RC_ADJUST_START(p, size);\n") ++
	    adjustments ++
	    (text "RC_ADJUST_END(p, sizeof *p);\n") in
    linedir ++ line ++ header ++ line ++ (wrapInBlock body) ++ line

  method private makeAdjustFile (name:string) (fn:doc) : unit =
    try
      begin
	try
	  Unix.mkdir !Ivyoptions.adjustDir 0o777;
	with
	  Unix.Unix_error (Unix.EEXIST, _, _) -> ()
	| Unix.Unix_error (e, _, _) -> raise (Sys_error (Unix.error_message e))
      end;
      let adjFname = Filename.concat !Ivyoptions.adjustDir (name ^ ".c") in 
      let adjChannel = open_out adjFname in 
      ignore(fprint adjChannel 80 fn)
    with
      Sys_error e -> 
	ignore(Errormsg.warn "Could not create file for adjust function %s: %s" name e)

  method private pAdjustFnOnce (name, t) : doc = 
    if H.mem autoGeneratedAdjustFunctions name then
      begin
	H.remove autoGeneratedAdjustFunctions name;
	let adjustDoc = self#pAdjustFn (name, t) in
	if !Ivyoptions.saveAdjust then
	  self#makeAdjustFile name adjustDoc;
	adjustDoc
      end
    else
      nil

  method dGlobal (out:out_channel) (g:global) : unit = 
    let adjustStuff = 
      match g with
      | GFun({svar = v}, _) | GVar (v,_,_) ->
	  let adjustFns = H.find_all adjustFunctionsToAdd v in
	  L.fold_left concat nil (L.map self#pAdjustFnOnce adjustFns)
      | _ -> nil
    in
    fprint out !lineLength adjustStuff;
    super#dGlobal out g

  method pAttr (a: attribute) : doc * bool =
    match a with
    | Attr(("hs_norc" | "hs_trace" | "hs_nofree" | "hs_untyped"), _) -> 
	text "", false
    | Attr(n,_) when List.mem n Sutil.sharc_attrs ||
                     Dutil.isDeputyAttr a ->
        text "", false
    | _ -> super#pAttr a
end

(* Generate the calls to CRC_ADJUST for all pointers in a variabled called
  'name' whose type is 't' 
*)
let cAdjustVariable (name:string) (t:typ) : doc =
  let nextTemp = ref 0 in (* For generating unique index variables *)

  (* accessor is a doc value (thunk because that's what dprintf's %t
     wants) that corresponds to the part of the value being adjusted.
     't' is the type of 'accessor'. *)
  let rec adjustByType t accessor = 
    match t with
    | TPtr _ when not (isNorc t) -> dprintf "CRC_ADJUST(&(%t),(by));\n" accessor
    | TNamed (ti, _) -> adjustByType ti.ttype accessor
    | TArray (ta, size, _) when typeContainsCountedPointers ta -> 
	(* Generate a loop over the array elements *)
	nextTemp := !nextTemp + 1;
	let name = dprintf "index%d" !nextTemp in
	let namet = fun () -> name in
	let decl = dprintf "unsigned long %t;\n" namet
	and loop = if isOpenArraySize size then
                dprintf "for (%t = 0; &((%t)[%t]) < (char*)x + size; %t++)" namet accessor namet namet
                else            
                dprintf "for (%t = 0; %t < sizeof %t / sizeof *%t; %t++)" namet namet accessor accessor namet
	and element = dprintf "%t[%t]" accessor namet in
	let elementt = fun () -> element in
	let elementBody = adjustByType ta elementt in
	let body = decl ++ line ++ loop ++ line ++ elementBody in
	wrapInBlock body
    | TComp (ci, _) ->
	(* Generate code for all structure fields *)
	let adjustField fi = 
	  if fi.fbitfield = None then
                let fOffset = dprintf "%t.%s" accessor fi.fname in
	        adjustByType fi.ftype (fun () -> fOffset)
          else nil
	in
	let body = L.fold_left concat nil (L.map adjustField ci.cfields) in
	wrapInBlock body
    | TInt(_, _) | TEnum(_, _) when !Ivyoptions.typeDebug ->
        dprintf "RC_CHECKPTR(%t);\n" accessor
    | _ -> nil
  in
  adjustByType t (fun () -> text ("(*" ^ name ^ ")"))

(* Generate the calls to CRC_INVALIDATE for all pointers in a variabled called
  'name' whose type is 't' 
*)
let cInvalidateVariable (name:string) (t:typ) : doc =
  let nextTemp = ref 0 in (* For generating unique index variables *)

  (* accessor is a doc value (thunk because that's what dprintf's %t
     wants) that corresponds to the part of the value being adjusted.
     't' is the type of 'accessor'. *)
  let rec adjustByType t accessor = 
    match t with
    | TPtr _ when not (isNorc t) -> dprintf "CRC_INVALIDATE(&(%t));\n" accessor
    | TNamed (ti, _) -> adjustByType ti.ttype accessor
    | TArray (ta, size, _) when typeContainsCountedPointers ta -> 
	(* Generate a loop over the array elements *)
	nextTemp := !nextTemp + 1;
	let name = dprintf "index%d" !nextTemp in
	let namet = fun () -> name in
	let decl = dprintf "unsigned long %t;\n" namet
	and loop = if isOpenArraySize size then
                dprintf "for (%t = 0; &((%t)[%t]) < (char*)x + size; %t++)" namet accessor namet namet
                else            
                dprintf "for (%t = 0; %t < sizeof %t / sizeof *%t; %t++)" namet namet accessor accessor namet
	and element = dprintf "%t[%t]" accessor namet in
	let elementt = fun () -> element in
	let elementBody = adjustByType ta elementt in
	let body = decl ++ line ++ loop ++ line ++ elementBody in
	wrapInBlock body
    | TComp (ci, _) ->
	(* Generate code for all structure fields *)
	let adjustField fi = 
	  if fi.fbitfield = None then
                let fOffset = dprintf "%t.%s" accessor fi.fname in
	        adjustByType fi.ftype (fun () -> fOffset)
          else nil
	in
	let body = L.fold_left concat nil (L.map adjustField ci.cfields) in
	wrapInBlock body
    | TInt(_, _) | TEnum(_, _) when !Ivyoptions.typeDebug ->
        dprintf "RC_CHECKPTR(%t);\n" accessor
    | _ -> nil
  in
  adjustByType t (fun () -> text ("(*" ^ name ^ ")"))

(* Printer that filters out our attributes, and prints adjust functions *)
class cRcPrinter : cilPrinter = object (self)
  inherit defaultCilPrinterClass as super

  (* Print an adjust function called 'name' for type 't' *)
  method private pAdjustFn (name, t) : doc = 
    let linedir = text ("#line 1 \"" ^ name ^ ".c\"") in
    let header = dprintf "static inline void %s(void *x, int by, %a size, int inv)" 
			 name d_type !typeOfSizeOf in
    let decl = dprintf "%a = x;\n" (self#pType (Some (text "p"))) (TPtr(t, []))
    and adjustments = cAdjustVariable "p" t in
    let invalidations = cInvalidateVariable "p" t in
    let actions = text "if (inv) {\n" ++ invalidations ++ text "} else {\n" ++ adjustments ++ text "}\n" in
    let body = if isOpenStruct t then
            decl ++ line ++ actions
        else 
            decl ++ line ++ 
	    (text "RC_ADJUST_START(p, size);\n") ++
	    actions ++
	    (text "RC_ADJUST_END(p, sizeof *p);\n") in
    linedir ++ line ++ header ++ line ++ (wrapInBlock body) ++ line

  method private makeAdjustFile (name:string) (fn:doc) : unit =
    try
      begin
	try
	  Unix.mkdir !Ivyoptions.adjustDir 0o777;
	with
	  Unix.Unix_error (Unix.EEXIST, _, _) -> ()
	| Unix.Unix_error (e, _, _) -> raise (Sys_error (Unix.error_message e))
      end;
      let adjFname = Filename.concat !Ivyoptions.adjustDir (name ^ ".c") in 
      let adjChannel = open_out adjFname in 
      ignore(fprint adjChannel 80 fn)
    with
      Sys_error e -> 
	ignore(Errormsg.warn "Could not create file for adjust function %s: %s" name e)

  method private pAdjustFnOnce (name, t) : doc = 
    if H.mem autoGeneratedAdjustFunctions name then
      begin
	H.remove autoGeneratedAdjustFunctions name;
	let adjustDoc = self#pAdjustFn (name, t) in
	if !Ivyoptions.saveAdjust then
	  self#makeAdjustFile name adjustDoc;
	adjustDoc
      end
    else
      nil

  method dGlobal (out:out_channel) (g:global) : unit =
    let adjustStuff = 
      match g with
      | GFun({svar = v}, _) | GVar (v,_,_) ->
	  let adjustFns = H.find_all adjustFunctionsToAdd v in
	  L.fold_left concat nil (L.map self#pAdjustFnOnce adjustFns)
      | _ -> nil
    in
    fprint out !lineLength adjustStuff;
    super#dGlobal out g

  method pAttr (a: attribute) : doc * bool =
    match a with
    | Attr(("hs_norc" | "hs_trace" | "hs_nofree" | "hs_untyped"), _) -> 
        text "", false
    | Attr(n,_) when List.mem n Sutil.sharc_attrs ||
                     Dutil.isDeputyAttr a ->
        text "", false
    | _ -> super#pAttr a
end
