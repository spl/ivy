(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
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

open Cil
open Pretty
open Dattrs
open Dutil

module E = Errormsg

(* Process a printf-like vararg function. Each argument gets a cast
 * to its expected type so that later type-checking phases work properly. *)
let processVarargs (args: exp list) (nrFormals: int) (formidx: int) : exp list = 
  (* Return the index of the next descriptor *)
  let findNextDescr (s: string) (from: int) : char * int =
    try
      let i = String.index_from s from '%' in
      let rec parseConversionSpec (start: int) : char * int =
        match Char.lowercase s.[start] with
        | 'e' | 'f' | 'g'     (* double arg *)
        | 'a' ->              (* double arg *)
            'f', start + 1
        | 'd' | 'i'           (* signed int arg *)
        | 'o' | 'u' | 'x'     (* unsigned int arg *)
        | 'c'                 (* unsigned char *)
        | 'p' ->              (* void pointer treated as int *)
            'd', start + 1
        | 's' -> 's', start + 1 (* char pointer *)
        | 'n' -> 'n', start + 1
        | '%' ->
            let i' = String.index_from s (start + 1) '%' in
            parseConversionSpec (i' + 1)
        | _ -> parseConversionSpec (start+1)
       in
       parseConversionSpec (i + 1)
     with _ ->
       '_', -1
  in

  let getDescrType (descr: char) : typ =
    match descr with
    | 'f' -> doubleType
    | 'd' -> intType
    | 'n' -> intPtrType
    | 's' -> typeAddAttributes Dattrs.stringAttrs charPtrType
    | _ -> E.s (bug "Unexpected vararg descr %c." descr)
  in
    
  let rec checkFormatArgs (form: string) (idx: int) (args: exp list)
      : exp list =
    let descr, idx' = findNextDescr form idx in
    match descr, args with
    | '_', [] -> []
    | '_', _ ->
        warn "Too many arguments to printf-like vararg function.";
        args
    | _, [] ->
        errorwarn "Too few arguments to printf-like vararg function.";
        args
    | _, arg :: rest ->
        (* TODO: This cast may change the behavior of the program; for
         * example, casting a pointer to an integer for %d may convert
         * a 64-bit pointer to a 32-bit integer on some architectures.
         * Is there a better way? *)
        mkCast arg (getDescrType descr) :: (checkFormatArgs form idx' rest)
  in

  if formidx <= 0 || formidx > nrFormals then 
    E.s (error "Expected the format string to be the %dth argument." formidx);
  if List.length args < nrFormals then 
    E.s (error "Too few arguments to vararg function.");

  match List.nth args (formidx - 1) with 
  | Const (CStr form) -> 
      let preArgs, vaArgs = split args nrFormals in
      preArgs @ (checkFormatArgs form 0 vaArgs)
  | _ -> 
      warn "Cannot check varargs due to non-literal format string.";
      args


(* Returns a pair containing the number of formal arguments and the index
 * of the format string. *)
let getVarargData (func: exp) : int * int = 
  match unrollType (typeOf func) with
  | TFun (_, Some forms, _, a) ->
      begin
        match filterAttributes "dvararg" a with 
        | Attr (_, [ACons("printf", [AInt fidx])]) :: _ -> 
            List.length forms, fidx
        | a -> raise Not_found
      end
  | _ -> assert false
  
      
(* Prepare the arguments in a call to a vararg function. *)
let prepareVarargArguments
    ~(mkTempVar: typ -> varinfo) (* how to make a temporary variable *)
    ~(func: exp)                 (* the called function *)
    ~(nrformals: int)            (* how many formals *)
    ~(args: exp list) : exp list = 

  try
    let forms, fidx = getVarargData func in
    processVarargs args forms fidx
  with Not_found -> begin
    if !Ivyoptions.warnVararg then
      warn "Call to vararg function %a not fully checked." d_exp func;
    args
  end


(* Turn the gcc format attribute into our own notation.  Returns a type
 * that may have a new attribute but which is otherwise the same. *)
let processFormatAttribute (funType: typ) : typ = 
  match filterAttributes "format" (typeAttrs funType) @
        filterAttributes "__format__" (typeAttrs funType)
  with
  | [Attr (_, [ACons (name, []); AInt format_idx; AInt _])] ->
      if name = "printf" || name = "__printf__" then begin
        match funType with 
        | TFun (rt, forms, isva, a) -> 
            TFun (rt, forms, isva, 
                  addAttribute
                    (Attr("dvararg", [ACons("printf", [AInt format_idx])])) a)
        | _ -> assert false
      end else if name = "scanf"    || name = "__scanf__"    ||
                  name = "strftime" || name = "__strftime__" ||
                  name = "strfmon"  || name = "__strfmon"    then begin
        (* Ignore these for now. *)
        funType
      end else begin
        warn "Did not understand %s format attribute." name;
        funType
      end

  | [] -> funType
  | al -> warn "Malformed format attribute."; funType
