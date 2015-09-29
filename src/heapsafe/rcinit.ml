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
(* Add code to clear all pointers in local variables on function entry *)
open Cil
open Rcutils
module L = List
module S = String

(* clear all pointers within the lvalue *)
let rec clearByType (f : fundec) (t:typ) (host,offset : lval) loc = 
  match t with
  | TPtr _ -> [ i2s (Set((host, offset), zero, loc)) ]
  | TNamed (ti, _) -> clearByType f ti.ttype (host,offset) loc
  | TArray (ta, _, _) when typeContainsCountedPointers ta -> 
      (* for (<var> = 0; <var> < sizeof 'offset' / sizeof *'offset'; <var>++)
	   {clear pointers in 'offset'[<var>]} *)
      let index = makeTempVar f ~name:"clear" intType in
      let indexOffset = addOffset (Index(v2e index, NoOffset)) offset in
      let body = clearByType f ta (host,indexOffset) loc in
      let arrayLval = (host, offset) in
      let arraySize = SizeOfE(Lval arrayLval) in
      let arrayDerefLval = (host, addOffset (Index(zero, NoOffset)) offset) in
      let arrayElemSize = SizeOfE(Lval arrayDerefLval) in
      let arrayElements = 
         constFoldBinOp true Div arraySize arrayElemSize !typeOfSizeOf in
      mkForIncr index zero arrayElements one body
  | TComp (ci, _) ->
      (* Generate code to clear pointers in all fields of 'ci' *)
      let clearField fi = 
        let fOffset = addOffset (Field(fi, NoOffset)) offset in
        clearByType f fi.ftype (host,fOffset) loc
      in
      L.concat (L.map clearField ci.cfields)

  | _ -> []

(* Return a statement list that clears all pointers in variable 'v' of 
   function 'f'. The location of the generated code is 'loc' *)
let clearVariable (f : fundec) (v : varinfo) (loc : location) : stmt list =
  clearByType f v.vtype (Var v, NoOffset) loc

(* Add code to 'f' to clear all pointers in its local variables. The location
   of the generated code is 'loc' *)
let clearFunctionLocals (f : fundec) (loc : location) : unit = 
  let mapCV v = clearVariable f v loc in
  let initialisers = L.concat (L.map mapCV f.slocals) in
  f.sbody.bstmts <- initialisers @ f.sbody.bstmts

let clearLocals (fi : file) : unit =
  iterGlobals fi (onlyFunctions (skipAdjustFunctions clearFunctionLocals))


(* generate a function to clear data of a particular type *)
(* let rcClearForType (fi:file) (inFn:fundec) (t:typ) (loc:location) : varinfo =
  let (name, nicename, t') = baseType "rc_clear" t in
  let (vi, isNew) = findFunction fi name rtTypes.rc_clear 
 *)

(* Fix the typeOfSizeOf and kindOfSizeOf references based on value of 
   'Ivyoptions.size_t' (specified by the -size_t option) *)
let fixSizeT () =
  let newkind = 
    match !Ivyoptions.size_t with
    | "" -> !kindOfSizeOf (* leave default *)
    | "int" -> IUInt
    | "long" -> IULong
    | "long long" -> IULongLong
    | x -> begin
	ignore(warn "Unknown -size_t option %s, specify int, long or long long" x);
	!kindOfSizeOf
    end
  in
  kindOfSizeOf := newkind;
  typeOfSizeOf := TInt(newkind, [])
