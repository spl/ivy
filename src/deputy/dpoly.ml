(*
 *
 * Copyright (c) 2006, 
 *  Jeremy Condit       <jcondit@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
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
open Expcompare

open Dattrs
open Dutil

module E = Errormsg
module H = Hashtbl

exception PolyError

type map = (string, typ) H.t

let polyTypes: (string, typ list) H.t = H.create 5
let polyMap: map = H.create 5

let polyStart () : unit =
  if H.length polyMap > 0 || H.length polyTypes > 0 then
    E.s (bug "Polymorphism info was not cleared appropriately.")

let polyClear () : unit =
  H.clear polyMap;
  H.clear polyTypes

let getPoly (t: typ) : string =
  match filterAttributes "tyvar" (typeAttrs t) with
  | [Attr ("tyvar", [ACons (tv, [])])] -> tv
  | [] -> raise Not_found
  | _ -> E.s (error "Too many type variable attributes.")

let isPoly (t: typ) : bool =
  hasAttribute "tyvar" (typeAttrs t)

let rec polyMakeSubst (tTo: typ) (tFrom: typ) : unit =
  let addSubst tyvar t =
    let oldList =
      try
        H.find polyTypes tyvar
      with Not_found ->
        []
    in
    H.replace polyTypes tyvar (t :: oldList)
  in
  match unrollType tTo, unrollType tFrom with
  | _ when isPoly tTo ->
      addSubst (getPoly tTo) tFrom
  | TPtr (bt1, _), TPtr (bt2, _)
  | TArray (bt1, _, _), TArray (bt2, _, _) ->
      polyMakeSubst bt1 bt2
  | TComp (_, attrs1), TComp (_, attrs2) ->
      if hasAttribute "typaram" attrs1 <> hasAttribute "typaram" attrs2 then
        error ("Type parameter mismatch in coercion:\n" ^^
               "  from: %a\n" ^^
               "    to: %a") dx_type tFrom dx_type tTo
      else begin
        match filterAttributes "typaram" attrs1,
              filterAttributes "typaram" attrs2 with
        | [Attr (_, [ASizeOf t1])], [Attr (_, [ASizeOf t2])] ->
            if isPoly t1 then
              addSubst (getPoly t1) t2
        | [Attr (_, _)], [Attr (_, _)] ->
            error "Malformed type parameter attribute."
        | _ :: _, _ | _, _ :: _ ->
            error "Too many type parameter attributes."
        | [], [] ->
            () (* Okay--no type parameters on either. *)
      end
  | _ -> ()

let polyResolve () : unit =
  H.iter
    (fun tyvar types ->
       let fancy, basic =
         List.partition
           (fun t -> hasAttribute "fancybounds" (typeAttrs t))
           types
       in
       let canonical =
         match basic with
         | t :: rest -> t
         | [] -> E.s (error "No non-fancy substitution discovered.")
       in
       List.iter
         (fun t ->
            if not (compareTypes canonical t) then
              E.s (error "Cannot unify types %a and %a."
                         dx_type canonical dx_type t))
         basic;
       let canonical' = typeRemoveAttributes ["bounds"] canonical in
       List.iter
         (fun t ->
            let t' = typeRemoveAttributes ["fancybounds"] t in
            if not (compareTypes canonical' t') then
              E.s (error "Cannot unify types %a and %a."
                         dx_type canonical' dx_type t'))
         fancy;
       H.replace polyMap tyvar canonical)
    polyTypes

let polyCompMap (t: typ) : map =
  let attrs =
    match unrollType t with
    | TComp (_, a) -> a
    | _ -> E.s (error "Bad field offset on type %a" dx_type t)
  in
  let map = H.create 5 in
  begin
    match filterAttributes "typaram" attrs with
    | [] -> ()
    | [Attr ("typaram", [ASizeOf t])] -> H.replace map "t" t
    | [_] -> E.s (error "Invalid type parameter on structure.")
    | _ -> E.s (error "Too many type parameters on structure.")
  end;
  map

let polySubstVisitor (map: map) = object (self)
  inherit nopCilVisitor

  method vtype t =
    if isPoly t then
      let tyvar = getPoly t in
      try
        ChangeTo (H.find map tyvar)
      with Not_found ->
        raise PolyError
    else
      DoChildren
end

let polySubst (map: map) (t: typ) : typ =
  visitCilType (polySubstVisitor map) t
