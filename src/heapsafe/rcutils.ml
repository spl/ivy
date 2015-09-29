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
(* Utility functions for the rest of HeapSafe *)
open Cil
module L = List
module H = Hashtbl
module S = String
module R = Str
module E = Errormsg

(* Attribute support functions.
   no<X>Attr: an attributes list containing just attribute <X>
   has<X>Attribute: true if attribute list contains attribute <X>
   is<X>: true if top-level of a type has attribute <X> *)
let nofreeAttr : attributes = [ Attr("hs_nofree", []) ]
let norcAttr : attributes = [ Attr("hs_norc", []) ]
let hasRctraceAttribute (a : attributes) : bool = hasAttribute "hs_trace" a
let hasNofreeAttribute (a : attributes) : bool = hasAttribute "hs_nofree" a
let hasNorcAttribute (a : attributes) : bool = hasAttribute "hs_norc" a
let hasBadfunAttribute (a : attributes) : bool = hasAttribute "hs_untyped" a
let isRctrace (t : typ) : bool = hasRctraceAttribute (typeAttrs t)
let isNofree (t : typ) : bool = hasNofreeAttribute (typeAttrs t)
let isNorc (t : typ) : bool = hasNorcAttribute (typeAttrs t)
let isBadfun (t : typ) : bool = hasBadfunAttribute (typeAttrs t)

let isHeapsafeAttr (a : attribute) : bool =
    match a with
    | Attr(("hs_nofree" | "hs_norc" | "hs_trace" | "hs_untyped"), _) -> true
    | _ -> false

(* The "const void *" type *)
let voidConstPtrType = TPtr(TVoid [Attr("const", [])], [])
let dummyVar = makeVarinfo false "foo" voidType

(* 'initRc' initialises the 'rcTypes' and 'rcFunctions' structures to
   contain the type and function definitions we need during reference
   count processing *)
type types = {
    mutable rc_adjust:typ; (* Type of 'rc_adjust...' functions *)
    mutable crc_adjust:typ;
    mutable type_t:typ;    (* 'type_t' type (pointer to rc_adjust function) *)
    mutable cType_t:typ;
  }
and functions = { (* Field <X> is the definition of __builtin_<X> *)
    mutable rctrace:varinfo;
    mutable rcadjust:varinfo;
    mutable crcadjust:varinfo;
    mutable rcpush:varinfo;
    mutable rcpop:varinfo;
    mutable ipush:varinfo;
    mutable ipop:varinfo;
    mutable cipush:varinfo;
    mutable cipop:varinfo;
    mutable cpush:varinfo;
    mutable cpop:varinfo;
    mutable argpush:varinfo;
    mutable argnull:varinfo;
    mutable retpush:varinfo;
    mutable retnull:varinfo;
    mutable rctypeof:varinfo;
    mutable rcclear:varinfo;
    mutable arrayclear:varinfo;
    mutable arraycopy:varinfo;
  }

let rcTypes : types = { rc_adjust = voidType; crc_adjust = voidType; 
                        type_t = voidType; cType_t = voidType; }
let rcFunctions : functions = 
  { rcpush = dummyVar; rcpop = dummyVar; ipush = dummyVar; ipop = dummyVar;
    cipush = dummyVar; cipop = dummyVar; cpush = dummyVar; cpop = dummyVar;
    argpush = dummyVar; argnull = dummyVar; retpush = dummyVar; retnull = dummyVar;
    rctypeof = dummyVar; rcclear = dummyVar; arrayclear = dummyVar;
    arraycopy = dummyVar; rcadjust = dummyVar; crcadjust = dummyVar;
    rctrace = dummyVar }

let nofreeFunctions : (string, bool) H.t = H.create 128

let loadNofreeFunctions (x:unit) = 
  try
    let nofreeFile = open_in (!Ivyoptions.home ^ "/lib/nofree") in
    while true do
      let nofreeName = input_line nofreeFile in
      if (S.get nofreeName 0) <> '#' then
	H.add nofreeFunctions nofreeName true
    done
  with
    Sys_error _ -> ()
  | End_of_file -> ()

let nofreeFunction (e:exp) : bool =
  isNofree (typeOf e) ||
  match e with
    Lval (Var x, NoOffset) when x.vglob && (H.mem nofreeFunctions x.vname) -> true
  | _ -> false


(* Setup 'rcTypes' and 'rcFunctions' for CIL file 'fi' *)
let initRc (fi:file) : unit =
  let rcAdjustArgs = [ "x", voidPtrType, []; 
		       "by", intType, [];
		       "size", !typeOfSizeOf, [] ] in
  let sprivate = Attr("sprivate",[]) in
  let pvoidType = TVoid([ sprivate ]) in
  let crcAdjustArgs = [ "x",TPtr(pvoidType, [ sprivate ]), [];
                        "by", TInt(IInt, [ sprivate ]), [];
                        "size", setTypeAttrs !typeOfSizeOf [ sprivate ], [];
                        "invalidate", TInt(IInt, [ sprivate ]), [] ] in
  rcTypes.rc_adjust <- TFun(voidType, Some rcAdjustArgs, false, nofreeAttr);
  rcTypes.crc_adjust <- TFun(pvoidType, Some crcAdjustArgs, false, nofreeAttr @ [ sprivate ]);
  rcTypes.type_t <- TPtr(rcTypes.rc_adjust, []);
  rcTypes.cType_t <- TPtr(rcTypes.crc_adjust, []);

  (* The meta rcadjust call, which takes the actual adjust function as argument
     (normally ends up as a macro in the final compilation) *)
  let adjustArgs = [ "adj", rcTypes.type_t, [];
		     "x", voidPtrType, []; 
		     "by", intType, [];
		     "size", !typeOfSizeOf, [] ] in
  let cAdjustArgs = [ "adj", rcTypes.cType_t, [];
                      "x", voidPtrType, [];
                      "by", intType, [];
                      "size", !typeOfSizeOf, [];
                      "invalidate", intType, [] ] in
  let adjustType = TFun(voidType, Some adjustArgs, false, nofreeAttr) in
  let cAdjustType = TFun(voidType, Some cAdjustArgs, false, nofreeAttr) in
  rcFunctions.rcadjust <- findOrCreateFunc fi "__builtin_hs_adjust" adjustType;
  rcFunctions.crcadjust <- findOrCreateFunc fi "__builtin_hs_cadjust" cAdjustType;

  let traceArgs = [] in
  let traceType = TFun(voidType, Some traceArgs, false, nofreeAttr) in
  rcFunctions.rctrace <- findOrCreateFunc fi "__builtin_hs_trace" traceType;

  let pushArgs = [ "x", voidConstPtrType, [] ] in
  let pushType = TFun(voidType, Some pushArgs, false, nofreeAttr) in
  rcFunctions.rcpush <- findOrCreateFunc fi "__builtin_hs_push" pushType;
  rcFunctions.rcpop <- findOrCreateFunc fi "__builtin_hs_pop" pushType;

  let iPushArgs = [ "x", voidConstPtrType, [];
		    "t", rcTypes.type_t, [];
		    "s", !typeOfSizeOf, [] ] in
  let iPushType = TFun(voidType, Some iPushArgs, false, nofreeAttr) in
  rcFunctions.ipush <- findOrCreateFunc fi "__builtin_hs_ipush" iPushType;
  rcFunctions.ipop <- findOrCreateFunc fi "__builtin_hs_ipop" iPushType;

  let cIPushArgs = [ "x", voidConstPtrType, [];
                     "t", rcTypes.cType_t, [];
                     "s", !typeOfSizeOf, [] ] in
  let cIPushType = TFun(voidType, Some cIPushArgs, false, nofreeAttr) in
  rcFunctions.cipush <- findOrCreateFunc fi "__builtin_hs_cipush" cIPushType;
  rcFunctions.cipop <- findOrCreateFunc fi "__builtin_hs_cipop" cIPushType;

  let cPushType = TFun(voidType, Some ["x", voidPtrType, []], false, nofreeAttr) in
  let cPopType = TFun(voidType, Some ["x", voidPtrType, []], false, nofreeAttr) in
  rcFunctions.cpush <- findOrCreateFunc fi "__builtin_hs_cpush" cPushType;
  rcFunctions.cpop <- findOrCreateFunc fi "__builtin_hs_cpop" cPopType;

  let argsPushType = TFun(voidType, Some ["x", voidPtrType, []], false, nofreeAttr) in
  let nullArgsType = TFun(voidType, Some [], false, nofreeAttr) in
  rcFunctions.argpush <- findOrCreateFunc fi "__builtin_hs_argpush" argsPushType;
  rcFunctions.argnull <- findOrCreateFunc fi "__builtin_hs_argnull" nullArgsType;
  rcFunctions.retpush <- findOrCreateFunc fi "__builtin_hs_retpush" argsPushType;
  rcFunctions.retnull <- findOrCreateFunc fi "__builtin_hs_retnull" nullArgsType;

  let clearTypeArgs = [ "x", voidConstPtrType, []] in
  let clearType = TFun(voidType, Some clearTypeArgs, false, nofreeAttr) in  
  rcFunctions.rcclear <- findOrCreateFunc fi "__builtin_hs_clear" clearType;
  
  let arrayClearArgs = [ "to", voidPtrType, [];
                               "n", intType, [];
                               "s", intType, [];
                               "type", rcTypes.type_t, [] ] in
  let arrayClearType = TFun(voidType, Some arrayClearArgs, false, nofreeAttr) in
  rcFunctions.arrayclear <- findOrCreateFunc fi "typed_sarrayclear" arrayClearType;
  
  let arrayCopyArgs = [ "to", voidPtrType, [];
                        "from", voidPtrType, [];
                        "n", intType, [];
                        "s", intType, [];
                        "type", rcTypes.type_t, []] in
  let arrayCopyType = TFun(voidType, Some arrayCopyArgs, false, nofreeAttr) in
  rcFunctions.arraycopy <- findOrCreateFunc fi "typed_sarraycopy" arrayCopyType;

  loadNofreeFunctions ()

let rc_functions = ["__builtin_hs_adjust";"__builtin_hs_cadjust";"__builtin_hs_trace";
                    "__builtin_hs_push";"__builtin_hs_pop";"__builtin_hs_ipush";
                    "__builtin_hs_ipop";"__builtin_hs_cipush";"__builtin_hs_cipop";
                    "__builtin_hs_cpush";"__builtin_hs_cpop";"__builtin_hs_argpush";
                    "__builtin_hs_argnull";"__builtin_hs_retpush";"__builtin_hs_retnull";
                    "__builtin_hs_clear";"typed_sarrayclear";"typed_sarraycopy";]

(* Generate a stmt for single instr 'i' *)
let i2s (i : instr) : stmt = mkStmt(Instr [i])

(* Generate an expression for variable 'v' *)
let v2e (v : varinfo) : exp = Lval(var v)

(* True if 't' is a type containing counted pointers (i.e., any pointer
   without the "norc" attribute *)
let rec typeContainsCountedPointers (t : typ) : bool =
  match t with
  | TPtr (t, a) -> not (hasNorcAttribute a)
  | TNamed (ti, _) -> typeContainsCountedPointers ti.ttype
  | TArray (ta, _, _) -> typeContainsCountedPointers ta
  | TComp (ci, _) ->
      let checkField fi = typeContainsCountedPointers fi.ftype in
      L.exists checkField ci.cfields
  | _ -> false

let rec list_last l = match l with
  | [] -> None
  | [x] -> Some x
  | x::xs -> list_last xs

let isZero (exp : exp) = match exp with
  | Const (CInt64 (i,_,_)) when i = Int64.zero -> true
  | _ -> false

let isOpenArraySize (opt_exp : exp option) = match opt_exp with
  | None -> true
  | Some (exp) -> isZero exp

let isOpenArrayField (opt_fld : fieldinfo option) = match opt_fld with
  | Some {ftype = TArray (_,sizeexp,_)} -> isOpenArraySize sizeexp
  | _ -> false

let isOpenStruct (t : typ) : bool = match t with
  | TComp(ci, _) -> ci.cstruct && isOpenArrayField (list_last ci.cfields)
  | _ -> false

(* True if 't' is a type containing a union containing counted pointers.
   Unions with a single field are not considered unions. *)
let rec typeContainsUnionWithCountedPointers (t : typ) : bool =
  match t with
  | TNamed (ti, _) -> typeContainsUnionWithCountedPointers ti.ttype
  | TArray (ta, _, _) -> typeContainsUnionWithCountedPointers ta
  | TComp (ci, _) ->
      if (not ci.cstruct) && (L.length ci.cfields > 1) then
	let checkField fi = typeContainsCountedPointers fi.ftype in
	L.exists checkField ci.cfields 
      else
	let checkField fi = typeContainsUnionWithCountedPointers fi.ftype in
	L.exists checkField ci.cfields
  | _ -> false

(* Apply 'fn' to 'g' if 'g' is a function definition *)
let onlyFunctions (fn : fundec -> location -> unit) (g : global) : unit = 
  match g with
  | GFun(f, loc) -> fn f loc
  | _ -> ()

(* Apply 'fn' to 'g' if 'g' is a non-function global *)
let onlyGlobVars (fn : varinfo -> initinfo -> location -> unit) (g : global) : unit = 
  match g with
  | GVar(v, init, loc) -> fn v init loc
  | _ -> ()


(* A regular expression that matches user-declared "rc_adjust..." functions *)
let adjustRegexp = R.regexp "^rc_adjust_"

(* True if 'f' is an "rc_adjust..." function definition *)
let isAdjustFunction (f : fundec) : bool = 
  R.string_match adjustRegexp f.svar.vname 0

(* Apply 'fn' to 'f' and 'loc' as long as 'f' is not an "rc_adjust..." 
   function *)
let skipAdjustFunctions (fn : fundec -> location -> unit) (f : fundec) (loc : location) : unit =
  if not (isAdjustFunction f) then
    fn f loc

let isRcFunction (fname : string) : bool =
    List.mem fname rc_functions ||
    R.string_match adjustRegexp fname 0

let isRcFnExp (fe : exp) : bool =
    match fe with
    | Lval(Var vi, NoOffset) when isRcFunction vi.vname -> true
    | _ -> false

let isRcInstr (i : instr) : bool =
    match i with
    | Call(_,fe,_,_) when isRcFnExp fe -> true
    | _ -> false
  
(* True if 't' is a pointer type *)
let isPointer (t : typ) = 
  match (unrollType t) with
  | TPtr(_, _) -> true
  | _ -> false

(* Declare 'vi' at the start of file 'fi' *)
let declareEarly (fi:file) (vi:varinfo) : unit =
  fi.globals <- GVarDecl(vi, locUnknown) :: fi.globals

(* A fixed, more useful version of the function from Cil *)
(** Find a function or function prototype with the given name in the file.
  * If it does not exist, create a prototype with the given type, and return
  * the new varinfo.  This is useful when you need to call a libc function
  * whose prototype may or may not already exist in the file.
  *
  * Because the new prototype is added to the start of the file, you shouldn't
  * refer to any struct or union types in the function type.
  * 
  * The result is a ('vi', 'b') where 'vi' represents the function's and
  * 'b' is true if the function wasn't previously declared or defined.
  *)
let findFunction (fi:file) (name:string) (t:typ) : varinfo * bool = 
  let checkType vi = 
    if not (isFunctionType vi.vtype) then 
      E.s (error ("findFunction: can't create %s because another "
                  ^^"global exists with that name.") name)
  in
  let rec search glist = 
    match glist with
    | GVarDecl(vi,_) :: rest when vi.vname = name -> 
	checkType vi;
        (vi, false)
    | GFun(f, _) :: rest when f.svar.vname = name -> 
	checkType f.svar;
	(f.svar, false)
    | _ :: rest -> search rest (* tail recursive *)
    | [] -> (*not found, so create one *)
        let t' = unrollTypeDeep t in
	let new_decl = makeGlobalVar name t' in
	declareEarly fi new_decl;
	(new_decl, true)
  in
  search fi.globals

let is_prefix prefix s = 
	prefix = String.sub s 0 (min (String.length prefix) (String.length s))

let treatAsRoot global = match global with
  | GVarDecl(v,_) when is_prefix "rc_adjust" v.vname -> true
  | GFun(f, _) when is_prefix "rc_adjust" f.svar.vname -> true 
  | _ -> Rmtmps.isDefaultRoot global  

