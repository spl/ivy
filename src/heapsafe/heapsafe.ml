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
module C = Cil

let init () : unit = 
  (* Declare our type-based attributes *)
  Hashtbl.add C.attributeHash "hs_trace" C.AttrType;
  Hashtbl.add C.attributeHash "hs_nofree" C.AttrType;
  Hashtbl.add C.attributeHash "hs_norc" C.AttrType;
  Hashtbl.add C.attributeHash "hs_untyped" C.AttrType;
  Rcinit.fixSizeT ()

let doPragmas global = match global with
  | C.GPragma (C.Attr ("hs_norc",_),_) -> Ivyoptions.noRc := true; false
  | _ -> true

let preprocess (cil: C.file) : unit =
  cil.C.globals <- List.filter doPragmas cil.C.globals

let root (f: C.file) : C.global -> bool = Rcutils.treatAsRoot

let process (cil: C.file) : C.file = 
  Rcutils.initRc cil;
  if not !Ivyoptions.noRc then begin
    if not !Ivyoptions.concRc then
        Rc.rcProcessFile cil 
    else
        Crc.cRcProcessFile cil
  end else 
    Rc.norcProcessFile cil;
  Rcinit.clearLocals cil;
  Rcopt.rcOptimize cil;
  Rc.postProcessFile cil;
  cil

let cleanup () : unit = 
  ()

