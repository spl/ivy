(*
 *
 * Copyright (c) 2004, 
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

(*
 *
 * dcheckstrengthen.ml
 *
 * This module looks at groups of checks and replaces them
 * with a smaller number of equivalent checks.
 *
 *)

open Cil
open Expcompare
open Pretty
open Dutil
open Dcheckdef
open Doptimutil

module E = Errormsg
module DCE = Dcanonexp

(******************
 *
 * Replace:
 * CPtrArith(e1,e2,e3,e4,s);
 * CLeq(e3+e4+1,e2);
 *
 * With:
 * CPtrArithAccess(e1,e2,e3,e4,s);
 *
 * Replace:
 * CNullOrLeq(e1,e2,e3)
 * CNonNull(e1)
 *
 * With:
 * CLeq(e2,e3)
 * CNonNull(e1)
 *
 ******************)
class checkStrengthenClass = object(self)
    inherit nopCilVisitor

  method private increaseStrength c1 c2 =
    match c1, c2 with
    | CPtrArith(e1,e2,e3,e4,e5), CLeq(e6,e7,_) -> begin
        match deputyStripCastsForPtrArith e6 with
        | BinOp((PlusA|PlusPI|IndexPI),
          BinOp((PlusA|PlusPI|IndexPI),e3',e4',_),ce,t) ->
            if (DCE.canonCompareExp e3 e3' &&
                DCE.canonCompareExp e4 e4' &&
                DCE.canonCompareExp e2 e7 ||
                DCE.canonCompareExp e4 e3' &&
                DCE.canonCompareExp e3 e4' &&
                DCE.canonCompareExp e2 e7) &&
                DCE.canonCompareExp ce one
            then
                [CPtrArithAccess(e1,e2,e3,e4,e5)]
            else 
                [c1;c2]
        | _ -> [c1;c2]
    end
    | CNullOrLeq(e1,e2,e3,r), CNonNull e4 ->
        if DCE.canonCompareExp e1 e4 then
            [c2;CLeq(e2,e3,r)]
        else [c1;c2]
    | _, _-> [c1;c2]

  method private processInstrs il =
    let rec helper il seen = match il with
    | [] -> List.rev seen
    | [x] -> List.rev (x::seen)
    | i1::i2::rest -> begin
	match instrToCheck i1, instrToCheck i2 with
	| Some c1, Some c2 -> begin
            (* Set location so that it is properly recorded by checkToInstr. *)
            currentLoc := get_instrLoc i1;
	    let cl = self#increaseStrength c1 c2 in
	    if cl = [] then helper rest seen else
	    let cl = List.map checkToInstr cl in
	    let c1 = List.hd cl in
	    helper ((List.tl cl)@rest) (c1::seen)
	end
	| _, _ -> helper (i2::rest) (i1::seen)
    end
    in
    helper il []

  method private procStmt s =
    match s.skind with
    | Instr il -> begin
	s.skind <- Instr(self#processInstrs il);
	s
    end
    | _ -> s

  method private processStmts sl =
    let rec helper sl seen = match sl with
    | [] -> List.rev seen
    | [x] -> List.rev ((self#procStmt x)::seen)
    | s1::s2::rest -> begin
	match s1.skind, s2.skind with
	| Instr il1, Instr il2 when s1.labels = [] && s2.labels = [] -> begin
	    s1.skind <- Instr(il1 @ il2);
	    helper (s1 :: rest) seen
	end
	| Instr il1, Instr il2 when il1 <> [] && il2 <> [] -> begin
	    (* get the last form il1 and the first from il2 *)
	    let i1 = List.hd (List.rev il1) in
	    let il1' = List.tl (List.rev il1) in
	    let i2 = List.hd il2 in
	    let il2' = List.tl il2 in
	    match self#processInstrs [i1;i2] with
	    | [] -> E.s "CheckStrengthen: processInstrs returned empty\n"
	    | [i] -> begin
		s1.skind <- Instr(List.rev(i::il1'));
		s2.skind <- Instr il2';
		helper (s2::rest) ((self#procStmt s1)::seen)
	    end
	    | [i1;i2] -> begin
		s1.skind <- Instr(List.rev(i1::il1'));
		s2.skind <- Instr(i2::il2');
		helper (s2::rest) ((self#procStmt s1)::seen)
	    end
	    | _ -> E.s "CheckStrengthen: processInstrs returned more than one\n"
	end
	| _, _ -> helper (s2::rest) ((self#procStmt s1)::seen)
    end
    in
    helper sl []

  method vblock b =
    b.bstmts <- self#processStmts b.bstmts;
    DoChildren

end

let checkStrengthener = new checkStrengthenClass
