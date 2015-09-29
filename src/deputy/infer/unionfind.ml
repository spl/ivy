(*
 *
 * Copyright (c) 2001-2006, 
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

(*
 * Union-Find Functor (no side effects, purely applicative)
 *
 * (used by physical type equality to keep equivalence classes of types)
 *) 
module N = Ptrnode
module E = Errormsg

module type UF = 
  sig
    type t

    type elt 

    val empty : t

    val check_equal : t -> elt -> elt -> bool 

        (* The chain is directed elt1 -> elt2 *)
    val make_equal : t -> elt -> elt -> N.chain -> t

    val eq_classes : t -> elt list list

    val class_of : t -> elt -> elt list

    (* Returns the chain why two elements are equal. Raises Failure if they 
     * are not actually equal *)
    val why_equal : t -> elt -> elt -> N.chain
  end


module Make(S : Set.S) =
  struct
    (* An equivalence class supports membership queries and can also explain 
     * why two elements are equal *)
    type aclass = 
        { set: S.t; (* For the membership query *)
          why: whyset }
    and whyset = 
        WSSingle of S.elt (* A singleton *)
      (* Was formed by unioning aclass1 (containing elt1) and aclass2 
       * (containing elt2) with the given chain for elt1->elt2 *) 
      | WSUnion of aclass * S.elt * N.chain * S.elt * aclass 

    type t = aclass list

    type elt = S.elt 

    let empty = []

    let check_equal uf e1 e2 =
      List.fold_left 
        (fun acc cls -> acc || (S.mem e1 cls.set && S.mem e2 cls.set)) false uf

    exception AlreadyEqual
    let make_equal (clss : aclass list) e1 e2 chain (* chain : e1->e2 *) =
      (* Find the classes of e1 and e2 *)
      let c1 : aclass ref = ref { set = S.singleton e1; why = WSSingle e1}  in
      let c2 : aclass ref = ref { set = S.singleton e2; why = WSSingle e2} in
      (* Collect a list of the classes that do not contain e1 or e2 *)
      try
        let uninvolved : aclass list ref = ref [] in
        List.iter (fun (cls : aclass) ->
          if S.mem e1 cls.set then begin
            if S.mem e2 cls.set then
              raise AlreadyEqual
            else 
              c1 := cls
          end else if S.mem e2 cls.set then
            c2 := cls
          else 
            uninvolved := cls :: !uninvolved) 
          clss ;
        let merged_set = 
          { set = S.union !c1.set !c2.set; 
            why = WSUnion (!c1, e1, chain, e2, !c2); }
        in
        let final_list_of_sets = merged_set :: !uninvolved in
        (final_list_of_sets : aclass list)
      with AlreadyEqual -> 
        clss

    let eq_classes clss = 
      List.map (fun eqclass -> S.elements eqclass.set) clss

    let class_of clss elt =
      let rec search = function
          [] -> []
        | cls :: tl -> 
            if S.mem elt cls.set then S.elements cls.set else search tl 
      in 
      search clss

    let why_equal (clss: aclass list) (e1: elt) (e2: elt) : N.chain = 
      (* Find the class of e1 *)
      let cls = 
        try List.find (fun cls -> S.mem e1 cls.set) clss 
        with _ -> E.s (E.bug "why_equal: element not known") in
      (* Check that e2 is in the same class *)
      if not (S.mem e2 cls.set) then 
        E.s (E.bug "why_equal: not actually equal");
      (* Now traverse the history of unions in reverse order. The invariant 
       * is that both e1 and e2 are in the set. *)
      let rec whyLoop (e1: elt) (e2: elt) (why: whyset) = 
        (* Maybe they are equal *)
        if compare e1 e2 = 0 then N.mkRIdent else
        match why with 
          WSSingle _ -> E.s (E.bug "why_equal: equal elements")
        | WSUnion (c1, e1', r', e2', c2) -> 
            if S.mem e1 c1.set then 
              if S.mem e2 c1.set then 
                (* Both e1 and e2 belong to c1 *)
                whyLoop e1 e2 c1.why
              else
                (* e1 in c1 and e2 in c2 *)
                N.mkRTrans (whyLoop e1 e1' c1.why)
                  (N.mkRTrans r'
                     (whyLoop e2' e2 c2.why))
            else (* e1 in c2 *)
              if S.mem e2 c2.set then 
                (* Both e1 and e2 in the c2 *)
                whyLoop e1 e2 c2.why
              else
                (* e1 in c2 and e2 in c1 *)
                N.mkRTrans (whyLoop e1 e2' c2.why)
                  (N.mkRTrans (N.mkRSym r')
                     (whyLoop e1' e2 c1.why))
      in
      whyLoop e1 e2 cls.why

  end


    
  
