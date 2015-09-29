open Cil
open Ivyoptions

(* Module for taking deputized code and replacing verbose error information 
 * with FLIDs *)

(* Nathan Cooprider coop@cs.utah.edu *)


(* Things we've added to CIL not in there right now *)

let rec find_unsigned_bitsize ui acc =
  let rec pow a b =
    if b <= 0 then 1 else a * (pow a (b-1))
  in
  if (ui < (pow 2 acc)) then acc
  else find_unsigned_bitsize ui (acc+1)
      
let rec ui_to_hex_string i num = 
  if num <= 0 then
    "0x"
  else begin
    let mask = (1 lsl 4) - 1 in
    let digit = mask land i in
    let character = 
      match digit with
	0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 -> 
	  string_of_int digit 
      | 10 -> "A" | 11 -> "B" | 12 -> "C" | 13 -> "D" 
      | 14 -> "E" | 15 -> "F"
      | _ -> "X"
    in
    (ui_to_hex_string (i lsr 4) (num - 4)) ^ character 
  end
      
let isStringType tp =
  match tp with 
    TPtr(TInt(IChar, atts),_) when hasAttribute "const" atts -> true
  | _ -> false

(* End of things we've added to CIL but aren't in CIL *)
      

(* Still need to hexify things *)

let function_list = 
  [ 
    "deputy_fail_mayreturn" ;
    "deputy_fail_noreturn" ;
    "deputy_fail_noreturn_fast" ;
    "CNonNull" ;
    "CEq";
    "CMult";
    "CPtrArith";
    "CPtrArithNT" ;
    "CPtrArithAccess" ;
    "CLessInt" ;
    "CLeqInt" ;
    "CLeq" ;
    "CLeqNT" ;
    "CNullOrLeq" ;
    "CNullOrLeqNT" ;
    "CWriteNT" ;
    "CNullUnionOrSelected" ;
    "CSelected" ;
    "CNotSelected" 
  ]

let exists_in_function_list str = 
  List.exists 
    (fun name -> 
      try 
	if (name = str) || 
	(String.sub str 2 ((String.length str)-2) = name) then
	  true
	else 
	  false
      with Invalid_argument e -> 
	false 
    )
    function_list
    
(* Goes through file and: 
     - replaces strings in list with ""
     - replaces uses of the line location with the FLID
     - deals with casts *)
class fixingFormalsVisitor line str_list flid = object (self)
  inherit nopCilVisitor
      
  method vexpr e =
    match e with 
      Lval(Var v, NoOffset) when List.mem v str_list ->
	ChangeTo(mkString "")
    | Lval(Var v, NoOffset) when compare v line = 0 ->
	ChangeTo(Lval (Var flid, NoOffset))
    | CastE(tp,x) -> 
	ChangeDoChildrenPost(x, 
			     (fun y -> if (Expcompare.compareExp y x) then e 
			     else y))
    | _ ->   
	DoChildren

end

class parameterVisitor oc = object (self)
  inherit nopCilVisitor
      
  val mutable count = 33 (* Sanity check, some random number to start *)
  val mutable string_count = 0
  val mutable current_func = dummyFunDec 

(* The plain Deputy executable does not insert these *)
  method vvdec v = 
    if (v.vstorage = Extern) && (exists_in_function_list v.vname) then
      match v.vtype with
	TFun(tp,Some (args),b,atts) ->
	  let flid =  "__FLID_int", intType, [] in
	  let nolocationargs = List.tl (List.rev args) in
	  let rec strip_string_arguments args =
	    match args with 
	      (str,tp,atts) :: tl when isStringType tp ->
		strip_string_arguments tl
	    | _ -> args 
	  in
	  let deputy_args = strip_string_arguments nolocationargs in

	  let new_args = 
	    List.rev 
	      (flid :: deputy_args)
	  in
	  v.vtype <- TFun(tp,Some(new_args),b, atts);
	  SkipChildren
      | _ ->
	  SkipChildren
    else
      DoChildren
	
(* Not necessary if using our own checks.h file *)
  method vfunc f = 
    current_func <- f;
    if (exists_in_function_list f.svar.vname)  then
      match (List.rev f.sformals) with
	i1 :: nolocationargs -> 
	  let add_name, add_type =  "__FLID_int", intType  in
	  let flid = makeVarinfo false add_name add_type in
	  let rec strip_string_arguments args acc=
	    match args with 
	      v :: tl when isStringType v.vtype ->
		strip_string_arguments tl (v::acc)
	    | _ -> args, acc
	  in
	  let deputy_args, dep_list = 
	    strip_string_arguments nolocationargs [] 
	  in

	  f.sformals <- List.rev (flid :: deputy_args);

	  ignore (visitCilFunction 
		    (new fixingFormalsVisitor 
		        i1 dep_list flid) f); 
  	  DoChildren
      | _ -> DoChildren
    else
      DoChildren

  method vinst i = 
    match i with 
      Call (olv, Lval(Var(vi),NoOffset), exl, l) 
      when exists_in_function_list vi.vname ->
	let new_list = 
	  match (List.rev exl) with 
	  (** ****************************************************************)
	    i1 :: nolocationargs ->

	      if (exists_in_function_list current_func.svar.vname) then
		(* Not a starting point, so not a new FLID *)
		let rec strip_string_arguments args =
		  match args with 
		    e :: tl when isStringType (typeOf e) ->
		      strip_string_arguments tl
		  | _ -> args 
		in
		let deputy_args = strip_string_arguments nolocationargs in
		(* Just use existing int for FLID *)
		List.rev (i1 :: deputy_args)

	      (* *************************************************************)
	      else begin
		(* Starting point, need a new FLID *)

		ignore (Pretty.fprintf oc "0x%x ### %s ### " count vi.vname);
		let rec strip_string_arguments args =
		  match args with 
		    e :: tl when isStringType (typeOf e) ->
		      ignore (Pretty.fprintf oc "%a ### " d_exp e);
		      strip_string_arguments tl
		  | _ -> args 
		in
		let deputy_args = strip_string_arguments nolocationargs in
		
		ignore (Pretty.fprintf oc " %a ### %s \n" 
			  d_loc l current_func.svar.vname);
		
		let flid = 
		  let bitsize = find_unsigned_bitsize count 1 in
		  let hex_count = ui_to_hex_string count bitsize in
		  let mint = integer count in
		  match mint with 
		    Const (CInt64(sf,ik,so)) ->
		      Const(CInt64(sf,ik,Some(hex_count)))
		  | _ -> mint (* shouldn't happen *)
		in
		count <- count + 20 + (Random.int 20); 
		List.rev (flid :: deputy_args)
	      end 
	 
	  (** ****************************************************************)
	  | _ -> exl

	in
	ChangeTo [Call (olv,Lval(Var(vi),NoOffset),new_list,l)]
    | _ -> SkipChildren
end

let insert_flids f = 
  Random.init 42;
  let oc = open_out (!insertFLIDs) in
  visitCilFileSameGlobals (new parameterVisitor oc) f;
  close_out oc
    
