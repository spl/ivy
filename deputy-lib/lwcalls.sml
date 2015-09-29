(*
 * This is an SML backend for Deputy instrumentation
 *
 * lwcalls.sml
 *
 *
 *
 *)

structure IHT = IntHashTable
structure HT = HashTable


(* Interval Map for storing taint data *)
fun interval_compare (lo1,hi1,_) (lo2,hi2,_) =
	if Word.<(hi1,lo2) then LESS else
	if Word.<(hi2,lo1) then GREATER else
	EQUAL

structure IntervalMap = RedBlackMapFn (
	struct
		type ord_key = word * word
		fun compare((lo1,hi1),(lo2,hi2)) =
			interval_compare (lo1,hi1,0wx0) (lo2,hi2,0wx0)
	end)

structure LocationSet = RedBlackSetFn (
	struct
		type ord_key = word * word
		fun compare((f1:word,l1:word),(f2:word,l2:word)) =
			if f1 < f2 orelse (f1 = f2 andalso l1 < l2) then LESS else
			if f2 < f1 orelse (f1 = f2 andalso l2 < l2) then GREATER else
			EQUAL
	end)

(* Expression tree data structures *)
datatype uop =
	  Neg
	| BNot
	| LNot
	| UKUop

datatype bop =
	  PlusA
	| PlusPI
	| IndexPI
	| MinusA
	| MinusPI
	| MinusPP
	| Mult
	| Div
	| Mod
	| ShiftL
	| ShiftR
	| Lt
	| Gt
	| Le
	| Ge
	| Eq
	| Ne
	| BAnd
	| BXor
	| BOr
	| LAnd
	| LOr
	| UKBop


fun bopToWord (b : bop) : word = case b of
	  PlusA => Word.fromInt 0
	| PlusPI => Word.fromInt 1
	| IndexPI => Word.fromInt 2
	| MinusA => Word.fromInt 3
	| MinusPI => Word.fromInt 4
	| MinusPP => Word.fromInt 5
	| Mult => Word.fromInt 6
	| Div => Word.fromInt 7
	| Mod => Word.fromInt 8
	| ShiftL => Word.fromInt 9
	| ShiftR => Word.fromInt 10
	| Lt => Word.fromInt 11
	| Gt => Word.fromInt 12
	| Le => Word.fromInt 13
	| Ge => Word.fromInt 14
	| Eq => Word.fromInt 15
	| Ne => Word.fromInt 16
	| BAnd => Word.fromInt 17
	| BXor => Word.fromInt 18
	| BOr => Word.fromInt 19
	| LAnd => Word.fromInt 20
	| LOr => Word.fromInt 21
	| UKBop => Word.fromInt 37

fun bop_eq (b1 : bop) (b2 : bop) : bool =
	(bopToWord b1) = (bopToWord b2)

fun bopToString (b : bop) : string = case b of
	  PlusA => "+"
	| PlusPI => "+"
	| IndexPI => "+"
	| MinusA => "-"
	| MinusPI => "-"
	| MinusPP => "-"
	| Mult => "*"
	| Div => "/"
	| Mod => "%"
	| ShiftL => "<<"
	| ShiftR => ">>"
	| Lt => "<"
	| Gt => ">"
	| Le => "<="
	| Ge => ">="
	| Eq => "=="
	| Ne => "!="
	| BAnd => "&"
	| BXor => "^"
	| BOr => "|"
	| LAnd => "&&"
	| LOr => "||"
	| UKBop => "??"

fun print_bop (b : bop) : unit =
	print(bopToString b)

fun negate_bop (b : bop) : bop = case b of
	  Lt => Ge
	| Gt => Le
	| Le => Gt
	| Ge => Lt
	| Eq => Ne
	| Ne => Eq
	| _ => b

fun wordToUop (w : word) : uop = case (Word.toInt w) of
	  0 => Neg
	| 1 => BNot
	| 2 => LNot
	| _ => UKUop

fun uopToWord (u : uop) : word = case u of
	  Neg => Word.fromInt 0
	| BNot => Word.fromInt 1
	| LNot => Word.fromInt 2
	| UKUop => Word.fromInt 37

fun uop_eq (u1 : uop) (u2 : uop) : bool =
	(uopToWord u1) = (uopToWord u2)

fun uopToString (u : uop) : string = case u of
	  Neg => "-"
	| BNot => "~"
	| LNot => "!"
	| UKUop => "??"

fun print_uop (u : uop) : unit =
	print(uopToString u)

type constdata = {
	value : word, (* The bits *)
	typ : word,   (* The type *)
	sz : word     (* The size *)
}

fun const_eq (c1 : constdata) (c2 : constdata) : bool =
	(#value c1) = (#value c2) andalso
	(#typ c1) = (#typ c2) andalso
	(#sz c1) = (#sz c2)

type inputdata = {
	addr : word,     (* The original address in memory *)
	fnres : word,    (* Function result address if needed *)
	fnaddr : word,   (* The function if needed *)
	uid : word,      (* unique ids to distinguish logically different inputs *)
	cval : word,     (* The concrete value *)
	typ : word,      (* The type *)
	sz : word,       (* The size *)
	file : word,     (* source file location *)
	line : word      (* source line number *)
}

fun input_eq((i1 : inputdata),(i2 : inputdata)) : bool =
	(#addr i1) = (#addr i2) andalso
	(#fnres i1) = (#fnres i2) andalso
	(#fnaddr i1) = (#fnaddr i2) andalso
	(#uid i1) = (#uid i2) andalso
	(#cval i1) = (#cval i2) andalso
	(#typ i1) = (#typ i2) andalso
	(#sz i1) = (#sz i2)

fun input_hash (id : inputdata) : word =
	Word.xorb((#addr id),
	Word.xorb((#fnres id),
	Word.xorb((#fnaddr id),(#uid id))))

fun print_input (id : inputdata) : unit =
	print("Input("^(Word.toString (#addr id))^","
	              ^(Word.toString (#cval id))^")")

(* Datatype for symbolic expressions *)
datatype exp =
	  BinOp of bop * exp * exp
	| UnOp  of uop * exp
	| Const of constdata
	| Input of inputdata

type int64 = Int64.int

type canonexp = {
	ct : int64,
	cf : (int64 * exp) list
}

fun mkConst(v,t,s) = Const{value=v,typ=t,sz=s}
fun mkInput(a,fr,fa,u,v,t,s,fl,ln) =
	let
		val id = {addr=a,fnres=fr,fnaddr=fa,uid=u,cval=v,typ=t,sz=s,file=fl,line=ln}
	in
		(*print_input id;*)
		Input id
	end

fun print_exp (e : exp) : unit = case e of
  BinOp(bop,e1,e2) =>
	(print("BinOp("^(bopToString bop)^",");
	 print_exp e1;print ",";print_exp e2;print ")")
| UnOp(uop,e) =>
	(print("UnOp("^(uopToString uop)^",");
	 print_exp e; print ")")
| Const c => (print(Word.toString (#value c)))
| Input id => print_input id


fun print_canexp (c : canonexp) : unit =
	let
		fun ppair((f,e),()) =
			(print("+"^(Int64.toString f)^"*");
			print_exp e)
	in
		print(Int64.toString (#ct c));
		foldl ppair () (#cf c)
	end

fun exp_eq (e1 : exp) (e2 : exp) : bool =
	case (e1,e2) of
	  (BinOp(b1,e11,e12),BinOp(b2,e21,e22)) =>
		(bop_eq b1 b2) andalso (exp_eq e11 e21) andalso (exp_eq e12 e22)
	| (UnOp(u1,e1),UnOp(u2,e2)) =>
		(uop_eq u1 u2) andalso (exp_eq e1 e2)
	| (Const cd1, Const cd2) => const_eq cd1 cd2
	| (Input id1, Input id2) => input_eq(id1,id2)
	| _ => false

fun wordToBop (w : word) : bop = case (Word.toInt w) of
	  0 => PlusA
	| 1 => PlusPI
	| 2 => IndexPI
	| 3 => MinusA
	| 4 => MinusPI
	| 5 => MinusPP
	| 6 => Mult
	| 7 => Div
	| 8 => Mod
	| 9 => ShiftL
	| 10 => ShiftR
	| 11 => Lt
	| 12 => Gt
	| 13 => Le
	| 14 => Ge
	| 15 => Eq
	| 16 => Ne
	| 17 => BAnd
	| 18 => BXor
	| 19 => BOr
	| 20 => LAnd
	| 21 => LOr
	| _ => UKBop

fun wordToUop (w : word) : uop = case (Word.toInt w) of
	  0 => Neg
	| 1 => BNot
	| 2 => LNot
	| _ => UKUop


fun mkCanInt (f : int64) : canonexp = {ct = f, cf = []}
fun mkCanAtomic (f : int64) (e : exp) : canonexp =
	if f = 0 then {ct = 0, cf = []}
	else {ct = 0, cf = [(f,e)]}
val mkCanZero = mkCanInt 0
fun mkCanWAdd (w1 : int64) (c1 : canonexp) (cacc : canonexp) : canonexp =
	let
		fun insert (w : int64) (e : exp) (fel : (int64 * exp) list) =
			case fel of
			  [] => if w = 0 then [] else [(w,e)]
			| (w',e') :: rst =>
				if exp_eq e e' then
					if w + w' = 0 then
						rst
					else (w + w',e') :: rst
				else (w',e') :: (insert w e rst)
		fun folder((w,e),acc) = insert (w1*w) e acc
	in
		{ct = w1 * (#ct c1) + (#ct cacc),
		 cf = foldl folder (#cf cacc) (#cf c1)}
	end
fun mkCanAdd (c1 : canonexp) (c2 : canonexp) : canonexp =
	mkCanWAdd 1 c1 c2
fun mkCanSub (c1 : canonexp) (c2 : canonexp) : canonexp =
	mkCanWAdd (~1) c2 c1
fun mkCanMult (c : canonexp) (n : int64) : canonexp =
	mkCanWAdd n c mkCanZero
fun mkCanAddConst (c : canonexp) (n : int64) : canonexp =
	{ct = n + (#ct c), cf = (#cf c)}


fun max x y = if x > y then x else y

fun typeOfExp (e : exp) : word * word = case e of
	  Const c => ((#typ c),(#sz c))
	| Input i => ((#typ i),(#sz i))
	| UnOp(_,e) => typeOfExp e
	| BinOp(_,e1,e2) =>
		let
			val (t1,sz1) = typeOfExp e1
			val (t2,sz2) = typeOfExp e2
		in
			case (t1,t2) of
			  (0wx0,0wx0) => (0wx0,max sz1 sz2)
			| (0wx1,0wx0) => (0wx1,sz1)
			| (0wx0,0wx1) => (0wx1,sz2)
			| (0wx1,0wx1) => (0wx1,0wx1)
			| _ => (0wx1,0wx1)
		end

fun wordToInt64 (w : word) (signed : bool) : int64 =
	(if signed
	then (Int64.fromLarge o Word.toLargeIntX) w
	else (Int64.fromLarge o Word.toLargeInt) w)
		handle Overflow =>
			(print("wordToInt64: Overflow: "^(Word.toString w)^"\n");
			 raise Overflow)

fun int64ToInt (i : int64) : int =
	((Int.fromLarge o Int64.toLarge) i)
	handle Overflow =>
		(print "Overflow in conversion from int64 to int\n";
		 raise Overflow)

fun canonExp (f : int64) (e : exp) : canonexp =
	(case e of
	  Const c => mkCanInt (f * (wordToInt64 (#value c) (Word.toIntX (#sz c) < 0)))
	| BinOp(PlusA,e1,e2) =>
		mkCanAdd (canonExp f e1) (canonExp f e2)
	| BinOp(PlusPI,e1,e2) =>
		let
			val (t1,sz1) = typeOfExp e1
			val (t2,sz2) = typeOfExp e2
		in
			case (t1,t2) of
			  (0wx0,0wx0) =>
			  	mkCanAdd (canonExp f e1) (canonExp f e2)
			| (0wx1,0wx0) =>
				mkCanAdd (canonExp f e1) (canonExp (f*(wordToInt64 sz1 false)) e2)
			| (0wx0,0wx1) =>
				mkCanAdd (canonExp (f*(wordToInt64 sz2 false)) e1) (canonExp f e2)
			| (0wx1,0wx1) =>
				mkCanAdd (canonExp f e1) (canonExp f e2)
			| _ =>
				mkCanAdd (canonExp f e1) (canonExp f e2)
		end
	| BinOp(IndexPI,e1,e2) =>
		let
			val (t1,sz1) = typeOfExp e1
			val (t2,sz2) = typeOfExp e2
		in
			case (t1,t2) of
			  (0wx0,0wx0) =>
			  	mkCanAdd (canonExp f e1) (canonExp f e2)
			| (0wx1,0wx0) =>
				mkCanAdd (canonExp f e1) (canonExp (f*(wordToInt64 sz1 false)) e2)
			| (0wx0,0wx1) =>
				mkCanAdd (canonExp (f*(wordToInt64 sz2 false)) e1) (canonExp f e2)
			| (0wx1,0wx1) =>
				mkCanAdd (canonExp f e1) (canonExp f e2)
			| _ =>
				mkCanAdd (canonExp f e1) (canonExp f e2)
		end
	| BinOp(MinusA,e1,e2) =>
		mkCanAdd (canonExp f e1) (canonExp (~f) e2)
	| BinOp(MinusPI,e1,e2) =>
		let
			val (t1,sz1) = typeOfExp e1
			val (t2,sz2) = typeOfExp e2
		in
			case (t1,t2) of
			  (0wx0,0wx0) =>
			  	mkCanAdd (canonExp f e1) (canonExp (~f) e2)
			| (0wx1,0wx0) =>
				mkCanAdd (canonExp f e1) (canonExp (~f*(wordToInt64 sz1 false)) e2)
			| (0wx0,0wx1) =>
				mkCanAdd (canonExp (f*(wordToInt64 sz2 false)) e1) (canonExp (~f) e2)
			| (0wx1,0wx1) =>
				mkCanAdd (canonExp f e1) (canonExp (~f) e2)
			| _ =>
				mkCanAdd (canonExp f e1) (canonExp (~f) e2)
		end
	| BinOp(MinusPP,e1,e2) =>
		mkCanAdd (canonExp f e1) (canonExp (~f) e2)
	| BinOp(Mult,e1,Const c) =>
		mkCanAtomic (f * (wordToInt64 (#value c) (Word.toIntX (#sz c) < 0))) e1
	| BinOp(Mult,Const c, e2) =>
		mkCanAtomic (f * (wordToInt64 (#value c) (Word.toIntX (#sz c) < 0))) e2
	| _ => mkCanAtomic f e)
		handle Overflow =>
			(print "canonExp: Overflow\n"; raise Overflow)

exception Not_found

fun incr (i : int ref) : unit = i := (!i) + 1
fun decr (i : int ref) : unit = i := (!i) - 1

fun fst (a,b) = a

type taintdata = {
	uid : word,
	file : word,
	line : word
}

fun mkTaint (uid : word) (file : word) (line : word) : taintdata =
	{uid=uid,file=file,line=line}

(* Functions for manipulating the taint map *)
val taintMap  : taintdata IntervalMap.map ref = ref IntervalMap.empty

fun taintSetRm (s : word) (e : word) : unit =
	(taintMap := fst(IntervalMap.remove(!taintMap,(s,e))))
	handle NotFound => ()

fun taintSetAdd (s : word) (esz : word) (ecnt : word)
                (file : word) (line : word)
                : unit
	=
	let
		val e = s + esz * ecnt
	in
		case IntervalMap.find(!taintMap,(s,e)) of
		  NONE =>
			let val td = mkTaint 0wx0 file line in
		  	taintMap := IntervalMap.insert(!taintMap,(s,e),td)
		  	end
		| SOME td =>
			let val td = mkTaint ((#uid td)+0wx1) file line in
			taintMap := IntervalMap.insert(!taintMap,(s,e),td)
			end
	end

fun taintSetFind (s : word) (e : word) : (word * word * taintdata) option =
	case IntervalMap.find(!taintMap,(s,e)) of
	  NONE => NONE
	| SOME td => SOME(s,e,td)


(* Functions for manipulating the symbolic state *)
val symStateShift = Word.fromInt 18
val symStateSize = Word.<<((Word.fromInt 1), symStateShift)
val symStateMask = symStateSize - (Word.fromInt 1)
(* Global hash table for symbolic state *)
(*WHash.mkTable(131072,Not_found)*)
val symState : exp option array = Array.array(Word.toInt symStateSize,NONE)
val c_int32_hash = _import "c_int32_hash": word * word -> int;
fun symStateHash (w : word) : int =
	(*c_int32_hash(w,symStateMask)*)
	Word.toInt (Word.andb(w, symStateMask))
val collisions : int ref = ref 0
fun symStateAdd (sop : word) (e : exp) : unit =
	((*print("Adding: "^(Word.toString sop)^" -> ");
	 print_exp e; print "\n";*)
	(case Array.sub(symState,symStateHash sop) of
	  NONE => Array.update(symState, (symStateHash sop), (SOME e))
	| SOME _ => (Array.update(symState, (symStateHash sop), (SOME e)))))
fun symStateLookup (sop : word) : exp option =
	Array.sub(symState, (symStateHash sop))
fun symStateRm (sop : word) : unit =
	Array.update(symState, (symStateHash sop), NONE)

(* Stuff for maintaining a mapping from inputs to sets of locations where those
   inputs are checked *)

val c_print_loc = _import "c_print_loc":
	word * word -> unit;

val inpChecks : LocationSet.set IHT.hash_table =
	IHT.mkTable (100, Not_found)

fun addInpCheck (vid : int) (file,line) : unit =
	case IHT.find inpChecks vid of
	  NONE =>
	  	IHT.insert inpChecks (vid,LocationSet.singleton(file,line))
	| SOME s =>
		IHT.insert inpChecks (vid,LocationSet.add(s,(file,line)))

fun getInpChecks (vid : int) : LocationSet.set =
	case IHT.find inpChecks vid of
	  NONE => LocationSet.empty
	| SOME s => s

fun printInpChecks (vid : int) : unit =
	let
		val set = getInpChecks vid
		fun printer((file,line),()) =
			c_print_loc(file,line)
	in
		if LocationSet.isEmpty set then
			print "No Checks"
		else
			LocationSet.foldl printer () set
	end

(* Octagon stuff *)

type oct_t = word

val c_oct_init = _import "c_oct_init":
	unit -> int;
val c_oct_add_constraint = _import "c_oct_add_constraint":
	oct_t * int array * int -> oct_t;
val c_oct_add_dimension = _import "c_oct_add_dimension":
	oct_t * word -> oct_t;
val c_oct_empty = _import "c_oct_empty":
	word -> oct_t;
val c_oct_universe = _import "c_oct_universe":
	word -> oct_t;
val c_oct_copy = _import "c_oct_copy":
	oct_t -> oct_t;
val c_oct_print = _import "c_oct_print":
	oct_t -> unit;
val c_oct_free = _import "c_oct_free":
	oct_t -> unit;
val c_oct_dimension = _import "c_oct_dimension":
	oct_t -> int;
val c_oct_is_empty = _import "c_oct_is_empty":
	oct_t -> bool;
val c_oct_is_universe = _import "c_oct_is_universe":
	oct_t -> bool;
val c_oct_is_included_in = _import "c_oct_is_included_in":
	oct_t * oct_t -> bool;
val c_oct_is_equal = _import "c_oct_is_equal":
	oct_t * oct_t -> bool;
val c_oct_get_box = _import "c_oct_get_box":
	oct_t * int array * int array -> unit;

type octagon = {
	oct : oct_t ref,
	maxvars : int ref,
	numvars : int ref
}

fun mkOct () : octagon =
	{oct = ref (c_oct_universe 0wx5), maxvars = ref 5, numvars = ref 0}
fun copyOct (oct : octagon) : octagon =
	{oct = ref (c_oct_copy (!(#oct oct))),
	 maxvars = ref (!(#maxvars oct)),
	 numvars = ref (!(#numvars oct))}
fun printOct (oct : octagon) : unit =
	c_oct_print (!(#oct oct))


val cOctagon : octagon = (ignore(c_oct_init()); mkOct())

val inpOVarHash : (inputdata,int) HT.hash_table = 
	HT.mkTable (input_hash,input_eq) (100,Not_found)
val oVarInpHash : inputdata IHT.hash_table =
	IHT.mkTable (100,Not_found)

fun addOctConstraint (oct : octagon) (cl : int array) : unit =
	(#oct oct) := c_oct_add_constraint(!(#oct oct),cl,Array.length cl);
fun addOctVar (oct : octagon) (id : inputdata) : int =
	(if !(#numvars oct) = !(#maxvars oct) then
		((#oct oct) := c_oct_add_dimension(!(#oct oct),0wx5);
		(#maxvars oct) := !(#maxvars oct) + 5)
	 else ();
	 HT.insert inpOVarHash (id, !(#numvars oct));
	 IHT.insert oVarInpHash (!(#numvars oct),id);
	 !(#numvars oct) before (incr (#numvars oct)))
fun getOctVar (oct : octagon) (id : inputdata) : int =
	 case HT.find inpOVarHash id of
	   NONE => addOctVar oct id
	 | SOME i => i

(* Convert a canonexp into a list of coefficients and octVar IDs.
   If the expression doesn't have the right form, return NONE *)
exception BadConExp
fun getCoefIdList (oct : octagon) (c : canonexp) : (int64 * int) list option =
	let
		fun handleTerm (f,e) : (int64 * int) = case e of
		  Input id => (f, getOctVar oct id)
		| _ => raise BadConExp
	in
		((*print "trying to add: ";
		 print_canexp c; print "\n";*)
		 SOME(map handleTerm (#cf c))(* before
		 print "constraint added\n"*)
		) handle BadConExp => NONE
	end

fun maxVID ipl m = case ipl of
  [] => m
| (f,id) :: rst =>
	if id > m then maxVID rst id else maxVID rst m

(* Adds the constraint c >= 0 to the octagon *)
fun addCEToOct (oct : octagon) (c : canonexp)
               (file : word) (line : word)
               : unit
	=
	case getCoefIdList oct c of
	  NONE => ()
	| SOME ipl =>
		let
			val dim = c_oct_dimension (!(#oct oct))
			val coefs = Array.array ((dim + 1),0)
			fun adder ((f, id),()) : unit =
				(Array.update (coefs,id,int64ToInt f);
				 if file <> 0wx0 then addInpCheck id (file,line) else ())
		in
			(foldl adder () ipl;
			Array.update (coefs,dim,int64ToInt (#ct c));
			addOctConstraint oct coefs)
			handle Overflow => ()
			| Subscript => ()
		end

fun addBopToOct (oct : octagon) (b : bop) (e1 : exp) (e2 : exp)
                (file : word) (line : word)
                : unit
	=
	let
		val e1 = canonExp 1 e1
		val e2 = canonExp 1 e2
		val one = mkCanInt 1
	in
		case b of
		  Lt => addCEToOct oct (mkCanSub e2 (mkCanAdd e1 one)) file line
		| Gt => addCEToOct oct (mkCanSub e1 (mkCanAdd e2 one)) file line
		| Le => addCEToOct oct (mkCanSub e2 e1) file line
		| Ge => addCEToOct oct (mkCanSub e1 e2) file line
		| _ => ()
	end

(* structures for dealing with call/return semantics *)
val call_depth = ref 0
val arg_stack : (word * word * word * word) array =
	Array.array(20,(0wx0,0wx0,0wx0,0wx0))
val arg_stack_top = ref 0
val ret_val : exp option ref = ref NONE

fun arg_stack_push wt =
	(Array.update(arg_stack, !arg_stack_top, wt);
	 incr arg_stack_top)

fun arg_stack_pop () =
	(decr arg_stack_top;
	 if !arg_stack_top < 0 then
	 	(arg_stack_top := 0; NONE)
	 else let val res = Array.sub(arg_stack,!arg_stack_top) in
		SOME res
	 end)

(* Functions for handling two-dimensional C arrays *)
type cArray = {
	arr : MLton.Pointer.t,
	cols : int,
	rows : int
}

fun cArray2Sub (iaa : cArray) (m : int) (n : int) : Word32.word =
	let val rowstart = m*(#cols iaa) in
		MLton.Pointer.getWord32 (#arr iaa, rowstart + n)
	end

(* This is used for pattern matching all the different Pluses and Minuses.
   Ocaml is much better in this regard *)
datatype stupidBop = Plus | Minus | Normal of bop

fun bopToSBop bop = case bop of
  PlusA => Plus
| PlusPI => Plus
| IndexPI => Plus
| MinusA => Minus
| MinusPI => Minus
| MinusPP => Minus
| _ => Normal bop

datatype visitAction = DoChildren | ChangeTo of exp

fun visitExp (f : exp -> visitAction) (e : exp) : exp =
	let
		fun visitChildren (e : exp) : exp = case e of
		  BinOp(bop,e1,e2) => BinOp(bop,visitExp f e1, visitExp f e2)
		| UnOp(bop,e) => UnOp(bop,visitExp f e)
		| _ => e
	in
		case f e of
		  DoChildren => visitChildren e
		| ChangeTo e => e
	end

fun symResolve (cop : word) (sop : word) (typ : word) (sz : word) : exp =
	if sop = 0wx0 then mkConst(cop,typ,sz) else
	case (symStateLookup sop, taintSetFind sop sop) of
	  (NONE, NONE) => mkConst(cop,typ,sz)
	| (NONE, SOME(_,_,{uid,file,line})) =>
		mkInput(sop,0wx0,0wx0,uid,cop,typ,sz,file,line)
	| (SOME e,_) => e

(* Functions imported from C *)
val cMain = _import "cMain": int * string vector -> int;

val c_eval_bop = _import "c_eval_bop":
	word * word * word * word * word * word * word
	-> word;

val c_eval_uop = _import "c_eval_uop":
	word * word * word * word
	-> word;

fun assignBasic (dest : word)
                (cop : word) (sop : word) (typ : word) (sz : word)
                : unit
	=
	if sop = 0wx0
	then symStateRm dest
	else case symStateLookup sop of
	  NONE => (symStateRm dest;
	           case taintSetFind sop sop of
	             NONE => ()
	           | SOME(l,h,{uid,file,line}) =>
	               symStateAdd dest (mkInput(sop,0wx0,0wx0,uid,cop,typ,sz,file,line)))
	| SOME e => symStateAdd dest e

datatype side = Left | Right

fun assocConst (ib : bop) (ob : bop) (e1 : exp) (e2 : exp)
               (cop,sop,typ,sz) (s : side)
               : exp
	=
	case (bopToSBop ib, bopToSBop ob, e1, e2) of
	  (Plus, Plus, _, Const{value=cop2,typ=typ2,sz=sz2}) =>
		let val c = c_eval_bop(bopToWord ob,cop2,typ2,sz2,cop,typ,sz) in
		BinOp(ib,e1,mkConst(c,typ2,sz2))
		end
	| (Plus, Plus, Const{value=cop1,typ=typ1,sz=sz1}, _) =>
		let val c = c_eval_bop(bopToWord ob,cop1,typ1,sz1,cop,typ,sz) in
		BinOp(ib,mkConst(c,typ1,sz1),e2)
		end
	| (Minus, Minus, _, Const{value=cop2,typ=typ2,sz=sz2}) =>
		let val c = c_eval_bop(bopToWord PlusA,cop2,typ2,sz2,cop,typ,sz) in
		case s of
		  Right => BinOp(ib,e1,mkConst(c,typ2,sz2))
		| Left => BinOp(ib,mkConst(c,typ2,sz2),e1)
		end
	| (Normal(Mult), Normal(Mult), _, Const{value=cop2,typ=typ2,sz=sz2}) =>
		let val c = c_eval_bop(bopToWord ob,cop2,typ2,sz2,cop,typ,sz) in
		BinOp(ib,e1,mkConst(c,typ2,sz2))
		end
	| (Normal(Mult), Normal(Mult), Const{value=cop1,typ=typ1,sz=sz1}, _) =>
		let val c = c_eval_bop(bopToWord ob,cop1,typ1,sz1,cop,typ,sz) in
		BinOp(ib,mkConst(c,typ1,sz1),e2)
		end
	| (Plus, Normal(Mult), Const{value=cop1,typ=typ1,sz=sz1}, _) =>
		let val c = c_eval_bop(bopToWord ob,cop1,typ1,sz1,cop,typ,sz) in
		BinOp(ib,mkConst(c,typ1,sz1), BinOp(ob,e2,mkConst(cop, typ, sz)))
		end
	| (Minus, Normal(Mult), Const{value=cop1,typ=typ1,sz=sz1}, _) =>
		let val c = c_eval_bop(bopToWord ob,cop1,typ1,sz1,cop,typ,sz) in
		BinOp(ib,mkConst(c,typ1,sz1), BinOp(ob,e2,mkConst(cop, typ, sz)))
		end
	| (Plus, Normal(Mult), _, Const{value=cop2,typ=typ2,sz=sz2}) =>
		let val c = c_eval_bop(bopToWord ob,cop2,typ2,sz2,cop,typ,sz) in
		BinOp(ib,BinOp(ob,e1,mkConst(cop, typ, sz)), mkConst(c,typ2,sz2))
		end
	| (Minus, Normal(Mult), _, Const{value=cop2,typ=typ2,sz=sz2}) =>
		let val c = c_eval_bop(bopToWord ob,cop2,typ2,sz2,cop,typ,sz) in
		BinOp(ib,BinOp(ob,e1,mkConst(cop, typ, sz)),mkConst(c,typ2,sz2))
		end
	| (_, _, _, _) => 
		(
		 case s of
		   Right => BinOp(ob,BinOp(ib,e1,e2),mkConst(cop, typ, sz))
		 | Left => BinOp(ob,mkConst(cop, typ, sz),BinOp(ib,e1,e2)))

fun simplBop (b : bop)
             (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
             (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
             : exp option
	=
	case (symStateLookup sop1, symStateLookup sop2) of
	  (NONE, NONE) =>
		(case (taintSetFind sop1 sop1, taintSetFind sop2 sop2) of
		  (NONE,NONE) => NONE
		| (SOME(_,_,{uid,file,line}),NONE) =>
			SOME(BinOp(b,mkInput(sop1,0wx0,0wx0,uid,cop1,typ1,sz1,file,line),
			             mkConst(cop2,typ2,sz2)))
		| (NONE,SOME(_,_,{uid,file,line})) =>
			SOME(BinOp(b,mkConst(cop1,typ1,sz1),
			             mkInput(sop2,0wx0,0wx0,uid,cop2,typ2,sz2,file,line)))
		| (SOME(_,_,{uid=i1,file=f1,line=l1}),SOME(_,_,{uid=i2,file=f2,line=l2})) =>
			SOME(BinOp(b,mkInput(sop1,0wx0,0wx0,i1,cop1,typ1,sz1,f1,l1),
			             mkInput(sop2,0wx0,0wx0,i2,cop2,typ2,sz2,f2,l2))))
	| (SOME(oe1 as BinOp(ib,e1,e2)), NONE) =>
		(case taintSetFind sop2 sop2 of
		  NONE =>
		  	SOME(assocConst ib b e1 e2 (cop2,sop2,typ2,sz2) Right)
		| SOME(_,_,{uid,file,line}) =>
			SOME(BinOp(b,oe1,mkInput(sop2,0wx0,0wx0,uid,cop2,typ2,sz2,file,line))))
	| (SOME e, NONE) =>
		(case taintSetFind sop2 sop2 of
		  NONE =>
		  	SOME(BinOp(b,e,mkConst(cop2,typ2,sz2)))
		| SOME(_,_,{uid,file,line}) =>
			SOME(BinOp(b,e,mkInput(sop2,0wx0,0wx0,uid,cop2,typ2,sz2,file,line))))
	| (NONE, SOME(oe2 as BinOp(ib,e1,e2))) =>
		(case taintSetFind sop1 sop1 of
		  NONE =>
		  	SOME(assocConst ib b e1 e2 (cop1,sop1,typ1,sz1) Left)
		| SOME(_,_,{uid,file,line}) =>
			SOME(BinOp(b,mkInput(sop1,0wx0,0wx0,uid,cop1,typ1,sz1,file,line),oe2)))
	| (NONE, SOME e) =>
		(case taintSetFind sop1 sop1 of
		  NONE =>
		  	SOME(BinOp(b,mkConst(cop1,typ1,sz1),e))
		| SOME(_,_,{uid,file,line}) =>
			SOME(BinOp(b,mkInput(sop1,0wx0,0wx0,uid,cop1,typ1,sz1,file,line),e)))
	(*| (SOME(BinOp(ib1,e11,e12)), SOME(BinOp(ib1,e21,e22))) =>*)
	| (SOME e1, SOME e2) => SOME(BinOp(b,e1,e2))

fun assignBop (dest : word) (bop : word)
              (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
              (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
              : unit
	=
	if sop1 = (Word.fromInt 0) andalso sop2 = (Word.fromInt 0)
	then symStateRm dest
	else let
		val res = simplBop (wordToBop bop) cop1 sop1 typ1 sz1 cop2 sop2 typ2 sz2
	in
		case res of
		  NONE => symStateRm dest
		| SOME res => symStateAdd dest res
	end

fun simplUop (u : uop)
            (cop : word) (sop : word) (typ : word) (sz : word)
            : exp option
	=
	case symStateLookup sop of
	  NONE => NONE
	| SOME e => SOME(UnOp(u,e))

fun assignUop (dest : word) (uop : word)
              (cop : word) (sop : word) (typ : word) (sz : word)
              : unit
	=
	if sop = (Word.fromInt 0)
	then symStateRm dest
	else let
		val res = simplUop (wordToUop uop) cop sop typ sz
	in
		case res of
		  NONE => symStateRm dest
		| SOME res => symStateAdd dest res
	end

fun assignCast (dest : word)
               (cop : word) (sop : word) (typ : word) (sz : word)
               : unit
	= assignBasic dest cop sop typ sz

(*fun forget_locals () : unit =
	let
		fun forget (sop,_) : unit =
			(symStateRm sop;
			 if taintSetExists sop sop then taintSetRm sop sop else ())
		in
		(case (!locals_stack) of
		   [] => ()
		 | x :: rst => (foldl forget () x;
		                locals_stack := rst))
	end*)

fun retBasic (cop : word) (sop : word) (typ : word) (sz : word) : unit =
	 case symStateLookup sop of
	   NONE =>
		(case taintSetFind sop sop of
		  NONE => ret_val := NONE
		| SOME(l,h,{uid,file,line}) =>
			(print "retBasic: making Input\n";
			 ret_val := SOME(mkInput(sop,0wx0,0wx0,uid,cop,typ,sz,file,line))))
	 | SOME e => ret_val := SOME e

fun retBop (bop : word)
           (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
           (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
           : unit
	=
	 case simplBop (wordToBop bop) cop1 sop1 typ1 sz1 cop2 sop2 typ2 sz2 of
	   NONE =>
	   	ret_val := NONE
	 | SOME e => ret_val := SOME e

fun retUop (uop : word)
              (cop : word) (sop : word) (typ : word) (sz : word)
              : unit
	=
	 case simplUop (wordToUop uop) cop sop typ sz of
	   NONE => ret_val := NONE
	 | SOME e => ret_val := SOME e

fun retVoid () : unit = ()

fun ifBasic (cop : word) (sop : word) (typ : word) (sz : word)
            (file : word) (line : word)
            : unit
	= ()

fun ifBop (bop : word)
          (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
          (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
          (file : word) (line : word)
          : unit
	=
	case simplBop (wordToBop bop) cop1 sop1 typ1 sz1 cop2 sop2 typ2 sz2 of
	  NONE => ()
	| SOME(BinOp(bop,e1,e2)) =>
		let val b = c_eval_bop(bopToWord bop,cop1,typ1,sz1,cop2,typ2,sz2)
		    val bop = if b = 0wx0 then negate_bop bop else bop in
		((*print "Branch: ";
		 print_canexp (canonExp 1 e1);
		 print " ";
		 print_bop bop;*)
		 addBopToOct cOctagon bop e1 e2 file line(*;
		 print " ";
		 print_canexp (canonExp 1 e2);
		 print "\n"*))
		 end
	| SOME e => (print_exp e; print "\n")

fun ifUop (uop : word)
          (cop : word) (sop : word) (typ : word) (sz : word)
          (file : word) (line : word)
          : unit
	= ()

fun switchBasic (c : word)
                (cop : word) (sop : word) (typ : word) (sz : word)
                : unit
	= ()

fun switchBop (c : word) (bop : word)
              (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
              (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
              : unit
	= ()

fun switchUop (c : word) (uop : word)
              (cop : word) (sop : word) (typ : word) (sz : word)
              : unit
	= ()

fun pushArg (cop : word) (sop : word) (typ : word) (sz : word) : unit =
	arg_stack_push (cop,sop,typ,sz)

fun unRegLocal (sop : word) (typ : word) (sz : word) : unit =
	symStateRm sop

fun popArg (dest : word) : unit =
	let val argo = arg_stack_pop () in
		case argo of
		  NONE => ()
		| SOME(cop,sop,typ,sz) =>
			assignBasic dest cop sop typ sz
	end

fun funStart (nargs : word) : unit =
	incr call_depth

fun retPop (cop : word) (sop : word) (typ : word) (sz : word) (nargs : word)
           : unit
	=
	(arg_stack_top := 0;
	 case !ret_val of
	   NONE => symStateRm sop
	 | SOME e => symStateAdd sop e)

fun retNoRet (nargs : word) : unit =
	(arg_stack_top := 0)


fun addTaint (start : word) (esz : word) (ecnt : word)
             (file : word) (line : word)
             : unit
	=
	taintSetAdd start esz ecnt file line

fun addCondTaint (src : word) (dst : word) (f : word)
                 (cop : word) (typ : word) (sz : word)
                 (file: word) (line : word)
                 : unit
	=
	case taintSetFind src src of
	  NONE =>
		(case symStateLookup src of
		  SOME(Input id) =>
		 	symStateAdd dst (mkInput((#addr id),dst,f,(#uid id),cop,typ,sz,file,line))
		 | _ => print("Not Adding CTaint: "^(Word.toString dst)^"\n"))
	| SOME(_,_,{uid,...}) =>
		(print("Adding CTaint: "^(Word.toString dst)^"\n");
		 symStateAdd dst (mkInput(src,dst,f,uid,cop,typ,sz,file,line)))


(* See if the octagon has enough information to prove that
   (e1 bop e2) is true *)
fun checkAssertion (b : bop) (e1 : exp) (e2 : exp) : unit =
	let
		val newoct = copyOct cOctagon
	in
		addBopToOct newoct b e1 e2 0wx0 0wx0;
		(if c_oct_is_included_in (!(#oct cOctagon),!(#oct newoct)) andalso
			not(c_oct_is_empty (!(#oct newoct))) andalso
			not(c_oct_is_universe (!(#oct newoct)))
		then
			print "program checks sufficient!\n"
		else
			print "program checks NOT sufficient!\n");
		c_oct_free (!(#oct newoct))
	end

datatype cex = Lower of int | Upper of int | Both of (int * int)

fun print_cex (bnd : cex) : unit =
	case bnd of
	  Lower l =>
	  	print((Int.toString l)^" <= input")
	| Upper u =>
		print("input <= "^(Int.toString u))
	| Both(l,u) =>
		print((Int.toString l)^" <= input <= "^(Int.toString u))

fun warnAboutCE (bnd : cex) (vid : int) (file : word) (line : word) : unit =
	case IHT.find oVarInpHash vid of
	  NONE => ()
	| SOME id =>
		let
			val ifile = (#file id)
			val iline = (#line id)
		in
			print "For input from: ";
			c_print_loc(ifile,iline);
			print "\n";
			print "The check(s): ";
			printInpChecks vid;
			print "\n";
			print "Must be strengthened because the memory op at: ";
			c_print_loc(file,line);
			print "\n";
			print "Will fail when: ";
			print_cex bnd;
			print "\n"
		end

fun printCounterExample (newoct : octagon) (oldoct : octagon)
                        (file : word) (line : word)
                        : unit
	=
	let
		val newdim = !(#maxvars newoct)
		val newbox = Array.array (2*newdim, 0)
		val newvalid = Array.array (2*newdim, 0)
		val olddim = !(#maxvars oldoct)
		val oldbox = Array.array (2*olddim, 0)
		val oldvalid = Array.array (2*olddim, 0)
		fun loop (i : int) : unit =
			if i >= newdim then () else let
				val newlowo =
					if Array.sub(newvalid,2*i+1) = 0
					then NONE else
						SOME(Array.sub(newbox,2*i + 1))
				val newhio =
					if Array.sub(newvalid,2*i) = 0
					then NONE else
						SOME(Array.sub(newbox,2*i))
				val oldlowo =
					if i >= olddim orelse Array.sub(oldvalid,2*i+1) = 0
					then NONE else
						SOME(Array.sub(oldbox,2*i+1))
				val oldhio =
					if i >= olddim orelse Array.sub(oldvalid,2*i) = 0
					then NONE else
						SOME(Array.sub(oldbox,2*i))
			in
				(case (newlowo,newhio) of
				   (NONE, NONE) => ()
				 | (SOME lo, NONE) =>
				 	if newlowo = oldlowo then () else
				 	warnAboutCE (Lower (~lo)) i file line
				 | (NONE, SOME hi) =>
				 	if newhio = oldhio then () else
				 	warnAboutCE (Upper hi) i file line
				 | (SOME lo, SOME hi) =>
				 	if newlowo = oldlowo andalso newhio = oldhio then () else
				 	warnAboutCE (Both(~lo,hi)) i file line);
				loop (i+1)
			end
	in
		c_oct_get_box(!(#oct newoct),newbox,newvalid);
		c_oct_get_box(!(#oct oldoct),oldbox,oldvalid);
		(*print "Check will fail when\n";*)
		(loop 0) handle Subscript =>
			(print "Subscript raised in printCounterExample\n";
			 raise Subscript)
	end

(* Find values for inputs allowed by the octagon that
   that cause (e1 bop e2) to be false *)
fun findCounterExamples (b : bop) (e1 : exp) (e2 : exp)
                        (file : word) (line : word)
                        : unit
	=
	let
		val newoct = copyOct cOctagon
	in
		addBopToOct newoct (negate_bop b) e1 e2 0wx0 0wx0;
		(if c_oct_is_empty (!(#oct newoct))
		then ()
			(*print "There are NO counterexamples!\n"*)
		else
			(print "There are counterexamples!\n";
			 printCounterExample newoct cOctagon file line));
		c_oct_free (!(#oct newoct))
	end


(* Check functions! *)
fun cLeq (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
         (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
         (file : word) (line : word)
         : unit
	=
	case simplBop Le cop1 sop1 typ1 sz1 cop2 sop2 typ2 sz2 of
	  SOME(BinOp(bop,e1,e2)) =>
	  	((*checkAssertion bop e1 e2;*)
	  	 findCounterExamples bop e1 e2 file line)
	| _ => ()

(* assert(op1 <= op2 + op3) *)
fun cLeqSum (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
            (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
            (cop3 : word) (sop3 : word) (typ3 : word) (sz3 : word)
            (file : word) (line : word)
            : unit
	=
	let
		val low = symResolve cop1 sop1 typ1 sz1
	in
		case simplBop PlusPI cop2 sop2 typ2 sz2 cop3 sop3 typ3 sz3 of
		  NONE => (case low of Const _ => () | _ =>
		  	let val c = c_eval_bop(bopToWord PlusPI,cop2,typ2,sz2,cop3,typ3,sz3) in
		  		(*checkAssertion Le low (mkConst(c,typ2,sz2));*)
		  		findCounterExamples Le low (mkConst(c,typ2,sz2)) file line
		  	end)
		| SOME e =>
			((*checkAssertion Le low e;*)
			 findCounterExamples Le low e file line)
	end

(* assert(op1 + op2 <= op3) *)
fun cSumLeq (cop1 : word) (sop1 : word) (typ1 : word) (sz1 : word)
            (cop2 : word) (sop2 : word) (typ2 : word) (sz2 : word)
            (cop3 : word) (sop3 : word) (typ3 : word) (sz3 : word)
            (file : word) (line : word)
            : unit
	=
	let
		val hi = symResolve cop3 sop3 typ3 sz3
	in
		case simplBop PlusPI cop1 sop1 typ1 sz1 cop2 sop2 typ2 sz2 of
		  NONE => (case hi of Const _ => () | _ =>
		  	let val c = c_eval_bop(bopToWord PlusPI,cop1,typ1,sz1,cop2,typ2,sz2) in
		  		(*checkAssertion Le (mkConst(c,typ1,sz1)) hi;*)
		  		findCounterExamples Le (mkConst(c,typ1,sz1)) hi file line
		  	end)
		| SOME e =>
			((*checkAssertion Le e hi;*)
			 findCounterExamples Le e hi file line)
	end

val instr_count = ref (Word64.fromInt 0)
fun instrDispatch (iaa : cArray) (row : int) : unit =
	(instr_count := (Word64.fromInt 1) + (!instr_count);
	let fun lu (c : int) = cArray2Sub iaa row c in
		(case (Word32.toInt (lu 0)) of
		  0 => assignBasic (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		| 10 => assignBop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		                  (lu 6) (lu 7) (lu 8) (lu 9) (lu 10)
		| 20 => assignUop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5) (lu 6)
		| 30 => assignCast (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		| 40 => retBasic (lu 1) (lu 2) (lu 3) (lu 4)
		| 50 => retBop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		               (lu 6) (lu 7) (lu 8) (lu 9)
		| 60 => retUop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		| 70 => retVoid ()
		| 80 => ifBasic (lu 1) (lu 2) (lu 3) (lu 4) (lu 5) (lu 6)
		| 90 => ifBop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		              (lu 6) (lu 7) (lu 8) (lu 9) (lu 10) (lu 11)
		| 100 => ifUop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5) (lu 6) (lu 7)
		| 110 => switchBasic (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		| 120 => switchBop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		                   (lu 6) (lu 7) (lu 8) (lu 9) (lu 10)
		| 130 => switchUop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5) (lu 6)
		| 140 => pushArg (lu 1) (lu 2) (lu 3) (lu 4)
		| 150 => popArg (lu 1)
		| 160 => funStart (lu 1)
		| 170 => retPop (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		| 180 => retNoRet (lu 1)
		| 190 => unRegLocal (lu 1) (lu 2) (lu 3)
		| 200 => addTaint (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		| 210 => addCondTaint (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		                      (lu 6) (lu 7) (lu 8)
		| 220 => cLeq (lu 1) (lu 2) (lu 3) (lu 4) (lu 5)
		              (lu 6) (lu 7) (lu 8) (lu 9) (lu 10)
		| 230 => cLeqSum (lu 1) (lu 2) (lu 3) (lu 4) (lu 5) (lu 6) 
		                 (lu 7) (lu 8) (lu 9) (lu 10) (lu 11) (lu 12)
		                 (lu 13) (lu 14)
		| 240 => cSumLeq (lu 1) (lu 2) (lu 3) (lu 4) (lu 5) (lu 6)
		                 (lu 7) (lu 8) (lu 9) (lu 10) (lu 11) (lu 12)
		                 (lu 13) (lu 14)
		| _ => ()) handle Overflow =>
			(print("instrDispatch: Overflow\n");
			 raise Overflow)
	end)


(* Function exported to C *)
val e = _export "process_instrs": (MLton.Pointer.t * int * int -> unit) -> unit;
fun at ((iaa : MLton.Pointer.t),(m : int),(n : int)) : unit =
	let val carr = {arr = iaa, cols = n, rows = m} in
		let fun loop (i:int) =
			if i >= m then () else
			(instrDispatch carr i;
			loop (i+1))
		in
			(loop 0)
		end 
	end
val _ = e at

val arg_list = (CommandLine.name())::(CommandLine.arguments())
val arg_list = map (fn s => s^"\000") arg_list
val arg_vec = vector arg_list
val exit_code = cMain (length (CommandLine.arguments())+1, arg_vec)
