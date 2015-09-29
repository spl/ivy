(*
 * dinstrumenter.ml
 *
 * This module converts CIL to 3-address code, and then
 * adds hooks for instrumentation.
 *
 *
 *)

open Cil
open Pretty
open Dcheckdef
open Dutil

module E = Errormsg

let fixBlock = Dcheck.fixBlock ~giveID:false

let mkInstrFun (name : string) (n : int) : exp =
    let args = Util.list_init n (fun _ -> uintType) in
    mkFun name voidType args Rcutils.nofreeAttr

let instrAssign     = mkInstrFun "DINSTR_Assign"   5
let instrBop        = mkInstrFun "DINSTR_Bop"      10
let instrUop        = mkInstrFun "DINSTR_Uop"      6
let instrPushArg    = mkInstrFun "DINSTR_PushArg"  4
let instrPopArg     = mkInstrFun "DINSTR_PopArg"   1
let instrUnRegLocal = mkInstrFun "DINSTR_UnRegLocal" 3
let instrFunStart   = mkInstrFun "DINSTR_FunStart" 1
let instrRegField   = mkInstrFun "DINSTR_RegField" 3
let instrRegArray   = mkInstrFun "DINSTR_RegArray" 4
let instrCast       = mkInstrFun "DINSTR_Cast"     5

let instrRetBasic = mkInstrFun "DINSTR_RetBasic" 4
let instrRetBop   = mkInstrFun "DINSTR_RetBop"   9
let instrRetUop   = mkInstrFun "DINSTR_RetUop"   5
let instrRetVoid  = mkInstrFun "DINSTR_RetVoid"  0
let instrPopRet   = mkInstrFun "DINSTR_RetPop"   5
let instrRetNoRet = mkInstrFun "DINSTR_RetNoRet" 1

let instrIfBasic = mkInstrFun "DINSTR_IfBasic" 6
let instrIfBop   = mkInstrFun "DINSTR_IfBop"   11
let instrIfUop   = mkInstrFun "DINSTR_IfUop"   7

let instrSwitchBasic = mkInstrFun "DINSTR_SwitchBasic" 5
let instrSwitchBop   = mkInstrFun "DINSTR_SwitchBop" 10
let instrSwitchUop   = mkInstrFun "DINSTR_SwitchUop" 6

let instrCNonNull        = mkInstrFun "DINSTR_CNonNull"         4
let instrCEq             = mkInstrFun "DINSTR_CEq"              8
let instrCMult           = mkInstrFun "DINSTR_CMult"            8
let instrCPtrArith       = mkInstrFun "DINSTR_CPtrArith"       17
let instrCPtrArithNT     = mkInstrFun "DINSTR_CPtrArithNT"     17
let instrCPtrArithAccess = mkInstrFun "DINSTR_CPtrArithAccess" 17
let instrCLeqInt         = mkInstrFun "DINSTR_CLeqInt"          8
let instrCLeq            = mkInstrFun "DINSTR_CLeq"            10
let instrCLeqSum         = mkInstrFun "DINSTR_CLeqSum"         14
let instrCSumLeq         = mkInstrFun "DINSTR_CSumLeq"         14
let instrCLeqNT          = mkInstrFun "DINSTR_CLeqNT"           9
let instrCNullOrLeq      = mkInstrFun "DINSTR_CNullOrLeq"      12
let instrCNullOrLeqNT    = mkInstrFun "DINSTR_CNullOrLeqNT"    13
let instrCWriteNT        = mkInstrFun "DINSTR_CWriteNT"        13
let instrCNullUnionOrSelected = mkInstrFun "DINSTR_CNullUnionOrSelected" 8
let instrCSelected       = mkInstrFun "DINSTR_CSelected"        4
let instrCNotSelected    = mkInstrFun "DINSTR_CNotSelected"     4

let instrInit            = mkInstrFun "DINSTR_init"  0
let instrEnd             = mkInstrFun "DINSTR_end"   0
let instrNop             = mkInstrFun "DINSTR_nop"   0

let instrTaint           = mkInstrFun "DINSTR_taint"  5
let instrCTaint          = mkInstrFun "DINSTR_ctaint" 8
let instrArgv            = mkInstrFun "DINSTR_Argv"   4

let fileToken : exp = Lval(var (makeGlobalVar "__FILE__" charPtrType))
let lineToken : exp = Lval(var (makeGlobalVar "__LINE__" uintType))

let isInstrFun (i : instr) : bool =
    match i with
    | Call(_,Lval(Var vi, NoOffset),_,_) ->
        (String.length vi.vname >= String.length "DINSTR_" &&
        String.compare (String.sub vi.vname 0 7) "DINSTR_" = 0) ||
        vi.vname = "caml_startup"
    | _ -> false

let isPtrCastableType (t : typ) : bool =
	match unrollType t with
	| TInt(_,_) | TPtr(_,_) | TArray(_,_,_) | TEnum(_,_) -> true
	| _ -> false


let constBop =
    function
    | PlusA -> integer 0
    | PlusPI -> integer 1
    | IndexPI -> integer 2
    | MinusA -> integer 3
    | MinusPI -> integer 4
    | MinusPP -> integer 5
    | Mult -> integer 6
    | Div -> integer 7
    | Mod -> integer 8
    | Shiftlt -> integer 9
    | Shiftrt -> integer 10
    | Lt -> integer 11
    | Gt -> integer 12
    | Le -> integer 13
    | Ge -> integer 14
    | Eq -> integer 15
    | Ne -> integer 16
    | BAnd -> integer 17
    | BXor -> integer 18
    | BOr -> integer 19
    | LAnd -> integer 20
    | LOr -> integer 21
let constUop =
    function
    | Neg -> integer 0
    | BNot -> integer 1
    | LNot -> integer 2

let makeInstr (call : exp) (args : exp list) : instr =
	if List.exists (fun e -> not(isPtrCastableType(typeOf e))) args then
		Call(None,instrNop,[],locUnknown)
	else
	let args = List.map (fun e -> mkCast e uintType) args in
    Call(None,call,args,locUnknown)

let isSignedType (t : typ) : bool =
	match unrollType t with
	| TInt(ik,_) -> isSigned ik
	| TEnum _ -> true
	| _ -> false

let baseType (t : typ) : typ option =
	match unrollType t with
	| TPtr(bt, _)
	| TArray(bt,_,_) -> Some bt
	| TInt _ -> Some voidType
	| _ -> None

let baseSize (t : typ) : int =
	try
		match baseType t with
		| None -> 0
		| Some t -> bitsSizeOf t / 8
	with _ -> 0

let integerSym = zero
let pointerSym = one
(* Takes a basic expression and returns the symbolic expression
 * and a constant telling us to treat the symbolic expression as
 * a constant or as the id of a symbolic variable *)
let rec opToTypeAndSym (op : exp) : (exp * exp * exp) =
    match op with
    | Const _ ->
		let size_exp =
			if isSignedType (typeOf op) then
				integer (-(bitsSizeOf(typeOf op)))
			else
				integer (bitsSizeOf (typeOf op))
		in
    	(integerSym,size_exp,zero)
    | AddrOf(_,_) | StartOf(_,_) ->
        (pointerSym, integer (baseSize (typeOf op)), zero)
    | Lval(Mem e, NoOffset) ->
    	(pointerSym, integer (baseSize (typeOf e)), e)
    | Lval lv ->
    	if isPtrOrArray (typeOf op) then
	        (pointerSym, integer (baseSize (typeOf op)), AddrOf lv)
	    else if isSignedType (typeOf op) then
	    	(integerSym, integer(-(bitsSizeOf(typeOf op))), AddrOf lv)
	    else
	    	(integerSym, integer(bitsSizeOf(typeOf op)), AddrOf lv)
    | CastE(t, op) ->
    	let (sym, sz, sop) = opToTypeAndSym op in
    	if isPtrOrArray t then
    		(pointerSym, integer (baseSize t), sop)
    	else if isSignedType t then
    		(integerSym, integer(-(bitsSizeOf t)), sop)
    	else
    		(integerSym, integer(bitsSizeOf t), sop)
    | _ -> E.s(bug "opToTypeAndSym: exp not basic: %a\n" d_plainexp op)


let makeCheckInstr (c : check) : instr list =
	let split3 l =
		let rec helper l acc1 acc2 acc3 =
			match l with
			| [] -> (List.rev acc1, List.rev acc2, List.rev acc3)
			| (a,b,c)::rst ->
				helper rst (a::acc1) (b::acc2) (c::acc3)
		in
		helper l [] [] []
	in
    let merge4 l1 l2 l3 l4 =
        let rec helper l1 l2 l3 l4 acc =
            match l1,l2,l3,l4 with
            | [], [], [], [] -> List.rev acc
            | x1::rst1, x2::rst2, x3::rst3, x4::rst4 ->
                helper rst1 rst2 rst3 rst4 (x4::x3::x2::x1::acc)
            | _, _, _, _ -> raise(Invalid_argument "merge4: different lengths")
        in
        helper l1 l2 l3 l4 []
    in
    let opsToArgList (ops : exp list) : exp list =
        let typ ,sz, sops = split3 (List.map opToTypeAndSym ops) in
        merge4 ops sops typ sz
    in
    match c with
    | CNonNull op -> begin
        match op with
        | Lval(Var vi, off) ->
        	let (typ,sz,sop) = opToTypeAndSym op in
            [makeInstr instrCNonNull [op;sop;typ;sz]]
        | _ -> E.s(bug "makeCheckInstr: CNonNull of constant remains\n")
    end
    | CEq(op1,op2,s,dl) ->
        [makeInstr instrCEq (opsToArgList [op1;op2])]
    | CMult(op1,op2) ->
        [makeInstr instrCMult (opsToArgList [op1;op2])]
    | CPtrArith(op1,op2,op3,op4,sz) ->
        let args_low = opsToArgList [op1;op3;op4] in
        let args_up = opsToArgList [op3;op4;op2] in
        [makeInstr instrCLeqSum (args_low@[fileToken;lineToken]);
         makeInstr instrCSumLeq (args_up@[fileToken;lineToken])]
    | CPtrArithNT(op1,op2,op3,op4,sz) ->
        let args = (integer sz)::(opsToArgList [op1;op2;op3;op4]) in
        [makeInstr instrCPtrArithNT args]
    | CPtrArithAccess(op1,op2,op3,op4,sz) ->
        let args = (integer sz)::(opsToArgList [op1;op2;op3;op4]) in
        [makeInstr instrCPtrArithAccess args]
    | CLeqInt(op1,op2,s) ->
        [makeInstr instrCLeqInt (opsToArgList [op1;op2])]
    | CLeq(op1,op2,s) ->
        [makeInstr instrCLeq ((opsToArgList [op1;op2])@[fileToken;lineToken])]
    | CLeqNT(op1,op2,sz,s) ->
        let args = (integer sz)::(opsToArgList [op1;op2]) in
        [makeInstr instrCLeqNT args]
    | CNullOrLeq(op1,op2,op3,s) ->
        [makeInstr instrCNullOrLeq (opsToArgList [op1;op2;op3])]
    | CNullOrLeqNT(op1,op2,op3,sz,s) ->
        let args = (integer sz)::(opsToArgList [op1;op2;op3]) in
        [makeInstr instrCNullOrLeqNT args]
    | CWriteNT(op1,op2,op3,sz) ->
        let args = (integer sz)::(opsToArgList [op1;op2;op3]) in
        [makeInstr instrCWriteNT args]
    | CNullUnionOrSelected(lv,e) ->
        [makeInstr instrCNullUnionOrSelected (opsToArgList [Lval lv;e])]
    | CSelected e ->
        [makeInstr instrCSelected (opsToArgList [e])]
    | CNotSelected e ->
        [makeInstr instrCNotSelected (opsToArgList [e])]


let paramTrans (ap : attrparam)
               (args : exp list)
               (ro : lval option) : exp option =
	match ap with
	| AStar(ACons(is,[])) ->
		if String.sub is 0 1 = "$" then begin
			let nstr = String.sub is 1 ((String.length is) - 1) in
			let i = int_of_string nstr in
			if i = 0 then match ro with
			| Some r -> Some(Lval(Mem (Lval r),NoOffset))
			| None -> None
			else Some(Lval(Mem(List.nth args (i-1)),NoOffset))
		end else None
	| ACons(is,[]) ->
		if String.sub is 0 1 = "$" then begin
			let nstr = String.sub is 1 ((String.length is) - 1) in
			let i = int_of_string nstr in
			if i = 0 then match ro with
			| None -> None
			| Some r -> Some(Lval r)
			else Some(List.nth args (i-1))
		end else None
	| AInt i -> Some(integer i)
	| _ -> None


let rec drop (l : 'a list) (n : int) : 'a list =
	if n = 0 then l else
	match l with [] -> []
	| x :: rst -> drop rst (n-1)


let taintVarArg (start : int) (el : exp list) : instr list =
	let el = drop el start in
	List.map (fun e ->
		makeInstr instrTaint [e;integer(baseSize(typeOf e));
		                      one;fileToken;lineToken]) el


let taintFlowCall (i : instr) : instr list =
	match i with
	| Call(None,Lval(Var fvi,NoOffset),el,_) -> begin
		List.fold_left (fun il (Attr(an, apl)) ->
			if an = "Taint" then begin
				match apl with
				| [ap;sz;num] -> begin
					match paramTrans ap el None,
					      paramTrans sz el None,
					      paramTrans num el None with
					| None, _, _ -> il
					| _, None, _ -> il
					| _, _, None -> il
					| Some e, Some s, Some n ->
						let (_,_,sop) = opToTypeAndSym e in
						(makeInstr instrTaint [sop;s;n;
						                       fileToken;lineToken])::il
				end
				| _ -> E.s(bug "taintFlowCall: bad attribute\n")
			end else if an = "CTaint" then begin
				match apl with
				| [iap; oap] -> begin
					match paramTrans iap el None, 
					      paramTrans oap el None with
					| _, None | None, _ -> il
					| Some ie, Some oe ->
						let (_,_,isop) = opToTypeAndSym ie in
						let (otyp,osz,osop) = opToTypeAndSym oe in
						let fe = AddrOf(Var fvi, NoOffset) in
						(makeInstr instrCTaint [isop;osop;fe;oe;otyp;osz;
						                        fileToken;lineToken])::il
				end
				| _ -> E.s(bug "taintFlowCall: bad attribute\n")
			end else if an = "ScanTaint" then begin
				match apl with
				| [AInt start] -> begin
					taintVarArg start el
				end
				| _ -> E.s(bug "taintFlowCall: bad attribute\n")
			end else il) [] fvi.vattr
	end
	| Call(Some dlv,Lval(Var fvi,NoOffset),el,_) -> begin
		List.fold_left (fun il (Attr(an,apl)) ->
			if an = "Taint" then begin
				match apl with
				| [ap;sz;num] -> begin
					match paramTrans ap el (Some dlv),
					      paramTrans sz el (Some dlv),
					      paramTrans num el (Some dlv) with
					| None, _, _ -> il
					| _, None, _ -> il
					| _, _, None -> il
					| Some e, Some s, Some n ->
						let (_,_,sop) = opToTypeAndSym e in
						(makeInstr instrTaint [sop;s;n;
						                       fileToken;lineToken])::il
				end
				| _ -> E.s(bug "taintFlowCall: bad Attribute\n")
			end else if an = "CTaint" then begin
				match apl with
				| [iap; oap] -> begin
					match paramTrans iap el (Some dlv),
					      paramTrans oap el (Some dlv) with
					| None, _ | _, None -> il
					| Some ine, Some oute ->
						let (_,_,isop) = opToTypeAndSym ine in
						let (otyp,osz,osop) = opToTypeAndSym oute in
						let fe = AddrOf(Var fvi, NoOffset) in
						(makeInstr instrCTaint [isop;osop;fe;oute;otyp;osz;
						                        fileToken;lineToken])::il
				end
				| _ -> E.s(bug "taintFlowCall: bad attribute\n")
			end else if an = "ScanTaint" then begin
				match apl with
				| [AInt start] -> begin
					taintVarArg start el
				end
				| _ -> E.s(bug "taintFlowCall: bad attribute\n")
			end else il) [] fvi.vattr
	end
	| _ -> []


let instrumentInstr (i : instr) : stmtkind =
    if isInstrFun i then Instr [i] else
    let (preinstri,postinstri) =
        match i with
        | Set(lv, e,_) -> begin
            let destaddr =
                match lv with
                | (Mem destaddr, NoOffset) -> destaddr
                | (Var vi, off) -> AddrOf lv
                | _ -> E.s(bug "instrumentInstr: lval not basic\n")
            in
            match e with
            | Const _ | AddrOf(_,_) | StartOf(_,_) ->
            	let (typ,sz,sop) = opToTypeAndSym e in
                ([makeInstr instrAssign [destaddr;e;sop;typ;sz]],[])
            | Lval(Var vi, off) ->
            	let (typ,sz,sop) = opToTypeAndSym e in
                ([makeInstr instrAssign
                    [destaddr;e;sop;typ;sz]],
                 [])
            | Lval(Mem srcaddr, NoOffset) ->
            	let (typ,sz,sop) = opToTypeAndSym e in
           		([makeInstr instrAssign [destaddr;e;srcaddr;typ;sz]],[])
            | BinOp(bop, op1, op2,_) ->
                let (t1, sz1, sop1) = opToTypeAndSym op1 in
                let (t2, sz2, sop2) = opToTypeAndSym op2 in
                ([makeInstr instrBop
                    [destaddr;constBop bop;op1;sop1;t1;sz1;op2;sop2;t2;sz2]],
                 [])
            | UnOp(uop, op,_) ->
                let (t, sz, sop) = opToTypeAndSym op in
                ([makeInstr instrUop [destaddr;constUop uop;op;sop;t;sz]],[])
            | CastE(t,bexp) ->
                let (typ, sz, sop) = opToTypeAndSym e in
                ([makeInstr instrAssign [destaddr;e;sop;typ;sz]],[])
            | _ -> E.s(bug "instrumentInstr: exp not 3-address\n")
        end
        | Call(None, fe, bel, loc) -> begin
            match instrToCheck i with
            | Some c -> begin
                (makeCheckInstr c, [])
            end
            | None ->
                (* XXX: check for libc calls here *)
                let pushList = List.map (fun e ->
                    let (typ, sz, sop) = opToTypeAndSym e in
                    makeInstr instrPushArg [e;sop;typ;sz])
                    bel
                in
                let taintInstrs = taintFlowCall i in
                (pushList,taintInstrs@[makeInstr instrRetNoRet [integer(List.length bel)]])
        end
        | Call(Some dlv, fe, bel, loc) ->
            let makeRetPop lv =
                match lv with
                | (Mem bexp, NoOffset) ->
                	let (typ,sz,sop) = opToTypeAndSym (Lval lv) in
                    makeInstr instrPopRet [Lval lv;bexp;typ;sz;integer(List.length bel)]
                | (Var vi, off) ->
                   	let (typ,sz,sop) = opToTypeAndSym (Lval lv) in
                    makeInstr instrPopRet [Lval lv;AddrOf lv;typ;sz;integer(List.length bel)]
                | _ -> E.s(bug "instrumentInstr: lval not basic\n")
            in
            let pushList = List.map (fun e ->
                let (typ, sz, sop) = opToTypeAndSym e in
                makeInstr instrPushArg [e;sop;typ;sz])
                bel
            in
            let taintInstrs = taintFlowCall i in
            let retInstrs =
            	match taintInstrs with
            	| [] -> [makeRetPop dlv]
            	| _ -> []
            in
            (pushList,taintInstrs@retInstrs)
        | Asm(_,_,_,_,_,_) ->
            (* XXX: do something reasonable *)
            ([],[])
    in
    Instr(preinstri@[i]@postinstri)

let instrUnRegLocals (sid : int) (fd : fundec) : instr list =
	List.fold_left (fun ls vi ->
		match unrollType vi.vtype with
		| TArray (_,_,_) | TComp(_,_) -> ls
		| _ ->
			if not(Dtaint.viTainted sid vi) then ls else
			let (typ,sz,sop) = opToTypeAndSym (Lval(Var vi, NoOffset)) in
			(makeInstr instrUnRegLocal [sop;typ;sz])::ls)
		[] (fd.slocals@fd.sformals)

let instrumentReturn (sid : int)
                     (fd : fundec)
                     (inMain : bool)
					 ((eo : exp option), (loc : location))
					 : stmtkind
	=
    let i e =
        match e with
        | Const _ | AddrOf(_,_) | StartOf(_,_) ->
        	let (typ, sz, sop) = opToTypeAndSym e in
            makeInstr instrRetBasic [e;sop;typ;sz]
        | Lval(Var vi, off) ->
        	let (typ, sz, sop) = opToTypeAndSym e in
            makeInstr instrRetBasic [e;sop;typ;sz]
        | Lval(Mem srcaddr, NoOffset) ->
        	let (typ,sz,sop) = opToTypeAndSym e in
        	makeInstr instrRetBasic [e;srcaddr;typ;sz]
        | BinOp(bop, op1, op2,_) ->
            let (t1, sz1, sop1) = opToTypeAndSym op1 in
            let (t2, sz2, sop2) = opToTypeAndSym op2 in
            makeInstr instrRetBop [constBop bop;op1;sop1;sz1;t1;op2;sop2;t2;sz2]
        | UnOp(uop,op,_) ->
            let (t, sz, sop) = opToTypeAndSym op in
            makeInstr instrRetUop [constUop uop;op;sop;t;sz]
        | CastE(t,bexp) ->
            let (typ, sz, sop) = opToTypeAndSym e in
            makeInstr instrRetBasic [e;sop;typ;sz]
        | _ -> E.s(bug "instrumentInstr: exp not 3-address\n")
    in
    let mainRet = if inMain then [makeInstr instrEnd []] else [] in
    let unregs = instrUnRegLocals sid fd in
    match eo with
    | None ->
    	let ri = makeInstr instrRetVoid [] in
    	Block(mkBlock [mkStmt (Instr(ri::(unregs@mainRet))); mkStmt (Return(eo,loc))])
    | Some e ->
        Block(mkBlock [mkStmt (Instr([i e]@unregs@mainRet)); mkStmt (Return(eo,loc))])

let instrumentIf ((ce : exp), (tb : block), (fb : block), (loc : location)) : stmtkind =
    let i =
        match ce with
        | Const _ | AddrOf(_,_) | StartOf(_,_) ->
        	let (typ,sz,sop) = opToTypeAndSym ce in
            makeInstr instrIfBasic [ce;sop;typ;sz;fileToken;lineToken]
        | Lval(Var vi, off) ->
        	let (typ,sz,sop) = opToTypeAndSym ce in
            makeInstr instrIfBasic [ce;sop;typ;sz;fileToken;lineToken]
        | Lval(Mem srcaddr, NoOffset) ->
        	let (typ,sz,sop) = opToTypeAndSym ce in
        	makeInstr instrIfBasic [ce;srcaddr;typ;sz;fileToken;lineToken]
        | BinOp(bop, op1, op2, _) ->
            let (t1,sz1,sop1) = opToTypeAndSym op1 in
            let (t2,sz2,sop2) = opToTypeAndSym op2 in
            makeInstr instrIfBop [constBop bop;op1;sop1;t1;sz1;op2;sop2;t2;sz2;
                                  fileToken;lineToken]
        | UnOp(uop, op, _) ->
            let (t, sz, sop) = opToTypeAndSym op in
            makeInstr instrIfUop [constUop uop;op;sop;t;sz;fileToken;lineToken]
        | CastE(t, op) ->
            let (typ, sz, sop) = opToTypeAndSym ce in
            makeInstr instrIfBasic [op;sop;typ;sz;fileToken;lineToken]
        | _ -> E.s(bug "instrumentIf: exp not 3-address\n")
    in
    Block(mkBlock [mkStmt (Instr [i]); mkStmt (If(ce,tb,fb,loc))])

let getCase x =
    let c =
        List.filter
        (function Case(_,_) -> true | _ -> false)
        x.labels
    in
    match c with
    | [Case(e,l)] -> Some e
    | _ -> None
    
let rec getCases stmts acc =
    match stmts with
    | [] -> acc
    | x :: rst -> begin
        match getCase x with
        | None -> getCases rst acc
        | Some e -> getCases rst (e::acc)
    end

let makeBasicSwitchInstrs (e : exp) (sl : stmt list) : instr list =
    let (t, sz, sop) = opToTypeAndSym e in
    List.map (fun conste ->
        makeInstr instrSwitchBasic [conste;e;sop;t;sz])
        (getCases sl [])

let makeBopSwitchInstrs ((bop:binop),(op1:exp),(op2:exp)) (sl:stmt list) : instr list =
    let (t1, sz1, sop1) = opToTypeAndSym op1 in
    let (t2, sz2, sop2) = opToTypeAndSym op2 in
    List.map (fun conste ->
        makeInstr instrSwitchBop [conste;constBop bop;op1;sop1;t1;sz1;op2;sop2;t2;sz2])
        (getCases sl [])

let makeUopSwitchInstrs ((uop:unop),(op:exp)) (sl:stmt list) : instr list =
    let (t, sz, sop) = opToTypeAndSym op in
    List.map (fun conste ->
        makeInstr instrSwitchUop [conste;constUop uop;op;sop;t;sz])
        (getCases sl [])

let instrumentSwitch ((e:exp), (b:block), (sl:stmt list), (loc:location)) : stmtkind =
    let il =
        match e with
        | Const _ | AddrOf(_,_) | StartOf(_,_)
        | Lval(Var _, _)
        | Lval(Mem _, NoOffset) ->
            makeBasicSwitchInstrs e sl
        | BinOp(bop, op1, op2, _) ->
            makeBopSwitchInstrs (bop,op1,op2) sl
        | UnOp(uop, op, _) ->
            makeUopSwitchInstrs (uop,op) sl
        | CastE(_, _) ->
            makeBasicSwitchInstrs e sl
        | _ -> E.s(bug "instrumentSwitch: exp not 3-address\n")
    in
    Block(mkBlock [mkStmt (Instr il); mkStmt (Switch(e,b,sl,loc))])

let rec instrumentStmt (fd : fundec) (inMain : bool) (s : stmt) : unit =
    match s.skind with
    | Instr il -> begin
        match il with
        | [] -> ()
        | [i] -> if Dtaint.instrContainsTaint s.sid i then
            s.skind <- instrumentInstr i
        | _ -> E.s(bug "instrumentStmt: Instr with more than one instr\n")
    end
    | Return(eo, loc) ->
        s.skind <- instrumentReturn s.sid fd inMain (eo,loc)
    | Goto(_,_) -> ()
    | Break _ -> ()
    | Continue _ -> ()
    | If(ce,tb,fb,loc) -> begin
        instrumentBlock fd inMain tb;
        instrumentBlock fd inMain fb;
        if Dtaint.expContainsTaint s.sid ce then
        	s.skind <- instrumentIf (ce,tb,fb,loc)
    end
    | Switch(e,b,sl,loc) -> begin
        instrumentBlock fd inMain b;
        s.skind <- instrumentSwitch (e,b,sl,loc)
    end
    | Loop(b,_,_,_) -> instrumentBlock fd inMain b
    | Block b -> instrumentBlock fd inMain b
    | TryFinally(b1,b2,_) -> begin
        instrumentBlock fd inMain b1;
        instrumentBlock fd inMain b2
    end
    | TryExcept(b1,_,b2,_) -> begin
        instrumentBlock fd inMain b1;
        instrumentBlock fd inMain b2
    end

and instrumentBlock (fd : fundec) (inMain : bool) (b : block) : unit =
    List.iter (instrumentStmt fd inMain) b.bstmts

let fixMain (fd : fundec) : unit =
	(*let arg =
		if List.exists (fun vi -> vi.vname = "argv") fd.sformals then
			Lval(Var(List.find (fun vi -> vi.vname = "argv") fd.sformals),NoOffset)
		else CastE(voidPtrType,zero)
	in*)
	let dinstr_init = makeInstr instrInit [] in
	let argv_init = makeInstr instrArgv
		((List.map (fun vi -> Lval(Var vi, NoOffset)) fd.sformals)@
		 [fileToken;lineToken])
	in
	fd.svar.vname <- "cMain";
	fd.sbody.bstmts <-
		(mkStmt(Instr [dinstr_init;argv_init]))::fd.sbody.bstmts
(*
type rfContext =
{
	rfHash : (string, fundec) Hashtbl.t; (* reg funs already built *)
	mutable rfTyps : typ list            (* types already seen in a traversal *)
	mutable rfAttrCtxt : context   (* attribute context *)
}

(* returns an expression for the start of an array, and the size in context c *)
let getCount (t : typ) (e : exp) (c : context) : exp * exp =
	if isNullterm t then (e, integer (-1))
	let rec getBounds (a : attributes) : exp * exp option =
		match a with
		| Attr ("bounds", [lo; hi]) :: _ ->
			let _, lo' = compileAttribute ctx lo in
			let _, hi' = compileAttribute ctx hi in
			Some(lo', hi')
		| Attr ("fancybounds", [AInt lo; AInt hi]) :: _ ->
			Some(getBoundsExp lo, getBoundsExp hi)
		| Attr _ :: rest -> getBounds rest
		| _ -> None
	in
	match getBounds (typeAttrs t) with
	| None -> (e, one)
	| Some(lo, hi) ->  (lo, BinOp(MinusPP, hi, lo, t))


let isStructType (t : typ) : bool =
	match unrollType t with
	| TComp(ci,_) when ci.cstruct -> true
	| _ -> false

let getRegFunForStructType (ctx : rfContext)
                           (f : file)
                           (baseTyp : typ)
                           : exp
	=
	match baseTyp with


(* Make a call to register an argument. Build the registration function and add
   it to rfHash if necessary. Do this recursively for structure fields. Punt on
   recursive and abstract types. *)
let getRegFunForFormal (ctx : rfContext) (* already built reg funs. ptr types already chased *)
                       (vi  : varinfo)   (* exp we're building for *)
                       : instr           (* call to the reg fun for e *)
	=
	let typ = vi.vtype in
	let e = Lval(Var vi, NoOffset) in
	if isPtrOrArray typ then (* potential aggregate *)
		if isAbstractPtr typ then (* can't look in, so register as a scalar *)
			let (typ,sz,sop) = opToTypeAndSym e
			makeInstr instrRegField [e;sop;typ;sz]
		else if isStructType (baseType typ) then
			let regFun = getRegFunForCompTyp ctx f (baseType typ) in
			let (base,cnt) = getCount typ e ctx.context in
			let sz = integer (baseSize typ) in
			makeInstr instrRegArray [base;sz;cnt;regFun]
	else (* yay it's just a scalar! Return call to RegisterField*)
		let (typ,sz,sop) = opToTypeAndSym e in
		makeInstr instrRegField [e;sop;typ;sz]
*)


let addPrologue (inMain : bool) (fd : fundec) : unit =
    let pinstrs =
        List.map (fun vi ->
            makeInstr instrPopArg [AddrOf(Var vi, NoOffset)])
            (List.rev fd.sformals)
    in
    (*let locinstrs = instrRegLocals fd in
    let pinstrs = locinstrs @ pinstrs in*)
    let pinstrs = (makeInstr instrFunStart [integer(List.length pinstrs)])::pinstrs in
    if pinstrs <> [] && not(inMain) then
        fd.sbody.bstmts <- (mkStmt(Instr pinstrs))::fd.sbody.bstmts;
    if inMain then
    	fixMain fd

let stripRegister (fd : fundec) : unit =
	let f vi =
		match vi.vstorage with
		| Register -> vi.vstorage <- NoStorage
		| _ -> ()
	in
	List.iter f fd.slocals

let instrumentFun (fd : fundec) : unit =
	let inMain = (fd.svar.vname = "main") in
	stripRegister fd;
    fixBlock fd.sbody;
    Dtaint.computeTaint fd;
    instrumentBlock fd inMain fd.sbody;
    addPrologue inMain fd

let mergeTaintAnnots (f : file) : unit =
	try
		let fn = "itaint.patch.h" in
		let fh = open_in fn in
		close_in fh;
		Dpatch.applyPatch f fn
	with Sys_error _ -> ignore(E.log "mergeTaintAnnots: failed")

let instrumentFile (f : file) : unit =
    Simplify.splitStructs := false;
    Simplify.simpleMem := false;
    Simplify.simplAddrOf := false;
    mergeTaintAnnots f;
    iterGlobals f Simplify.doGlobal;
    iterGlobals f (function GFun(fd,_) -> instrumentFun fd | _ -> ());
    iterGlobals f (function GFun(fd,_) -> Oneret.oneret fd | _ -> ());
    f.globals <- (GText("#include <deputy/sml_instrumenter.h>"))::f.globals
