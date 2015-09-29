(*
 * dsolverfront.ml
 *
 * Translate Doptim.absState and Doptim.Can.t
 * into a conjunction of constraints.
 *
 *
 *)

open Cil
open Expcompare
open Pretty
open Dutil

module H = Hashtbl
(*module DFS = Dflowsens*)
module DCE = Dcanonexp
module Can = DCE.Can

(*
type absState = DFS.absState
let emptyAbsState = DFS.top
*)

type 'a translator =
{
 mkTrue   : unit -> 'a;
 mkFalse  : unit -> 'a;

 mkAnd    : 'a -> 'a -> 'a;
 mkOr     : 'a -> 'a -> 'a;
 mkNot    : 'a -> 'a;
 mkIte    : 'a -> 'a -> 'a -> 'a;
 mkImp    : 'a -> 'a -> 'a;

 mkEq     : 'a -> 'a -> 'a;
 mkNe     : 'a -> 'a -> 'a;
 mkLt     : 'a -> 'a -> 'a;
 mkLe     : 'a -> 'a -> 'a;
 mkGt     : 'a -> 'a -> 'a;
 mkGe     : 'a -> 'a -> 'a;

 mkPlus   : 'a -> 'a -> 'a;
 mkTimes  : 'a -> 'a -> 'a;
 mkMinus  : 'a -> 'a -> 'a;
 mkDiv    : 'a -> 'a -> 'a;
 mkMod    : 'a -> 'a -> 'a;
 mkLShift : 'a -> 'a -> 'a;
 mkRShift : 'a -> 'a -> 'a;
 mkBAnd   : 'a -> 'a -> 'a;
 mkBXor   : 'a -> 'a -> 'a;
 mkBOr    : 'a -> 'a -> 'a;

 mkNeg    : 'a -> 'a;
 mkCompl  : 'a -> 'a;

 mkVar    : string -> 'a;
 mkConst  : int -> 'a;

 isValidWithAssumptions : 'a list -> 'a -> (bool * (string * int) list);
 isValid  : 'a -> (bool * (string * int) list);
}

let baseFVarName = "FV"

let nameMakerMaker base =
  let c = ref 0 in
  (fun () ->
    incr c;
    base^(Int32.to_string (Int32.of_int !c)))

let fvNameMaker = nameMakerMaker baseFVarName

(* map expressions that we can't
 * translate to variable names *)
(*let unkExpHash = H.create 100*)

(* if e isn't mapped to a fv then
 * make one for it and return it *)
(*
let mkUnk t (e:exp) =
  try H.find unkExpHash e
  with Not_found -> begin
    let fv = t.mkVar (fvNameMaker()) in
    H.add unkExpHash e fv;
    fv
  end
*)

exception NYI

let transUnOp t op e =
  match op with
  | Neg -> t.mkNeg e
  | BNot -> t.mkCompl e
  | _ -> raise NYI

let transBinOp t op e1 e2 =
  match op with
  | PlusA | PlusPI | IndexPI -> t.mkPlus e1 e2
  | MinusA | MinusPI | MinusPP -> t.mkMinus e1 e2
  | Mult -> t.mkTimes e1 e2
  | Div -> t.mkDiv e1 e2
  | Mod -> t.mkMod e1 e2
  | Shiftlt -> t.mkLShift e1 e2
  | Shiftrt -> t.mkRShift e1 e2
  | Lt -> t.mkLt e1 e2
  | Gt -> t.mkGt e1 e2
  | Le -> t.mkLe e1 e2
  | Ge -> t.mkGe e1 e2
  | Eq -> t.mkEq e1 e2
  | Ne -> t.mkNe e1 e2
  | BAnd -> t.mkBAnd e1 e2
  | BXor -> t.mkBXor e1 e2
  | BOr -> t.mkBOr e1 e2
  | LAnd -> t.mkAnd e1 e2
  | LOr -> t.mkOr e1 e2


let rec transCilExp t (e:exp) =
  (*ignore(E.log "DSF.transCilExp: %a\n" d_exp e);*)
  match e with
  | Const(CInt64(v,k,so)) -> t.mkConst (Int64.to_int v)
  | Const _ -> raise NYI
  | Lval(Var vi,NoOffset) when vi.vname = "_ZERO_" ->
      t.mkConst 0
  | Lval l -> t.mkVar (sprint 80 (d_lval () l))
  | UnOp(op,e,_) -> 
      let e = transCilExp t e in
      transUnOp t op e
  | BinOp(op,e1,e2,_) ->
      let e1 = transCilExp t e1 in
      let e2 = transCilExp t e2 in
      transBinOp t op e1 e2
  | SizeOf typ -> t.mkConst ((bitsSizeOf typ)/8)
  | SizeOfE e -> transCilExp t (SizeOf(typeOf e))
  | SizeOfStr s -> t.mkConst (1 + String.length s)
  | AlignOf typ -> t.mkConst (alignOf_int typ)
  | AlignOfE e -> transCilExp t (AlignOf(typeOf e))
  | CastE(typ,e) -> transCilExp t e
	(* Cast should check if signed type, and if so, make an ite term *)
  | AddrOf lv -> t.mkVar (sprint 80 (d_exp () e))
  | StartOf lv -> t.mkVar (sprint 80 (d_exp () e))


(* 'a translator -> Doptim.Can.t -> 'a *)
let transCan t (cane:  Can.t) =
  let cExp = t.mkConst (Int64.to_int cane.Can.ct) in
  List.fold_left (fun (te,ce) (c, ue) ->
    let f = t.mkConst (Int64.to_int c) in
    let ue' = transCilExp t ue in
    let tc = 
      match typeOf ue with
      | TInt(ku,_) -> t.mkLe (t.mkConst 0) ue'
      | TPtr(_,_) -> t.mkLe (t.mkConst 0) ue'
      | _ -> t.mkTrue ()
    in
    let tm = t.mkTimes f ue' in
    (t.mkPlus te tm,t.mkAnd ce tc)) (cExp,t.mkTrue()) cane.Can.cf
  
(* 'a translator -> Doptim.absState -> 'a *)
(*
let transAbsState t (state: DFS.absState) =
  List.fold_left (fun e (x,c,y,_) ->
    let xe = transCilExp t (Lval x) in
    let ye = transCilExp t (Lval y) in
    let ce = t.mkConst (Int64.to_int c) in
    let te = 
      match typeOf(Lval x), typeOf(Lval y) with
      | TInt(kx,_), TInt(ky,_) ->
	  if not(isSigned kx) && not(isSigned ky)
	  then t.mkAnd (t.mkLe (t.mkConst 0) ye) (t.mkLe (t.mkConst 0) xe)
	  else t.mkTrue ()
      | TPtr(_,_), TPtr(_,_) ->
	  t.mkAnd (t.mkLe (t.mkConst 0) ye) (t.mkLe (t.mkConst 0) xe)
      | _,_ -> t.mkTrue ()
    in
    t.mkAnd te (t.mkAnd e (t.mkLe (t.mkPlus xe ce) ye)))
      (t.mkTrue()) state.DFS.ineqs

let valid t (state: absState)
            (op:    binop)
            (cane1: Can.t)
            (cane2: Can.t) 
  =
  let state = transAbsState t state in
  let (cane1,c1) = transCan t cane1 in
  let (cane2,c2) = transCan t cane2 in
  let cs = t.mkAnd state (t.mkAnd c1 c2) in
  let e = t.mkImp cs (transBinOp t op cane1 cane2) in
  t.isValid e
*)
