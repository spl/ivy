
(*
 * solverInterface.ml
 *
 * This is the interface of cvcl provided to the Deputy optimizer
 *
 *)

open Pretty

module E = Errormsg
module C = Cvcl
module D = Dsolverfront

exception NYI of string

let is_real = true

let getCounterExample vc () =
    let el = C.getCounterExample vc in
    List.fold_left (fun l e ->
        C.printExpr vc e;
        if not(C.isEq e) then begin
            ignore(E.log "SI.getCounterExample: not an equality\n");
            l
        end else begin
            (*ignore(E.log "SI.getCounterExample: %s is a %s, and %s is a %s\n"
                (C.exprString (C.getChild e 0))
                (exprKindString vc (C.getChild e 0))
                (C.exprString (C.getChild e 1))
                (exprKindString vc (C.getChild e 1)));*)
                (C.exprString (C.getChild e 0), C.getInt (C.getChild e 1)) :: l
        end)
    [] el

let isValid vc e : (bool * (string * int) list) =
  ignore(E.log "Checking: %s\n" (C.exprString e));
  C.push vc;
  let r = C.query vc e in
  let ce = if not r then getCounterExample vc () else [] in
  C.pop vc;
  ignore(E.log "Returned: %s\n" (if r then "valid" else "not valid"));
  (r, ce)

let isValidWithAssumptions vc al e : (bool * (string * int) list) =
    ignore(E.log "Checking: %s with assuptions\n" (C.exprString e));
    List.iter (fun a -> ignore(E.log "\t%s\n" (C.exprString a))) al;
    C.push vc;
    List.iter (C.assertFormula vc) al;
    let r = C.query vc e in
    ignore(E.log "Returned: %s\n" (if r then "valid" else "not valid"));
    let ce = if not r then getCounterExample vc () else [] in
    C.pop vc;
    (r, ce)


let cvcl_bv_translator vc =
{
 D.mkTrue   = (fun () -> C.trueExpr vc);
 D.mkFalse  = (fun () -> C.falseExpr vc);

 D.mkAnd    = C.andExpr vc;
 D.mkOr     = C.orExpr vc;
 D.mkNot    = C.notExpr vc;
 D.mkIte    = C.iteExpr vc;
 D.mkImp    = C.impliesExpr vc;

 D.mkEq     = C.eqExpr vc;
 D.mkNe     = (fun e1 e2 -> C.notExpr vc (C.eqExpr vc e1 e2));
 D.mkLt     = C.sbvLtExpr vc;
 D.mkLe     = C.sbvLeExpr vc;
 D.mkGt     = C.sbvGtExpr vc;
 D.mkGe     = C.sbvGeExpr vc;

 D.mkPlus   = C.bv32PlusExpr vc;
 D.mkTimes  = C.bv32MultExpr vc;
 D.mkMinus  = C.bv32MinusExpr vc;
 D.mkDiv    = (fun _ _ -> raise(NYI "mkDiv"));
 D.mkMod    = (fun _ _ -> raise(NYI "mkMod"));
 D.mkLShift = C.bvVar32LeftShiftExpr vc;
 D.mkRShift = C.bvVar32RightShiftExpr vc;
 D.mkBAnd   = C.bvAndExpr vc;
 D.mkBXor   = C.bvXorExpr vc;
 D.mkBOr    = C.bvOrExpr vc;

 D.mkNeg    = C.bvUMinusExpr vc;
 D.mkCompl  = C.bvXorExpr vc (C.bv32ConstExprFromInt vc 0);

 D.mkVar    = (fun s -> C.varExpr vc s (C.bv32Type vc));
 D.mkConst  = C.bv32ConstExprFromInt vc;

 D.isValidWithAssumptions = isValidWithAssumptions vc;
 D.isValid  = isValid vc;
}

let andExpr vc e1 e2 =
  if not(C.compare_exprs e1 (C.falseExpr vc)) ||
     not(C.compare_exprs e2 (C.falseExpr vc))
  then C.falseExpr vc
  else if not(C.compare_exprs e1 (C.trueExpr vc))
  then e2
  else if not(C.compare_exprs e2 (C.trueExpr vc))
  then e1
  else C.andExpr vc e1 e2

let orExpr vc e1 e2 =
  if not(C.compare_exprs e1 (C.falseExpr vc)) ||
     not(C.compare_exprs e2 (C.falseExpr vc))
  then C.trueExpr vc
  else if not(C.compare_exprs e1 (C.falseExpr vc))
  then e2
  else if not(C.compare_exprs e2 (C.falseExpr vc))
  then e1
  else C.orExpr vc e1 e2

let notExpr vc e =
  if not(C.compare_exprs e (C.falseExpr vc))
  then C.trueExpr vc
  else if not(C.compare_exprs e (C.trueExpr vc))
  then C.falseExpr vc
  else C.notExpr vc e

let iteExpr vc e1 e2 e3 =
  if not(C.compare_exprs e1 (C.trueExpr vc))
  then e2
  else if not(C.compare_exprs e1 (C.falseExpr vc))
  then e3
  else C.iteExpr vc e1 e2 e3

let impliesExpr vc e1 e2 =
  if not(C.compare_exprs e1 (C.trueExpr vc))
  then e2
  else if not(C.compare_exprs e1 (C.falseExpr vc))
  then C.trueExpr vc
  else C.impliesExpr vc e1 e2


let eqExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    if e1 = e2
    then C.trueExpr vc
    else C.falseExpr vc
  else C.eqExpr vc e1 e2

let neExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    if not(e1 = e2)
    then C.trueExpr vc
    else C.falseExpr vc
  else C.notExpr vc (C.eqExpr vc e1 e2)

let ltExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    if e1 < e2
    then C.trueExpr vc
    else C.falseExpr vc
  else C.ltExpr vc e1 e2

let leExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    if e1 <= e2
    then C.trueExpr vc
    else C.falseExpr vc
  else C.leExpr vc e1 e2

let gtExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    if e1 > e2
    then C.trueExpr vc
    else C.falseExpr vc
  else C.gtExpr vc e1 e2

let geExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    if e1 >= e2
    then C.trueExpr vc
    else C.falseExpr vc
  else C.geExpr vc e1 e2

let plusExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    C.ratExpr vc (e1 + e2) 1
  else C.plusExpr vc e1 e2

let timesExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    C.ratExpr vc (e1 * e2) 1
  else C.multExpr vc e1 e2

let minusExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    C.ratExpr vc (e1 - e2) 1
  else C.minusExpr vc e1 e2

let divideExpr vc e1 e2 =
  if C.isConst e1 && C.isConst e2 then
    let e1 = C.getInt e1 in
    let e2 = C.getInt e2 in
    C.ratExpr vc (e1 / e2) 1
  else C.divideExpr vc e1 e2

let uminusExpr vc e =
  if C.isConst e then
    let e = C.getInt e in
    C.ratExpr vc (-e) 1
  else C.uminusExpr vc e

let exprKindString vc e =
    C.getKindString vc (C.getKind e)

let cvcl_translator vc =
{
 D.mkTrue   = (fun () -> C.trueExpr vc);
 D.mkFalse  = (fun () -> C.falseExpr vc);

 D.mkAnd    = andExpr vc;
 D.mkOr     = orExpr vc;
 D.mkNot    = notExpr vc;
 D.mkIte    = iteExpr vc;
 D.mkImp    = impliesExpr vc;

 D.mkEq     = eqExpr vc;
 D.mkNe     = neExpr vc;
 D.mkLt     = ltExpr vc;
 D.mkLe     = leExpr vc;
 D.mkGt     = gtExpr vc;
 D.mkGe     = geExpr vc;

 D.mkPlus   = plusExpr vc;
 D.mkTimes  = timesExpr vc;
 D.mkMinus  = minusExpr vc;
 D.mkDiv    = divideExpr vc;
 D.mkMod    = (fun _ _ -> raise(NYI "mkMod"));
 D.mkLShift = (fun _ _ -> raise(NYI "mkLShift"));
 D.mkRShift = (fun _ _ -> raise(NYI "mkRShift"));
 D.mkBAnd   = (fun _ _ -> raise(NYI "mkBAnd"));
 D.mkBXor   = (fun _ _ -> raise(NYI "mkBXor"));
 D.mkBOr    = (fun _ _ -> raise(NYI "mkBOr"));

 D.mkNeg    = uminusExpr vc;
 D.mkCompl  = (fun _ -> raise(NYI "mkCompl"));

 D.mkVar    = (fun s -> C.varExpr vc s (C.intType vc));
 D.mkConst  = (fun i -> C.ratExpr vc i 1);

 D.isValidWithAssumptions = isValidWithAssumptions vc;
 D.isValid  = isValid vc;
}

let curVC = ref None

let getBVTranslator rl =
  match !curVC with
  | Some vc -> cvcl_bv_translator vc
  | None -> begin
      let flags = C.createFlags () in
      let vc = C.createVC flags in
      C.setResourceLimit vc rl;
      curVC := (Some vc);
      cvcl_bv_translator vc
  end

(* rl is the resource limit for the solver if supported.
 * rl =  0 => no limits
 * rl =  1 => don't use this.
 * rl >= 2 => OK *)
let getTranslator (rl : int) =
  match !curVC with
  | Some vc -> cvcl_translator vc
  | None -> begin
      let flags = C.createFlags () in
      let vc = C.createVC flags in
      C.setResourceLimit vc rl;
      curVC := (Some vc);
      cvcl_translator vc
  end

(* This is the interface exposed to doptim.ml *)
(* check if (e1 op e2) is valid in state s *)
(*
let valid s op e1 e2 =
  ignore(E.log "calling the solver: %a <? %a\n" D.Can.d_t e1 D.Can.d_t e2);
  try
    let r = D.valid (getTranslator()) s op e1 e2 in
    ignore(E.log "the solver returned!\n");
    r
  with NYI s ->
    ignore(E.log "the solver raised an exception: %s\n" s);
    false
*)
