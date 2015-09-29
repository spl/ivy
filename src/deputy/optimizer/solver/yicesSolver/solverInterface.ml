(*
 * solverInterface.ml
 *
 * This is the interface of yices provided to the Deputy optimizer
 *
 *)

open Pretty

module E = Errormsg
module Y = Yices
module D = Dsolverfront
 
exception NYI of string

let is_real = true

let andExpr yc e1 e2 =
    Y.mk_and yc [e1;e2] 2

let orExpr yc e1 e2 =
    Y.mk_or yc [e1;e2] 2

let notExpr yc e1 =
    Y.mk_not yc e1

let iteExpr yc e1 e2 e3 =
    Y.mk_ite yc e1 e2 e3

let impliesExpr yc e1 e2 =
    orExpr yc (notExpr yc e1) e2

let eqExpr yc e1 e2 =
    Y.mk_eq yc e1 e2

let neExpr yc e1 e2 =
    Y.mk_diseq yc e1 e2

let ltExpr yc e1 e2 =
    Y.mk_lt yc e1 e2

let leExpr yc e1 e2 =
    Y.mk_le yc e1 e2

let gtExpr yc e1 e2 =
    Y.mk_gt yc e1 e2

let geExpr yc e1 e2 =
    Y.mk_ge yc e1 e2

let plusExpr yc e1 e2 =
    Y.mk_sum yc [e1;e2] 2

let minusExpr yc e1 e2 =
    Y.mk_sub yc [e1;e2] 2

let timesExpr yc e1 e2 =
    Y.mk_mul yc [e1;e2] 2

let uminusExpr yc e =
    Y.mk_sub yc [(Y.mk_num yc 0);e] 2

let varExpr yc name =
    match Y.get_var_decl_from_name yc name with
    | [] -> begin
        Y.mk_var_from_decl yc (Y.mk_var_decl yc name (Y.mk_type yc "int"))
    end
    | vd :: _ -> Y.mk_var_from_decl yc vd

let isValidWithAssumptions yc el e : (bool * (string * int) list) =
    Y.push_context yc;
    List.iter (Y.assert_expr yc) el;
    Y.assert_expr yc (notExpr yc e);
    Y.dump_context yc;
    match Y.check_context yc with
    | 1 -> begin
        ignore(E.log "SI: valid\n");
        let m = Y.get_model yc in
        match m with
        | [] -> begin
            ignore(E.log "SI: model not available\n");
            (false, [])
        end
        | m :: _ -> begin
            ignore(E.log "SI: model available:\n");
            (*Y.display_model m;*)
            let it = Y.create_var_decl_iterator yc in
            let rec loop sil =
                if Y.iterator_has_next it then begin
                    let vd = Y.iterator_next it in
                    let (res,v) = Y.get_int_value m vd in
                    if res then begin
                        let name = Y.get_var_decl_name vd in
                        ignore(E.log "SI: model: %s -> %d\n" name v);
                        loop ((name,v)::sil)
                    end else begin
                        let name = Y.get_var_decl_name vd in
                        ignore(E.log "SI: model: %s -> undef\n" name);
                        loop sil
                    end
                end else begin
                    ignore(E.log "SI:model: done\n");
                    sil
                end
            in
            let sil = loop [] in
            Y.del_iterator it;
            Y.pop_context yc;
            (false, sil)
        end
    end
    | 0 -> begin
        ignore(E.log "SI: invalid\n");
        Y.pop_context yc;
        (true, [])
    end
    | -1 -> begin
        ignore(E.log "SI: unknown\n");
        Y.pop_context yc;
        (false, [])
    end
    | _ -> begin
        ignore(E.log "SI: error\n");
        Y.pop_context yc;
        (false, [])
    end

let isValid yc e = isValidWithAssumptions yc [] e

let yices_translator yc =
{
 D.mkTrue   = (fun () -> Y.mk_true yc);
 D.mkFalse  = (fun () -> Y.mk_false yc);

 D.mkAnd    = andExpr yc;
 D.mkOr     = orExpr yc;
 D.mkNot    = notExpr yc;
 D.mkIte    = iteExpr yc;
 D.mkImp    = impliesExpr yc;

 D.mkEq     = eqExpr yc;
 D.mkNe     = neExpr yc;
 D.mkLt     = ltExpr yc;
 D.mkLe     = leExpr yc;
 D.mkGt     = gtExpr yc;
 D.mkGe     = geExpr yc;

 D.mkPlus   = plusExpr yc;
 D.mkTimes  = timesExpr yc;
 D.mkMinus  = minusExpr yc;
 D.mkDiv    = (fun _ _ -> raise(NYI "mkDiv"));
 D.mkMod    = (fun _ _ -> raise(NYI "mkMod"));
 D.mkLShift = (fun _ _ -> raise(NYI "mkLShift"));
 D.mkRShift = (fun _ _ -> raise(NYI "mkRShift"));
 D.mkBAnd   = (fun _ _ -> raise(NYI "mkBAnd"));
 D.mkBXor   = (fun _ _ -> raise(NYI "mkBXor"));
 D.mkBOr    = (fun _ _ -> raise(NYI "mkBOr"));

 D.mkNeg    = uminusExpr yc;
 D.mkCompl  = (fun _ -> raise(NYI "mkCompl"));

 D.mkVar    = varExpr yc;
 D.mkConst  = (fun i -> Y.mk_num yc i);

 D.isValidWithAssumptions = isValidWithAssumptions yc;
 D.isValid  = isValid yc;
}

let curYC = ref None

let getTranslator (rl : int) =
    match !curYC with
    | Some yc -> yices_translator yc
    | None  -> begin
        Y.set_arith_only true;
        Y.enable_log_file "yices.log.txt";
        let yc = Y.mk_context () in
        curYC := (Some yc);
        yices_translator yc
    end

let valid s op e1 e2 = raise(NYI "valid")
