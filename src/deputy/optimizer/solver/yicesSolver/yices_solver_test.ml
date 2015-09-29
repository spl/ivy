
open Printf

module Y = Yices

let test () =
    (*Y.enable_type_checker true;
    Y.set_arith_only true;*)
    let yc = Y.mk_context () in
    let intType = Y.mk_type yc "int" in
    let x = Y.mk_var_decl yc "x" intType in
    let y = Y.mk_var_decl yc "y" intType in
    let xe = Y.mk_var_from_decl yc x in
    let ye = Y.mk_var_from_decl yc y in

    let ten = Y.mk_num yc 10 in
    let xpy = Y.mk_sum yc [xe;ye] 2 in
    let xpygtten = Y.mk_gt yc xpy ten in
    let e = xpygtten in
    (*let e = Y.mk_not yc xpygtten in*)
    (*let e = Y.mk_gt yc xe (Y.mk_num yc 10) in*)

    Y.assert_expr yc e;
    Y.dump_context yc;
    match Y.check_context yc with
    | 1 -> begin
        let m = Y.get_model yc in
        match m with
        | [] -> print_string "Sat but no model\n"
        | m :: _ -> begin
            print_string "Satisfiable. Printing model:\n";
            let it = Y.create_var_decl_iterator yc in (* XXX: why doesn't this work??? *)
            let rec loop () =
                if Y.iterator_has_next it then begin
                    let vd = Y.iterator_next it in
                    let (res, v) = Y.get_int_value m vd in
                    if res then begin
                        let name = Y.get_var_decl_name vd in
                         printf "model: %s -> %d\n" name v;
                        loop ()
                    end else begin
                        let name = Y.get_var_decl_name vd in
                        printf "model: %s -> undef\n" name;
                        loop ()
                    end
                end else begin
                    printf "model: done\n";
                    ()
                end
            in
            loop ();
            Y.del_iterator it;
            ()
        end
    end
    | 0 -> print_string "Not Satisfiable\n"
    | -1 -> print_string "Couldn't determine anything\n"
    | _ -> print_string "Internal Error\n"


let _ = test ();


