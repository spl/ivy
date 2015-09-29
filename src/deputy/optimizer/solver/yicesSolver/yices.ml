(*
 * yices.ml
 * 
 * This file contains external declarations for
 * calls into yices.
 *
 *)

type yices_expr
type yices_type
type yices_var_decl
type yices_context
type yices_model
type yices_var_decl_iterator
type yices_ast


(*
 *          Set some options
 *)
external set_verbosity : int -> unit = "caml_yices_set_verbosity"
external version : unit -> string = "caml_yices_version"
external set_max_num_conflicts_in_maxsat_iteration : int -> unit =
    "caml_yices_set_max_num_conflicts_in_maxsat_iteration"
external enable_type_checker : bool -> unit = "caml_yices_enable_type_checker"
external set_max_num_iterations_in_maxsat : int -> unit =
    "caml_yices_set_max_num_iterations_in_maxsat"
external set_maxsat_initial_cost : int64 -> unit =
    "caml_yices_set_maxsat_initial_cost"
external set_arith_only : bool -> unit = "caml_yices_set_arith_only"
external enable_log_file : string -> unit = "caml_yices_enable_log_file"

(*
 *          Context manipulation
 *)
external mk_context : unit -> yices_context = "caml_yices_mk_context"
external del_context : yices_context -> unit = "caml_yices_del_context"
external reset_context : yices_context -> unit = "caml_yices_reset"
external dump_context : yices_context -> unit = "caml_yices_dump_context"
external push_context : yices_context -> unit = "caml_yices_push"
external pop_context : yices_context -> unit = "caml_yices_pop"
external assert_expr : yices_context -> yices_expr -> unit =
    "caml_yices_assert"
external assert_expr_weighted : yices_context -> yices_expr -> int64 -> int =
    "caml_yices_assert_weighted"
external assert_expr_retractable : yices_context -> yices_expr -> int =
    "caml_yices_assert_retractable"
external retract_expr : yices_context -> int -> unit = "caml_yices_retract"
external inconsistent_context : yices_context -> bool = "caml_yices_inconsistent"
external check_context : yices_context -> int = "caml_yices_check"
external find_weighted_model : yices_context -> int -> int =
    "caml_yices_find_weighted_model"
external max_sat : yices_context -> int = "caml_yices_max_sat"
external max_sat_cost_leq : yices_context -> int64 -> int =
    "caml_yices_max_sat_cost_leq"
external get_model : yices_context -> yices_model list = "caml_yices_get_model"

(*
 *          Functions for Models
 *)
external get_value : yices_model -> yices_var_decl -> int =
    "caml_yices_get_value"
external get_int_value : yices_model -> yices_var_decl -> (bool * int) =
    "caml_yices_get_int_value"
external get_arith_value : yices_model -> yices_var_decl -> (bool * int * int) =
    "caml_yices_get_arith_value"
external get_double_value : yices_model -> yices_var_decl -> (bool * float) =
    "caml_yices_get_double_value"
external get_bitvector_value : yices_model -> yices_var_decl -> int -> (bool * int array) =
    "caml_yices_get_bitvector_value"
external get_assertion_value : yices_model -> int -> int =
    "caml_yices_get_assertion_value"
external display_model : yices_model -> unit = "caml_yices_display_model"
external get_cost : yices_model -> int64 = "caml_yices_get_cost"
external get_cost_as_double : yices_model -> float =
    "caml_yices_get_cost_as_double"

(*
 *          Expression Building
 *)
external mk_true : yices_context -> yices_expr = "caml_yices_mk_true"
external mk_false : yices_context -> yices_expr = "caml_yices_mk_false"
external mk_bool_var : yices_context -> string -> yices_expr =
    "caml_yices_mk_bool_var"
external mk_fresh_bool_var : yices_context -> yices_expr =
    "caml_yices_mk_fresh_bool_var"
external get_var_decl : yices_expr -> yices_var_decl = "caml_yices_get_var_decl"
external mk_bool_var_decl : yices_context -> string -> yices_var_decl =
    "caml_yices_mk_bool_var_decl"
external get_var_decl_name : yices_var_decl -> string =
    "caml_yices_get_var_decl_name"
external mk_bool_var_from_decl : yices_context -> yices_var_decl -> yices_expr =
    "caml_yices_mk_bool_var_from_decl"
external mk_or : yices_context -> yices_expr list -> int -> yices_expr =
    "caml_yices_mk_or"
external mk_and : yices_context -> yices_expr list -> int -> yices_expr =
    "caml_yices_mk_and"
external mk_eq : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_eq"
external mk_diseq : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_diseq"
external mk_ite : yices_context -> yices_expr -> yices_expr -> yices_expr ->
                  yices_expr = "caml_yices_mk_ite"
external mk_not : yices_context -> yices_expr -> yices_expr =
    "caml_yices_mk_not"
external create_var_decl_iterator : yices_context -> yices_var_decl_iterator =
    "caml_yices_create_var_decl_iterator"
external iterator_has_next : yices_var_decl_iterator -> bool =
    "caml_yices_iterator_has_next"
external iterator_next : yices_var_decl_iterator -> yices_var_decl =
    "caml_yices_iterator_next"
external iterator_reset : yices_var_decl_iterator -> unit =
    "caml_yices_iterator_reset"
external del_iterator : yices_var_decl_iterator -> unit =
    "caml_yices_del_iterator"
external mk_type : yices_context -> string -> yices_type = "caml_yices_mk_type"
external mk_bv_type : yices_context -> int -> yices_type =
    "caml_yices_mk_bitvector_type"
external mk_var_decl : yices_context -> string -> yices_type -> yices_var_decl =
    "caml_yices_mk_var_decl"
external mk_var_from_decl : yices_context -> yices_var_decl -> yices_expr =
    "caml_yices_mk_var_from_decl"
external get_var_decl_from_name : yices_context -> string -> yices_var_decl list =
    "caml_yices_get_var_decl_from_name"
external mk_num : yices_context -> int -> yices_expr = "caml_yices_mk_num"
external mk_num_from_string : yices_context -> string -> yices_expr =
    "caml_yices_mk_num_from_string"
external mk_sum : yices_context -> yices_expr list -> int -> yices_expr =
    "caml_yices_mk_sum"
external mk_sub : yices_context -> yices_expr list -> int -> yices_expr =
    "caml_yices_mk_sub"
external mk_mul : yices_context -> yices_expr list -> int -> yices_expr =
    "caml_yices_mk_mul"
external mk_lt : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_lt"
external mk_le : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_le"
external mk_gt : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_gt"
external mk_ge : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_ge"

(*
 *           Bit-vector expression construction
 *)
external mk_bv_constant : yices_context -> int -> int -> yices_expr =
    "caml_yices_mk_bv_constant"
external mk_bv_add : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_add"
external mk_bv_sub : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_sub"
external mk_bv_mul : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_mul"
external mk_bv_minus : yices_context -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_minus"
external mk_bv_concat : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_concat"
external mk_bv_and : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_and"
external mk_bv_or : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_or"
external mk_bv_xor : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_xor"
external mk_bv_not : yices_context -> yices_expr -> yices_expr =
    "caml_yices_mk_bv_not"
external mk_bv_extract : yices_context -> int -> int -> yices_expr =
    "caml_yices_mk_bv_extract"
external mk_bv_sign_extend : yices_context -> yices_expr -> int -> yices_expr =
    "caml_yices_mk_bv_sign_extend"
external mk_bv_shift_left0 : yices_context -> yices_expr -> int -> yices_expr =
    "caml_yices_bv_shift_left0"
external mk_bv_shift_left1 : yices_context -> yices_expr -> int -> yices_expr =
    "caml_yices_bv_shift_left1"
external mk_bv_shift_right0 : yices_context -> yices_expr -> int -> yices_expr =
    "caml_yices_bv_shift_right0"
external mk_bv_shift_right1 : yices_context -> yices_expr -> int -> yices_expr =
    "caml_yices_bv_shift_right1"
external mk_bv_lt : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_lt"
external mk_bv_le : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_le"
external mk_bv_gt : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_gt"
external mk_bv_ge : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_ge"
external mk_bv_slt : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_slt"
external mk_bv_sle : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_sle"
external mk_bv_sgt : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_sgt"
external mk_bv_sge : yices_context -> yices_expr -> yices_expr -> yices_expr =
    "caml_yices_bv_sge"

external pp_expr : yices_expr -> unit = "caml_yices_pp_expr"
