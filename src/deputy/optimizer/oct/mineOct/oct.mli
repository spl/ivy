(* oct_common.mli
   Abstract semantics functions.

   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/
   
   Copyright (C) Antoine Mine' 2000-2002  
*)


(* initialization *)
external init: unit -> bool = "ocaml_oct_init"


(* numerical domain *)
type num
type vnum

external num_of_int: int -> num = "ocaml_num_int"
external num_of_frac: int*int -> num = "ocaml_num_frac"
external num_of_float: float -> num = "ocaml_num_float"
external num_infty: unit -> num = "ocaml_num_infty"

external vnum_of_int: int array -> vnum = "ocaml_vnum_int"
external vnum_of_frac: int*int array -> vnum = "ocaml_vnum_frac"
external vnum_of_float: float array -> vnum = "ocaml_vnum_float"

external vnum_of_int_opt: int option array -> vnum = "ocaml_vnum_int_opt"
external vnum_of_frac_opt: int*int option array -> vnum = "ocaml_vnum_frac_opt"

external string_of_num: num -> string = "ocaml_num_string"
external string_of_vnum: vnum -> int -> string = "ocaml_vnum_string"
external vnum_length: vnum -> int = "ocaml_vnum_length"

external int_of_num: num -> int option = "ocaml_int_num"
external frac_of_num: num -> int*int option = "ocaml_frac_num"
external float_of_num: num -> float = "ocaml_float_num"

external int_of_vnum: vnum -> int option array = "ocaml_int_vnum"
external frac_of_vnum: vnum -> int*int option array = "ocaml_frac_vnum"
external float_of_vnum: vnum -> float array = "ocaml_float_vnum"

val fnumprinter: Format.formatter -> num -> unit
val fvnumprinter: Format.formatter -> vnum -> unit
val numprinter: num -> unit
val vnumprinter: vnum -> unit

(* boolean lattice *)
type tbool = Bottom | True | False | Top

(* abstract types of regular & minimized octagons *)
type oct
type moct

(* octagon creation *)
external empty:    int -> oct = "ocaml_oct_empty"
external universe: int -> oct = "ocaml_oct_universe"

(* query functions *)
external dim:           oct -> int = "ocaml_oct_dim"
external nbconstraints: oct -> int = "ocaml_oct_nbconstraints"
external get_elem:      oct -> int -> int -> num = "ocaml_oct_get_elem"

(* tests *)
external is_empty: oct -> bool = "ocaml_oct_is_empty"
external is_empty_lazy: oct -> tbool= "ocaml_oct_is_empty_lazy"
external is_universe: oct -> bool= "ocaml_oct_is_universe"
external is_included_in: oct -> oct -> bool= "ocaml_oct_is_included_in"
external is_included_in_lazy: 
  oct -> oct -> tbool= "ocaml_oct_is_included_in_lazy"
external is_equal: oct -> oct -> bool= "ocaml_oct_is_equal"
external is_equal_lazy: oct -> oct -> tbool= "ocaml_oct_is_equal_lazy"
external is_in: oct -> vnum -> bool= "ocaml_oct_is_in"

(* operators *)
type wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum | PreWiden
external inter: oct -> oct -> oct = "ocaml_oct_inter"
external union: oct -> oct -> oct = "ocaml_oct_union"
external widening: oct -> oct -> wident -> oct = "ocaml_oct_widening"
external narrowing: oct -> oct -> oct = "ocaml_oct_narrowing"

(* transfer function *)
type constr = 
    PX of int*num         (*   x  <= c *)
  | MX of int*num         (*  -x  <= c *)
  | PXPY of int*int*num   (*  x+y <= c *)
  | PXMY of int*int*num   (*  x-y <= c *)
  | MXPY of int*int*num   (* -x+y <= c *)
  | MXMY of int*int*num   (* -x-y <= c *)
external forget: oct -> int -> oct = "ocaml_oct_forget"
external add_bin_constraints: oct -> constr array -> oct = "ocaml_oct_add_bin_constraints"
external assign_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_assign_variable"
external substitute_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_substitute_variable"
external add_constraint: oct -> vnum -> oct = "ocaml_oct_add_constraint"
external interv_assign_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_interv_assign_variable"
external interv_add_constraint: 
  oct -> vnum -> oct = "ocaml_oct_interv_add_constraint"
external interv_substitute_var: 
  oct -> int -> vnum -> oct = "ocaml_oct_interv_substitute_variable"
external time_flow:
  oct -> num -> num -> vnum -> oct = "ocaml_oct_time_flow"

(* change of dimensions *)
external add_dims_and_embed: 
  oct -> int -> oct = "ocaml_oct_add_dimensions_and_embed"
external add_dims_and_project: 
  oct -> int -> oct = "ocaml_oct_add_dimensions_and_project"
external del_dims: oct -> int -> oct = "ocaml_oct_remove_dimensions"

(* change of dimensions at arbitrary positions *)
type dimsup = { pos:int; nbdims:int; }
external add_dims_and_embed_multi: 
    oct -> dimsup array -> oct = "ocaml_oct_add_dimensions_and_embed_multi"
external add_dims_and_project_multi: 
    oct -> dimsup array -> oct = "ocaml_oct_add_dimensions_and_project_multi"
external del_dims_multi: 
    oct -> dimsup array -> oct = "ocaml_oct_remove_dimensions_multi"

(* change of dimensions with permutation *)
external add_permute_dims_and_embed: 
  oct -> int -> int array -> oct = "ocaml_oct_add_permute_dimensions_and_embed"
external add_permute_dims_and_project: 
  oct -> int -> int array -> oct = "ocaml_oct_add_permute_dimensions_and_project"
external permute_del_dims: 
  oct -> int -> int array -> oct = "ocaml_oct_permute_remove_dimensions"

(* normal form *)
external close: oct -> oct = "ocaml_oct_close"

(* interval functions *)
external get_box: oct -> vnum = "ocaml_oct_get_box"
external from_box: vnum -> oct = "ocaml_oct_from_box"
external get_bounds: oct -> int -> num*num = "ocaml_oct_get_bounds"
external set_bounds: oct -> int -> num*num -> oct = "ocaml_oct_set_bounds"

(* preturbation *)
external add_epsilon: oct -> num -> oct = "ocaml_oct_add_epsilon"
external add_epsilon_max: oct -> num -> oct = "ocaml_oct_add_epsilon_max"
external add_epsilon_bin: oct -> oct -> num -> oct ="ocaml_oct_add_epsilon_bin"

(* utilities *)
external print: oct -> unit = "ocaml_oct_print"

(* minimal form *)
external m_to_oct: moct -> oct = "ocaml_oct_m_to_oct"
external m_from_oct: oct -> moct = "ocaml_oct_m_from_oct"
external m_print: moct -> unit = "ocaml_oct_m_print"
external m_dim: moct -> int = "ocaml_oct_m_dim"
external m_is_empty: moct -> bool = "ocaml_oct_m_is_empty"
external m_is_equal: moct -> moct -> bool = "ocaml_oct_m_is_equal"
external m_get_elem:  moct -> int -> int -> num = "ocaml_oct_m_get_elem"

(* top-level prettry_printers *)

val foctprinter: (int -> string) -> Format.formatter -> oct -> unit
val octprinter: (int -> string) -> oct -> unit
val fmoctprinter: (int -> string) -> Format.formatter -> moct -> unit
val moctprinter: (int -> string) -> moct -> unit

(* prints only constraints that differ between two two octagons *)

(* only prints _new_ constraints in the difference *)
val foctnewprinter: (int -> string) -> Format.formatter -> oct -> oct -> unit

(* prints both old and new constraints in the difference *)
val foctdiffprinter: (int -> string) -> Format.formatter -> oct -> oct -> unit


(* utilities *)
external memprint: unit -> unit = "ocaml_oct_memprint"
external timeprint: unit -> unit = "ocaml_oct_timeprint"

