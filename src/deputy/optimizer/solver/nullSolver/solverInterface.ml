(*
 * solverInterface.ml
 *
 * This is the interface of a null solver provided to the Deputy optimizer
 *
 *)

exception NYI of string

let is_real = false

let getTranslator (rl : int) = raise(NYI "null solver")

(* This is the interface exposed to doptim.ml *)
(* check if (e1 op e2) is valid in state s *)
let valid s op e1 e2 = raise(NYI "null solver")

