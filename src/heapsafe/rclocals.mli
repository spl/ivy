open Cil
open Usedef

val rcLocals : fundec -> varinfo list -> unit

val getLiveness : stmt -> VS.t
val getPostLiveness : stmt -> VS.t
