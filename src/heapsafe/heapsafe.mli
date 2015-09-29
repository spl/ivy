open Cil

val init : unit -> unit
val root : file -> global -> bool
val preprocess : file -> unit
val process : file -> file
val cleanup: unit -> unit
