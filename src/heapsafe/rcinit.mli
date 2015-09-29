open Cil

val clearLocals : file -> unit
val clearVariable : fundec -> varinfo -> location -> stmt list
val clearByType : fundec -> typ -> lval -> location -> stmt list
val fixSizeT : unit -> unit
