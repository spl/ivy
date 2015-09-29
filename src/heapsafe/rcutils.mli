open Cil

type types = {
    mutable rc_adjust:typ;
    mutable crc_adjust:typ;
    mutable type_t:typ;
    mutable cType_t:typ;
  }
and functions = {
    mutable rctrace:varinfo;
    mutable rcadjust:varinfo;
    mutable crcadjust:varinfo;
    mutable rcpush:varinfo;
    mutable rcpop:varinfo;
    mutable ipush:varinfo;
    mutable ipop:varinfo;
    mutable cipush:varinfo;
    mutable cipop:varinfo;
    mutable cpush:varinfo;
    mutable cpop:varinfo;
    mutable argpush:varinfo;
    mutable argnull:varinfo;
    mutable retpush:varinfo;
    mutable retnull:varinfo;
    mutable rctypeof:varinfo;
    mutable rcclear:varinfo;
    mutable arrayclear:varinfo;
    mutable arraycopy:varinfo;
  }

val rcTypes : types
val rcFunctions : functions
val dummyVar : varinfo

val i2s : instr -> stmt
val v2e : varinfo -> exp
val hasRctraceAttribute : attributes -> bool
val hasNorcAttribute : attributes -> bool
val hasNofreeAttribute : attributes -> bool
val hasBadfunAttribute : attributes -> bool
val isRctrace : typ -> bool
val isNofree : typ -> bool
val isNorc : typ -> bool
val isBadfun : typ -> bool
val isZero : exp -> bool
val isHeapsafeAttr : attribute -> bool
val isRcFunction : string -> bool

val typeContainsCountedPointers : typ -> bool
val typeContainsUnionWithCountedPointers : typ -> bool
val isRcInstr: instr -> bool
val onlyFunctions: (fundec -> location -> unit) -> global -> unit
val skipAdjustFunctions: (fundec -> location -> unit) -> fundec -> location -> unit
val isPointer: typ -> bool
val isOpenArraySize : exp option -> bool
val isOpenStruct : typ -> bool
val findFunction : file -> string -> typ -> varinfo * bool
val declareEarly : file -> varinfo -> unit
val voidConstPtrType : typ
val nofreeAttr : attributes
val nofreeFunction : exp -> bool
val initRc : file -> unit
val treatAsRoot : global -> bool
