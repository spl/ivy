(*
 * cvcl.ml
 *
 * This file contains external declarations for
 * calls into cvc lite
 *)

type vc
type context
type em
type flags
type expr
type op
type typ

(* create validity checker *)
external createVC : flags -> vc = "caml_vc_createValidityChecker"

(* create flags *)
external createFlags : unit -> flags = "caml_vc_createFlags"

(* destroy validity checker *)
external destroyVC : vc -> unit = "caml_vc_destroyValidityChecker"

(* delete flags *)
external deleteFlags : flags -> unit = "caml_vc_deleteFlags"

(* delete type *)
external deleteType : typ -> unit = "caml_vc_deleteType"

(* delete expr *)
external deleteExpr : expr -> unit = "caml_vc_deleteExpr"

(* delete op *)
external deleteOp : op -> unit = "caml_vc_deleteOp"

(* flag setting *)
external setBoolFlag : flags -> string -> int -> unit = 
  "caml_vc_setBoolFlag"
external setIntFlag : flags -> string -> int -> unit =
  "caml_vc_setIntFlag"
external setStringFlag : flags -> string -> string -> unit = 
  "caml_vc_setStringFlag"
external setStrSeqFlag : flags -> string -> string -> int -> unit =
  "caml_vc_setStrSeqFlag"

(* Basic Types *)
external boolType : vc -> typ = "caml_vc_boolType"
external realType : vc -> typ = "caml_vc_realType"
external intType  : vc -> typ = "caml_vc_intType"

(* Tuple Types *)
external tupleType2 : vc -> typ -> typ -> typ = "caml_vc_tupleType2"
external tupleType3 : vc -> typ -> typ -> typ -> typ = "caml_vc_tupleType3"
external tupleTypeN : vc -> typ array -> int -> typ = "caml_vc_tupleTypeN"

(* Record Types *)
external recordType1 : vc -> string -> typ -> typ =
  "caml_vc_recordType1"
external recordType2 : vc -> string -> typ -> string -> typ -> typ =
  "caml_vc_recordType2"
(*external recordType3 : vc -> string -> typ -> string -> typ -> string -> typ -> typ =
  "caml_vc_recordType3"*)
external recordTypeN : vc -> string array -> typ array -> int -> typ =
  "caml_vc_recordTypeN"

(* Array Type *)
external arrayType : vc -> typ -> typ -> typ = "caml_vc_arrayType"

(* SubRange Type *)
external subRangeType : vc -> int -> int -> typ = "caml_vc_subRangeType"

(* Function Types *)
external funType1 : vc -> typ -> typ -> typ = "caml_vc_funType1"
external funType2 : vc -> typ -> typ -> typ -> typ = "caml_vc_funType2"
external funType3 : vc -> typ -> typ -> typ -> typ -> typ =
  "caml_vc_funType3"
external funTypeN : vc -> typ array -> typ -> typ = "caml_vc_funTypeN"

(* User defined Types *)
external createType : vc -> string -> typ = "caml_vc_createType"
external lookupType : vc -> string -> typ = "caml_vc_lookupType"

(* Expression Manipulation *)
external varExpr : vc -> string -> typ -> expr = "caml_vc_varExpr"
external lookupVar : vc -> string -> typ -> expr = "caml_vc_lookupExpr"
external getType : vc -> expr -> typ = "caml_vc_getType"
external eqExpr : vc -> expr -> expr -> expr = "caml_vc_eqExpr"
external trueExpr : vc -> expr = "caml_vc_trueExpr"
external falseExpr : vc -> expr = "caml_vc_falseExpr"
external notExpr : vc -> expr -> expr = "caml_vc_notExpr"
external andExpr : vc -> expr -> expr -> expr = "caml_vc_andExpr"
external andExprN : vc -> expr array -> expr = "caml_vc_andExprN"
external orExpr : vc -> expr -> expr -> expr = "caml_vc_orExpr"
external orExprN : vc -> expr array -> expr = "caml_vc_orExprN"
external impliesExpr : vc -> expr -> expr -> expr = "caml_vc_impliesExpr"
external iffExpr : vc -> expr -> expr -> expr = "caml_vc_iffExpr"
external iteExpr : vc -> expr -> expr -> expr -> expr = "caml_vc_iteExpr"

(* Arithmetic Expressions *)
external ratExpr : vc -> int -> int -> expr = "caml_vc_ratExpr"
external ratExprFromStr : vc -> string -> string -> int -> expr =
  "caml_vc_ratExprFromStr"

external uminusExpr : vc -> expr -> expr = "caml_vc_uminusExpr"
external plusExpr : vc -> expr -> expr -> expr = "caml_vc_plusExpr"
external minusExpr : vc -> expr -> expr -> expr = "caml_vc_minusExpr"
external multExpr : vc -> expr -> expr -> expr = "caml_vc_multExpr"
external powExpr : vc -> expr -> expr -> expr = "caml_vc_powExpr"
external divideExpr : vc -> expr -> expr -> expr = "caml_vc_divideExpr"

external ltExpr : vc -> expr -> expr -> expr = "caml_vc_ltExpr"
external leExpr : vc -> expr -> expr -> expr = "caml_vc_leExpr"
external gtExpr : vc -> expr -> expr -> expr = "caml_vc_gtExpr"
external geExpr : vc -> expr -> expr -> expr = "caml_vc_geExpr"

(* Records *)
(* Arrays *)
(* Functions *)
(* Tuples *)
(* Quantifiers *)

(* Expr I/O *)
external printExpr : vc -> expr -> unit = "caml_vc_printExpr"
external printExprFile : vc -> expr -> int -> unit = 
  "caml_vc_printExprFile"

(* Contexts *)
external assertFormula : vc -> expr -> unit = "caml_vc_assertFormula"
external registerAtom : vc -> expr -> unit = "caml_vc_registerAtom"
external getImpliedLiteral : vc -> expr = "caml_vc_getImpliedLiteral"
external simplify : vc -> expr -> expr = "caml_vc_simplify"
external query : vc -> expr -> bool = "caml_vc_query"
external getCounterExample : vc -> expr list = "caml_vc_getCounterExample"
external setResourceLimit : vc -> int -> unit = "caml_vc_setResourceLimit"
external getProof : vc -> expr = "caml_vc_getProof"
external getProofOfFile : vc -> string -> expr = "caml_vc_getProofOfFile"
external push : vc -> unit = "caml_vc_push"
external pop : vc -> unit = "caml_vc_pop"
external popto : vc -> int -> unit = "caml_vc_popto"
external scopeLevel : vc -> int = "caml_vc_scopeLevel"

(* Util *)
external compare_exprs : expr -> expr -> bool = "caml_compare_exprs"
external exprString : expr -> string = "caml_exprString"
external typeString : typ -> string = "caml_typeString"
external isClosure : expr -> bool = "caml_isClosure"
external isQuantifier : expr -> bool = "caml_isQuantifier"
external isLambda : expr -> bool = "caml_isLambda"
external isVar : expr -> bool = "caml_isVar"
external isConst : expr -> bool = "caml_isConst"
external arity : expr -> int = "caml_arity"
external getKind : expr -> int = "caml_getKind"
external isEq : expr -> bool = "caml_isEq"
external getChild : expr -> int -> expr = "caml_getChild"
external getNumVars : expr -> expr = "caml_getNumVars"
external getVar : expr -> int -> expr = "caml_getVar"
external getBody : expr -> expr = "caml_getBody"
external getFun : vc -> expr -> expr = "caml_getFun"
external toExpr : typ -> expr = "caml_toExpr"
external getKindString : vc -> int -> string = "caml_vc_getKindString"
external getKindInt : vc -> string -> int = "caml_vc_getKindInt"
external getInt : expr -> int = "caml_getInt"
external getBVInt : expr -> int = "caml_getBVInt"
external getBVUnsigned : expr -> int = "caml_getBVUnsigned"

(* Print Statistics *)
external print_statistics : vc -> unit = "caml_print_statistics"

(* Bit Vector Operations *)
(* Construction *)
external bvType : vc -> int -> typ = "caml_vc_bvType"
external bv32Type : vc -> typ = "caml_vc_bv32Type"
external bvConstExprFromStr : vc -> string -> expr = 
  "caml_vc_bvConstExprFromStr"
external bvConstExprFromInt : vc -> int -> int -> expr =
  "caml_vc_bvConstExprFromInt"
external bv32ConstExprFromInt : vc -> int -> expr =
  "caml_vc_bv32ConstExprFromInt"
external bvConcatExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvConcatExpr"

(* Arithmetic *)
external bvPlusExpr : vc -> int -> expr -> expr -> expr =
  "caml_vc_bvPlusExpr"
external bv32PlusExpr : vc -> expr -> expr -> expr =
  "caml_vc_bv32PlusExpr"
external bvMinusExpr : vc -> int -> expr -> expr -> expr =
  "caml_vc_bvMinusExpr"
external bv32MinusExpr : vc -> expr -> expr -> expr =
  "caml_vc_bv32MinusExpr"
external bvMultExpr : vc -> int -> expr -> expr -> expr =
  "caml_vc_bvMultExpr"
external bv32MultExpr : vc -> expr -> expr -> expr =
  "caml_vc_bv32MultExpr"

external bvUMinusExpr : vc -> expr -> expr =
  "caml_vc_bvUMinusExpr"
external bvNotExpr : vc -> expr -> expr =
  "caml_vc_bvNotExpr"
external bvAndExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvAndExpr"
external bvOrExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvOrExpr"
external bvXorExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvXorExpr"

external bvLeftShiftExpr : vc -> int -> expr -> expr =
  "caml_vc_bvLeftShiftExpr"
external bvRightShiftExpr : vc -> int -> expr -> expr =
  "caml_vc_bvRightShiftExpr"
external bv32LeftShiftExpr : vc -> int -> expr -> expr =
  "caml_vc_bv32LeftShiftExpr"
external bv32RightShiftExpr : vc -> int -> expr -> expr =
  "caml_vc_bv32RightShiftExpr"

external bvVar32LeftShiftExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvVar32LeftShiftExpr"
external bvVar32RightShiftExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvVar32RightShiftExpr"
external bvVar32DivByPowOfTwoExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvVar32DivByPowOfTwoExpr"

external bvExtract : vc -> expr -> int -> int -> expr =
  "caml_vc_bvExtract"
external bvBoolExtract : vc -> expr -> int -> expr =
  "caml_vc_bvBoolExtract"

external bvSignExtend : vc -> expr -> int -> expr =
  "caml_vc_bvSignExtend"

(* unsigned comparators *)
external bvLtExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvLtExpr"
external bvLeExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvLeExpr"
external bvGtExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvGtExpr"
external bvGeExpr : vc -> expr -> expr -> expr =
  "caml_vc_bvGeExpr"

(* signed comparators *)
external sbvLtExpr : vc -> expr -> expr -> expr =
  "caml_vc_sbvLtExpr"
external sbvLeExpr : vc -> expr -> expr -> expr =
  "caml_vc_sbvLeExpr"
external sbvGtExpr : vc -> expr -> expr -> expr =
  "caml_vc_sbvGtExpr"
external sbvGeExpr : vc -> expr -> expr -> expr =
  "caml_vc_sbvGeExpr"

(* for C arrays *)
external bvCreateMemoryArray : vc -> string -> expr =
  "caml_vc_bvCreateMemoryArray"
external bvReadMemoryArray : vc -> expr -> expr -> int -> expr =
  "caml_vc_bvReadMemoryArray"
external bvWriteToMemoryArray : vc -> expr -> expr -> expr -> int -> expr =
  "caml_vc_bvWriteToMemoryArray"
