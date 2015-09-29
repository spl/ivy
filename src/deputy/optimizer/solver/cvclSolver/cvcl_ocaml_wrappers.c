/*

cvcl_ocaml_wrappers.c

This file contains wrappers for the C interface to CVCL
that are callable from ocaml code.

Search for XXX to find unimplemented things

*/

#include <c_interface.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

  // The commonly used kinds and the kinds needed by the parser.  All
  // these kinds are registered by the ExprManager and are readily
  // available for everyone else.
typedef enum {
  NULL_KIND = 0,
  // Generic LISP kinds for representing raw parsed expressions
  RAW_LIST, //!< May have any number of children >= 0
  //! Identifier is (ID (STRING_EXPR "name"))
  ID,
  // Leaf exprs
  STRING_EXPR,
  RATIONAL_EXPR,
  TRUE,
  FALSE,
  // Types
  BOOLEAN,
//   TUPLE_TYPE,
  ANY_TYPE,
  ARROW,
  // The "type" of any expression type (as in BOOLEAN : TYPE).
  TYPE,
  // Declaration of new (uninterpreted) types: T1, T2, ... : TYPE
  // (TYPEDECL T1 T2 ...)
  TYPEDECL,
  // Declaration of a defined type T : TYPE = type === (TYPEDEF T type)
  TYPEDEF,

  // Equality
  EQ,
  NEQ,

  // Propositional connectives
  NOT,
  AND,
  OR,
  XOR,
  IFF,
  IMPLIES,
  //  BOOL_VAR, //!< Boolean variables are treated as 0-ary predicates

  // Propositional relations (for circuit propagation)
  AND_R,
  IFF_R,
  ITE_R,

  // (ITE c e1 e2) == IF c THEN e1 ELSE e2 ENDIF, the internal
  // representation of the conditional.  Parser produces (IF ...).
  ITE, 

  // Quantifiers
  FORALL,
  EXISTS,

  // Uninterpreted function
  UFUNC,
  // Application of a function
  APPLY,

  // Top-level Commands
  ASSERT,
  QUERY,
  CHECKSAT,
  CONTINUE,
  RESTART,
  DBG,
  TRACE,
  UNTRACE,
  OPTION,
  HELP,
  TRANSFORM,
  PRINT,
  CALL,
  ECHO,
  INCLUDE,
  DUMP_PROOF,
  DUMP_ASSUMPTIONS,
  DUMP_SIG,
  DUMP_TCC,
  DUMP_TCC_ASSUMPTIONS,
  DUMP_TCC_PROOF,
  DUMP_CLOSURE,
  DUMP_CLOSURE_PROOF,
  WHERE,
  ASSERTIONS,
  ASSUMPTIONS,
  COUNTEREXAMPLE,
  COUNTERMODEL,
  PUSH,
  POP,
  POPTO,
  PUSH_SCOPE,
  POP_SCOPE,
  POPTO_SCOPE,
  CONTEXT,
  FORGET,
  GET_TYPE,
  CHECK_TYPE,
  GET_CHILD,
  SUBSTITUTE,
  SEQ,

  // Kinds used mostly in the parser

  TCC,
  // Variable declaration (VARDECL v1 v2 ... v_n type).  A variable
  // can be an ID or a BOUNDVAR.
  VARDECL,
  // A list of variable declarations (VARDECLS (VARDECL ...) (VARDECL ...) ...)
  VARDECLS,

  // Bound variables have a "printable name", the one the user typed
  // in, and a uniqueID used to distinguish it from other bound
  // variables, which is effectively the alpha-renaming: 

  // Op(BOUND_VAR (BOUND_ID "user_name" "uniqueID")).  Note that
  // BOUND_VAR is an operator (Expr without children), just as UFUNC
  // and UCONST.

  // The uniqueID normally is just a number, so one can print a bound
  // variable X as X_17.

  // NOTE that in the parsed expressions like LET x: T = e IN foo(x),
  // the second instance of 'x' will be an ID, and *not* a BOUNDVAR.
  // The parser does not know how to resolve bound variables, and it
  // has to be resolved later.
  BOUND_VAR,
  BOUND_ID,

  // Updator "e1 WITH <bunch of stuff> := e2" is represented as
  // (UPDATE e1 (UPDATE_SELECT <bunch of stuff>) e2), where <bunch
  // of stuff> is the list of accessors: 
  // (READ idx)
  // ID (what's that for?)
  // (REC_SELECT ID)
  // and (TUPLE_SELECT num).
//   UPDATE,
//   UPDATE_SELECT,
  // Record type [# f1 : t1, f2 : t2 ... #] is represented as 
  // (RECORD_TYPE (f1 t1) (f2 t2) ... )
//   RECORD_TYPE,
//   // (# f1=e1, f2=e2, ...#) == (RECORD (f1 e1) ...)
//   RECORD,
//   RECORD_SELECT,
//   RECORD_UPDATE,

//   // (e1, e2, ...) == (TUPLE e1 e2 ...)
//   TUPLE,
//   TUPLE_SELECT,
//   TUPLE_UPDATE,

//   SUBRANGE,
  // Enumerated type (SCALARTYPE v1 v2 ...)
//   SCALARTYPE,
  // Predicate subtype: the argument is the predicate (lambda-expression)
  SUBTYPE,
  // Datatype is Expr(DATATYPE, Constructors), where Constructors is a
  // vector of Expr(CONSTRUCTOR, id [ , arg ]), where 'id' is an ID,
  // and 'arg' a VARDECL node (list of variable declarations with
  // types).  If 'arg' is present, the constructor has arguments
  // corresponding to the declared variables.
//   DATATYPE,
//   THISTYPE, // Used to indicate recursion in recursive datatypes
//   CONSTRUCTOR,
//   SELECTOR,
//   TESTER,
  // Expression e WITH accessor := e2 is transformed by the command
  // processor into (DATATYPE_UPDATE e accessor e2), where e is the
  // original datatype value C(a1, ..., an) (here C is the
  // constructor), and "accessor" is the name of one of the arguments
  // a_i of C.
  //  DATATYPE_UPDATE,
  // Statement IF c1 THEN e1 ELSIF c2 THEN e2 ... ELSE e_n ENDIF is
  // represented as (IF (IFTHEN c1 e1) (IFTHEN c2 e2) ... (ELSE e_n))
  IF,
  IFTHEN,
  ELSE,
  // Lisp version of multi-branch IF:
  // (COND (c1 e1) (c2 e2) ... (ELSE en))
  COND,

  // LET x1: t1 = e1, x2: t2 = e2, ... IN e
  // Parser builds:
  // (LET (LETDECLS (LETDECL x1 t1 e1) (LETDECL x2 t2 e2) ... ) e)
  // where each x_i is a BOUNDVAR.
  // After processing, it is rebuilt to have (LETDECL var def); the
  // type is set as the attribute to var.
  LET,
  LETDECLS,
  LETDECL,
  // Lambda-abstraction LAMBDA (<vars>) : e  === (LAMBDA <vars> e)
  LAMBDA,
  // Symbolic simulation operator
  SIMULATE,

  // Uninterpreted constants (variables) x1, x2, ... , x_n : type
  // (CONST (VARLIST x1 x2 ... x_n) type)
  // Uninterpreted functions are declared as constants of functional type.

  // After processing, uninterpreted functions and constants
  // (a.k.a. variables) are represented as Op(UFUNC, (ID "name")) and
  // Op(UCONST, (ID "name")) with the appropriate type attribute.
  CONST,  
  VARLIST,
  UCONST,

  // User function definition f(args) : type = e === (DEFUN args type e)
  // Here 'args' are bound var declarations
  DEFUN,

  // Arithmetic types and operators
//   REAL,
//   INT,

//   UMINUS,
//   PLUS,
//   MINUS,
//   MULT,
//   DIVIDE,
//   INTDIV,
//   MOD,
//   LT,
//   LE,
//   GT,
//   GE,
//   IS_INTEGER,
//   NEGINF,
//   POSINF,
//   DARK_SHADOW,
//   GRAY_SHADOW,

//   //Floor theory operators
//   FLOOR,
  // Kind for Extension to Non-linear Arithmetic
//   POW,

  // Kinds for proof terms
  PF_APPLY,
  PF_HOLE,


//   // Mlss
//   EMPTY, // {}
//   UNION, // +
//   INTER, // * 
//   DIFF,  
//   SINGLETON,
//   IN,
//   INCS,
//   INCIN,

  //Skolem variable
  SKOLEM_VAR,
  //! Must always be the last kind
  LAST_KIND
} Kind;

/************************************************************

Structures that tell the ocaml runtime how to deal with
things of abstract types that we will ll be passing it.

************************************************************/

/* Encapsulation of ValidityChecker
   as Caml custom blocks. */
static struct custom_operations VC_ops = {
  "CVCL.ValidityChecker",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of Context
   as Caml custom blocks. */
static struct custom_operations Context_ops = {
  "CVCL.Context",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of ExprManager
   as Caml custom blocks. */
static struct custom_operations EM_ops = {
  "CVCL.ExprManager",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of Flags
   as Caml custom blocks. */
static struct custom_operations Flags_ops = {
  "CVCL.Flags",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of Expr
   as Caml custom blocks. */
static struct custom_operations Expr_ops = {
  "CVCL.Expr",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of Op
   as Caml custom blocks. */
static struct custom_operations Op_ops = {
  "CVCL.Op",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of Type
   as Caml custom blocks. */
static struct custom_operations Type_ops = {
  "CVCL.Type",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/************************************************************

Functions for wrapping and unwrapping ocaml values for the
abstract types above.

************************************************************/

/* Accessing the relevant part of a Caml custom block */
#define VC_val(v)      (*((VC *) Data_custom_val(v)))
#define Context_val(v) (*((Context *) Data_custom_val(v)))
#define EM_val(v)      (*((ExprManager *) Data_custom_val(v)))
#define Flags_val(v)   (*((Flags *) Data_custom_val(v)))
#define Expr_val(v)    (*((Expr *) Data_custom_val(v)))
#define OP_val(v)      (*((Op *) Data_custom_val(v)))
#define Type_val(v)    (*((Type *) Data_custom_val(v)))

/* Allocating a Caml custom block to hold the given CVCL structure */
static value alloc_VC(VC vc)
{
  value v = alloc_custom(&VC_ops, sizeof(VC), 0, 1);
  VC_val(v) = vc;
  return v;
}

static value alloc_Context(Context ctxt)
{
  value v = alloc_custom(&Context_ops, sizeof(Context), 0, 1);
  Context_val(v) = ctxt;
  return v;
}

static value alloc_EM(ExprManager em)
{
  value v = alloc_custom(&EM_ops, sizeof(ExprManager), 0, 1);
  EM_val(v) = em;
  return v;
}

static value alloc_Flags(Flags f)
{
  value v = alloc_custom(&Flags_ops, sizeof(Flags), 0, 1);
  Flags_val(v) = f;
  return v;
}

static value alloc_Expr(Expr e)
{
  value v = alloc_custom(&Expr_ops, sizeof(Expr), 0, 1);
  Expr_val(v) = e;
  return v;
}

static value alloc_Op(Op op)
{
  value v = alloc_custom(&Op_ops, sizeof(Op), 0, 1);
  OP_val(v) = op;
  return v;
}

static value alloc_Type(Type t)
{
  value v = alloc_custom(&Type_ops, sizeof(Type), 0, 1);
  Type_val(v) = t;
  return v;
}

/************************************************************

Wrappers

************************************************************/

value caml_vc_createValidityChecker(value flags)
{
  CAMLparam1(flags);
  CAMLreturn(alloc_VC(vc_createValidityChecker(Flags_val(flags))));
}

value caml_vc_createFlags(value unit)
{
  CAMLparam1(unit);
  CAMLreturn(alloc_Flags(vc_createFlags()));
}

value caml_vc_destroyValidityChecker(value vc)
{
  CAMLparam1(vc);
  vc_destroyValidityChecker(VC_val(vc));
  CAMLreturn(Val_unit);
}

value caml_vc_deleteFlags(value flags)
{
  CAMLparam1(flags);
  vc_deleteFlags(Flags_val(flags));
  CAMLreturn(Val_unit);
}

value caml_vc_deleteType(value type)
{
  CAMLparam1(type);
  vc_deleteType(Type_val(type));
  CAMLreturn(Val_unit);
}

value caml_vc_deleteExpr(value e)
{
  CAMLparam1(e);
  vc_deleteExpr(Expr_val(e));
  CAMLreturn(Val_unit);
}

value caml_vc_deleteOp(value op)
{
  CAMLparam1(op);
  vc_deleteOp(OP_val(op));
  CAMLreturn(Val_unit);
}

// Setting the flags
value caml_vc_setBoolFlag(value flags, value name, value val)
{
  CAMLparam3(flags,name,val);
  vc_setBoolFlag(Flags_val(flags),String_val(name),Int_val(val));
  CAMLreturn(Val_unit);
}

value caml_vc_setIntFlag(value flags, value name, value val)
{
  CAMLparam3(flags,name,val);
  vc_setIntFlag(Flags_val(flags),String_val(name),Int_val(val));
  CAMLreturn(Val_unit);
}

value caml_vc_setStringFlag(value flags, value name, value val)
{
  CAMLparam3(flags,name,val);
  vc_setStringFlag(Flags_val(flags),String_val(name),String_val(val));
  CAMLreturn(Val_unit);
}

value caml_vc_setStrSeqFlag(value flags, value name, value str, value val)
{
  CAMLparam4(flags,name,str,val);
  vc_setStrSeqFlag(Flags_val(flags),String_val(name),
		   String_val(val),Int_val(val));
  CAMLreturn(Val_unit);
}

// Basic Types
value caml_vc_boolType(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Type(vc_boolType(VC_val(vc))));
}

value caml_vc_realType(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Type(vc_realType(VC_val(vc))));
}

value caml_vc_intType(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Type(vc_intType(VC_val(vc))));
}

// Tuple Types
value caml_vc_tupleType2(value vc, value t0, value t1)
{
  CAMLparam3(vc,t0,t1);
  CAMLreturn(alloc_Type(vc_tupleType2(VC_val(vc),Type_val(t0),Type_val(t1))));
}

value caml_vc_tupleType3(value vc, value t0, value t1, value t2)
{
  CAMLparam4(vc,t0,t1,t2);
  CAMLreturn(alloc_Type(vc_tupleType3(VC_val(vc),Type_val(t0),
				      Type_val(t1),Type_val(t2))));
}

value caml_vc_tupleTypeN(value vc, value types, value numTypes)
{
  Type *ts;
  int i;

  CAMLparam3(vc,types,numTypes);
  CAMLlocal1(result);

  ts = (Type *)malloc(Int_val(numTypes) * sizeof(Type));
  if( !ts )
    caml_failwith("malloc returned NULL in vc_tupleTypeN wrapper");

  for( i = 0; i < Int_val(numTypes); i++ ) {
    ts[i] = Type_val(Field(types,i));
  }

  result = alloc_Type(vc_tupleTypeN(VC_val(vc), ts, Int_val(numTypes)));

  free( ts );

  CAMLreturn(result);
}

// Record Types
value caml_vc_recordType1(value vc, value field, value t)
{
  CAMLparam3(vc, field, t);
  CAMLreturn(alloc_Type(vc_recordType1(VC_val(vc),String_val(field),
				       Type_val(t))));
}

value caml_vc_recordType2(value vc, value f0, value t0, value f1, value t1)
{
  CAMLparam5(vc,f0,t0,f1,t1);
  CAMLreturn(alloc_Type(vc_recordType2(VC_val(vc),String_val(f0),Type_val(t0),
				       String_val(f1),Type_val(t1))));
}

/*
value caml_vc_recordType3_(value vc, value f0, value t0, value f1, value t1,
			   value f2, value t2)
{
  CAMLparam5(vc,f0,t0,f1,t1);
  CAMLxparam2(f2,t2);
  CAMLreturn(alloc_Type(vc_recordType3(VC_val(vc),String_val(f0),Type_val(t0),
				       String_val(f1),Type_val(t1),
				       String_val(f2),Type_val(t2))));
}

value caml_vc_recordType3(value *args, int num)
{

  return(caml_vc_recordType3_(args[0],args[1],args[2],
			      args[3],args[4],args[5],
			      args[6]));
}
*/

value caml_vc_recordTypeN(value vc, value fields, value types, value num)
{
  char **fs;
  Type *ts;
  int i;

  CAMLparam4(vc,fields,types,num);
  CAMLlocal1(result);

  fs = (char **)malloc(Int_val(num) * sizeof(char *));
  if( !fs )
    caml_failwith("malloc returned NULL in vc_recordTypeN wrapper");

  ts = (Type *)malloc(Int_val(num) * sizeof(Type));
  if( !ts ) {
    free( fs );
    caml_failwith("malloc returned NULL in vc_recordTypeN wrapper");
  }

  for( i = 0; i < Int_val(num); i++ ) {
    fs[i] = String_val(Field(fields,i));
    ts[i] = Type_val(Field(types,i));
  }

  result = alloc_Type(vc_recordTypeN(VC_val(vc),fs,ts,Int_val(num)));

  free(ts);
  free(fs);

  CAMLreturn(result);
}

// Create an array type
value caml_vc_arrayType(value vc, value it, value dt)
{
  CAMLparam3(vc,it,dt);
  CAMLreturn(alloc_Type(vc_arrayType(VC_val(vc),Type_val(it),Type_val(dt))));
}

// Create a subrange type
value caml_vc_subRangeType(value vc, value low, value hi)
{
  CAMLparam3(vc,low,hi);
  CAMLreturn(alloc_Type(vc_subRangeType(VC_val(vc),Int_val(low),Int_val(hi))));
}

// Create function types
value caml_vc_funType1(value vc, value a1, value tr)
{
  CAMLparam3(vc,a1,tr);
  CAMLreturn(alloc_Type(vc_funType1(VC_val(vc),Type_val(a1),Type_val(tr))));
}

value caml_vc_funType2(value vc, value a1, value a2, value tr)
{
  CAMLparam4(vc,a1,a2,tr);
  CAMLreturn(alloc_Type(vc_funType2(VC_val(vc),Type_val(a1),
				    Type_val(a2),Type_val(tr))));
}

value caml_vc_funType3(value vc, value a1, value a2, value a3, value tr)
{
  CAMLparam5(vc,a1,a2,a3,tr);
  CAMLreturn(alloc_Type(vc_funType3(VC_val(vc),Type_val(a1),
				    Type_val(a2),Type_val(a3),
				    Type_val(tr))));
}

value caml_vc_funTypeN(value vc, value args, value r, value num)
{
  Type *ts;
  int i;

  CAMLparam4(vc,args,r,num);
  CAMLlocal1(result);

  ts = (Type *)malloc(Int_val(num) * sizeof(Type));
  if( !ts )
    caml_failwith("malloc returned NULL in vc_funTypeN wrapper");

  for( i = 0; i < Int_val(num); i++ ) {
    ts[i] = Type_val(Field(args,i));
  }

  result = alloc_Type(vc_funTypeN(VC_val(vc), ts, Type_val(r),
				  Int_val(num)));

  free( ts );

  CAMLreturn(result);
}

// User-defined types
value caml_vc_createType(value vc, value name)
{
  CAMLparam2(vc, name);
  CAMLreturn(alloc_Type(vc_createType(VC_val(vc),String_val(name))));
}

value caml_vc_lookupType(value vc, value name)
{
  CAMLparam2(vc,name);
  CAMLreturn(alloc_Type(vc_lookupType(VC_val(vc),String_val(name))));
}

/*
 * Expr manipulation methods
 */

// XXX
// ExprManager * vc_getEM(VC vc);

// Create a variable with a given name and type
value caml_vc_varExpr(value vc, value name, value t)
{
  CAMLparam3(vc, name, t);
  CAMLreturn(alloc_Expr(vc_varExpr(VC_val(vc),String_val(name),Type_val(t))));
}

// Get the expression and type associated with a name
value caml_vc_lookupVar(value vc, value name, value t)
{
  CAMLparam3(vc,name,t);
  CAMLreturn(alloc_Expr(vc_lookupVar(VC_val(vc),String_val(name),Type_val(t))));
}

// Get the type of the expr
value caml_vc_getType(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Type(vc_getType(VC_val(vc),Expr_val(e))));
}

// Create and equality expression. Children have same type
value caml_vc_eqExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_eqExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

// Boolean expressions
value caml_vc_trueExpr(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Expr(vc_trueExpr(VC_val(vc))));
}

value caml_vc_falseExpr(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Expr(vc_falseExpr(VC_val(vc))));
}

value caml_vc_notExpr(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Expr(vc_notExpr(VC_val(vc),Expr_val(e))));
}

value caml_vc_andExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_andExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_andExprN(value vc, value exprs, value num)
{
  Expr *es;
  int i;

  CAMLparam3(vc,exprs,num);
  CAMLlocal1(result);

  es = (Expr *)malloc(Int_val(num) * sizeof(Expr));
  if( !es )
    caml_failwith("malloc returned NULL in vc_andExprN wrapper");

  for( i = 0; i < Int_val(num); i++ ) {
    es[i] = Expr_val(Field(exprs,i));
  }

  result = alloc_Expr(vc_andExprN(VC_val(vc),es,Int_val(num)));

  free( es );

  CAMLreturn(result);
}

value caml_vc_orExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_orExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_orExprN(value vc, value exprs, value num)
{
  Expr *es;
  int i;

  CAMLparam3(vc,exprs,num);
  CAMLlocal1(result);

  es = (Expr *)malloc(Int_val(num) * sizeof(Expr));
  if( !es )
    caml_failwith("malloc returned NULL in vc_orExprN wrapper");

  for( i = 0; i < Int_val(num); i++ ) {
    es[i] = Expr_val(Field(exprs,i));
  }

  result = alloc_Expr(vc_orExprN(VC_val(vc),es,Int_val(num)));

  free( es );

  CAMLreturn(result);
}

value caml_vc_impliesExpr(value vc, value h, value c)
{
  CAMLparam3(vc,h,c);
  CAMLreturn(alloc_Expr(vc_impliesExpr(VC_val(vc),Expr_val(h),Expr_val(c))));
}

value caml_vc_iffExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_iffExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_iteExpr(value vc, value i, value t, value e)
{
  CAMLparam4(vc,i,t,e);
  CAMLreturn(alloc_Expr(vc_iteExpr(VC_val(vc),Expr_val(i),Expr_val(t),
				   Expr_val(e))));
}

/*
 * Arithmetic
 */

// Create a rational number of numerator n and denominator d.
value caml_vc_ratExpr(value vc, value n, value d)
{
  CAMLparam3(vc,n,d);
  CAMLreturn(alloc_Expr(vc_ratExpr(VC_val(vc),Int_val(n),Int_val(d))));
}

// Create a rational number n/d. n and d given as strings
value caml_vc_ratExprFromStr(value vc, value n, value d, value b)
{
  CAMLparam4(vc,n,d,b);
  CAMLreturn(alloc_Expr(vc_ratExprFromStr(VC_val(vc),String_val(n),
					  String_val(d),Int_val(b))));
}

// Unary minus
value caml_vc_uminusExpr(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Expr(vc_uminusExpr(VC_val(vc),Expr_val(e))));
}

// plus, minus, mult... exprs must have numeric type
value caml_vc_plusExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_plusExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_minusExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_minusExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_multExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_multExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_powExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_powExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_divideExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_divideExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

// comparators. produce boolean expressions expressions must have numeric type
value caml_vc_ltExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_ltExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_leExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_leExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_gtExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_gtExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_geExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_geExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

/* XXX
 * Records
 */

/* XXX
 * Arrays
 */

/* XXX
 * Functions
 */

/* XXX
 * Tuples
 */

/* XXX
 * Quantifiers
 */

/*
 * Expr I/O
 */

value caml_vc_printExpr(value vc, value e)
{
  CAMLparam2(vc,e);
  vc_printExpr(VC_val(vc),Expr_val(e));
  CAMLreturn(Val_unit);
}

value caml_vc_printExprFile(value vc, value e, value fd)
{
  CAMLparam3(vc,e,fd);
  vc_printExprFile(VC_val(vc),Expr_val(e),Int_val(fd));
  CAMLreturn(Val_unit);
}

/*
 * Context related methods
 */

// Assert a new formula in the current context
value caml_vc_assertFormula(value vc, value e)
{
  CAMLparam2(vc,e);
  vc_assertFormula(VC_val(vc),Expr_val(e));
  CAMLreturn(Val_unit);
}

// Register an atomic formula of interest
value caml_vc_registerAtom(value vc, value e)
{
  CAMLparam2(vc,e);
  vc_registerAtom(VC_val(vc),Expr_val(e));
  CAMLreturn(Val_unit);
}

// Return next literal implied by last assertion
value caml_vc_getImpliedLiteral(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Expr(vc_getImpliedLiteral(VC_val(vc))));
}

// Simplify e w.r.t. the current context
value caml_vc_simplify(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Expr(vc_simplify(VC_val(vc),Expr_val(e))));
}

// Check validity of e in the current context
value caml_vc_query(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(Val_int(vc_query(VC_val(vc),Expr_val(e))));
}

// XXX
// Expr * vc_getCounterExample(VC vc, int *size)
value caml_vc_getCounterExample(value vc)
{
  CAMLparam1(vc);
  CAMLlocal2(tmp,result);
  Expr *e;
  int i, size;

  e = vc_getCounterExample(VC_val(vc), &size);

  if( !e ) CAMLreturn(Val_int(0)); // empty list

  result = Val_int(0);
  for( i = 0; i < size; i++ ) {
    tmp = caml_alloc(2, 0);
    Store_field(tmp, 0, alloc_Expr(e[i]));
    Store_field(tmp, 1, result);
    result = tmp;
  }

  free(e);
  CAMLreturn(result);

}


// XXX
// int vc_inconsistent(VC vc, Expr **assumptions, int * size)

// Set the resource limit (0==unlimited, 1==exhausted)
value caml_vc_setResourceLimit(value vc, value limit)
{
  CAMLparam2(vc,limit);
  vc_setResourceLimit(VC_val(vc), Int_val(limit));
  CAMLreturn(Val_unit);
}

// Returns the proof for the last proven query
value caml_vc_getProof(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Expr(vc_getProof(VC_val(vc))));
}

// Returns the proof of a .cvc file, if it is valid
value caml_vc_getProofOfFile(value vc, value fname)
{
  CAMLparam2(vc,fname);
  CAMLreturn(alloc_Expr(vc_getProofOfFile(VC_val(vc),String_val(fname))));
}

// Checkpoint the current context and increase the scope level
value caml_vc_push(value vc)
{
  CAMLparam1(vc);
  vc_push(VC_val(vc));
  CAMLreturn(Val_unit);
}

// Restore the current context to its state at the last checkpoint
value caml_vc_pop(value vc)
{
  CAMLparam1(vc);
  vc_pop(VC_val(vc));
  CAMLreturn(Val_unit);
}

// Restore the current context to the given scope level
value caml_vc_popto(value vc, value l)
{
  CAMLparam2(vc,l);
  vc_popto(VC_val(vc),Int_val(l));
  CAMLreturn(Val_unit);
}

// Returns the current scope level
value caml_vc_scopeLevel(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(Val_int(vc_scopeLevel(VC_val(vc))));
}

// XXX
// Context *vc_getCurrentContext(VC vc)

/*
 * Util
 */

// Returns 1, 0, -1
value caml_compare_exprs(value e1, value e2)
{
  CAMLparam2(e1,e2);
  CAMLreturn(Val_int(compare_exprs(Expr_val(e1),Expr_val(e2))));
}

// Converts expression to a string
value caml_exprString(value e)
{
  CAMLparam1(e);
  CAMLlocal1(r);

  r = caml_copy_string(exprString(Expr_val(e)));

  CAMLreturn(r);
}

// Convertsa Type to a string
value caml_typeString(value t)
{
  CAMLparam1(t);
  CAMLlocal1(r);

  r = caml_copy_string(typeString(Type_val(t)));

  CAMLreturn(r);
}

// what kind of Expr?
value caml_isClosure(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(isClosure(Expr_val(e))));
}

value caml_isQuantifier(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(isQuantifier(Expr_val(e))));
}

value caml_isLambda(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(isLambda(Expr_val(e))));
}

value caml_isVar(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(isVar(Expr_val(e))));
}

value caml_isConst(value e)
{
  int k,r=0;
  CAMLparam1(e);
  
  k = getKind(Expr_val(e));
  if( k == CONST ) r = 1;
  CAMLreturn(Val_int(r));
}

value caml_arity(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(arity(Expr_val(e))));
}

value caml_getKind(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(getKind(Expr_val(e))));
}

value caml_isEq(value e)
{
    CAMLparam1(e);
    CAMLreturn(Val_int(getKind(Expr_val(e)) == EQ));
}

value caml_getChild(value e, value i)
{
  CAMLparam2(e,i);
  CAMLreturn(alloc_Expr(getChild(Expr_val(e),Int_val(i))));
}

value caml_getNumVars(value e)
{
  CAMLparam1(e);
  CAMLreturn(alloc_Expr(getNumVars(Expr_val(e))));
}

value caml_getVar(value e, value i)
{
  CAMLparam2(e,i);
  CAMLreturn(alloc_Expr(getVar(Expr_val(e),Int_val(i))));
}

value caml_getBody(value e)
{
  CAMLparam1(e);
  CAMLreturn(alloc_Expr(getBody(Expr_val(e))));
}

value caml_vc_getFun(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Expr(vc_getFun(VC_val(vc),Expr_val(e))));
}

value caml_toExpr(value t)
{
  CAMLparam1(t);
  CAMLreturn(alloc_Expr(toExpr(Type_val(t))));
}

// Translate a kind int to a string
value caml_vc_getKindString(value vc, value k)
{
  CAMLparam2(vc,k);
  CAMLlocal1(r);

  r = caml_copy_string(vc_getKindString(VC_val(vc),Int_val(k)));

  CAMLreturn(r); 
}

// Translate a kind string to an int
value caml_vc_getKindInt(value vc, value name)
{
  CAMLparam2(vc,name);
  CAMLreturn(Val_int(vc_getKindInt(VC_val(vc),String_val(name))));
}

// Return an in from a rational exp
value caml_getInt(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(getInt(Expr_val(e))));
}

// Return an int from a constant bitvector expression
value caml_getBVInt(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(getBVInt(Expr_val(e))));
}

value caml_getBVUnsigned(value e)
{
  CAMLparam1(e);
  CAMLreturn(Val_int(getBVUnsigned(Expr_val(e))));
}

// XXX
// Debug

// Print statistics
value caml_print_statistics(value vc)
{
  CAMLparam1(vc);
  print_statistics(VC_val(vc));
  CAMLreturn(Val_unit);
}

/*
 * Bit Vector Operations
 */

value caml_vc_bvType(value vc, value no_bits)
{
  CAMLparam2(vc,no_bits);
  CAMLreturn(alloc_Type(vc_bvType(VC_val(vc),Int_val(no_bits))));
}

value caml_vc_bv32Type(value vc)
{
  CAMLparam1(vc);
  CAMLreturn(alloc_Type(vc_bv32Type(VC_val(vc))));
}

value caml_vc_bvConstExprFromStr(value vc, value binstr)
{
  CAMLparam2(vc,binstr);
  CAMLreturn(alloc_Expr(vc_bvConstExprFromStr(VC_val(vc),String_val(binstr))));
}

value caml_vc_bvConstExprFromInt(value vc, value nbits,value i)
{
  CAMLparam3(vc,nbits,i);
  CAMLreturn(alloc_Expr(vc_bvConstExprFromInt(VC_val(vc),Int_val(nbits),
					      Int_val(i))));
}

value caml_vc_bv32ConstExprFromInt(value vc, value i)
{
  CAMLparam2(vc,i);
  CAMLreturn(alloc_Expr(vc_bv32ConstExprFromInt(VC_val(vc),Int_val(i))));
}

value caml_vc_bvConcatExpr(value vc, value l, value r)
{
  CAMLparam3(vc,l,r);
  CAMLreturn(alloc_Expr(vc_bvConcatExpr(VC_val(vc),Expr_val(l),Expr_val(r))));
}

// XXX
// Expr vc_bvConcatExprN(VC vc, Expr *c, int num)

value caml_vc_bvPlusExpr(value vc, value bits, value e1, value e2)
{
  CAMLparam4(vc,bits,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvPlusExpr(VC_val(vc),Int_val(bits),
				      Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bv32PlusExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bv32PlusExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvMinusExpr(value vc, value bits, value e1, value e2)
{
  CAMLparam4(vc,bits,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvMinusExpr(VC_val(vc),Int_val(bits),
				      Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bv32MinusExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bv32MinusExpr(VC_val(vc),Expr_val(e1),
					 Expr_val(e2))));
}

value caml_vc_bvMultExpr(value vc, value bits, value e1, value e2)
{
  CAMLparam4(vc,bits,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvMultExpr(VC_val(vc),Int_val(bits),
				      Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bv32MultExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bv32MultExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvLtExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvLtExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvLeExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvLeExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvGtExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvGtExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvGeExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvGeExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_sbvLtExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_sbvLtExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_sbvLeExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_sbvLeExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_sbvGtExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_sbvGtExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_sbvGeExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_sbvGeExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvUMinusExpr(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Expr(vc_bvUMinusExpr(VC_val(vc),Expr_val(e))));
}

value caml_vc_bvNotExpr(value vc, value e)
{
  CAMLparam2(vc,e);
  CAMLreturn(alloc_Expr(vc_bvNotExpr(VC_val(vc),Expr_val(e))));
}

value caml_vc_bvAndExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvAndExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvOrExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvOrExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvXorExpr(value vc, value e1, value e2)
{
  CAMLparam3(vc,e1,e2);
  CAMLreturn(alloc_Expr(vc_bvXorExpr(VC_val(vc),Expr_val(e1),Expr_val(e2))));
}

value caml_vc_bvLeftShiftExpr(value vc, value amt, value e)
{
  CAMLparam3(vc,amt,e);
  CAMLreturn(alloc_Expr(vc_bvLeftShiftExpr(VC_val(vc),Int_val(amt),
					   Expr_val(e))));
}

value caml_vc_bvRightShiftExpr(value vc, value amt, value e)
{
  CAMLparam3(vc,amt,e);
  CAMLreturn(alloc_Expr(vc_bvRightShiftExpr(VC_val(vc),Int_val(amt),
					    Expr_val(e))));
}

value caml_vc_bv32LeftShiftExpr(value vc, value amt, value e)
{
  CAMLparam3(vc,amt,e);
  CAMLreturn(alloc_Expr(vc_bv32LeftShiftExpr(VC_val(vc),Int_val(amt),
					     Expr_val(e))));
}

value caml_vc_bv32RightShiftExpr(value vc, value amt, value e)
{
  CAMLparam3(vc,amt,e);
  CAMLreturn(alloc_Expr(vc_bv32RightShiftExpr(VC_val(vc),Int_val(amt),
					      Expr_val(e))));
}

value caml_vc_bvVar32LeftShiftExpr(value vc, value she, value e)
{
  CAMLparam3(vc,she,e);
  CAMLreturn(alloc_Expr(vc_bvVar32LeftShiftExpr(VC_val(vc),Expr_val(she),
						Expr_val(e))));
}

value caml_vc_bvVar32RightShiftExpr(value vc, value she, value e)
{
  CAMLparam3(vc,she,e);
  CAMLreturn(alloc_Expr(vc_bvVar32RightShiftExpr(VC_val(vc),Expr_val(she),
						 Expr_val(e))));
}

value caml_vc_bvVar32DivByPowOfTwoExpr(value vc, value e, value rhs)
{
  CAMLparam3(vc,e,rhs);
  CAMLreturn(alloc_Expr(vc_bvVar32DivByPowOfTwoExpr(VC_val(vc),Expr_val(e),
						    Expr_val(rhs))));
}

value caml_vc_bvExtract(value vc, value e, value hi, value lo)
{
  CAMLparam4(vc,e,hi,lo);
  CAMLreturn(alloc_Expr(vc_bvExtract(VC_val(vc),Expr_val(e),Int_val(hi),
				     Int_val(lo))));
}

value caml_vc_bvBoolExtract(value vc, value e, value b)
{
  CAMLparam3(vc,e,b);
  CAMLreturn(alloc_Expr(vc_bvBoolExtract(VC_val(vc),Expr_val(e),Int_val(b))));
}

value caml_vc_bvSignExtend(value vc, value e, value nb)
{
  CAMLparam3(vc,e,nb);
  CAMLreturn(alloc_Expr(vc_bvSignExtend(VC_val(vc),Expr_val(e),Int_val(nb))));
}

value caml_vc_bvCreateMemoryArray(value vc, value name)
{
  CAMLparam2(vc,name);
  CAMLreturn(alloc_Expr(vc_bvCreateMemoryArray(VC_val(vc),String_val(name))));
}

value caml_vc_bvReadMemoryArray(value vc, value arr, value b, value num)
{
  CAMLparam4(vc,arr,b,num);
  CAMLreturn(alloc_Expr(vc_bvReadMemoryArray(VC_val(vc), Expr_val(arr),
					     Expr_val(b), Int_val(num))));
}

value caml_vc_bvWriteToMemoryArray(value vc, value arr, value bi,
				   value e, value num)
{
  CAMLparam5(vc,arr,bi,e,num);
  CAMLreturn(alloc_Expr(vc_bvWriteToMemoryArray(VC_val(vc),Expr_val(arr),
						Expr_val(bi),Expr_val(e),
						Int_val(num))));
}

// XXX
// Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value)
