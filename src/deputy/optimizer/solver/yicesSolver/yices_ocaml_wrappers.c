/*

yices_ocaml_wrappers.c

This file contains wrappers for the C interface to yices
that are callable from ocaml code.

Search for XXX to find unimplemented things

*/

#include <yices_c.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

/************************************************************

Structures that tell the ocaml runtime how to deal with
things of abstract types that we will ll be passing it.

************************************************************/

/* Encapsulation of yices_expr
   as Caml custom blocks. */
static struct custom_operations yices_expr_ops = {
  "Yices.yices_expr",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of yices_type
   as Caml custom blocks. */
static struct custom_operations yices_type_ops = {
  "Yices.yices_type",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of yices_var_decl
   as Caml custom blocks. */
static struct custom_operations yices_var_decl_ops = {
  "Yices.yices_var_decl",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of yices_context
   as Caml custom blocks. */
static struct custom_operations yices_context_ops = {
  "Yices.yices_context",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of yices_model
   as Caml custom blocks. */
static struct custom_operations yices_model_ops = {
  "Yices.yices_model",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

/* Encapsulation of yices_var_decl_iterator
   as Caml custom blocks. */
static struct custom_operations yices_var_decl_iterator_ops = {
  "Yices.yices_var_decl_iterator",
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
#define yices_expr_val(v)              (*((yices_expr *) Data_custom_val(v)))
#define yices_type_val(v)              (*((yices_type *) Data_custom_val(v)))
#define yices_var_decl_val(v)          (*((yices_var_decl *) Data_custom_val(v)))
#define yices_context_val(v)           (*((yices_context *) Data_custom_val(v)))
#define yices_model_val(v)             (*((yices_model *) Data_custom_val(v)))
#define yices_var_decl_iterator_val(v) (*((yices_var_decl_iterator *) Data_custom_val(v)))

/* Allocating a Caml custom block to hold the given CVCL structure */
static value alloc_yices_expr(yices_expr ye)
{
  value v = alloc_custom(&yices_expr_ops, sizeof(yices_expr), 0, 1);
  yices_expr_val(v) = ye;
  return v;
}

static value alloc_yices_type(yices_type t)
{
  value v = alloc_custom(&yices_type_ops, sizeof(yices_type), 0, 1);
  yices_type_val(v) = t;
  return v;
}

static value alloc_yices_var_decl(yices_var_decl vd)
{
  value v = alloc_custom(&yices_var_decl_ops, sizeof(yices_var_decl), 0, 1);
  yices_var_decl_val(v) = vd;
  return v;
}

static value alloc_yices_context(yices_context ctxt)
{
  value v = alloc_custom(&yices_context_ops, sizeof(yices_context), 0, 1);
  yices_context_val(v) = ctxt;
  return v;
}

static value alloc_yices_model(yices_model m)
{
  value v = alloc_custom(&yices_model_ops, sizeof(yices_model), 0, 1);
  yices_model_val(v) = m;
  return v;
}

static value alloc_yices_var_decl_iterator(yices_var_decl_iterator vdi)
{
  value v = alloc_custom(&yices_var_decl_iterator_ops,
                         sizeof(yices_var_decl_iterator), 0, 1);
  yices_var_decl_iterator_val(v) = vdi;
  return v;
}


/************************************************************

Wrappers

************************************************************/

value caml_yices_set_verbosity(value i)
{
  CAMLparam1(i);
  yices_set_verbosity(Int_val(i));
  CAMLreturn(Val_unit);
}

value caml_yices_version(value unit)
{
  CAMLparam1(unit);
  CAMLlocal1(r);
  r = caml_copy_string(yices_version());
  CAMLreturn(r);
}

value caml_yices_set_max_num_conflicts_in_maxsat_iteration(value n)
{
  CAMLparam1(n);
  yices_set_max_num_conflicts_in_maxsat_iteration(Int_val(n));
  CAMLreturn(Val_unit);
}

value caml_yices_enable_type_checker(value flag)
{
  CAMLparam1(flag);
  yices_enable_type_checker(Int_val(flag));
  CAMLreturn(Val_unit);
}

value caml_yices_set_max_num_iterations_in_maxsat(value n)
{
  CAMLparam1(n);
  yices_set_max_num_iterations_in_maxsat(Int_val(n));
  CAMLreturn(Val_unit);
}

value caml_yices_set_maxsat_initial_cost(value c)
{
  CAMLparam1(c);
  yices_set_maxsat_initial_cost(Int64_val(c));
  CAMLreturn(Val_unit);
}

value caml_yices_set_arith_only(value flag)
{
  CAMLparam1(flag);
  yices_set_arith_only(Int_val(flag));
  CAMLreturn(Val_unit);
}

value caml_yices_enable_log_file(value fname)
{
  CAMLparam1(fname);
  yices_enable_log_file(String_val(fname));
  CAMLreturn(Val_unit);
}

value caml_yices_mk_context(value unit)
{
  CAMLparam1(unit);
  CAMLreturn(alloc_yices_context(yices_mk_context()));
}

value caml_yices_del_context(value yc)
{
  CAMLparam1(yc);
  yices_del_context(yices_context_val(yc));
  CAMLreturn(Val_unit);
}

value caml_yices_reset(value yc)
{
  CAMLparam1(yc);
  yices_reset(yices_context_val(yc));
  CAMLreturn(Val_unit);
}

value caml_yices_dump_context(value yc)
{
  CAMLparam1(yc);
  yices_dump_context(yices_context_val(yc));
  CAMLreturn(Val_unit);
}

value caml_yices_push(value yc)
{
  CAMLparam1(yc);
  yices_push(yices_context_val(yc));
  CAMLreturn(Val_unit);
}

value caml_yices_pop(value yc)
{
  CAMLparam1(yc);
  yices_pop(yices_context_val(yc));
  CAMLreturn(Val_unit);
}

value caml_yices_assert(value yc, value expr)
{
  CAMLparam2(yc, expr);
  yices_assert(yices_context_val(yc), yices_expr_val(expr));
  CAMLreturn(Val_unit);
}

value caml_yices_assert_weighted(value yc, value expr, value w)
{
  CAMLparam3(yc,expr,w);
  CAMLreturn(Val_int(yices_assert_weighted(yices_context_val(yc),yices_expr_val(expr),
                                           Int64_val(w))));
}

value caml_yices_assert_retractable(value yc, value expr)
{
  CAMLparam2(yc,expr);
  CAMLreturn(Val_int(yices_assert_retractable(yices_context_val(yc),
                                              yices_expr_val(expr))));
}

value caml_yices_retract(value yc, value id)
{
  CAMLparam2(yc, id);
  yices_retract(yices_context_val(yc), Int_val(id));
  CAMLreturn(Val_unit);
}

value caml_yices_inconsistent(value yc)
{
  CAMLparam1(yc);
  CAMLreturn(Val_int(yices_inconsistent(yices_context_val(yc))));
}

value caml_yices_check(value yc)
{
  int cr = -1;
  lbool r;

  CAMLparam1(yc);
  r = yices_check(yices_context_val(yc));
  switch(r) {
    case l_true:  cr = 1; break;
    case l_false: cr = 0; break;
    case l_undef: cr = -1; break;
  }
  
  CAMLreturn(Val_int(cr));
}

value caml_yices_find_weighted_model(value yc, value r)
{
  int cr = -1;
  lbool res;

  CAMLparam2(yc,r);
  res = yices_find_weighted_model(yices_context_val(yc), Int_val(r));
  switch(res) {
    case l_true:  cr = 1; break;
    case l_false: cr = 0; break;
    case l_undef: cr = -1; break;
  }
  
  CAMLreturn(Int_val(cr));
}

value caml_yices_max_sat(value yc)
{
  int cr = -1;
  lbool r;
  
  CAMLparam1(yc);
  r = yices_max_sat(yices_context_val(yc));
  switch(r) {
    case l_true: cr = 1; break;
    case l_false: cr = 0; break;
    case l_undef: cr = -1; break;
  }
  
  CAMLreturn(Int_val(cr));
}

value caml_yices_max_sat_cost_leq(value yc, value max)
{
  int cr = -1;
  lbool r;
  
  CAMLparam2(yc, max);
  r = yices_max_sat_cost_leq(yices_context_val(yc),Int64_val(max));
  switch(r) {
    case l_true: cr = 1; break;
    case l_false: cr = 0; break;
    case l_undef: cr = -1; break;
  }
  
  CAMLreturn(Int_val(cr)); 
}

value caml_yices_get_model(value yc)
{
  yices_model m;

  CAMLparam1(yc);
  CAMLlocal1(res);

  m = yices_get_model(yices_context_val(yc));
  if( m ) {
    res = caml_alloc_tuple(2);
    Store_field(res, 0, alloc_yices_model(m));
    Store_field(res, 1, Int_val(0));
  }
  else {
    res = Int_val(0);
  }

  CAMLreturn(res);
}

value caml_yices_get_value(value m, value vd)
{
  int cr = -1;
  lbool r;

  CAMLparam2(m, vd);
  r = yices_get_value(yices_model_val(m), yices_var_decl_val(vd));
  switch(r) {
    case l_true: cr = 1; break;
    case l_false: cr = 0; break;
    case l_undef: cr = -1; break;
  }
  
  CAMLreturn(Int_val(cr));
}

value caml_yices_get_int_value(value m, value vd)
{
  long val;
  int res;

  CAMLparam2(m, vd);
  CAMLlocal1(r);
  res = yices_get_int_value(yices_model_val(m), yices_var_decl_val(vd), &val);
  r = caml_alloc_tuple(2);
  Store_field(r, 0, Int_val(res));
  Store_field(r, 1, Long_val(val));
  
  CAMLreturn(r);
}

value caml_yices_get_arith_value(value m, value vd)
{
  long num, den;
  int res;
  
  CAMLparam2(m, vd);
  CAMLlocal1(r);
  res = yices_get_arith_value(yices_model_val(m), yices_var_decl_val(vd),
                              &num, &den);
  r = caml_alloc_tuple(3);
  Store_field(r, 0, Int_val(res));
  Store_field(r, 1, Long_val(num));
  Store_field(r, 2, Long_val(den));
  
  CAMLreturn(r);
}

value caml_yices_get_double_value(value m, value vd)
{
  double val;
  int res;
  
  CAMLparam2(m, vd);
  CAMLlocal1(r);
  res = yices_get_double_value(yices_model_val(m), yices_var_decl_val(vd), &val);
  r = caml_alloc_tuple(2);
  Store_field(r, 0, Int_val(res));
  Store_field(r, 1, caml_copy_double(val));
  
  CAMLreturn(r);
}

value caml_yices_get_bitvector_value(value m, value vd, value n)
{
  int *bv;
  int res;
  int i;

  CAMLparam3(m, vd, n);
  CAMLlocal2(cbv, cr);
  bv = (int *)malloc(Int_val(n) * sizeof(int));
  res = yices_get_bitvector_value(yices_model_val(m), yices_var_decl_val(vd),
                                  Int_val(n), bv);
  cbv = caml_alloc_tuple(n);
  for(i = 0; i < n; i++) {
    Store_field(cbv, i, Int_val(bv[i]));
  }
  free(bv);
  cr = caml_alloc_tuple(2);
  Store_field(cr, 0, Int_val(res));
  Store_field(cr, 1, cbv);
  
  CAMLreturn(cr);
}

value caml_yices_get_assertion_value(value m, value id)
{
  CAMLparam2(m, id);
  CAMLreturn(Val_int(yices_get_assertion_value(yices_model_val(m),Int_val(id))));
}

value caml_yices_display_model(value m)
{
  CAMLparam1(m);
  yices_display_model(yices_model_val(m));
  CAMLreturn(Val_unit);
}

value caml_yices_get_cost(value m)
{
  CAMLparam1(m);
  CAMLreturn(caml_copy_int64(yices_get_cost(yices_model_val(m))));
}

value caml_yices_get_cost_as_double(value m)
{
  CAMLparam1(m);
  CAMLreturn(caml_copy_double(yices_get_cost_as_double(yices_model_val(m))));
}

/*
 * Expression Building
 *
 *
 */

value caml_yices_mk_true(value yc)
{
  CAMLparam1(yc);
  CAMLreturn(alloc_yices_expr(yices_mk_true(yices_context_val(yc))));
}

value caml_yices_mk_false(value yc)
{
  CAMLparam1(yc);
  CAMLreturn(alloc_yices_expr(yices_mk_false(yices_context_val(yc))));
}

value caml_yices_mk_bool_var(value yc, value name)
{
  CAMLparam2(yc, name);
  CAMLreturn(alloc_yices_expr(yices_mk_bool_var(yices_context_val(yc),
                                                String_val(name))));
}

value caml_yices_mk_fresh_bool_var(value yc)
{
  CAMLparam1(yc);
  CAMLreturn(alloc_yices_expr(yices_mk_fresh_bool_var(yices_context_val(yc))));
}

value caml_yices_get_var_decl(value ye)
{
  CAMLparam1(ye);
  CAMLreturn(alloc_yices_var_decl(yices_get_var_decl(yices_expr_val(ye))));
}

value caml_yices_mk_bool_var_decl(value yc, value name)
{
  CAMLparam2(yc,name);
  CAMLreturn(alloc_yices_var_decl(yices_mk_bool_var_decl(yices_context_val(yc),
                                                         String_val(name))));
}

value caml_yices_get_var_decl_name(value vd)
{
  CAMLparam1(vd);
  CAMLreturn(caml_copy_string(yices_get_var_decl_name(yices_var_decl_val(vd))));
}

value caml_yices_mk_bool_var_from_decl(value yc, value vd)
{
  CAMLparam2(yc,vd);
  CAMLreturn(alloc_yices_expr(yices_mk_bool_var_from_decl(yices_context_val(yc),
                                                          yices_var_decl_val(vd))));
}

value caml_yices_mk_or(value yc, value args, value n)
{
  yices_expr *cargs;
  yices_expr res;
  int i = 0;

  CAMLparam3(yc, args, n);
  CAMLlocal1(tmp);

  cargs = (yices_expr *)malloc(Int_val(n) * sizeof(yices_expr));
  tmp = args;
  while(Int_val(tmp) != 0 && i < n) {
    cargs[i] = yices_expr_val(Field(tmp, 0));
    tmp = Field(tmp, 1);
    i++;
  }
  res = yices_mk_or(yices_context_val(yc), cargs, Int_val(n));
  free(cargs);
  
  CAMLreturn(alloc_yices_expr(res));
}

value caml_yices_mk_and(value yc, value args, value n)
{
  yices_expr *cargs;
  yices_expr res;
  int i = 0;

  CAMLparam3(yc, args, n);
  CAMLlocal1(tmp);

  cargs = (yices_expr *)malloc(Int_val(n) * sizeof(yices_expr));
  tmp = args;
  while(Int_val(tmp) != 0 && i < n) {
    cargs[i] = yices_expr_val(Field(tmp, 0));
    tmp = Field(tmp, 1);
    i++;
  }
  res = yices_mk_and(yices_context_val(yc), cargs, Int_val(n));
  free(cargs);
  
  CAMLreturn(alloc_yices_expr(res));
}

value caml_yices_mk_eq(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_eq(yices_context_val(yc),
                                          yices_expr_val(e1),
                                          yices_expr_val(e2))));
}

value caml_yices_mk_diseq(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_diseq(yices_context_val(yc),
                                             yices_expr_val(e1),
                                             yices_expr_val(e2))));
}

value caml_yices_mk_ite(value yc, value c, value t, value e)
{
  CAMLparam4(yc, c, t, e);
  CAMLreturn(alloc_yices_expr(yices_mk_ite(yices_context_val(yc),
                                           yices_expr_val(c),
                                           yices_expr_val(t),
                                           yices_expr_val(e))));
}

value caml_yices_mk_not(value yc, value e)
{
  CAMLparam2(yc, e);
  CAMLreturn(alloc_yices_expr(yices_mk_not(yices_context_val(yc),
                                           yices_expr_val(e))));
}

value caml_yices_create_var_decl_iterator(value yc)
{
  CAMLparam1(yc);
  CAMLreturn(alloc_yices_var_decl_iterator(yices_create_var_decl_iterator(
    yices_context_val(yc))));
}

value caml_yices_iterator_has_next(value it)
{
  CAMLparam1(it);
  CAMLreturn(Val_int(yices_iterator_has_next(yices_var_decl_iterator_val(it))));
}

value caml_yices_iterator_next(value it)
{
  CAMLparam1(it);
  CAMLreturn(alloc_yices_var_decl(yices_iterator_next(
    yices_var_decl_iterator_val(it))));
}

value caml_yices_iterator_reset(value it)
{
  CAMLparam1(it);
  yices_iterator_reset(yices_var_decl_iterator_val(it));
  CAMLreturn(Val_unit);
}

value caml_yices_del_iterator(value it)
{
  CAMLparam1(it);
  yices_del_iterator(yices_var_decl_iterator_val(it));
  CAMLreturn(Val_unit);
}

value caml_yices_mk_type(value yc, value name)
{
  CAMLparam2(yc, name);
  CAMLreturn(alloc_yices_type(yices_mk_type(yices_context_val(yc),
                                            String_val(name))));
}

/* XXX: value caml_yices_mk_function_type */

value caml_yices_mk_bitvector_type(value yc, value size)
{
  CAMLparam2(yc,size);
  CAMLreturn(alloc_yices_type(yices_mk_bitvector_type(yices_context_val(yc),
                                                      Int_val(size))));
}

/* XXX: value caml_yices_mk_tuple_type */

value caml_yices_mk_var_decl(value yc, value name, value ty)
{
  CAMLparam3(yc, name, ty);
  CAMLreturn(alloc_yices_var_decl(yices_mk_var_decl(yices_context_val(yc),
                                                    String_val(name),
                                                    yices_type_val(ty))));
}

/* Returns a list! */
value caml_yices_get_var_decl_from_name(value yc, value name)
{
  yices_var_decl yvd;

  CAMLparam2(yc, name);
  CAMLlocal1(res);
  yvd = yices_get_var_decl_from_name(yices_context_val(yc),String_val(name));
  if( yvd ) {
    res = caml_alloc_tuple(2);
    Store_field(res, 0, alloc_yices_var_decl(yvd));
    Store_field(res, 1, Val_int(0));
  }
  else {
    res = Val_int(0);
  }
  
  CAMLreturn(res);
}

value caml_yices_mk_var_from_decl(value yc, value vd)
{
  CAMLparam2(yc,vd);
  CAMLreturn(alloc_yices_expr(yices_mk_var_from_decl(yices_context_val(yc),
                                                     yices_var_decl_val(vd))));
}

/* XXX: value caml_yices_mk_app */

value caml_yices_mk_num(value yc, value n)
{
  CAMLparam2(yc, n);
  CAMLreturn(alloc_yices_expr(yices_mk_num(yices_context_val(yc),Int_val(n))));
}

value caml_yices_mk_num_from_string(value yc, value numstr)
{
  CAMLparam2(yc, numstr);
  CAMLreturn(alloc_yices_expr(yices_mk_num_from_string(yices_context_val(yc),
                                                       String_val(numstr))));
}

value caml_yices_mk_sum(value yc, value args, value n)
{
  yices_expr *cargs;
  yices_expr res;
  int i = 0;

  CAMLparam3(yc, args, n);
  CAMLlocal1(tmp);

  cargs = (yices_expr *)malloc(Int_val(n) * sizeof(yices_expr));
  tmp = args;
  while(Int_val(tmp) != 0 && i < n) {
    cargs[i] = yices_expr_val(Field(tmp, 0));
    tmp = Field(tmp, 1);
    i++;
  }
  res = yices_mk_sum(yices_context_val(yc), cargs, Int_val(n));
  free(cargs);
  
  CAMLreturn(alloc_yices_expr(res));
}

value caml_yices_mk_sub(value yc, value args, value n)
{
  yices_expr *cargs;
  yices_expr res;
  int i = 0;

  CAMLparam3(yc, args, n);
  CAMLlocal1(tmp);

  cargs = (yices_expr *)malloc(Int_val(n) * sizeof(yices_expr));
  tmp = args;
  while(Int_val(tmp) != 0 && i < n) {
    cargs[i] = yices_expr_val(Field(tmp, 0));
    tmp = Field(tmp, 1);
    i++;
  }
  res = yices_mk_sub(yices_context_val(yc), cargs, Int_val(n));
  free(cargs);
  
  CAMLreturn(alloc_yices_expr(res));
}

value caml_yices_mk_mul(value yc, value args, value n)
{
  yices_expr *cargs;
  yices_expr res;
  int i = 0;

  CAMLparam3(yc, args, n);
  CAMLlocal1(tmp);

  cargs = (yices_expr *)malloc(Int_val(n) * sizeof(yices_expr));
  tmp = args;
  while(Int_val(tmp) != 0 && i < n) {
    cargs[i] = yices_expr_val(Field(tmp, 0));
    tmp = Field(tmp, 1);
    i++;
  }
  res = yices_mk_mul(yices_context_val(yc), cargs, Int_val(n));
  free(cargs);
  
  CAMLreturn(alloc_yices_expr(res));
}

value caml_yices_mk_lt(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_lt(yices_context_val(yc),
                                          yices_expr_val(e1),
                                          yices_expr_val(e2))));
}

value caml_yices_mk_le(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_le(yices_context_val(yc),
                                          yices_expr_val(e1),
                                          yices_expr_val(e2))));
}

value caml_yices_mk_gt(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_gt(yices_context_val(yc),
                                          yices_expr_val(e1),
                                          yices_expr_val(e2))));
}

value caml_yices_mk_ge(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_ge(yices_context_val(yc),
                                          yices_expr_val(e1),
                                          yices_expr_val(e2))));
}

value caml_yices_mk_bv_constant(value yc, value size, value val)
{
  CAMLparam3(yc,size,val);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_constant(yices_context_val(yc),
                                                   Int_val(size),
                                                   Int_val(val))));
}

/* XXX: value vaml_yices_mk_bv_constant_from_array */

value caml_yices_mk_bv_add(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_add(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_sub(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_sub(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_mul(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_mul(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_minus(value yc, value e)
{
  CAMLparam2(yc, e);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_minus(yices_context_val(yc),
                                                yices_expr_val(e))));
}

value caml_yices_mk_bv_concat(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_concat(yices_context_val(yc),
                                                 yices_expr_val(e1),
                                                 yices_expr_val(e2))));
}

value caml_yices_mk_bv_and(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_and(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_or(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_or(yices_context_val(yc),
                                             yices_expr_val(e1),
                                             yices_expr_val(e2))));
}

value caml_yices_mk_bv_xor(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_xor(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_not(value yc, value e)
{
  CAMLparam2(yc, e);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_not(yices_context_val(yc),
                                              yices_expr_val(e))));
}

value caml_yices_mk_bv_extract(value yc, value end, value begin, value e)
{
  CAMLparam4(yc, end, begin, e);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_extract(yices_context_val(yc),
                                                  Int_val(end),Int_val(begin),
                                                  yices_expr_val(e))));
}

value caml_yices_mk_bv_sign_extend(value yc, value e, value n)
{
  CAMLparam3(yc,e,n);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_sign_extend(yices_context_val(yc),
                                                      yices_expr_val(e),
                                                      Int_val(n))));
}

value caml_yices_mk_bv_shift_left0(value yc, value e, value n)
{
  CAMLparam3(yc, e, n);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_shift_left0(yices_context_val(yc),
                                                      yices_expr_val(e),
                                                      Int_val(n))));
}

value caml_yices_mk_bv_shift_left1(value yc, value e, value n)
{
  CAMLparam3(yc, e, n);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_shift_left1(yices_context_val(yc),
                                                      yices_expr_val(e),
                                                      Int_val(n))));
}

value caml_yices_mk_bv_shift_right0(value yc, value e, value n)
{
  CAMLparam3(yc, e, n);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_shift_right0(yices_context_val(yc),
                                                       yices_expr_val(e),
                                                       Int_val(n))));
}

value caml_yices_mk_bv_shift_right1(value yc, value e, value n)
{
  CAMLparam3(yc, e, n);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_shift_right1(yices_context_val(yc),
                                                       yices_expr_val(e),
                                                       Int_val(n))));
}

value caml_yices_mk_bv_lt(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_lt(yices_context_val(yc),
                                             yices_expr_val(e1),
                                             yices_expr_val(e2))));
}

value caml_yices_mk_bv_le(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_le(yices_context_val(yc),
                                             yices_expr_val(e1),
                                             yices_expr_val(e2))));
}

value caml_yices_mk_bv_gt(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_gt(yices_context_val(yc),
                                             yices_expr_val(e1),
                                             yices_expr_val(e2))));
}

value caml_yices_mk_bv_ge(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_ge(yices_context_val(yc),
                                             yices_expr_val(e1),
                                             yices_expr_val(e2))));
}

value caml_yices_mk_bv_slt(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_slt(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_sle(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_sle(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_sgt(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_sgt(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_mk_bv_sge(value yc, value e1, value e2)
{
  CAMLparam3(yc, e1, e2);
  CAMLreturn(alloc_yices_expr(yices_mk_bv_sge(yices_context_val(yc),
                                              yices_expr_val(e1),
                                              yices_expr_val(e2))));
}

value caml_yices_pp_expr(value e)
{
  CAMLparam1(e);
  yices_pp_expr(yices_expr_val(e));
  CAMLreturn(Val_unit);
}
