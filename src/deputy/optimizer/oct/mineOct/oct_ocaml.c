/* oct_ocaml.c
   OCaml binding for all library functions.

   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/intext.h>
#include <oct.h>
#include <oct_private.h>
#include <oct_ocaml.h>

/* define to 1 if you want octagons to be marshalized in minimized form */
#define OCAML_SERIALIZE_COMPRESS 1

/* num/vnum -> num_t */

void ocaml_num_finalize (value o) 
{
  num_clear(Num_val(o)); 
}

int
ocaml_num_compare (value a, value b)
{
  return num_cmp(Num_val(a),Num_val(b));
}

void ocaml_vnum_finalize (value o) 
{ 
  num_clear_n(Vnum_val(o)->n,Vnum_val(o)->nb);
  oct_mm_free(Vnum_val(o)->n);
}

#ifdef OCT_NUM_SERIALIZE

void ocaml_num_serialize (value a, unsigned long * w32, unsigned long * w64)
{
  num_t* n = Num_val(a);
  unsigned size = num_serialize_size(n);
  char* data = new_n(char,size);
  num_serialize(n,data);
  serialize_int_4(num_serialize_id);
  serialize_int_4(size);
  serialize_block_1(data,size);
  *w32=size;
  *w64=size;
  oct_mm_free(data);
}

unsigned long ocaml_num_deserialize (void * dst)
{
  int id = deserialize_sint_4();
  unsigned size;
  char* data;
  if (id!=num_serialize_id) 
    failwith ("ocaml_num_deserialize: incompatible serialized num");
  size = deserialize_uint_4();
  data = new_n(char,size);
  deserialize_block_1(data,size);
  num_init((num_t*)dst);
  num_deserialize((num_t*)dst,data);
  oct_mm_free(data);
  return(size);
}

void ocaml_vnum_serialize (value a, unsigned long * w32, unsigned long * w64)
{
  vnum_t* v = Vnum_val(a);
  unsigned size,i;
  char* data, *d;
  for (i=0,size=0;i<v->nb;i++)
    size += num_serialize_size(v->n+i);

  data = new_n(char,size);
  for (i=0,d=data;i<v->nb;i++)
    d += num_serialize(v->n+i,d);

  serialize_int_4(num_serialize_id);
  serialize_int_4(size);
  serialize_int_4(v->nb);
  serialize_block_1(data,size);
  *w32=4*2;
  *w64=8*2;
  oct_mm_free(data);
}

unsigned long ocaml_vnum_deserialize (void * dst)
{
  int id = deserialize_sint_4();
  unsigned size, nb, i;
  char* data, *d;
  if (id!=num_serialize_id) 
    failwith ("ocaml_vnum_deserialize: incompatible serialized vnum");
  size = deserialize_uint_4();
  nb = deserialize_uint_4();
  data = new_n(char,size);
  deserialize_block_1(data,size);

  ((vnum_t*)dst)-> nb = nb;
  ((vnum_t*)dst)->n = new_n(num_t,nb);
  num_init_n(((vnum_t*)dst)->n, nb);
  for (i=0,d=data;i<nb;i++)
    d += num_deserialize(((vnum_t*)dst)->n+i,d);
  
  oct_mm_free(data);
  return(sizeof(vnum_t));
}

#endif

static struct custom_operations ocaml_num_custom = { 
  "o_n@1", 
  ocaml_num_finalize,
  ocaml_num_compare,
  custom_hash_default,
#ifdef OCT_NUM_SERIALIZE
  ocaml_num_serialize,
  ocaml_num_deserialize
#else
  custom_serialize_default,
  custom_deserialize_default
#endif
};

static struct custom_operations ocaml_vnum_custom = { 
  "o_v@1", 
  ocaml_vnum_finalize ,
  custom_compare_default,
  custom_hash_default,
#ifdef OCT_NUM_SERIALIZE
  ocaml_vnum_serialize,
  ocaml_vnum_deserialize
#else
  custom_serialize_default,
  custom_deserialize_default
#endif
};

CAMLprim value
ocaml_num_infty (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init_set_infty(Num_val(r));
  CAMLreturn(r);
}

CAMLprim value
ocaml_num_int (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init_set_int(Num_val(r),Int_val(v));
  CAMLreturn(r);
}

CAMLprim value
ocaml_num_frac (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init_set_frac(Num_val(r),Int_val(Field(v,0)),Int_val(Field(v,1)));
  CAMLreturn(r);
}

CAMLprim value
ocaml_num_float (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init_set_float(Num_val(r),Double_val(v));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_int (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  for (i=0;i<n;i++) 
    num_init_set_int(k+i,Int_val(Field(v,i)));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_frac (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  for (i=0;i<n;i++) 
    num_init_set_frac(k+i,
		      Int_val(Field(Field(v,i),0)),
		      Int_val(Field(Field(v,i),1)));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_float (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v)/Double_wosize;
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  for (i=0;i<n;i++)
    num_init_set_float(k+i,Double_field(v,i));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_int_opt (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  for (i=0;i<n;i++)
    if (Is_long(Field(v,i))) num_init_set_infty(k+i);
    else num_init_set_int(k+i,Int_val(Field(Field(v,i),0)));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_frac_opt (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  for (i=0;i<n;i++) 
    if (Is_long(Field(v,i))) num_init_set_infty(k+i);
    else num_init_set_frac(k+i,
			   Int_val(Field(Field(v,i),0)),
			   Int_val(Field(Field(v,i),1)));
  CAMLreturn(r);
}

CAMLprim value
ocaml_int_num (value v)
{
  long i;
  CAMLparam1(v);
  CAMLlocal1(r);
  if (!num_fits_int(Num_val(v))) r = Val_int(0); 
  else {
    i = num_get_int(Num_val(v));
    if (i<(1<<30) && i>=-(1<<30)) {
      r = alloc_tuple(1);
      Store_field (r,0,Val_int(i));
    }
    else r = Val_int(0);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_frac_num (value v)
{
  long i,j;
  CAMLparam1(v);
  CAMLlocal1(r);
  if (!num_fits_frac(Num_val(v))) r = Val_int(0);
  else {
    i = num_get_num(Num_val(v));
    j = num_get_den(Num_val(v));
    if (i<(1<<30) && i>=-(1<<30) && j<(1<<30)) {
      r = alloc_tuple(2);
      Store_field (r,0,Val_int(i));
      Store_field (r,1,Val_int(j));
    }
    else r = Val_int(0);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_float_num (value v)
{
  //double d; zra
  CAMLparam1(v);
  CAMLlocal1(r);
  if (!num_fits_float(Num_val(v))) r = copy_double(1./0.);
  else r = copy_double(num_get_float(Num_val(v)));
  CAMLreturn(r);
}


CAMLprim value
ocaml_int_vnum (value v)
{
  size_t i;//,n; zra
  vnum_t* k;
  CAMLparam1(v);
  CAMLlocal2(r,s);
  k = Vnum_val(v);
  r = alloc_tuple(k->nb);
  for (i=0;i<k->nb;i++) {
    if (!num_fits_int(k->n+i)) s = Val_int(0);
    else {
      long a = num_get_int(k->n+i);
      if (a<(1<<30) && a>=-(1<<30)) {
	s = alloc_tuple(1);
	Store_field (s,0,Val_int(a));
      }
      else s = Val_int(0);
    }
    Store_field (r,i,s);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_frac_vnum (value v)
{
  size_t i;//,n; zra
  vnum_t* k;
  CAMLparam1(v);
  CAMLlocal2(r,s);
  k = Vnum_val(v);
  r = alloc_tuple(k->nb);
  for (i=0;i<k->nb;i++) {
    if (!num_fits_frac(k->n+i)) s = Val_int(0);
    else {
      long a = num_get_num(k->n+i);
      long b = num_get_den(k->n+i);
      if (a<(1<<30) && a>=-(1<<30) && b<(1<<30)) {
	s = alloc_tuple(2);
	Store_field (s,0,Val_int(a));
	Store_field (s,1,Val_int(b));
       }
      else s = Val_int(0);
    }
    Store_field (r,i,s);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_float_vnum (value v)
{
  size_t i;//,n; zra
  vnum_t* k;
  CAMLparam1(v);
  CAMLlocal2(r,s);
  k = Vnum_val(v);
  r = alloc(k->nb*Double_wosize,Double_array_tag);
  for (i=0;i<k->nb;i++) {
    if (!num_fits_float(k->n+i)) Store_double_field(r,i,1./0.);
    else Store_double_field(r,i,num_get_float(k->n+i));
}
  CAMLreturn(r);
}


#if defined(OCT_HAS_GMP) && defined(OCT_HAS_OCAML_GMP)

#include <gmp.h>

extern struct custom_operations _mlgmp_custom_z;
extern struct custom_operations _mlgmp_custom_q;

CAMLprim value
ocaml_num_mpz (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init(Num_val(r));
  num_set_mpz(Num_val(r),*((mpz_t*)(Data_custom_val(v))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_num_mpq (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init(Num_val(r));
  num_set_mpq(Num_val(r),*((mpq_t*)(Data_custom_val(v))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_mpz (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  num_init_n(k,n);
  for (i=0;i<n;i++) 
    num_set_mpz(k+i,*((mpz_t*)(Data_custom_val(Field(v,i)))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_mpq (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  num_init_n(k,n);
  for (i=0;i<n;i++) 
    num_set_mpq(k+i,*((mpq_t*)(Data_custom_val(Field(v,i)))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_mpz_opt (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  num_init_n(k,n);
  for (i=0;i<n;i++)
    if (Is_long(Field(v,i))) num_set_infty(k+i);
    else num_set_mpz(k+i,*((mpz_t*)(Data_custom_val(Field(Field(v,i),0)))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_mpq_opt (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  num_init_n(k,n);
  for (i=0;i<n;i++)
    if (Is_long(Field(v,i))) num_set_infty(k+i);
    else num_set_mpq(k+i,*((mpq_t*)(Data_custom_val(Field(Field(v,i),0)))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_mpz_num (value v)
{
  CAMLparam1(v);
  CAMLlocal2(r,s);
  if (num_infty(Num_val(v))) r = Val_int(0); 
  else {
    s = alloc_custom(&_mlgmp_custom_z,sizeof(mpz_t),0,1);
    num_get_mpz (*((mpz_t*)Data_custom_val(s)), Num_val(v));
    r = alloc_tuple(1);
    Store_field (r,0,s);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_mpq_num (value v)
{
  CAMLparam1(v);
  CAMLlocal2(r,s);
  if (num_infty(Num_val(v))) r = Val_int(0); 
  else {
    s = alloc_custom(&_mlgmp_custom_q,sizeof(mpq_t),0,1);
    num_get_mpq (*((mpq_t*)Data_custom_val(s)), Num_val(v));
    r = alloc_tuple(1);
    Store_field (r,0,s);
  }
  CAMLreturn(r);
}


CAMLprim value
ocaml_mpz_vnum (value v)
{
  size_t i,n;
  vnum_t* k;
  CAMLparam1(v);
  CAMLlocal2(r,s);
  k = Vnum_val(v);
  r = alloc_tuple(k->nb);
  for (i=0;i<k->nb;i++) {
    if (!num_infty(k->n+i)) s = Val_int(0);
    else {
      s = alloc_custom(&_mlgmp_custom_z,sizeof(mpz_t),0,1);
      num_get_mpz (*((mpz_t*)Data_custom_val(s)), k->n+i);
    }
    Store_field (r,i,s);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_mpq_vnum (value v)
{
  size_t i,n;
  vnum_t* k;
  CAMLparam1(v);
  CAMLlocal2(r,s);
  k = Vnum_val(v);
  r = alloc_tuple(k->nb);
  for (i=0;i<k->nb;i++) {
    if (!num_infty(k->n+i)) s = Val_int(0);
    else {
      s = alloc_custom(&_mlgmp_custom_q,sizeof(mpq_t),0,1);
      num_get_mpq (*((mpq_t*)Data_custom_val(s)), k->n+i);
    }
    Store_field (r,i,s);
  }
  CAMLreturn(r);
}

#else

CAMLprim void
ocaml_num_mpz (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_num_mpz: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_num_mpq (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_num_mpq: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_vnum_mpz (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_vnum_mpz: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_vnum_mpq (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_vnum_mpq: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_vnum_mpz_opt (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_vnum_mpz_opt: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_vnum_mpq_opt (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_vnum_mpq_opt: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_mpz_num (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_mpz_num: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_mpq_num (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_mpq_num: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_mpz_vnum (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_mpz_vnum: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_mpq_vnum (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_mpq_vnum: GMP support not enabled");
  CAMLreturn0;
}

#endif

#if defined(OCT_HAS_MPFR) && defined(OCT_HAS_OCAML_GMP)

#include <mpfr.h>

extern  struct custom_operations _mlgmp_custom_fr;

CAMLprim value
ocaml_num_mpfr (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init(Num_val(r));
  num_set_mpfr(Num_val(r),*((mpfr_t*)(Data_custom_val(v))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_mpfr (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  num_init_n(k,n);
  for (i=0;i<n;i++) 
    num_set_mpfr(k+i,*((mpfr_t*)(Data_custom_val(Field(v,i)))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_vnum_mpfr_opt (value v)
{
  CAMLparam1(v);
  CAMLlocal1(r);
  size_t i, n = Wosize_val(v);
  num_t* k = new_n(num_t,n);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1); 
  Vnum_val(r)->nb = n;
  Vnum_val(r)->n = k;
  num_init_n(k,n);
  for (i=0;i<n;i++)
    if (Is_long(Field(v,i))) num_set_infty(k+i);
    else num_set_mpfr(k+i,(*(mpfr_t*)(Data_custom_val(Field(Field(v,i),0)))));
  CAMLreturn(r);
}

CAMLprim value
ocaml_mpfr_num (value v)
{
  CAMLparam1(v);
  CAMLlocal2(r,s);
  if (num_infty(Num_val(v))) r = Val_int(0); 
  else {
    s = alloc_custom(&_mlgmp_custom_fr,sizeof(mpfr_t),0,1);
    num_get_mpfr (*((mpfr_t*)Data_custom_val(s)), Num_val(v));
    r = alloc_tuple(1);
    Store_field (r,0,s);
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_mpfr_vnum (value v)
{
  size_t i,n;
  vnum_t* k;
  CAMLparam1(v);
  CAMLlocal2(r,s);
  k = Vnum_val(v);
  r = alloc_tuple(k->nb);
  for (i=0;i<k->nb;i++) {
    if (!num_infty(k->n+i)) s = Val_int(0);
    else {
      s = alloc_custom(&_mlgmp_custom_fr,sizeof(mpfr_t),0,1);
      num_get_mpfr (*((mpfr_t*)Data_custom_val(s)), k->n+i);
    }
    Store_field (r,i,s);
  }
  CAMLreturn(r);
}

#else

CAMLprim void
ocaml_num_mpfr (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_num_mpfr: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_vnum_mpfr (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_vnum_mpfr: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_vnum_mpfr_opt (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_vnum_mpfr_opt: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_mpfr_num (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_mpfr_num: GMP support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_mpfr_vnum (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_mpfr_vnum: GMP support not enabled");
  CAMLreturn0;
}

#endif


CAMLprim value
ocaml_num_string(value m)
{
  char buf[4096];
  CAMLparam1(m);
  num_snprint(buf,4095,Num_val(m));
  CAMLreturn(copy_string(buf));
}


CAMLprim value
ocaml_vnum_string(value m, value i)
{
  char buf[4096];
  int j;
  CAMLparam2(m,i);
  j = Int_val(i);
  if (j<0 || j>=Vnum_val(m)->nb)
    failwith("ocaml_vnum_string: invalid index");
  num_snprint(buf,4095,Vnum_val(m)->n+j);
  CAMLreturn(copy_string(buf));
}

CAMLprim value
ocaml_vnum_length(value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_int(Vnum_val(m)->nb));
}

/* octagons management */

void
ocaml_oct_finalize (value o)
{
  oct_free(Oct_val(o));
}

void 
ocaml_oct_serialize (value a, unsigned long * w32, unsigned long * w64)
{
  size_t size;
  char* data;
#if OCAML_SERIALIZE_COMPRESS
  moct_t* m = oct_m_from_oct (Oct_val(a));
  data = oct_m_serialize(m,&size);
  oct_m_free(m);
#else
  data = oct_serialize(Oct_val(a),&size);
#endif
  serialize_int_8(size);
  serialize_block_1(data,size);
  *w32=4;
  *w64=8;
  oct_mm_free(data);
}

unsigned long 
ocaml_oct_deserialize (void * dst)
{
  size_t size;
  void* data;
  size = deserialize_uint_8() & 0xFFFFFFFFUL;  /* DM kludge */
  data = new_n(char, size);
  deserialize_block_1(data,size);
#if OCAML_SERIALIZE_COMPRESS
  { 
    moct_t* m = oct_m_deserialize(data);
    *((oct_t**)dst) = oct_m_to_oct(m);
    oct_m_free(m);
  }
#else
  *((oct_t**)dst) = oct_deserialize(data);
#endif
  oct_mm_free(data);  
  return(sizeof(oct_t*));
}

static struct custom_operations ocaml_oct_custom = { 
  "o_o@1", 
  ocaml_oct_finalize ,
  custom_compare_default,
  custom_hash_default,
  ocaml_oct_serialize,
  ocaml_oct_deserialize
};

inline 
CAMLprim value
Val_oct (const oct_t* o)
{
  CAMLparam0();
  CAMLlocal1(v);
  v = alloc_custom(&ocaml_oct_custom,sizeof(oct_t*),0,1);
  Oct_val(v) = (oct_t*)o;
  CAMLreturn(v);
}


/* functions wrappers */

CAMLprim value 
ocaml_oct_empty (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_oct(oct_empty(Int_val(n))));
}

CAMLprim value 
ocaml_oct_universe (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_oct(oct_universe(Int_val(n))));
}

CAMLprim value
ocaml_oct_dim (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_int(oct_dimension(Oct_val(n))));;
}

CAMLprim value
ocaml_oct_nbconstraints (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_int(oct_nbconstraints(Oct_val(n))));
}

CAMLprim value
ocaml_oct_get_elem (value m, value i, value j)
{
  CAMLparam3(m,i,j);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init_set(Num_val(r),oct_elem(Oct_val(m),Int_val(i),Int_val(j)));
  CAMLreturn(r);
}

CAMLprim value
ocaml_oct_is_empty (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_bool(oct_is_empty(Oct_val(n))));
}

CAMLprim value
ocaml_oct_is_empty_lazy (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_int(oct_is_empty_lazy(Oct_val(n))));
}

CAMLprim value
ocaml_oct_is_universe (value n)
{
  CAMLparam1(n);
  CAMLreturn(Val_bool(oct_is_universe(Oct_val(n))));
}

CAMLprim value
ocaml_oct_is_included_in (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_bool(oct_is_included_in(Oct_val(n),Oct_val(m))));
}

CAMLprim value
ocaml_oct_is_included_in_lazy (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_int(oct_is_included_in_lazy(Oct_val(n),Oct_val(m))));
}

CAMLprim value
ocaml_oct_is_equal (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_bool(oct_is_equal(Oct_val(n),Oct_val(m))));
}

CAMLprim value
ocaml_oct_is_equal_lazy (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_int(oct_is_equal_lazy(Oct_val(n),Oct_val(m))));
}

CAMLprim value
ocaml_oct_is_in (value n, value m)
{
  CAMLparam2(n,m);
  if (Vnum_val(m)->nb!=Oct_val(n)->n)
    failwith("ocaml_oct_is_in: incompatible dimensions");
  CAMLreturn(Val_bool(oct_is_in (Oct_val(n),Vnum_val(m)->n)));
}

CAMLprim value
ocaml_oct_inter (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_intersection(Oct_val(n),Oct_val(m),false)));
}

CAMLprim value
ocaml_oct_union (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_convex_hull(Oct_val(n),Oct_val(m),false)));
}

CAMLprim value
ocaml_oct_widening (value n, value m, value t)
{
  oct_t* r;
  CAMLparam3(n,m,t);
  if (Is_block(t)) r = oct_widening_steps(Oct_val(n),Oct_val(m),false,
					  Vnum_val(Field(t,0))->nb,
					  Vnum_val(Field(t,0))->n);
  else {
    oct_widening_type w;
    switch (Int_val(t)) {
    case 0: w = OCT_WIDENING_FAST; break;
    case 1: w = OCT_WIDENING_ZERO; break;
    case 2: w = OCT_WIDENING_UNIT; break;
    case 3: w = OCT_PRE_WIDENING; break;
    default: w = OCT_WIDENING_FAST;
    }
    r = oct_widening(Oct_val(n),Oct_val(m),false,w);
  }
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_narrowing (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_narrowing(Oct_val(n),Oct_val(m),false)));
}

CAMLprim value
ocaml_oct_forget (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_forget(Oct_val(n),Int_val(m),false)));
}

CAMLprim value
ocaml_oct_add_bin_constraints (value n, value m)
{
  int i, nb;
  oct_t* r;
  oct_cons* c;
  CAMLparam2(n,m);
  CAMLlocal1(l);
  nb = Wosize_val(m);
  c = new_n(oct_cons,nb);
  for (i=0;i<nb;i++) {
    l = Field(m,i);
    switch (Tag_val(l)) {
    case 0: /* PX     x  <= c */
      c[i].x = Int_val(Field(l,0));
      num_init_set(&c[i].c,Num_val(Field(l,1)));
      c[i].type = px;
      break;
    case 1: /* MX    -x  <= c */
      c[i].x =Int_val( Field(l,0));
      num_init_set(&c[i].c,Num_val(Field(l,1)));
      c[i].type = mx;
      break;
    case 2: /* PXPY  x+y <= c */
      c[i].x = Int_val(Field(l,0));
      c[i].y = Int_val(Field(l,1));
      num_init_set(&c[i].c,Num_val(Field(l,2)));
      c[i].type = pxpy;
      break;
    case 3: /* PXMY  x-y <= c */
      c[i].x = Int_val(Field(l,0));
      c[i].y = Int_val(Field(l,1));
      num_init_set(&c[i].c,Num_val(Field(l,2)));
      c[i].type = pxmy;
      break;
    case 4: /* MXPY  x+y <= c */
      c[i].x = Int_val(Field(l,0));
      c[i].y = Int_val(Field(l,1));
      num_init_set(&c[i].c,Num_val(Field(l,2)));
      c[i].type = mxpy;
      break;
   case 5: /* MXMY -x+y <= c */
      c[i].x = Int_val(Field(l,0));
      c[i].y = Int_val(Field(l,1));
      num_init_set(&c[i].c,Num_val(Field(l,2)));
      c[i].type = mxmy;
      break;
    default: 
      oct_mm_free(c);
      failwith("ocaml_oct_add_bin_constraints: invalid element of type constr");      
    }
  }
  r = oct_add_bin_constraints(Oct_val(n),nb,c,false);
  for (i=0;i<nb;i++) num_clear(&c[i].c);
  oct_mm_free(c);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_assign_variable (value n, value m, value o)
{
  CAMLparam3(n,m,o);
  if (Vnum_val(o)->nb!=Oct_val(n)->n+1)
    failwith("ocaml_oct_assign_variable: incompatible dimensions");
  CAMLreturn(Val_oct(oct_assign_variable(Oct_val(n),Int_val(m),
					 Vnum_val(o)->n,false)));
}

CAMLprim value
ocaml_oct_substitute_variable (value n, value m, value o)
{
  CAMLparam3(n,m,o);
  if (Vnum_val(o)->nb!=Oct_val(n)->n+1)
    failwith("ocaml_oct_substitute_variable: incompatible dimensions");
  CAMLreturn(Val_oct(oct_substitute_variable(Oct_val(n),Int_val(m),
					     Vnum_val(o)->n,false)));
}

CAMLprim value
ocaml_oct_add_constraint (value n, value o)
{
  CAMLparam2(n,o);
  if (Vnum_val(o)->nb!=Oct_val(n)->n+1)
    failwith("ocaml_oct_add_constraint: incompatible dimensions");
  CAMLreturn(Val_oct(oct_add_constraint (Oct_val(n),Vnum_val(o)->n,false)));
}

CAMLprim value
ocaml_oct_interv_assign_variable (value n, value m, value o)
{
  CAMLparam3(n,m,o);
  if (Vnum_val(o)->nb!=2*(Oct_val(n)->n+1))
    failwith("ocaml_oct_interv_assign_variable: incompatible dimensions");
  CAMLreturn(Val_oct(oct_interv_assign_variable(Oct_val(n),Int_val(m),
						Vnum_val(o)->n,false)));
}

CAMLprim value
ocaml_oct_interv_add_constraint (value n, value o)
{
  CAMLparam2(n,o);
  if (Vnum_val(o)->nb!=2*(Oct_val(n)->n+1))
    failwith("ocaml_oct_interv_add_constraint: incompatible dimensions");
  CAMLreturn(Val_oct(oct_interv_add_constraint (Oct_val(n),Vnum_val(o)->n,false)));
}

CAMLprim value
ocaml_oct_interv_substitute_variable (value n, value m, value o)
{
  CAMLparam3(n,m,o);
  if (Vnum_val(o)->nb!=2*(Oct_val(n)->n+1))
    failwith("ocaml_oct_interv_substitute_variable: incompatible dimensions");
  CAMLreturn(Val_oct(oct_interv_substitute_variable(Oct_val(n),Int_val(m),
						    Vnum_val(o)->n,false)));
}


CAMLprim value
ocaml_oct_add_dimensions_and_embed (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_add_dimensions_and_embed(Oct_val(n),Int_val(m),false)));
}

CAMLprim value
ocaml_oct_add_dimensions_and_project (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_add_dimensions_and_project(Oct_val(n),Int_val(m),false)));
}

CAMLprim value
ocaml_oct_remove_dimensions (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_oct(oct_remove_dimensions(Oct_val(n),Int_val(m),false)));
}

static dimsup_t* 
get_dimsup (value tab)
{
  size_t i,n = Wosize_val(tab);
  dimsup_t* d = new_n(dimsup_t,n);
  for (i=0;i<n;i++) {
    d[i].pos    = Int_val(Field(Field(tab,i),0));
    d[i].nbdims = Int_val(Field(Field(tab,i),1));
  }
  return d;
}

CAMLprim value
ocaml_oct_add_dimensions_and_embed_multi (value n, value m)
{
  dimsup_t* t;
  oct_t* r;
  CAMLparam2(n,m);  
  t = get_dimsup(m);
  r = oct_add_dimensions_and_embed_multi(Oct_val(n),t,Wosize_val(m),false);
  oct_mm_free(t);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_add_dimensions_and_project_multi (value n, value m)
{
  dimsup_t* t;
  oct_t* r;
  CAMLparam2(n,m);  
  t = get_dimsup(m);
  r = oct_add_dimensions_and_project_multi(Oct_val(n),t,Wosize_val(m),false);
  oct_mm_free(t);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_remove_dimensions_multi (value n, value m)
{
  dimsup_t* t;
  oct_t* r;
  CAMLparam2(n,m);  
  t = get_dimsup(m);
  r = oct_remove_dimensions_multi(Oct_val(n),t,Wosize_val(m),false);
  oct_mm_free(t);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_add_permute_dimensions_and_embed (value n, value m, value t)
{
  CAMLparam3(n,m,t);
  oct_t* r;
  var_t* tt,i,sz=Wosize_val(t);
  if (Oct_val(n)->n+Int_val(m)!=sz)
    failwith("ocaml_oct_add_permute_dimensions_and_embed: invalid permutation dimension");
  tt = new_n(var_t,sz);
  for (i=0;i<sz;i++) tt[i] = Int_val(Field(t,i));
  r = oct_add_permute_dimensions_and_embed(Oct_val(n),Int_val(m),tt,false);
  oct_mm_free(tt);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_add_permute_dimensions_and_project (value n, value m, value t)
{
  CAMLparam3(n,m,t);
  oct_t* r;
  var_t* tt,i,sz=Wosize_val(t);
  if (Oct_val(n)->n+Int_val(m)!=sz)
    failwith("ocaml_oct_add_permute_dimensions_and_project: invalid permutation dimension");
  tt = new_n(var_t,sz);
  for (i=0;i<sz;i++) tt[i] = Int_val(Field(t,i));
  r = oct_add_permute_dimensions_and_project(Oct_val(n),Int_val(m),tt,false);
  oct_mm_free(tt);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_permute_remove_dimensions (value n, value m, value t)
{
  CAMLparam3(n,m,t);
  oct_t* r;
  var_t* tt,i,sz=Wosize_val(t);
  if (Oct_val(n)->n!=sz)
    failwith("ocaml_oct_permute_remove_dimensions: invalid permutation dimension");
  tt = new_n(var_t,sz);
  for (i=0;i<sz;i++) tt[i] = Int_val(Field(t,i));
  r = oct_permute_remove_dimensions(Oct_val(n),Int_val(m),tt,false);
  oct_mm_free(tt);
  CAMLreturn(Val_oct(r));
}

CAMLprim value
ocaml_oct_print (value m)
{
  CAMLparam1(m);
  fflush(stdout);
  oct_print(Oct_val(m));
  fflush(stdout);
  CAMLreturn(Val_unit);
}

CAMLprim value
ocaml_oct_close (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_oct(oct_close(Oct_val(m),false,false)));
}

CAMLprim value
ocaml_oct_from_box (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_oct(oct_from_box(Vnum_val(m)->nb/2,Vnum_val(m)->n)));
}

CAMLprim value
ocaml_oct_get_box (value m)
{
  CAMLparam1(m);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_vnum_custom,sizeof(vnum_t),0,1);
  Vnum_val(r)->nb = Oct_val(m)->n*2;
  Vnum_val(r)->n = oct_get_box (Oct_val(m));;
  CAMLreturn(r);
}

CAMLprim value
ocaml_oct_set_bounds (value m, value i, value t)
{
  CAMLparam3(m,i,t);
  CAMLreturn(Val_oct(oct_set_bounds(Oct_val(m),Int_val(i),
				    Num_val(Field(t,0)), Num_val(Field(t,1)),
				    false)));
}

CAMLprim value
ocaml_oct_get_bounds (value m, value i)
{
  CAMLparam2(m,i);
  CAMLlocal1(r);
  r = alloc_tuple(2);
  Store_field(r,0,alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1));
  Store_field(r,1,alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1));
  num_init(Num_val(Field(r,0))); num_init(Num_val(Field(r,1)));
  oct_get_bounds(Oct_val(m),Int_val(i),
		 Num_val(Field(r,0)),Num_val(Field(r,1)));
  CAMLreturn(r);
}


CAMLprim value
ocaml_oct_add_epsilon (value m, value n)
{
  CAMLparam2(m,n);
  CAMLreturn(Val_oct(oct_add_epsilon(Oct_val(m),Num_val(n),false)));
}

CAMLprim value
ocaml_oct_add_epsilon_max (value m, value n)
{
  CAMLparam2(m,n);
  CAMLreturn(Val_oct(oct_add_epsilon_max(Oct_val(m),Num_val(n),false)));
}

CAMLprim value
ocaml_oct_add_epsilon_bin (value m, value n, value o)
{
  CAMLparam3(m,n,o);
  CAMLreturn(Val_oct(oct_add_epsilon_bin(Oct_val(m),Oct_val(n),Num_val(o),
					 false)));
}


CAMLprim value ocaml_oct_time_flow (value m, value min, value max,
                                    value tab)
{
    CAMLparam4(m,min,max,tab);
    if (Vnum_val(tab)->nb!=2*Oct_val(m)->n)
      failwith("ocaml_oct_time_flow: incompatible dimensions");
    CAMLreturn(Val_oct(oct_time_flow(Oct_val(m),Num_val(min),Num_val(max),
				     Vnum_val(tab)->n,false)));
}


/* minimized octagons management */

void
ocaml_oct_m_finalize (value o)
{
  oct_m_free(Moct_val(o));
}

void 
ocaml_oct_m_serialize (value a, unsigned long * w32, unsigned long * w64)
{
  size_t size;
  char* data = oct_m_serialize(Moct_val(a),&size);
  serialize_int_8(size);
  serialize_block_1(data,size);
  *w32=4;
  *w64=8;
  oct_mm_free(data);
}

unsigned long 
ocaml_oct_m_deserialize (void * dst)
{
  size_t size;
  void* data;
  size = deserialize_uint_8();
  data = new_n(char,size);
  deserialize_block_1(data,size);
  *((moct_t**)dst) = oct_m_deserialize(data);
  oct_mm_free(data);  
  return(sizeof(moct_t*));
}

struct custom_operations ocaml_moct_custom = { 
  "o_m@1", 
  ocaml_oct_m_finalize ,
  custom_compare_default,
  custom_hash_default,
  ocaml_oct_m_serialize,
  ocaml_oct_m_deserialize
};

inline 
CAMLprim value 
Val_moct (const moct_t* o)
{
  CAMLparam0();
  CAMLlocal1(v);
  v = alloc_custom(&ocaml_moct_custom,sizeof(moct_t*),0,1);
  Moct_val(v) = (moct_t*)o;
  CAMLreturn(v);
}

/* functions */


CAMLprim value
ocaml_oct_m_from_oct (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_moct(oct_m_from_oct(Oct_val(m))));
}

CAMLprim value
ocaml_oct_m_to_oct (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_oct(oct_m_to_oct(Moct_val(m))));
}

CAMLprim value
ocaml_oct_m_print (value m)
{
  CAMLparam1(m);
  fflush(stdout);
  oct_m_print(Moct_val(m));
  fflush(stdout);
  CAMLreturn(Val_unit);
}

CAMLprim value
ocaml_oct_m_dim (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_int(oct_m_dimension(Moct_val(m))));
}

CAMLprim value
ocaml_oct_m_is_empty (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_bool(oct_m_is_empty(Moct_val(m))));
}

CAMLprim value
ocaml_oct_m_is_equal (value n, value m)
{
  CAMLparam2(n,m);
  CAMLreturn(Val_bool(oct_m_is_equal(Moct_val(n),Moct_val(m))));
}

CAMLprim value
ocaml_oct_m_get_elem (value m, value i, value j)
{
  CAMLparam3(m,i,j);
  CAMLlocal1(r);
  r = alloc_custom(&ocaml_num_custom,sizeof(num_t),0,1);
  num_init_set(Num_val(r),oct_m_elem(Moct_val(m),Int_val(i),Int_val(j)));
  CAMLreturn(r);
}


/* used pretty-printing, not intended for the user, only for octprinter */

CAMLprim value
ocaml_oct_elem_to_string (value m, value i, value j)
{
  char buf[4096];
  int ii,jj;
  num_t* c;
  CAMLparam3(m,i,j);
  CAMLlocal1(r);
  ii = Int_val(i);
  jj = Int_val(j);
  c = oct_elem(Oct_val(m),ii,jj);
  if (num_infty(c)) r = Val_int(0);
  else {
    r = alloc_tuple(1);
    num_snprint (buf,4095,c);
    Store_field (r,0,copy_string (buf));
  }
  CAMLreturn(r);
}

CAMLprim value
ocaml_oct_elem_to_string2 (value m, value i,  value j, value s)
{
  char buf[4096*3+20];
  int ii,jj;
  num_t *cp, *cm;
  num_t c;
  CAMLparam4(m,i,j,s);
  CAMLlocal1(r);
  ii = Int_val(i);
  jj = Int_val(j);
  cp = oct_elem(Oct_val(m),ii,jj);
  cm = oct_elem(Oct_val(m),jj,ii);
  num_init(&c);
  if (num_infty(cp) && num_infty(cm)) r = Val_int(0);
  else if (num_infty(cm)) {
    strncpy(buf,String_val(s),4096);
    strcat(buf," <= ");
    if ((ii^1)==jj) num_div_by_2(&c,cp); else num_set(&c,cp);
    num_snprint (buf+strlen(buf),4096,&c);
    r = alloc_tuple(1);
    Store_field (r,0,copy_string (buf));
  }
  else if (num_infty(cp)) {
    strncpy(buf,String_val(s),4096);
    strcat(buf," >= ");
    num_neg(&c,cm);
    if ((ii^1)==jj) num_div_by_2(&c,&c);
    num_snprint (buf+strlen(buf),4096,&c);
    r = alloc_tuple(1);
    Store_field (r,0,copy_string (buf));
  }
  else {
    num_neg(&c,cm);
    if (!num_cmp(&c,cp)) {
      strncpy(buf,String_val(s),4096);
      strcat(buf," = ");
      if ((ii^1)==jj) num_div_by_2(&c,cp); else num_set(&c,cp);
      num_snprint (buf+strlen(buf),4096,&c);
      r = alloc_tuple(1);
      Store_field (r,0,copy_string (buf));
    }
    else {
      num_neg(&c,cm);
      if ((ii^1)==jj) num_div_by_2(&c,&c);
      num_snprint (buf,4096,&c);
      strcat(buf," <= ");
      strncat(buf,String_val(s),4096);
      strcat(buf," <= ");
      if ((ii^1)==jj) num_div_by_2(&c,cp); else num_set(&c,cp);
      num_snprint (buf+strlen(buf),4096,&c);
      r = alloc_tuple(1);
      Store_field (r,0,copy_string (buf));
    }
  }
  num_clear (&c);
  CAMLreturn(r);
}

CAMLprim value
ocaml_oct_get_state (value m)
{
  CAMLparam1(m);
  CAMLreturn(Val_int(Oct_val(m)->state));
}

CAMLprim value
ocaml_oct_melem_to_string (value m, value i, value j)
{
  char buf[4096];
  int ii,jj;
  num_t* c;
  CAMLparam3(m,i,j);
  CAMLlocal1(r);
  ii = Int_val(i);
  jj = Int_val(j);
  c = oct_m_elem(Moct_val(m),ii,jj);
  if (!c || num_infty(c)) r = Val_int(0);
  else {
    r = alloc_tuple(1);
    num_snprint (buf,4095,c);
    Store_field (r,0,copy_string (buf));
  }
  CAMLreturn(r);
}


CAMLprim value
ocaml_oct_melem_to_string2 (value m, value i,  value j, value s)
{
  char buf[4096*3+20];
  int ii,jj;
  num_t *cp,*cm;
  num_t c;
  CAMLparam4(m,i,j,s);
  CAMLlocal1(r);
  ii = Int_val(i);
  jj = Int_val(j);
  cp = oct_m_elem(Moct_val(m),ii,jj);
  cm = oct_m_elem(Moct_val(m),jj,ii);
  num_init(&c);
  if ((!cp || num_infty(cp)) && (!cm || num_infty(cm))) r = Val_int(0);
  else if (!cm || num_infty(cm)) {
    strncpy(buf,String_val(s),4096);
    strcat(buf," <= ");
    if ((ii^1)==jj) num_div_by_2(&c,cp); else num_set(&c,cp);
    num_snprint (buf+strlen(buf),4096,&c);
    r = alloc_tuple(1);
    Store_field (r,0,copy_string (buf));
  }
  else if (!cp || num_infty(cp)) {
    strncpy(buf,String_val(s),4096);
    strcat(buf," >= ");
    num_neg(&c,cm);
    if ((ii^1)==jj) num_div_by_2(&c,&c);
    num_snprint (buf+strlen(buf),4096,&c);
    r = alloc_tuple(1);
    Store_field (r,0,copy_string (buf));
  }
  else {
    num_neg(&c,cm);
    if (!num_cmp(&c,cp)) {
      strncpy(buf,String_val(s),4096);
      strcat(buf," = ");
      if ((ii^1)==jj) num_div_by_2(&c,cp); else num_set(&c,cp);
      num_snprint (buf+strlen(buf),4096,&c);
      r = alloc_tuple(1);
      Store_field (r,0,copy_string (buf));
    }
    else {
      num_neg(&c,cm);
      if ((ii^1)==jj) num_div_by_2(&c,&c);
      num_snprint (buf,4096,&c);
      strcat(buf," <= ");
      strncat(buf,String_val(s),4096);
      strcat(buf," <= ");
      if ((ii^1)==jj) num_div_by_2(&c,cp); else num_set(&c,cp);
      num_snprint (buf+strlen(buf),4096,&c);
      r = alloc_tuple(1);
      Store_field (r,0,copy_string (buf));
    }
  }
  num_clear (&c);
  CAMLreturn(r);
}

CAMLprim value
ocaml_oct_memprint (value v)
{
  CAMLparam1(v);
  oct_mmalloc_print(oct_mmalloc_get_current());
  CAMLreturn(Val_unit);
}


CAMLprim value
ocaml_oct_timeprint (value v)
{
  CAMLparam1(v);
  oct_timing_print_all ();
  CAMLreturn(Val_unit);
}

/* New Polka interface */

#ifdef OCT_HAS_OCAML_NEW_POLKA

#include <polka_caml.h>

CAMLprim value
ocaml_oct_from_poly (value v)
{
  CAMLparam1(v);
  poly_t* p;
  camlidl_polka_poly_ml2c(v,&p);
  CAMLreturn(Val_oct(oct_from_poly(p)));
}

CAMLprim value
ocaml_oct_to_poly (value v)
{
  CAMLparam1(v);
  poly_t* p = oct_to_poly(Oct_val(v));
  CAMLreturn(camlidl_polka_poly_c2ml(&p));
}

#else

CAMLprim void
ocaml_oct_from_poly (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_oct_from_poly: New Polka library support not enabled");
  CAMLreturn0;
}

CAMLprim void
ocaml_oct_to_poly (value v)
{
  CAMLparam1(v);
  failwith ("ocaml_oct_to_poly: New Polka library support not enabled");
  CAMLreturn0;
}

#endif



CAMLprim value
ocaml_oct_init (value dummy)
{
  CAMLparam1(dummy);
#ifdef OCT_NUM_SERIALIZE
  register_custom_operations(&ocaml_num_custom);
  register_custom_operations(&ocaml_vnum_custom);
  register_custom_operations(&ocaml_oct_custom);
  register_custom_operations(&ocaml_moct_custom);
#endif
  CAMLreturn(oct_init() ? Val_int(1) : Val_int(0));
}
