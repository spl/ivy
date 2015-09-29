/* oct_ocaml.h
   Include this to access to OCaml wrappers for the C library data-structures.

   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#ifndef OCT_OCAMLH__
#define OCT_OCAMLH__

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>

#include <oct.h>
#include <oct_private.h>

#ifdef __cplusplus
extern "C" {
#endif

/* value <-> num_t conversion */

typedef struct /* array of num_t */
{
  size_t nb;
  num_t* n;
} vnum_t;

#define Num_val(v) ((num_t*)Data_custom_val(v))   /* v: Oct.num */
#define Vnum_val(v) ((vnum_t*)Data_custom_val(v)) /* v: Oct.vnum */

/* value <-> oct_t conversion */
#define Oct_val(v) (*((oct_t**)Data_custom_val(v))) /* v: Oct.oct */
value   Val_oct (const oct_t* o); /* Return a *new* value containing o */

/* value <-> moct_t conversion */
#define Moct_val(v) (*((moct_t**)Data_custom_val(v)))  /* v: Oct.moct */
value   Val_moct (const moct_t* o); /* Return a *new* value containing o */

/* Use Int_val / Val_int to convert objects of type
    tbool_t / Oct.tbool, 
    oct_widening_type / Oct.wident
*/



#ifdef __cplusplus
}
#endif

#endif
