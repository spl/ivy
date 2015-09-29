#include <limits.h>
#include <sys/param.h>
#include <stdlib.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>

CAMLprim value ocaml_realpath(value inpath)
{
  char resolved[PATH_MAX];

  CAMLparam1 (inpath);

  if (realpath(String_val(inpath), resolved))
    CAMLreturn (caml_copy_string(resolved));
  else
    CAMLreturn (caml_copy_string("")); /* failure marker */
}
