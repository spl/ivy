#ifdef __APPLE__
void *malloc(size_t reqsize)
{
  return hs_malloc(reqsize);
}

void *calloc(size_t n, size_t s)
{
  return hs_calloc(n, s);
}
#else
#include "symbols.h"

strong_alias(hs_malloc, malloc);
strong_alias(hs_memalign, memalign);
strong_alias(hs_calloc, calloc);
#endif

void free(void *p)
{
  return hs_typed_free(p, 0);
}

void *realloc(void *p, size_t n)
{
  return hs_typed_realloc(p, 0, n);
}
