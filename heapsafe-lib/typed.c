void *hs_typed_memcpy(void *to, void *from, size_t size, hs_type_t t)
{
#ifndef NORC
  if (t && size)
#ifdef __HS_NOCONCRC__
    t(to, -1, size);
#else
    t(to, -1, size, 0);
#endif
#endif

  memcpy(to, from, size);

#ifndef NORC
  if (t && size)
#ifdef __HS_NOCONCRC__
    t(to, 1, size);
#else
    t(to, 1, size, 0);
#endif
#endif

  return to;
}

void *hs_typed_memmove(void *to, void *from, size_t size, hs_type_t t)
{
#ifndef NORC
  if (t && size)
#ifdef __HS_NOCONCRC__
    t(to, -1, size);
#else
    t(to, -1, size, 0);
#endif
#endif

  memmove(to, from, size);

#ifndef NORC
  if (t && size)
#ifdef __HS_NOCONCRC__
    t(to, 1, size);
#else
    t(to, 1, size, 0);
#endif
#endif

  return to;
}

void *hs_typed_memset(void *to, int c, size_t size, hs_type_t t)
{
#ifndef NORC
  if (t && size)
#ifdef __HS_NOCONCRC__
    t(to, -1, size);
#else
    t(to, -1, size, 0);
#endif
#endif

  memset(to, c, size);

#ifndef NORC
  if (t && size && c)
#ifdef __HS_NOCONCRC__
    t(to, 1, size);
#else
    t(to, 1, size, 0);
#endif
#endif

  return to;
}

void hs_typed_mutate(void *obj, void *union_part, hs_type_t obj_t, size_t union_size)
{
#ifndef NORC
#ifdef __HS_NOCONCRC__
  obj_t(obj, -1, 0);
#else
  obj_t(obj, -1, 0, 0);
#endif
#endif
  memset(union_part, 0, union_size);
#ifndef NORC
#ifdef __HS_NOCONCRC__
  obj_t(obj, 1, 0);
#else
  obj_t(obj, 1, 0, 0);
#endif
#endif
}
