/* Debugging support */
#define PTRALIGNMENT __alignof(void *)
#define PTRSIZE sizeof(void *)
#define ALIGNUP(x, n) (((x) + ((n) - 1)) & ~((n) - 1))
#define PALIGNUP(x, n) ((void *)ALIGNUP((unsigned long)(x), n))


#ifdef __APPLE__
#include <mach-o/getsect.h>
#else
extern int __data_start, _end;
#define get_etext() ((unsigned long)&__data_start)
#define get_end() ((unsigned long)&_end)
#endif

static FILE *out;

static header_t *refinfo(void *x)
{
  if ((unsigned long)x >= get_etext() && (unsigned long)x < get_end())
    {
      fprintf(out, "[%p global]", x);
      return NULL;
    }
  void **vars;
  for (vars = indirect_vars; vars < __hs_indirect_vars; vars += 3)
    {
      size_t s = (size_t)vars[1];

      if (x >= vars[0] && (char *)x < (char *)vars[0] + s)
	{
	  fprintf(out, "[%p in local %p/%lu]", x, vars[0], (unsigned long)s);
	  return NULL;
	}
    }
  header_t *h = locateobject(x);
  if (h)
    {
      fprintf(out, "[%p in O:%p/%lu (A:%s:%d)]",
	      x, h + 1, (unsigned long)(dlsizeof(h) - sizeof(header_t)),
	      h->alloc_loc.file, h->alloc_loc.line);
      return h;
    }
  fprintf(out, "[%p unknown]", x);
  return NULL;
}

static void printdref(void *value)
{
  fprintf(out, "# stack contains value %p\n", value);
}

static void printrcref(__rcinfo *ref, char *expected_target)
{
  /* Check if pointer described by ref points to expected address */
  int valid = *(char **)ref->from >= expected_target &&
    *(char **)ref->from < expected_target + (1 << __HS_RCLOG);

  fprintf(out, "#R:");
  refinfo(ref->from);
  fprintf(out, " to %p, W:%s:%d%s\n",
	  *(void **)ref->from, ref->loc.file, ref->loc.line,
	  valid ? "" : " INVALID");
}

static void rcinfo_object(header_t *obj)
{
  size_t objsize = dlsizeof(obj);
  void *objend = (char *)obj + objsize;

  void **vars;
  for (vars = direct_vars; vars < __hs_direct_vars; vars++)
    {
      void *p = *vars;

      if (p >= (void *)obj && p <= objend)
	printdref(p);
    }

  __rcinfo **rcs = reflist_for(obj);
  __rcinfo **rce = rcs + (objsize >> __HS_RCLOG) + 1; /* +1 because objsize is a bit less than a multiple of 1 << HS_RCLOG */
  __rcinfo *l;
  /* objp[0..1 << __HS_RCLOG - 1] is where the rcinfo values 
     should be pointing */
  char *objp = (char *)obj;

  while (rcs < rce)
    {
      l = *rcs++;

      if ((uintptr_t)l & 1)
	{
	  refhash_table refs = (refhash_table)((uintptr_t)l & ~1);
	  unsigned long i;
	  
	  for (i = 0; i < refs->size; i++)
	    for (l = refs->elements[i]; l; l = l->next)
	      printrcref(l, objp);
	}
      else
	for (; l; l = l->next)
	  printrcref(l, objp);

      objp += 1 << __HS_RCLOG;
    }
}

void hsinfo(void *x)
{
  if (!out)
    out = fopen("/dev/tty", "w");

  header_t *obj = refinfo(x);
  fprintf(out, "\n");
  if (obj)
    rcinfo_object(obj);

  fflush(out);
}

