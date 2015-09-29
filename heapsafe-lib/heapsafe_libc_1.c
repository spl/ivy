/* Copyright (c) 2007 Intel Corporation 
 * All rights reserved. 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 	Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 	Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *     Neither the name of the Intel Corporation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE INTEL OR ITS
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* Some functions in this file are based on Doug Lea's public domain
   dlmalloc.c code, v2.8.3 */

static void clear(void *p, size_t n)
{
#if 0
  double *x = p;
  int32_t nn = n - 4;

  while (nn > 0)
    {
      *x++ = 0;
      nn -= 8;
    }
  if (nn == 0)
    *(uint32_t *)x = 0;
#elif 1
  uint32_t *x = p;

  do
    {
      *x++ = 0;
      n -= 4;
    }
  while (n);
#else
  asm("movl $0, %%eax; movl %0, %%edi; movl %1, %%ecx; rep stosl" : : "r" (p), "r" (n >> 2) : "%%eax", "%%ecx", "%%edi");
#endif
}

static unsigned long bad_frees;
/* Grow an object using mmap */
static int mmap_grow_and_clear(mstate m, mchunkptr oldp, size_t nb) {
  size_t oldsize = chunksize(oldp);

  if (is_small(nb)) /* Can't shrink mmap regions below small size */
    return 0;
  /* Keep old chunk if big enough but not too big */
  if (oldsize >= nb + SIZE_T_SIZE)
    return (oldsize - nb) <= (mparams.granularity << 1);
  else {
    /* grow chunk in place if possible */
    size_t offset = oldp->prev_foot & ~IS_MMAPPED_BIT;
    size_t oldmmsize = oldsize + offset + MMAP_FOOT_PAD;
    size_t newmmsize = granularity_align(nb + SIX_SIZE_T_SIZES +
                                         CHUNK_ALIGN_MASK);
    char* cp = (char*)CALL_MREMAP((char*)oldp - offset,
                                  oldmmsize, newmmsize, 0);
    if (cp != CMFAIL) {
      size_t psize = newmmsize - offset - MMAP_FOOT_PAD;
      oldp->head = (psize|CINUSE_BIT);
      mark_inuse_foot(m, oldp, psize);
      chunk_plus_offset(oldp, psize)->head = FENCEPOST_HEAD;
      chunk_plus_offset(oldp, psize+SIZE_T_SIZE)->head = 0;

      if (cp < m->least_addr)
        m->least_addr = cp;
      if ((m->footprint += newmmsize - oldmmsize) > m->max_footprint)
        m->max_footprint = m->footprint;
      check_mmapped_chunk(m, oldp);

#ifndef MMAP_CLEARS
      void *oldend = (char *)oldp + oldsize;
      size_t extra = psize - oldsize;

      clear(oldend, extra);
#endif

      return 1;
    }
  }
  return 0;
}

static int internal_grow_and_clear(void* oldmem, size_t bytes) {
  if (slow_realloc)
    return 0;

#if ! FOOTERS
    mstate m = gm;
#else /* FOOTERS */
    mstate m = get_mstate_for(mem2chunk(oldmem));
    if (!ok_magic(m)) {
      USAGE_ERROR_ACTION(m, oldmem);
      return 0;
    }
#endif /* FOOTERS */

  if (bytes >= MAX_REQUEST) {
    MALLOC_FAILURE_ACTION;
    return 0;
  }
  if (!PREACTION(m)) {
    mchunkptr oldp = mem2chunk(oldmem);
    size_t oldsize = chunksize(oldp);
    mchunkptr next = chunk_plus_offset(oldp, oldsize);
    int grew = 0;

    /* Try to extend into top. Else fail */

    if (RTCHECK(ok_address(m, oldp) && ok_cinuse(oldp) &&
                ok_next(oldp, next) && ok_pinuse(next))) {
      size_t nb = request2size(bytes);
      if (is_mmapped(oldp))
        grew = mmap_grow_and_clear(m, oldp, nb);
      else if (oldsize >= nb) { /* already big enough */
	/* If we're not shrinking much, just keep this block */
        if (oldsize - nb < MIN_CHUNK_SIZE)
	  grew = 1;
      }
      else if (next == m->top && oldsize + m->topsize > nb) {
        /* Expand into top */
        size_t newsize = oldsize + m->topsize;
        size_t newtopsize = newsize - nb;
        mchunkptr newtop = chunk_plus_offset(oldp, nb);
	void *oldend = (char *)&oldp->head + oldsize;
	size_t extra = nb - oldsize;

        set_inuse(m, oldp, nb);
        newtop->head = newtopsize |PINUSE_BIT;
        m->top = newtop;
        m->topsize = newtopsize;
#ifndef HS_NOCLEAR
	clear(oldend, extra);
#endif
        grew = 1;
      }
    }
    else {
      USAGE_ERROR_ACTION(m, oldmem);
      POSTACTION(m);
      return 0;
    }

    POSTACTION(m);

#ifdef HS_STATS
    if (grew)
      {
	stats_freeing(oldsize);
	stats_allocating(chunksize(mem2chunk(oldmem)));
      }
#endif

    return grew;
  }
  return 0;
}

static size_t dlsizeof(const void *mem) 
{
  mchunkptr mc = mem2chunk(mem);
  size_t s = chunksize(mc);
  assert(!(s & ((1 << __HS_RCLOG) - 1)));
  return s - overhead_for(mc);
}


enum {
  FREELIST_SIZE = 8192
};

#if 0
struct freed {
  void *p;
#ifndef HS_NORC
  hs_type_t t;
#endif
};
#endif

static struct freed main_freelist[FREELIST_SIZE];
static struct freed *freelist_start, *freelist_pos;
unsigned __hs_scount;
__rc_type __hs_rcs[1UL << (32 - __HS_RCLOG)];
static void *indirect_vars[1000000], *direct_vars[1000000];
#ifdef DEFER_GLOBALS
static void **deferred_globals[256], ***last_deferred_global = deferred_globals;
#endif
void **__hs_indirect_vars = indirect_vars, **__hs_direct_vars = direct_vars;

static int extend_freelist(void);
static void free_freelist(void);
static void adjust_direct_refs(int by);
static int check_direct_refs(char *base, char *end);

/* This is noinline so one can easily set a breakpoint on bad frees */
static int __attribute__((noinline)) forcefree(const void *p)
{
  bad_frees++;

  /* The object was still accessible, so there's a chance that it
     will be accessed/modified. Clear the memory to:
     - increase the chance the bug will be caught
     - prevent reference counts from going wrong (we've adjusted the
       refcounts from this object, so if we leave the pointer values
       there any subsequent overwrite will corrupt ref counts) */
  memset((void *)p, 0, dlsizeof(p));

#ifdef HS_NOADJUST
  return 1;
#else
  return free_refed;
#endif

}

static void clear_extra(void *p, size_t n)
{
#ifndef HS_NOCLEAR
  n = (n + 3) & ~3;
  size_t extra = dlsizeof(p) - n;

  if (extra)
    clear((char *)p + n, extra);
#endif
}

static inline void adjust_object(void *x, size_t s, hs_type_t t, int by)
{
#if !(defined(HS_NORC) || defined(HS_NOADJUST))
  if (t)
    t(x, by, s);
#endif
}

void *hs_malloc(size_t reqsize)
{
  void* mem = dlmalloc(reqsize);

  /* Clear all allocated memory to avoid surprises in the "array"
     handling in free */
#ifndef HS_NOCLEAR
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear(mem, dlsizeof(mem)); 
#endif

#ifdef HS_STATS
  if (mem)
    stats_allocating(chunksize(mem2chunk(mem)));
#endif

  return mem;
}

void *hs_memalign(size_t boundary, size_t size)
{
  void *mem = dlmemalign(boundary, size);

  /* Clear all allocated memory to avoid surprises in the "array"
     handling in free */
#ifndef HS_NOCLEAR
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear(mem, dlsizeof(mem)); 
#endif

#ifdef HS_STATS
  if (mem)
    stats_allocating(chunksize(mem2chunk(mem)));
#endif

  return mem;
}

void *hs_calloc(size_t n, size_t s)
{
  void* mem;
  size_t req;

  if (n != 0)
    {
      req = n * s;
      if (((n | s) & ~(size_t)0xffff) && (req / n != s))
	req = MAX_SIZE_T; /* force downstream failure on overflow */
    }
  else
    req = 1;
  mem = dlmalloc(req);
  /* Clear all allocated memory to avoid surprises in the "array"
     handling in free */
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear(mem, dlsizeof(mem));

#ifdef HS_STATS
  if (mem)
    stats_allocating(chunksize(mem2chunk(mem)));
#endif

  return mem;
}

void *hs_typed_realloc(void *p, hs_type_t t, size_t n)
{
  if (!p)
    return hs_malloc(n);

  if (!n)
    {
      hs_typed_free(p, t);
      return NULL;
    }

  if (internal_grow_and_clear(p, n))
    return p;

  /* The inefficient version */
  void *new = hs_malloc(n);
  if (!new)
    return NULL;

  size_t oldsize = dlsizeof(p);
  memcpy(new, p, oldsize < n ? oldsize : n);
  adjust_object(new, n, t, 1);
  hs_typed_free(p, t);

  return new;
}

void hs_typed_free(const void *pp, hs_type_t t)
{
  void *p = (void *)pp;

  if (!p)
    return;

  if (__hs_scount == 0)
    {
	size_t s = dlsizeof(p);

	adjust_object(p, s, t, -1);

#ifdef HS_STATS
	stats_freeing(chunksize(mem2chunk(p)));
#endif

	if (check_direct_refs(p, (char *)p + s) && !forcefree(p))
	  return;

	ircfree(p);
	return;
    }

  if (--freelist_pos == freelist_start)
    if (!extend_freelist())
      {
	/* Oops, no space for freelist. Just free anyway then. */
	size_t s = dlsizeof(p);

	freelist_pos++;
	adjust_object(p, s, t, -1);
#ifdef HS_STATS
	stats_freeing(chunksize(mem2chunk(p)));
#endif
	dlfree(p);
	return;
      }

  freelist_pos->p = p;
#ifndef HS_NORC
  freelist_pos->t = t;
#endif
}

void hs_delayed_free_end(void)
{
#ifndef HS_NOSCOPES
  if (__hs_scount == 0)
    mprintf("invalid delayed free end\n");
  else if (!--__hs_scount && freelist_pos != main_freelist + FREELIST_SIZE)
    free_freelist();
#endif
}

static int extend_freelist(void)
{
  struct freed *newlist = dlmalloc(sizeof(struct freed) * FREELIST_SIZE);

  if (!newlist)
    return 0;

  freelist_pos = newlist + (FREELIST_SIZE - 1);
  newlist->p = freelist_start;
  freelist_start = newlist;

  return 1;
}

static long refcount(const void *p, size_t s)
{
#ifdef HS_NORC
  return 0;
#else
  __rc_type *rcs = &__hs_rcs[(size_t)p >> __HS_RCLOG], *rce;
  __rc_type rc = 0;

  rce = rcs + (s >> __HS_RCLOG);
  do
    {
      int8_t r1 = *rcs;

      if (r1)
	{
	  rc += r1;
	  *rcs = 0;
	}
    }
  while (++rcs < rce);

  return rc;
#endif
}

static void adjust_direct_refs(int by)
{
#if !(defined(HS_NORC) || defined(HS_NOLOCALS))
  void **ref = direct_vars;

  while (ref < __hs_direct_vars)
    {
      void *p = *ref++;
      RC_ADJUST(p, by);
    }

#ifdef DEFER_GLOBALS
  {
    void ***gref = deferred_globals, ***glast = last_deferred_global;
    while (gref < glast)
      {
	void *p = **gref++;
	RC_ADJUST(p, by);
      }
  }
#endif
#endif
}

#ifdef DEFER_GLOBALS
void hs_defer_global(void **g)
{
  *last_deferred_global++ = g;
}
#endif

static int check_direct_refs(char *s, char *e)
{
#if !(defined(HS_NORC) || defined(HS_NOLOCALS))
  void **ref = direct_vars;

  while (ref < __hs_direct_vars)
    {
      uintptr_t r = (uintptr_t)*ref;

      if (r - (uintptr_t)s < (uintptr_t)e - (uintptr_t)s)
	return 1;
      else
	ref++;
    }

#ifdef DEFER_GLOBALS
  {
    void ***gref = deferred_globals, ***glast = last_deferred_global;

    while (gref < glast)
      {
	char *p = **gref++;

	if (p >= s && p < e)
	  return 1;
      }
  }
#endif
#endif

  return 0;
}


#if 0
static void free_small_freelist(void)
{
  struct freed *pos;

  foo++;

#ifndef HS_NORC
  pos = freelist_pos;
  size_t s = dlsizeof(pos->p);

  adjust_object(pos->p, dlsizeof(pos->p), pos->t, -1);
  if (check_direct_refs((char *)pos->p, (char *)pos->p + s) &&
      !forcefree())
    return;
#endif

  rcfree(pos->p);

  freelist_pos = main_freelist + FREELIST_SIZE;
}
#endif

static void free_freelist(void)
{
  struct freed *start, *pos, *end;
  unsigned long count = 0;

#ifndef HS_NORC
  pos = freelist_pos;
  start = freelist_start;
  for (;;)
    {
      for (end = start + FREELIST_SIZE; pos != end; pos++)
	{
	  adjust_object(pos->p, dlsizeof(pos->p), pos->t, -1);
	  count++;
	}

      if (start == main_freelist)
	break;
      start = start->p;
      pos = start + 1;
    }
#endif

#ifdef HS_STATS
  stats_scope(count);
#endif

  adjust_direct_refs(1);
  pos = freelist_pos;
  start = freelist_start;
  for (;;)
    {
      for (end = start + FREELIST_SIZE; pos != end; pos++)
	{
#ifdef HS_STATS
	  stats_freeing(chunksize(mem2chunk(pos->p)));
#endif
	  rcfree(pos->p);
	}
      if (start == main_freelist)
	break;
      start = start->p;
      dlfree(end - FREELIST_SIZE);
      pos = start + 1;
    }
  adjust_direct_refs(-1);

  freelist_start = main_freelist;
  freelist_pos = main_freelist + FREELIST_SIZE;
}

__attribute__((destructor)) static void exit_report(void)
{
  if (printlog)
    {
      double clktck = sysconf(_SC_CLK_TCK);
      struct tms cpu_e;
      struct rusage usage;

      times(&cpu_e);
      if (getrusage(RUSAGE_SELF, &usage) < 0)
	perror("getrusage");

      print_header();

      if (shortlog)
	{
	  mprintf(", %10.2f, %10.2f, %10lu, %10lu\n",
		  (cpu_e.tms_utime + cpu_e.tms_stime) / clktck,
		  cpu_e.tms_utime / clktck, usage.ru_majflt, usage.ru_minflt);
	}
      else
	{
	  mprintf("cputime: %.2f\n", (cpu_e.tms_utime + cpu_e.tms_stime) / clktck);
	  mprintf("  (user: %.2f)\n", cpu_e.tms_utime / clktck);
	  mprintf("faults maj/min: %lu/%lu\n", usage.ru_majflt, usage.ru_minflt);
	}

#ifdef HS_STATS
      stats_report(shortlog);
#endif

#if 0
      /* This gets triggered by calls to exit, so is confusing */
      if (direct_vars != __hs_direct_vars)
	mprintf("__hs_direct_vars went wrong by %d\n", __hs_direct_vars - direct_vars);
      if (indirect_vars != __hs_indirect_vars)
	mprintf("__hs_indirect_vars went wrong by %d\n", __hs_indirect_vars - indirect_vars);
#endif

      if (!shortlog || bad_frees)
	mprintf("%lu bad frees\n", bad_frees);
    }
}

__attribute__((constructor)) static void heapsafe_init(void)
{
  dlmalloc(1); /* Work around unitialised mstate bug */
  parse_options();
  mprintf_init();

  freelist_start = main_freelist;
  freelist_pos = main_freelist + FREELIST_SIZE;
}

#include "typed.c"
#include "compat.c"
