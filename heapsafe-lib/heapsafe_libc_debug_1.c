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
#ifndef NOCLEAR
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

    return grew;
  }
  return 0;
}

enum {
  FREELIST_SIZE = 8192
};

struct freed {
  void *h;
  __rc_location loc;
#ifndef NORC
  hs_type_t t;
#endif
};

static struct freed main_freelist[FREELIST_SIZE];
static struct freed *freelist_start, *freelist_pos;
unsigned __hs_scount;
__rcinfo *__rc_refs[1UL << (32 - __HS_RCLOG)], *__rcinfo_freelist;
static void *indirect_vars[1000000], *direct_vars[1000000];
void **__hs_indirect_vars = indirect_vars, **__hs_direct_vars = direct_vars;
__rc_location __rc_loc;
static header_t memhead, memtail;
static int meminit;


static int extend_freelist(void);
static void free_freelist(void);
static void adjust_direct_refs(int by);
static int check_direct_refs(const char *base, size_t s);

#ifdef HS_STATS
#include "stats_debug.c"
#endif

#define INFO_CHUNK 65534

static size_t dlsizeof(header_t *h) 
{
  mchunkptr mc = mem2chunk(h);
  size_t s = chunksize(mc);
  assert(!(s & ((1 << __HS_RCLOG) - 1)));
  return s - overhead_for(mc);
}

static __rcinfo **reflist_for(const void *ptr)
{
  return &__rc_refs[(uintptr_t)ptr >> __HS_RCLOG];
}

static header_t *locateobject(void *x)
{
  header_t *h;

  if (meminit)
    for (h = memhead.links.next; h->links.next; h = h->links.next)
      {
	size_t s = dlsizeof(h);

	if (x >= (void *)h && x < (void *)((char *)h + s))
	  return h;
      }
  return NULL;
}


void __hs_rcinfo_refill(void)
{
  __rcinfo *newchunk = dlmalloc(INFO_CHUNK * sizeof(*newchunk));
  long i;

  if (!newchunk)
    {
      fprintf(stderr, "out of memory (internal refs)\n");
      exit(2);
    }

  newchunk[0].next = NULL;
  for (i = 1; i < INFO_CHUNK; i++)
    newchunk[i].next = &newchunk[i - 1];

  __rcinfo_freelist = &newchunk[INFO_CHUNK - 1];
}

static __rcinfo *__hs_rcinfo_alloc(void)
{
  __rcinfo *entry;

  if (!__rcinfo_freelist)
    __hs_rcinfo_refill();
  
  entry = __rcinfo_freelist;
  __rcinfo_freelist = entry->next;

  return entry;
}

static void __hs_rcinfo_free(__rcinfo *entry)
{
  entry->next = __rcinfo_freelist;
  __rcinfo_freelist = entry;
}

#include "refhash.c"

static unsigned log2p1(unsigned n)
{
  unsigned x, l;

  for (l = 0, x = 1; x && x < n; l++)
    x <<= 1;

  return l;
}

void __hs_rc_big(void *ptr)
{
  __rcinfo **list = reflist_for(ptr), *entry, *next;
  unsigned long len = 0, size;

  for (entry = *list; entry; entry = entry->next)
    len++;

  size = 1 << log2p1(len);
  if (7 * (size / 8) < len)
    size *= 2;

  refhash_table refs = rhnew(size);

  for (entry = *list; entry; entry = next)
    {
      next = entry->next;
      rhadd(refs, entry);
    }
  update_quality(refs);

  *list = (__rcinfo *)((uintptr_t)refs | 1);
}

static refhash_table refhash_for(void *ptr)
{
  uintptr_t adr = (uintptr_t)*reflist_for(ptr) & ~1;

  return (refhash_table)adr;
}

int __hs_rcref(void *from, void *ptr)
{
  __rcinfo **list = &__rc_refs[(uintptr_t)ptr >> __HS_RCLOG], *entry;

  if ((uintptr_t)*list & 1)
    {
      refhash_table refs = refhash_for(ptr);

      entry = __hs_rcinfo_alloc();
      entry->from = from;
      entry->loc = __rc_loc;
      rhadd(refs, entry);
    }
  else
    {
      entry = __hs_rcinfo_alloc();
      entry->from = from;
      entry->loc = __rc_loc;
      entry->next = *list;
      *list = entry;
    }
  return 0;
}

static void __attribute__((noinline)) badref(void *from, void *ptr) 
{
  /* Called when we can't find a reference from 'from' to 'ptr' to remove */
}

/* The deref_slow_list/hash functions handle the case where we didn't
   find an entry for from in ptr's references. At that point, we
   search for any reference from the object containing from and remove
   that instead. This supports functions like qsort, which:
   - are not compiled by HeapSafe
   - may copy pointers
   - but, only permute pointers within an object, so do not lead to
     incorrect per-object reference counts (and hence bad frees) with
     the non-debug library.

   The search/removal process avoids reporting bad frees with the
   debug library which are not a problem with the regular library.

   If we cannot find any reference to remove, we call the badref function
   (setting a breakpoint there can be useful for tracking down reference
   counting problems).
*/

static void deref_slow_list(void *from, void *ptr)
{
  void *from_s = locateobject(from), *from_e;
  __rcinfo **list = &__rc_refs[(uintptr_t)ptr >> __HS_RCLOG], *entry;

  if (!from_s)
    {
      badref(from, ptr);
      return;
    }

  /* Scan ptr's references for something within from_s .. from_e */
  from_e = (char *)from_s + dlsizeof(from_s);
  while ((entry = *list))
    {
      if (entry->from >= from_s && entry->from <= from_e)
	{
	  *list = entry->next;
	  __hs_rcinfo_free(entry);
	  return;
	}
      list = &entry->next;
    }

  badref(from, ptr);
}

static void deref_slow_hash(void *from, void *ptr)
{
  void *from_s = locateobject(from), *from_e;
  __rcinfo *entry;
  refhash_table refs;

  if (!from_s)
    {
      badref(from, ptr);
      return;
    }

  /* Check the reference hash table for something in the from_s .. from_e range */
  from_e = (char *)from_s + dlsizeof(from_s);
  refs = refhash_for(ptr);
  entry = rhlookup_range(refs, from_s, from_e, 1);
  if (entry)
    {
      __hs_rcinfo_free(entry);
      if (rhused(refs) == 0)
	{
	  rhfree(refs);
	  *reflist_for(ptr) = 0;
	}
    }
  else
    badref(from, ptr);
}

int __hs_rcderef(void *from, void *ptr)
{
  __rcinfo **list = &__rc_refs[(uintptr_t)ptr >> __HS_RCLOG], *entry;

  if ((uintptr_t)*list & 1)
    {
      refhash_table refs = refhash_for(ptr);

      entry = rhlookup(refs, from, 1);
      if (entry)
	{
	  __hs_rcinfo_free(entry);
	  if (rhused(refs) == 0)
	    {
	      rhfree(refs);
	      *reflist_for(ptr) = 0;
	    }
	}
      else
	deref_slow_hash(from, ptr);
    }
  else
    {
      unsigned len = 0;

      while ((entry = *list))
	{
	  len++;
	  if (entry->from == from)
	    {
	      *list = entry->next;
	      __hs_rcinfo_free(entry);
	      goto done;
	    }
	  list = &entry->next;
	}
      /* Removed unknown ref - see if the pointer could've moved within the
	 same object. */
      deref_slow_list(from, ptr);
    done:
      if (len > __HS_LIST_MAX)
	__hs_rc_big(ptr);
    }
  return 0;
}

static int __attribute__((noinline)) forcefree(header_t *h)
{
  bad_frees++;

  /* The object was still accessible, so there's a chance that it
     will be accessed/modified. Clear the memory to:
     - increase the chance the bug will be caught
     - prevent reference counts from going wrong (we've adjusted the
       refcounts from this object, so if we leave the pointer values
       there any subsequent overwrite will corrupt ref counts) */
  memset(h + 1, 0, dlsizeof(h) - sizeof(header_t));

#ifdef NOADJUST
  return 1;
#else
  return free_refed;
#endif

}

static inline void adjust_object(void *x, size_t s, hs_type_t t, int by)
{
#if !(defined(HS_NORC) || defined(HS_NOADJUST))
  if (t)
    t(x, by, s);
#endif
}

static void *memlink(header_t *h)
{
  if (!meminit)
    {
      meminit = 1;
      memhead.links.prev = memtail.links.next = NULL;
      memhead.links.next = &memtail;
      memtail.links.prev = &memhead;
    }

  if (!h)
    return NULL;

  h->links.next = memhead.links.next;
  h->links.prev = &memhead;
  memhead.links.next->links.prev = h;
  memhead.links.next = h;

  return h + 1;
}

static void memunlink(header_t *h)
{
#ifdef HS_STATS
  stats_freeing(h->size);
#endif
  h->links.prev->links.next = h->links.next;
  h->links.next->links.prev = h->links.prev;
  h->links.next = h->links.prev = NULL; /* paranoia */
}

static header_t *headerof(void *p)
{
  return (header_t *)((char *)p - sizeof(header_t));
}

static void *init_header(header_t *h, unsigned long size)
{
  h->alloc_loc = __rc_loc;
#ifdef HS_STATS
  h->size = size;
  stats_allocating(size);
#endif
  return memlink(h);
}

void *hs_malloc(size_t reqsize)
{
  void* mem = dlmalloc(reqsize + sizeof(header_t));

  /* Clear all allocated memory to avoid surprises in the "array"
     handling in free */
#ifndef HS_NOCLEAR
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear(mem, dlsizeof(mem)); 
#endif

  return init_header(mem, reqsize);
}

static void clear_extra(header_t *h, size_t n)
{
  n = (n + 3) & ~3;
  size_t extra = dlsizeof(h) - n;

  if (extra)
    clear((char *)h + n, extra);
}

void *__hs_malloc_noclear(size_t reqsize)
{
  void *mem = dlmalloc(reqsize + sizeof(header_t));

  /* Clear extra allocated memory to avoid surprises in the "array"
     handling in free (the explicit clearing in code that calls
     __hs_malloc_noclear will not see this extra memory) */
#ifndef HS_NOCLEAR
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear_extra(mem, reqsize + sizeof(header_t));
#endif

  return init_header(mem, reqsize);
}

void *hs_memalign(size_t boundary, size_t size)
{
  void *mem;

  /* Life is nicer if the boundary is >= than a debug header... */
  while (boundary < sizeof(header_t))
    boundary <<= 1;

  /* We need to get an extra boundary bytes so that we can return something
     w/ a header and aligned to boundary bytes... */
  mem = dlmemalign(boundary, size + boundary);
  /* Clear all allocated memory to avoid surprises in the "array"
     handling in free */
#ifndef HS_NOCLEAR
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear(mem, dlsizeof(mem)); 
#endif
  mem = (char *)mem + boundary - sizeof(header_t);

  return init_header(mem, size);
}

void *hs_calloc(size_t n, size_t s)
{
  void* mem;
  size_t req;

  if (n != 0)
    {
      req = n * s;
      if (((n | s) & ~(size_t)0xffff) && (req / n != s))
	req = MAX_SIZE_T - sizeof(header_t); /* force downstream failure on overflow */
    }
  else
    req = 0;

  mem = dlmalloc(req + sizeof(header_t));
  /* Clear all allocated memory to avoid surprises in the "array"
     handling in free */
  if (mem != 0 && calloc_must_clear(mem2chunk(mem)))
    clear(mem, dlsizeof(mem));

  return init_header(mem, req);
}

void *hs_typed_realloc(void *p, hs_type_t t, size_t n)
{
  header_t *h;

  if (!p)
    return hs_malloc(n);

  if (!n)
    {
      hs_typed_free(p, t);
      return NULL;
    }

  h = headerof(p);
  if (internal_grow_and_clear(h, n + sizeof(header_t)))
    {
      h->alloc_loc = __rc_loc;
#ifdef HS_STATS
      stats_freeing(h->size);
      h->size = n;
      stats_allocating(h->size);
#endif
      return p;
    }

  /* The inefficient version */
  void *new = hs_malloc(n);
  if (!new)
    return NULL;

  size_t oldsize = dlsizeof(h) - sizeof(header_t);
  memcpy(new, p, oldsize < n ? oldsize : n);
  adjust_object(new, n, t, 1);
  hs_typed_free(p, t);

  return new;
}

void hs_typed_free(const void *pp, hs_type_t t)
{
  void *p = (void *)pp;
  header_t *h;

  if (!p)
    return;

  h = headerof(p);
  if (__hs_scount == 0)
    {
	size_t s = dlsizeof(h) - sizeof(header_t);
	adjust_object(p, s, t, -1);

	rcfree(h);
	return;
    }

  if (--freelist_pos == freelist_start)
    if (!extend_freelist())
      {
	/* Oops, no space for freelist. Just free anyway then. */
	size_t s = dlsizeof(h) - sizeof(header_t);
	freelist_pos++;
	adjust_object(p, s, t, -1);
	memunlink(h);
	dlfree(h);
	return;
      }

  freelist_pos->h = h;
  freelist_pos->loc = __rc_loc;
#ifndef HS_NORC
  freelist_pos->t = t;
#endif
}

void hs_delayed_free_end(void)
{
#ifndef HS_NOSCOPES
  if (__hs_scount == 0)
    mprintf("invalid scoped free end\n");
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
  newlist->h = freelist_start;
  freelist_start = newlist;

  return 1;
}

static int check_direct_refs(const char *s, size_t l)
{
#if !(defined(HS_NORC) || defined(HS_NOLOCALS))
  void **ref = direct_vars;

  while (ref < __hs_direct_vars)
    {
      uintptr_t r = (uintptr_t)*ref;

      if (r - (uintptr_t)s < l)
	return 1;
      else
	ref++;
    }
#endif

  return 0;
}

static long refcount(const void *p, size_t s)
{
#ifndef HS_NORC
  __rcinfo **rcs = reflist_for(p), **rce;

  rce = rcs + (s >> __HS_RCLOG);
  do
    {
      if (*rcs)
	return 1;
    }
  while (++rcs < rce);
#endif

  return check_direct_refs(p, s);
}

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
	  __rc_loc = pos->loc;
	  adjust_object((header_t *)pos->h + 1,
			dlsizeof(pos->h) - sizeof(header_t), pos->t, -1);
	  count++;
	}

      if (start == main_freelist)
	break;
      start = start->h;
      pos = start + 1;
    }
#endif

#ifdef HS_STATS
  stats_scope(count);
#endif

  pos = freelist_pos;
  start = freelist_start;
  for (;;)
    {
      for (end = start + FREELIST_SIZE; pos != end; pos++)
	rcfree(pos->h);
      if (start == main_freelist)
	break;
      start = start->h;
      dlfree(end - FREELIST_SIZE);
      pos = start + 1;
    }

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
#if 0
#ifdef __APPLE__
	  mprintf("rss: max %lu, ix %lu, id %lu, is %lu\n",
		  usage.ru_maxrss, usage.ru_ixrss, usage.ru_idrss, usage.ru_isrss);
#endif
#endif
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
#include "findrefs.c"

