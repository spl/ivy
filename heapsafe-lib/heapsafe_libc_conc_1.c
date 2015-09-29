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

#include <pthread.h>
#include "heapsafe_internals.h"

#define STOREBARRIER asm volatile("sfence" : : : "memory")
#define GCCBARRIER asm volatile("" : : : "memory")

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

unsigned int __hs_num_threads;
volatile int __hs_rcidx;
pthread_mutex_t thread_list_mutex = PTHREAD_MUTEX_INITIALIZER;
struct chs_thread *thread_list_head = NULL;
volatile unsigned char __hs_dirty[2][1UL << (32 - __HS_DIRTY)];
volatile __rc_type __hs_rcs[1UL << (32 - __HS_RCLOG)];

#ifdef __APPLE__
/* No __thread */
pthread_key_t __this_chs_thread_key;
#define CHS_THREAD_INIT() (pthread_key_create(&__this_chs_thread_key, NULL))

#else

__thread struct chs_thread *__this_chs_thread;

#define CHS_THREAD_INIT()
#endif

static int extend_freelist(void);
static void free_freelist(void);
static void adjust_direct_refs(int by);
//static int check_direct_refs(char *base, char *end);

/* This is noinline so one can easily set a breakpoint on bad frees */
static int __attribute__((noinline)) forcefree(const void *p)
{
  bad_frees++; /* XXX: Make update atomic */

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

static inline void adjust_object(void *x, int by, size_t s, hs_type_t t, int inv)
{
#if !(defined(HS_NORC) || defined(HS_NOADJUST))
  if (t)
    t(x, by, s, inv);
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
  //adjust_object(new,-1,n,t,0);
  memcpy(new, p, oldsize < n ? oldsize : n);
  adjust_object(new, 1, n, t, 0);
  hs_typed_free(p, t);

  return new;
}

void hs_typed_free(const void *pp, hs_type_t t)
{
  void *p = (void *)pp;
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();

  if (!p)
    return;

  if (!this_chs_thread) {
    dlfree(p);
    return;
  }

  __builtin_hs_argnull();

  if (this_chs_thread->__hs_scount == 0)
    {
      size_t s = dlsizeof(p);

      adjust_object(p, 0, s, t, 1);

#ifdef HS_STATS
      stats_freeing(chunksize(mem2chunk(p)));
#endif

      //if (check_direct_refs(p, (char *)p + s) && !forcefree(p))
      //  return;

      ircfree(p);
      return;
    }

  if (--this_chs_thread->freelist_pos == this_chs_thread->freelist_start)
    if (!extend_freelist())
      {
	/* Oops, no space for freelist. Just free anyway then. */
	size_t s = dlsizeof(p);

	this_chs_thread->freelist_pos++;
	adjust_object(p, 0, s, t, 1);
#ifdef HS_STATS
	stats_freeing(chunksize(mem2chunk(p)));
#endif
	dlfree(p);
	return;
      }

  this_chs_thread->freelist_pos->p = p;
#ifndef HS_NORC
  this_chs_thread->freelist_pos->t = t;
#endif
}

void hs_delayed_free_start(void) {
#ifndef HS_NOSCOPES
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  this_chs_thread->__hs_scount++;
#endif
}

void hs_delayed_free_end(void)
{
#ifndef HS_NOSCOPES
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  if (this_chs_thread->__hs_scount == 0)
    mprintf("invalid delayed free end\n");
  else if (!--this_chs_thread->__hs_scount &&
           this_chs_thread->freelist_pos != this_chs_thread->freelist_main + FREELIST_SIZE)
    free_freelist();
#endif
}

static int extend_freelist(void)
{
  struct freed *newlist = dlmalloc(sizeof(struct freed) * FREELIST_SIZE);
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();

  if (!newlist)
    return 0;

  this_chs_thread->freelist_pos = newlist + (FREELIST_SIZE - 1);
  newlist->p = this_chs_thread->freelist_start;
  this_chs_thread->freelist_start = newlist;

  return 1;
}

int existsOldOrChoosingIdx(int oldidx)
{
  struct chs_thread *tmp;

  pthread_mutex_lock(&thread_list_mutex);
  tmp = thread_list_head;
  while (tmp) {
    if (tmp->rcidx == oldidx || tmp->choosingidx) {
      pthread_mutex_unlock(&thread_list_mutex);
      return 1;
    }
    tmp = tmp->next;
  }
  pthread_mutex_unlock(&thread_list_mutex);

  return 0;
}

int arr_exists(void **arr, void *val, int max)
{
  int i;
  for (i = 0; i < max; i++)
    if (arr[i] == val)
      return 1;

  return 0;
}

pthread_mutex_t rcs_mutex = PTHREAD_MUTEX_INITIALIZER;
static void *undetermined_slots[100000];
static void *peek_update_slots[100000];
static void *peek_update_olds[100000];
long hs_refcount(const void *p, size_t s, unsigned int zero)
{
  int i;
  unsigned int oldidx;
  int und_index = 0;
  int peek_index = 0;
  struct chs_thread *tmp;
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();

  pthread_mutex_lock(&rcs_mutex);

  oldidx = __hs_rcidx;
  __hs_rcidx = __hs_rcidx ? 0 : 1;
  while (existsOldOrChoosingIdx(oldidx))
#ifdef __APPLE__
    sched_yield();
#else
  pthread_yield();
#endif

  pthread_mutex_lock(&thread_list_mutex);
  tmp = thread_list_head;
  while (tmp) {
    void **slots_pos = tmp->slots_pos[oldidx];
    void **olds_pos = tmp->olds_pos[oldidx];

    while (--slots_pos >= tmp->slots[oldidx]) 
      {
	void *slot = *slots_pos;
	void *old  = *--olds_pos;


	if ((unsigned int)slot & 0x1) 
	  {
	    /* invalidation log. non-updated slot was invalidated. */
	    if (old) __hs_rcs[(size_t)old >> __HS_RCLOG]--;
#ifdef CRC_DEBUG
	    printf("%p DEC0<%p> %p -> %p\n", this_chs_thread, tmp, slot, old);
#endif
	  }
	else if (slot && CHECK_DIRTY(oldidx,slot)) 
	  {
	    size_t val;

	    /* updated since last rc */
	    if (old) __hs_rcs[(size_t)old >> __HS_RCLOG]--;
	    val = *(size_t *)slot;
	    GCCBARRIER;
	    if (CHECK_DIRTY(__hs_rcidx,slot))
	      {
		/* updated since last rc, and updated again since log switch */
		undetermined_slots[und_index++] = slot;
#ifdef CRC_DEBUG
		printf("%p DEC99<%p> %p -> %p\n", this_chs_thread, tmp, slot, old);
#endif
	      }
	    else
	      {
		/* updated since last rc, and no updates since log switch */
		__hs_rcs[val >> __HS_RCLOG]++;
#ifdef CRC_DEBUG
		printf("%p DEC/INC<%p> %p: %p -> %x\n", this_chs_thread, tmp, slot, old, val);
#endif
	      }
	  }
	else if (slot && !CHECK_DIRTY(__hs_rcidx,slot)) 
	  {
	    /* updated since last rc, but then invalidated,
	       not updated since log switch */
	    if (old) __hs_rcs[(size_t)old >> __HS_RCLOG]--;
#ifdef CRC_DEBUG
	    printf("%p DEC3<%p> %p -> %p\n", this_chs_thread, tmp, slot, old);
#endif
	  }
	else if (slot) 
	  {
	    /* updated since last rc, but then invalidated, and then updated
	       again since log switch */
	    if (old) __hs_rcs[(size_t)old >> __HS_RCLOG]--;
	    undetermined_slots[und_index++] = slot;
#ifdef CRC_DEBUG
	    printf("DEC4<%p> %p -> %p\n", tmp, slot, old);
#endif
	  }
	CLEAR_DIRTY(oldidx,slot);
      }

    tmp->slots_pos[oldidx] = tmp->slots[oldidx];
    tmp->olds_pos[oldidx] = tmp->olds[oldidx];
    tmp = tmp->next;
  }

  tmp = thread_list_head;
  while (tmp) 
    {
      void **slots_pos = tmp->slots_pos[__hs_rcidx];
      void **olds_pos = tmp->olds_pos[__hs_rcidx];

      while (--slots_pos >= tmp->slots[__hs_rcidx]) 
	{
	  void *slot = *slots_pos;
	  void *old  = *--olds_pos;

	  if (!arr_exists(peek_update_slots,slot,peek_index-1)) 
	    {
	      peek_update_slots[peek_index] = slot;
	      peek_update_olds[peek_index] = old;
	      peek_index++;
	    }
	}
      tmp = tmp->next;
    }

  for (i = 0; i < peek_index; i++) 
    {
      void *slot = peek_update_slots[i];
      void *old = peek_update_olds[i];
      if (arr_exists(undetermined_slots,slot,und_index))
	if (old) 
	  {
	    __hs_rcs[(size_t)old >> __HS_RCLOG]++;
#ifdef CRC_DEBUG
	    printf("%p INC1 %p\n", this_chs_thread, old);
#endif
	  }
    }

  if (p) 
    {
      __rc_type *rcs = &__hs_rcs[(size_t)p >> __HS_RCLOG], *rce;
      __rc_type rc = 0;
      __rc_type lrc = 0;

      rce = rcs + ((s + (1 << __HS_RCLOG) - 1) >> __HS_RCLOG);
      do 
	{
	  int8_t r1 = *rcs;

	  if (r1) 
	    {
	      rc += r1;
	      if (zero) *rcs = 0;
	    }
	} 
      while (++rcs < rce);

      tmp = thread_list_head;
      while (tmp) 
	{
	  int idx = tmp->dvar_head;
	  while(idx != -1) 
	    {
	      unsigned addr = (unsigned)tmp->direct_vars[idx].addr;
	      if (addr == -1) 
		{
		  idx = tmp->direct_vars[idx].next;
		  //continue;
		}
	      else 
		{
		  unsigned contents = *(unsigned *)addr;
		  if (((unsigned)p <= contents &&
		       contents < ((unsigned)p + s))) 
		    {
		      lrc++;
#if 0
		      printf("IVYDEBUG: hs_refcount: thread %p found %x in (%x,%d) at %x\n",
			     tmp, contents, (unsigned)p, s, addr);
#endif
		    }
		  idx = tmp->direct_vars[idx].next;
		}
	    }
	  tmp = tmp->next;
	}

#ifdef CRC_DEBUG
      printf("IVYDEBUG: hs_refcount(%p,%p,%d,%d,log=%d) = %d heap + %d local = %d\n",
	     GET_CHS_THREAD(),p, s, zero, oldidx, rc, lrc, rc + lrc);
      fflush(0);
#endif
      pthread_mutex_unlock(&thread_list_mutex);
      pthread_mutex_unlock(&rcs_mutex);
      return rc + lrc;
    }
  else 
    {
      pthread_mutex_unlock(&thread_list_mutex);
      pthread_mutex_unlock(&rcs_mutex);
      return 0;
    }
}

static long refcount(const void *p, size_t s)
{
#ifdef HS_NORC
  return 0;
#else
  /* Note: the size s actually includes the header of the next
     object, so adjust s by -1 to avoid counting pointers
     to the next object on the heap */
  return hs_refcount(p, s - 1, 0);
#endif
}

#if 0
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
#endif

#ifdef DEFER_GLOBALS
void hs_defer_global(void **g)
{
  *last_deferred_global++ = g;
}
#endif

#if 0
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
#endif

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
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();

#ifndef HS_NORC
  pos = this_chs_thread->freelist_pos;
  start = this_chs_thread->freelist_start;
  for (;;)
    {
      for (end = start + FREELIST_SIZE; pos != end; pos++)
	{
	  adjust_object(pos->p, 0, dlsizeof(pos->p), pos->t, 1);
	  count++;
	}

      if (start == this_chs_thread->freelist_main)
	break;
      start = start->p;
      pos = start + 1;
    }
#endif

#ifdef HS_STATS
  stats_scope(count);
#endif

  //adjust_direct_refs(1);
  pos = this_chs_thread->freelist_pos;
  start = this_chs_thread->freelist_start;
  for (;;)
    {
      for (end = start + FREELIST_SIZE; pos != end; pos++)
	{
#ifdef HS_STATS
	  stats_freeing(chunksize(mem2chunk(pos->p)));
#endif
	  rcfree(pos->p);
	}
      if (start == this_chs_thread->freelist_main)
	break;
      start = start->p;
      dlfree(end - FREELIST_SIZE);
      pos = start + 1;
    }
  //adjust_direct_refs(-1);

  this_chs_thread->freelist_start = this_chs_thread->freelist_main;
  this_chs_thread->freelist_pos = this_chs_thread->freelist_main + FREELIST_SIZE;
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

void heapsafe_thread_init(void)
{
  struct chs_thread *this_chs_thread = dlmalloc(sizeof(struct chs_thread));

  this_chs_thread->freelist_main = dlmalloc(sizeof(struct freed) * FREELIST_SIZE);
  this_chs_thread->freelist_start = this_chs_thread->freelist_main;
  this_chs_thread->freelist_pos = this_chs_thread->freelist_main + FREELIST_SIZE;

  this_chs_thread->indirect_vars = dlmalloc(sizeof(void *) * 300000);
  this_chs_thread->indirect_vars_pos = this_chs_thread->indirect_vars;

  /*
    this_chs_thread->direct_vars = dlmalloc(sizeof(void **) * 300000);
    this_chs_thread->direct_vars_pos = this_chs_thread->direct_vars;
  */
  this_chs_thread->direct_vars = dlmalloc(sizeof(struct dvar_ht_entry) * VSTACKSIZE);
  this_chs_thread->dvar_head = -1;

  this_chs_thread->args = dlmalloc(sizeof(void **) * ARGSSIZE);
  this_chs_thread->args_pos = this_chs_thread->args;

  this_chs_thread->rets = dlmalloc(sizeof(void **) * RETSSIZE);
  this_chs_thread->rets_pos = this_chs_thread->rets;

  this_chs_thread->slots[0] = dlmalloc(sizeof(void *) * SLOTLOGSIZE);
  this_chs_thread->slots_pos[0] = this_chs_thread->slots[0];

  this_chs_thread->olds[0] = dlmalloc(sizeof(void *) * SLOTLOGSIZE);
  this_chs_thread->olds_pos[0] = this_chs_thread->olds[0];

  this_chs_thread->slots[1] = dlmalloc(sizeof(void *) * SLOTLOGSIZE);
  this_chs_thread->slots_pos[1] = this_chs_thread->slots[1];

  this_chs_thread->olds[1] = dlmalloc(sizeof(void *) * SLOTLOGSIZE);
  this_chs_thread->olds_pos[1] = this_chs_thread->olds[1];

  this_chs_thread->rcidx = -1;
  this_chs_thread->choosingidx = 0;
  this_chs_thread->__hs_scount = 0;

  pthread_mutex_lock(&thread_list_mutex);
  this_chs_thread->next = thread_list_head;
  this_chs_thread->prev = NULL;
  thread_list_head = this_chs_thread;
  if (thread_list_head->next)
    thread_list_head->next->prev = thread_list_head;
  __hs_num_threads++;
  SET_CHS_THREAD(this_chs_thread);
  pthread_mutex_unlock(&thread_list_mutex);

}

void heapsafe_thread_destroy(void)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();

  /* make sure the logs for this thread are processed */
  hs_refcount(0,0,0);

  /* remove from thread list */
  pthread_mutex_lock(&thread_list_mutex);
  if (this_chs_thread->prev)
    this_chs_thread->prev->next = this_chs_thread->next;
  if (this_chs_thread->next)
    this_chs_thread->next->prev = this_chs_thread->prev;
  if (this_chs_thread == thread_list_head)
    thread_list_head = this_chs_thread->next;
  __hs_num_threads--;
  pthread_mutex_unlock(&thread_list_mutex);

    /* deallocate logs */
    free_freelist();
    dlfree(this_chs_thread->freelist_main);
    this_chs_thread->freelist_main = NULL;
    dlfree(this_chs_thread->indirect_vars);
    this_chs_thread->indirect_vars = NULL;

    dlfree(this_chs_thread->direct_vars);
    this_chs_thread->direct_vars = NULL;
    this_chs_thread->dvar_head = -1;
    dlfree(this_chs_thread->args);
    this_chs_thread->args = NULL;
    this_chs_thread->args_pos = NULL;
    dlfree(this_chs_thread->rets);
    this_chs_thread->rets = NULL;
    this_chs_thread->rets_pos = NULL;
    dlfree(this_chs_thread->slots[0]);
    this_chs_thread->slots[0] = NULL;
    dlfree(this_chs_thread->slots[1]);
    this_chs_thread->slots[1] = NULL;
    dlfree(this_chs_thread->olds[0]);
    this_chs_thread->olds[0] = NULL;
    dlfree(this_chs_thread->olds[1]);
    this_chs_thread->olds[1] = NULL;

    dlfree(this_chs_thread);
    this_chs_thread = NULL;
    SET_CHS_THREAD(NULL);
}

__attribute__((constructor)) static void heapsafe_init(void)
{
  CHS_THREAD_INIT();
  dlmalloc(1); /* Work around unitialised mstate bug */
  parse_options();
  mprintf_init();

  __hs_rcidx = 0;
  __hs_num_threads = 0;

  heapsafe_thread_init();  
}

/* these are useful for performance debugging */
#if 0
void CRC_ADJUST(void **slot, int by)
{
  if (__hs_num_threads == 1) {
    RC_ADJUST(*(slot), by);
  }
  else if (by == -1) {
    int __hs_redo = 0;
    void *__hs_old = *(slot);
    struct chs_thread *this_chs_thread = GET_CHS_THREAD();
    do {
      __hs_redo = 0;
      this_chs_thread->choosingidx = 1;
      STOREBARRIER;
      this_chs_thread->rcidx = __hs_rcidx;
      this_chs_thread->choosingidx = 0;
      if (this_chs_thread->slots_pos[this_chs_thread->rcidx] -
	  this_chs_thread->slots[this_chs_thread->rcidx] >= SLOTLOGSIZE) {
	this_chs_thread->rcidx = -1;
	hs_refcount(0,0,0);
	__hs_redo = 1;
      }
    } while (__hs_redo);
    if (!CHECK_DIRTY(this_chs_thread->rcidx,(slot))) {
      *this_chs_thread->slots_pos[this_chs_thread->rcidx]++ = (slot);
      *this_chs_thread->olds_pos[this_chs_thread->rcidx]++ = __hs_old;
      SET_DIRTY(this_chs_thread->rcidx,(slot));
    }
    this_chs_thread->rcidx = -1;
  }
}

void CRC_INVALIDATE(void **slot)
{
  if (__hs_num_threads == 1) {
    RC_ADJUST(*(slot),-1);
  }
  else {
    struct chs_thread *this_chs_thread = GET_CHS_THREAD();
    this_chs_thread->choosingidx = 1;
    STOREBARRIER;
    this_chs_thread->rcidx = __hs_rcidx;
    this_chs_thread->choosingidx = 0;
    CLEAR_DIRTY(this_chs_thread->rcidx,(slot));
    this_chs_thread->rcidx = -1;
  }
}
#endif

#include "typed.c"
#include "compat.c"
