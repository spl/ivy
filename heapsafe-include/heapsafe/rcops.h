#ifndef __HS_OPS_H
#define __HS_OPS_H

#include <stdint.h>

void abort(void);

#ifdef __HS_DEBUG__

#include "rcops_debug.h"

#else



#ifndef __HS_NOCONCRC__

#define STOREBARRIER asm volatile("sfence" : : : "memory")
#define GCCBARRIER asm volatile("" : : : "memory")

struct __rc_xchg_dummy { unsigned long a[100]; };
#define __rcxg(x) ((struct __rc_xchg_dummy *)(x))


static inline unsigned long
__rc_cmpxchgb(volatile void *ptr, unsigned char old, unsigned char new)
{
  unsigned long prev;
  __asm__ __volatile__("lock; cmpxchgb %b1,%2"
		       : "=a"(prev)
		       : "q"(new), "m"(*__rcxg(ptr)), "0"(old)
		       : "memory");
  return prev;
}

static inline unsigned long
__rc_cmpxchgl(volatile void *ptr, unsigned long old, unsigned long new)
{
  unsigned long prev;
  __asm__ __volatile__("lock; cmpxchgl %1,%2"
		       : "=a"(prev)
		       : "r"(new), "m"(*__rcxg(ptr)), "0"(old)
		       : "memory");
  return prev;
}

static inline void __rc_spinlock_acquire(volatile int *l)
{
  int old = *l;
  while (old == 1 || __rc_cmpxchgl(l,old,1) != (unsigned)old)
    old = *l;
}

static inline void __rc_spinlock_release(volatile int *l)
{
  *l = 0;
}

/*
  extern void __rc_spinlock_acquire(void *l);
  extern void __rc_spinlock_release(void *l);
*/

#define SINLINE inline

#define SLOTLOGSIZE 1000000
#define ARGSSIZE 1000
#define RETSSIZE 1000
#define VSTACKSHIFT 17
#define VSTACKSIZE (1 << VSTACKSHIFT)
#define VSTACKMASK (VSTACKSIZE - 1)

struct dvar_ht_entry;

struct chs_thread 
{
  /** Pointers for thread list */
  struct chs_thread *next, *prev;

  /** Which set of reference count logs are currently in use. -1 if neither */
  int rcidx;

  /** Set when deciding which set of reference count logs to use */
  unsigned int choosingidx;

  /** Nesting depth of delayed free scopes */
  unsigned __hs_scount;

  /** List of things whose deallocation has been delayed */
  struct freed *freelist_start, *freelist_pos, *freelist_main;

  /** Slots to invalidate on a longjump */
  void **indirect_vars, **indirect_vars_pos;

  /** Addresses of local slots to reference count directly for each thread */
  //void ***direct_vars, ***direct_vars_pos;
  struct dvar_ht_entry *direct_vars;
  int dvar_head; /* index of head of dvar list. -1 for empty */

  /** Arguments dying after the next function call. */
  void ***args, ***args_pos;

  /** Var dying after return completed */
  void ***rets, ***rets_pos;

  /** Log of reference slots */
  void **slots[2], **slots_pos[2];

  /** Log of overwritten values */
  void **olds[2], **olds_pos[2];
};

extern unsigned int __hs_num_threads;
extern volatile int __hs_rcidx;

#ifdef __APPLE__
/* This has to match apple's def - hopefully that won't change for a while */
typedef unsigned long __hs_pthread_key_t;
int       pthread_setspecific(__hs_pthread_key_t key,
			      const void *value);
void     *pthread_getspecific(__hs_pthread_key_t key);

/* No __thread */
extern __hs_pthread_key_t __this_chs_thread_key;
#define SET_CHS_THREAD(t) (pthread_setspecific(__this_chs_thread_key, (t)))
#define GET_CHS_THREAD() ((struct chs_thread *)pthread_getspecific(__this_chs_thread_key))

#else

extern __thread struct chs_thread *__this_chs_thread;

#define SET_CHS_THREAD(t) (__this_chs_thread = (t))
#define GET_CHS_THREAD(t) __this_chs_thread
#endif

void *tombstone;

struct dvar_ht_entry {
  void **addr; /* -1 for tombstone, 0 for empty */
  int next; /* -1 for NULL */
  int prev;
};

#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))
#define mix(a,b,c)				\
  {						\
    a -= c;  a ^= rot(c, 4);  c += b;		\
    b -= a;  b ^= rot(a, 6);  a += c;		\
    c -= b;  c ^= rot(b, 8);  b += a;		\
    a -= c;  a ^= rot(c,16);  c += b;		\
    b -= a;  b ^= rot(a,19);  a += c;		\
    c -= b;  c ^= rot(b, 4);  b += a;		\
  }
#define final(a,b,c)				\
  {						\
    c ^= b; c -= rot(b,14);			\
    a ^= c; a -= rot(c,11);			\
    b ^= a; b -= rot(a,25);			\
    c ^= b; c -= rot(b,16);			\
    a ^= c; a -= rot(c,4);			\
    b ^= a; b -= rot(a,14);			\
    c ^= b; c -= rot(b,24);			\
  }
static SINLINE unsigned int hashword(unsigned int k, unsigned int init)
{
  uint32_t a,b,c;

  /* Set up the internal state */
  a = b = c = 0xdeadbeef + init;

  a += k;
  final(a,b,c);

  return c;
}

/* Assumes HT has VSTACKSIZE elements */
/* XXX: Resize the HT if it's full? */
static SINLINE void dvar_ht_insert(struct dvar_ht_entry *HT,
                                   int *head, void **var)
{
  unsigned int idx;
  unsigned int init = 0;

#ifdef CRC_DEBUG
  printf("dvar_ht_insert(%p,%p,%p)\n",GET_CHS_THREAD(),var,*var);
  fflush(0);
#endif

  do {
    idx = hashword((unsigned int)var,init) & VSTACKMASK;
    init++;
  } while (HT[idx].addr != 0 &&
           HT[idx].addr != &tombstone &&
           HT[idx].addr != var);

  //__asm__ __volatile__ ("");

  if (HT[idx].addr == var) return;

  HT[idx].addr = var;
  HT[idx].next = *head;
  HT[idx].prev = -1;
  if (*head != -1)
    HT[*head].prev = idx;
  *head = idx;

  return;
}

static SINLINE void dvar_ht_remove(struct dvar_ht_entry *HT,
                                  int *head, void **var)
{
  unsigned int idx;
  unsigned int init = 0;

    if (*head == -1) return; /* empty */

#ifdef CRC_DEBUG
  printf("dvar_ht_remove(%p,%p,%p)\n",GET_CHS_THREAD(),var,*var);
  fflush(0);
#endif

    do {
        idx = hashword((unsigned int)var, init) & VSTACKMASK;
        init++;
    } while(HT[idx].addr != 0 && 
            HT[idx].addr != var);

  //__asm__ __volatile__ ("");

  if (HT[idx].addr == 0) return;

  if (HT[idx].next != -1)
    HT[HT[idx].next].prev = HT[idx].prev;
  if (HT[idx].prev != -1)
    HT[HT[idx].prev].next = HT[idx].next;
  if ((int)idx == *head)
    *head = HT[idx].next;
  HT[idx].addr = &tombstone;

  return;
}

static SINLINE void __builtin_hs_cpush(void *x)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  //*this_chs_thread->direct_vars_pos++ = (void *)x;
  dvar_ht_insert(this_chs_thread->direct_vars,
		 &this_chs_thread->dvar_head,
		 x);
}

static SINLINE void __builtin_hs_cpop(void *x)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();

  //*this_chs_thread->direct_vars_pos -= num;
  *(void **)x = (void *)0;
  dvar_ht_remove(this_chs_thread->direct_vars,
		 &this_chs_thread->dvar_head,
		 x);
}

static SINLINE void __builtin_hs_argpush(void *arg)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  if (this_chs_thread->args_pos - this_chs_thread->args > ARGSSIZE)
      abort(); /* XXX: generate a real error here */
  *this_chs_thread->args_pos++ = (void **)arg;
}

static SINLINE void __builtin_hs_argnull(void)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  void ***arg_pos = this_chs_thread->args_pos;
  if (!this_chs_thread->args) return;
  while (--arg_pos >= this_chs_thread->args)
    __builtin_hs_cpop(*arg_pos);
  this_chs_thread->args_pos = this_chs_thread->args;
}

static SINLINE void __builtin_hs_retpush(void *ret)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  if (this_chs_thread->rets_pos - this_chs_thread->rets > RETSSIZE)
      abort(); /* XXX: generate a real error here */
  *this_chs_thread->rets_pos++ = (void **)ret;
}

static SINLINE void __builtin_hs_retnull(void)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  void ***ret_pos = this_chs_thread->rets_pos;
  if(!this_chs_thread->rets) return;
  /* call dvar_ht_remove directly because otherwise cpop would try to null out
     things in a stack frame that we just returned from */
  while (--ret_pos >= this_chs_thread->rets)
      dvar_ht_remove(this_chs_thread->direct_vars,
		     &this_chs_thread->dvar_head,
		     *ret_pos);
  this_chs_thread->rets_pos = this_chs_thread->rets;
}

#define __HS_DIRTY 5
#define CHECK_DIRTY(idx,p) (__hs_dirty[(idx)][(uintptr_t)(p)>>__HS_DIRTY]&(1UL<<(((uintptr_t)(p)>>2)&0x7)))
#define SET_DIRTY(idx,p) __hs_dirty[(idx)][(uintptr_t)(p)>>__HS_DIRTY]|=(1UL<<(((uintptr_t)(p)>>2)&0x7))
#define CLEAR_DIRTY(idx,p) __hs_dirty[(idx)][(uintptr_t)(p)>>__HS_DIRTY]&=~(1UL<<(((uintptr_t)(p)>>2)&0x7))
#endif

#define __HS_RCLOG 3
#ifdef __HS_NOCONCRC__
extern int8_t __hs_rcs[];
#else
extern volatile int8_t __hs_rcs[];
#endif

#define min(a,b) ((a) < (b) ? (a) : (b))

#define RC_ADJUST(p, by)					\
    ((p) ? __hs_rcs[(uintptr_t)(p) >> __HS_RCLOG] += (by) : 0)

/* define CRC_DEBUG when building an app to get lots of reference counting
   debug message dumped to stdout */
#ifdef CRC_DEBUG

#define CRC_ADJUST(slot, by)\
do {\
    if (__hs_num_threads == 1) {\
        RC_ADJUST(*(slot), (by));\
        printf("RC_ADJUST(%p,%p,%d)\n",(slot),*(slot),(by));\
        fflush(0);\
    }\
    else if (by == -1) {\
        struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
        int __hs_redo = 0;\
        void *__hs_old = *(slot);\
        do {\
            __hs_redo = 0;\
            this_chs_thread->choosingidx = 1;\
            STOREBARRIER;\
            this_chs_thread->rcidx = __hs_rcidx;\
            this_chs_thread->choosingidx = 0;\
            if (this_chs_thread->slots_pos[this_chs_thread->rcidx] -\
                this_chs_thread->slots[this_chs_thread->rcidx] >= SLOTLOGSIZE) {\
                this_chs_thread->rcidx = -1;\
                hs_refcount(0,0,0);\
                __hs_redo = 1;\
            }\
        } while (__hs_redo);\
        if (!CHECK_DIRTY(this_chs_thread->rcidx,(slot))) {\
            *this_chs_thread->slots_pos[this_chs_thread->rcidx]++ = (slot);\
            *this_chs_thread->olds_pos[this_chs_thread->rcidx]++ = __hs_old;\
            SET_DIRTY(this_chs_thread->rcidx,(slot));\
	    GCCBARRIER;\
            printf("ADJUST(%p,%p,%p,%d,log=%d)\n",this_chs_thread,(slot),*(slot),(by),this_chs_thread->rcidx);\
            fflush(0);\
        }\
        else {\
            printf("ANOMRK(%p,%p,%p,%d,log=%d)\n",this_chs_thread,(slot),*(slot),(by),this_chs_thread->rcidx);\
            fflush(0);\
        }\
    }\
    else {\
        struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
        this_chs_thread->rcidx = -1;\
        printf("ADJUST(%p,%p,%p,%d)\n",GET_CHS_THREAD(),(slot),*(slot),(by));\
        fflush(0);\
    }\
} while(0)

#define CRC_INVALIDATE(slot)\
  do {\
    if (__hs_num_threads == 1) {\
      RC_ADJUST(*(slot),-1);\
      printf("RC_ADJUST(%p,%p,-1)\n",(slot),*(slot));\
      fflush(0);\
    }\
    else {\
        struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
        int __hs_redo = 0;\
        void *__hs_old = *(slot);\
        do {\
            __hs_redo = 0;\
            this_chs_thread->choosingidx = 1;\
            STOREBARRIER;\
            this_chs_thread->rcidx = __hs_rcidx;\
            this_chs_thread->choosingidx = 0;\
            if (this_chs_thread->slots_pos[this_chs_thread->rcidx] -\
                this_chs_thread->slots[this_chs_thread->rcidx] >= SLOTLOGSIZE) {\
                this_chs_thread->rcidx = -1;\
                hs_refcount(0,0,0);\
                __hs_redo = 1;\
            }\
        } while (__hs_redo);\
        if (!CHECK_DIRTY(this_chs_thread->rcidx,(slot))) {\
            *this_chs_thread->slots_pos[this_chs_thread->rcidx]++ = (void *)((unsigned int)slot|0x1); \
            *this_chs_thread->olds_pos[this_chs_thread->rcidx]++ = __hs_old;\
            printf("INV_LOG(%p,%p,%p,%d,log=%d)\n",this_chs_thread,(slot),*(slot),(by),this_chs_thread->rcidx);\
            fflush(0);\
        }\
        else {\
            printf("INV_CLEAR(%p,%p,%p,%d,log=%d)\n",this_chs_thread,(slot),*(slot),(by),this_chs_thread->rcidx);\
            fflush(0);\
            CLEAR_DIRTY(this_chs_thread->rcidx,(slot));\
	    GCCBARRIER;\
        }\
        this_chs_thread->rcidx = -1;\
    }\
  } while(0)



/*
      this_chs_thread->choosingidx = 1;\
      STOREBARRIER;\
      this_chs_thread->rcidx = __hs_rcidx;\
      this_chs_thread->choosingidx = 0;\
      CLEAR_DIRTY(this_chs_thread->rcidx,(slot));\
      this_chs_thread->rcidx = -1;\
      printf("INVALIDATE(%p,%p)\n",(slot),*(slot));\
    }\
  } while(0)
*/
#else /* CRC_DEBUG*/

#define CRC_ADJUST(slot, by)\
do {\
    if (__hs_num_threads <= 1) {\
        RC_ADJUST(*(slot), (by));\
    }\
    else if ((by) == -1) {\
        struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
        int __hs_redo = 0;\
        void *__hs_old = *(slot);\
        do {\
            __hs_redo = 0;\
            this_chs_thread->choosingidx = 1;\
            STOREBARRIER;\
            this_chs_thread->rcidx = __hs_rcidx;\
            this_chs_thread->choosingidx = 0;\
            if (this_chs_thread->slots_pos[this_chs_thread->rcidx] -\
                this_chs_thread->slots[this_chs_thread->rcidx] >= SLOTLOGSIZE) {\
                this_chs_thread->rcidx = -1;\
                hs_refcount(0,0,0);\
                __hs_redo = 1;\
            }\
        } while (__hs_redo);\
        if (!CHECK_DIRTY(this_chs_thread->rcidx,(slot))) {\
            *this_chs_thread->slots_pos[this_chs_thread->rcidx]++ = (slot);\
            *this_chs_thread->olds_pos[this_chs_thread->rcidx]++ = __hs_old;\
            SET_DIRTY(this_chs_thread->rcidx,(slot));\
	    GCCBARRIER;\
        }\
    }\
    else {\
        struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
        this_chs_thread->rcidx = -1;\
    }\
} while(0)


#define CRC_INVALIDATE(slot)\
  do {\
    if (__hs_num_threads <= 1) {\
      RC_ADJUST(*(slot),-1);\
    }\
    else if (__hs_num_threads > 1) {\
        struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
        int __hs_redo = 0;\
        void *__hs_old = *(slot);\
        do {\
            __hs_redo = 0;\
            this_chs_thread->choosingidx = 1;\
            STOREBARRIER;\
            this_chs_thread->rcidx = __hs_rcidx;\
            this_chs_thread->choosingidx = 0;\
            if (this_chs_thread->slots_pos[this_chs_thread->rcidx] -\
                this_chs_thread->slots[this_chs_thread->rcidx] >= SLOTLOGSIZE) {\
                this_chs_thread->rcidx = -1;\
                hs_refcount(0,0,0);\
                __hs_redo = 1;\
            }\
        } while (__hs_redo);\
        if (!CHECK_DIRTY(this_chs_thread->rcidx,(slot))) {\
            *this_chs_thread->slots_pos[this_chs_thread->rcidx]++ = (void *)((unsigned int)(slot)|0x1); \
            *this_chs_thread->olds_pos[this_chs_thread->rcidx]++ = __hs_old;\
        }\
        else {\
            CLEAR_DIRTY(this_chs_thread->rcidx,(slot));\
        }\
        this_chs_thread->rcidx = -1;\
    }\
  } while(0)

#if 0
#define CRC_INVALIDATE(slot)\
  do {\
    if (__hs_num_threads == 1) {\
      RC_ADJUST(*(slot),-1);\
    }\
    else {\
      struct chs_thread *this_chs_thread = GET_CHS_THREAD();\
      this_chs_thread->choosingidx = 1;\
      STOREBARRIER;\
      this_chs_thread->rcidx = __hs_rcidx;\
      this_chs_thread->choosingidx = 0;\
      CLEAR_DIRTY(this_chs_thread->rcidx,(slot));\
      this_chs_thread->rcidx = -1;\
    }\
  } while(0)
#endif

#endif /* CRC_DEBUG */

#define __builtin_hs_trace()
#define __builtin_hs_adjust(adj, x, by, s)	\
  ((adj)((x), (by), (s)))

#define __builtin_hs_cadjust(adj,x,by,s,inv) \
  ((adj)((x),(by),(s),(inv)))

#endif /* __HS_DEBUG__ */

#define RC_ADJUST_START(x, s)			\
  typeof(s) __rcs = (s);			\
	    char *__rcend = (char *)(x) + (s);	\
__rcnext:

#define RC_ADJUST_END(x, s)			\
  if (__rcs && (s))				\
    {						\
      (x) = (void *)((char *)(x) + (s));	\
      if ((char *)(x) + (s) <= __rcend)		\
	goto __rcnext;				\
    }

#ifdef __HS_NOCONCRC__
extern void **__hs_indirect_vars, **__hs_direct_vars;
#endif

#ifndef __HEAPSAFE__
/* Strangely enough, this means the time we're included after the cil pass */

#ifdef __HS_NOCONCRC__
static inline void __builtin_hs_push(const void *x)
{
  *__hs_direct_vars++ = (void *)x;
}

static inline void __builtin_hs_pop(const void *x)
{
  --__hs_direct_vars;
}

static inline void __builtin_hs_ipush(const void *x,
				      void (*t)(void *x, int by, __SIZE_TYPE__ s),
				      __SIZE_TYPE__ s)
{
  *__hs_indirect_vars++ = (void *)x;
  *__hs_indirect_vars++ = (void *)s;
  *__hs_indirect_vars++ = (void *)t;
}

static inline void __builtin_hs_ipop(const void *x,
				     void (*t)(void *x, int by, __SIZE_TYPE__ s),
				     __SIZE_TYPE__ s)
{
  __hs_indirect_vars -= 3;
}
#else

extern volatile unsigned char __hs_dirty[2][1UL << (32 - __HS_DIRTY)];

static inline void __builtin_hs_cipush(const void *x,
				       void (*t)(void *x, int by, __SIZE_TYPE__ s, int inv),
				       __SIZE_TYPE__ s)
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  *this_chs_thread->indirect_vars_pos++ = (void *)x;
  *this_chs_thread->indirect_vars_pos++ = (void *)s;
  *this_chs_thread->indirect_vars_pos++ = (void *)t;
}

static inline void __builtin_hs_cipop(const void *x __attribute__((unused)),
				      void (*t)(void *, int, __SIZE_TYPE__, int) __attribute__((unused)),
				      __SIZE_TYPE__ s __attribute__((unused)))
{
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  this_chs_thread->indirect_vars_pos -= 3;
}


#endif

#endif /* !__HEAPSAFE__ */

#endif /* __HS_OPS_H */
