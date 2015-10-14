#ifndef __HS_H
#define __HS_H

/* =========================================================================
 * User-visible API for working with HeapSafe
 * Included manually by a programmer if they want to use the HeapSafe API.
 * When HeapSafe is not in use, the HeapSafe API is defined to give erasure semantics.
 * ========================================================================= */

#include <stdint.h>
#include <stddef.h>

#ifdef __HS_LIB__
#define SAFE
#define TRUSTED
#define DMEMCPY(a,b,c)
#define DMEMSET(a,b,c)
#define DALLOC(p)
#define DREALLOC(p, n)
#define DFREE(p)
#define TC(x) (x)
#define COUNT(x)
#endif

#if defined(__HEAPSAFE__) && !defined(__HS_LIB__)

/* Type attribute to disable reference counting */
#define hs_norc __attribute__((hs_norc))

/* Function attribute declaring that calls to this function do not
   call free directly or indirectly */
#define hs_nofree __attribute__((hs_nofree))

/* Function attribute requesting tracing of calls to this function */
#define hs_trace __attribute__((hs_trace))

/* Function attribute requesting warnings when calling this function
   with arguments containing pointers */
#define hs_untyped __attribute__((hs_untyped))

#else

#define hs_norc
#define hs_nofree
#define hs_trace
#define hs_untyped

#endif

#ifdef __HS_NOCONCRC__
typedef void (*hs_type_t SAFE)(void *x, int by, size_t s) hs_nofree;
#else
typedef void (*hs_type_t SAFE)(void *x, int by, size_t s, int inv) hs_nofree;
#endif


#ifndef __HS_DEBUG__
struct freed {
  void *p;
#ifndef HS_NORC
  hs_type_t t;
#endif
};
#endif

#ifdef __HEAPSAFE__
#include <heapsafe/rcops.h>
#endif

/* -------------------------------------------------------------------------
 * Runtime type information
 * -------------------------------------------------------------------------*/

#if defined(__HEAPSAFE__) && !defined(HS_NORC) && !defined(__HS_LIB__)
extern size_t __hs_magic_typeof;
#define hs_typeof(t_or_e) ((hs_type_t TRUSTED)(sizeof(t_or_e) + __hs_magic_typeof))
#else
#define hs_typeof(t_or_e) ((hs_type_t)0)
#endif

/* -------------------------------------------------------------------------
 * Type-preserving versions of common operations, and union type changes
 * -------------------------------------------------------------------------*/

#ifdef __HEAPSAFE__

void *(DMEMCPY(1, 2, 3) hs_typed_memcpy)(void *to, void *from, size_t s, hs_type_t t) hs_trace;
void *(DMEMCPY(1, 2, 3) hs_typed_memmove)(void *to, void *from, size_t s, hs_type_t t) hs_trace;
void *(DMEMSET(1, 2, 3) hs_typed_memset)(void *to, int c, size_t s, hs_type_t t) hs_trace;
void hs_typed_mutate(void *obj, void *union_part, hs_type_t obj_t, size_t union_s) hs_trace;

#else

#define hs_typed_memcpy(to, from, size, t) \
  memcpy((to), (from), (size))
#define hs_typed_memmove(to, from, size, t) \
  memmove((to), (from), (size))
#define hs_typed_memset(to, c, size, t)		\
  memset((to), (c), (size))
#define hs_typed_mutate(obj, union_part, obj_t, union_s)	\
  memset((union_part), 0, (union_s))

#endif

/* -------------------------------------------------------------------------
 * Allocation, deallocation and scopes
 * -------------------------------------------------------------------------*/

#ifdef __HEAPSAFE__

#ifdef __HS_NOCONCRC__
extern unsigned __hs_scount;
#endif

void *(DALLOC(n) hs_malloc)(size_t n) hs_trace;
void *(DALLOC(n) __hs_malloc_noclear)(size_t n) hs_trace;
void *(DALLOC(n * s) hs_calloc)(size_t n, size_t s) hs_trace;
void *(DREALLOC(p, n) hs_typed_realloc)(void *p, hs_type_t t, size_t n) hs_trace;
void (DFREE(p) hs_typed_free)(const void *p, hs_type_t t) hs_trace;
#ifdef __HS_NOCONCRC__
static inline void hs_delayed_free_start(void) {
#ifndef HS_NOSCOPES
  __hs_scount++;
#endif
}
#else
void hs_delayed_free_start(void);
#endif
void hs_delayed_free_end(void);

#else

#define hs_safe_mode()

#define hs_malloc(n) calloc((n), 1)
#define __hs_malloc_noclear malloc
#define hs_calloc calloc
#define hs_typed_realloc(p, t, n) realloc((p), (n))
#define hs_typed_free(p, t) free((p))
#define hs_delayed_free_start()
#define hs_delayed_free_end()

#endif

/* -------------------------------------------------------------------------
 * Type-sensitive malloc. Only clears pointer fields.
 * -------------------------------------------------------------------------*/

#define HS_ALLOC(type) ({				     \
      type *TRUSTED __hs1 = __hs_malloc_noclear(sizeof(type));	     \
      __builtin_hs_clear(__hs1);			     \
      (type *SAFE)__hs1; })

#define HS_ARRAYALLOC(type, n) ({					\
      size_t __hsn = (n);						\
      type *__hs1 = __hs_malloc_noclear(__hsn * sizeof(type)), *TRUSTED __hs2;	\
      if (hs_typeof(type) != 0)						\
	for (__hs2 = __hs1; __hs2 < __hs1 + __hsn; __hs2++)		\
	  __builtin_hs_clear(__hs2);					\
      __hs1; })


/* -------------------------------------------------------------------------
 * Efficiently clear all pointers in a given type
 * (useful for efficient implementation of deallocation functions in 
 * type-specific custom allocators)
 * -------------------------------------------------------------------------*/

#if defined(__HEAPSAFE__) && !defined(HS_NOCLEAR)
void __builtin_hs_clear(void *p);
#define HS_DESTROY(p) ({				\
      typeof(p) __hsl = (p);				\
      if (hs_typeof(*(__hsl)) != 0)	{	\
	__builtin_hs_trace();				\
	((hs_type_t)hs_typeof(*(p)))(__hsl, -1, 0);	\
      }							\
      __builtin_hs_clear(__hsl); })
#else
#define __builtin_hs_clear(p)
#define HS_DESTROY(p)
#endif

/* -------------------------------------------------------------------------
 * Macros automating use of hs_typeof
 * -------------------------------------------------------------------------*/

#define HS_REALLOC(p, n) hs_typed_realloc((p), hs_typeof(*(p)), (n))
#define HS_FREE(p) hs_typed_free((p), hs_typeof(*(p)))

#define HS_MEMCPY(to, from, size)					\
  hs_typed_memcpy((to), (from), (size), hs_typeof(*(to)))
#define HS_MEMMOVE(to, from, size)				\
  hs_typed_memmove((to), (from), (size), hs_typeof(*(to)))
#define HS_MEMSET(to, c, size)				\
  hs_typed_memset((to), (c), (size), hs_typeof(*(to)))
#define HS_MUTATE(obj, union_path)					\
  hs_typed_mutate(&(obj), &(obj).union_path, hs_typeof((obj)), sizeof((obj).union_path))

/* -------------------------------------------------------------------------
 * Simple zeroing macros
 * -------------------------------------------------------------------------*/

#define HS_ZFREE(x)				\
  ({ typeof((x)) __hs_z2 = (x);			\
    (x) = NULL;					\
    HS_FREE(__hs_z2); })

#define HS_ZREALLOC(x, size)			\
  ({ typeof((x)) __hs_z2 = (x);			\
    (x) = NULL;					\
    HS_REALLOC(__hs_z2, (size)); })


/* -------------------------------------------------------------------------
 * Warnings for memcpy and friends
 * -------------------------------------------------------------------------*/

#ifdef HAVE_STRING_H
void *memcpy(void *to, const void *from, size_t s) hs_untyped;
void *memmove(void *to, const void *from, size_t s) hs_untyped;
void *memset(void *to, int c, size_t s) hs_untyped;
#endif

void bcopy(const void *from, void *to, size_t s) hs_untyped;
void bzero(void *to, size_t s) hs_untyped;

/* -------------------------------------------------------------------------
 * Debug interface - use within GDB to find out how things are referenced
 * -------------------------------------------------------------------------*/

void hsinfo(void *x);

#endif /* __HS_ H */
