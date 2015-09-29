/* oct.h
   Public interface for the library.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#ifndef OCT_H__
#define OCT_H__

#ifdef __cplusplus
#ifndef OCT_HAS_BOOL
#define OCT_HAS_BOOL
#endif
#endif

#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/time.h>
#include <unistd.h>
#include <limits.h>

#include <oct_config_2.h>

#ifdef OCT_HAS_NEW_POLKA
#include <poly.h>
#endif

#ifdef OCT_ENABLE_ASSERT
#include <signal.h>
#include <unistd.h>
#endif

/* zra */
#define OCT_PREFIX CAT(octiag_

#define CAT(a,b) a##b
#define OCT_PROTO(s) OCT_PREFIX,s)


/************/
/* Booleans */
/************/

#ifndef OCT_HAS_NEW_POLKA  /* booleans are already defined in New Polka */

/* true/false */
#ifndef OCT_HAS_BOOL /* bool/true/false are defined in recent C++ compilers */
typedef int bool;
#define true  (int)1
#define false (int)0
#endif

/* complete lattice: bot<true,false<top */
typedef enum { 
  tbool_bottom = 0,
  tbool_true   = 1, 
  tbool_false  = 2,
  tbool_top    = 3 
} tbool;

#endif


/********************/
/* Numerical Domain */
/********************/

#include <oct_num.h>

#ifdef __cplusplus
extern "C" {
#endif


/*************/
/* Shortcuts */
/*************/

#define oct_init                 OCT_PROTO(init)

#define oct_mmalloc_new          OCT_PROTO(mmalloc_new)
#define oct_mmalloc_print        OCT_PROTO(mmalloc_print)
#define oct_mmalloc_use          OCT_PROTO(mmalloc_use)
#define oct_mmalloc_get_current  OCT_PROTO(mmalloc_get_current)
#define oct_mmalloc_reset        OCT_PROTO(mmalloc_reset)
#define oct_mm_malloc            OCT_PROTO(mm_malloc)
#define oct_mm_realloc           OCT_PROTO(mm_realloc)
#define oct_mm_free              OCT_PROTO(mm_free)
#define oct_empty                OCT_PROTO(empty)
#define oct_universe             OCT_PROTO(universe)
#define oct_copy                 OCT_PROTO(copy)
#define oct_free                 OCT_PROTO(free)

#define oct_dimension            OCT_PROTO(dimension)
#define oct_nbconstraints        OCT_PROTO(nbconstraints)
#define oct_get_box              OCT_PROTO(get_box)
#define oct_from_box             OCT_PROTO(from_box)
#define oct_get_bounds           OCT_PROTO(get_bounds)
#define oct_set_bounds           OCT_PROTO(set_bounds)
#define oct_is_empty             OCT_PROTO(is_empty)
#define oct_is_empty_lazy        OCT_PROTO(is_empty_lazy)
#define oct_is_universe          OCT_PROTO(is_universe)
#define oct_is_included_in       OCT_PROTO(is_included_in)
#define oct_is_included_in_lazy  OCT_PROTO(is_included_in_lazy)
#define oct_is_equal             OCT_PROTO(is_equal)
#define oct_is_equal_lazy        OCT_PROTO(is_equal_lazy)
#define oct_is_in                OCT_PROTO(is_in)
#define oct_intersection         OCT_PROTO(intersection)
#define oct_convex_hull          OCT_PROTO(convex_hull)
#define oct_widening             OCT_PROTO(widening)
#define oct_widening_steps       OCT_PROTO(widening_steps)
#define oct_narrowing            OCT_PROTO(narrowing)
#define oct_forget               OCT_PROTO(forget)
#define oct_add_bin_constraints  OCT_PROTO(add_bin_constraints)
#define oct_assign_variable      OCT_PROTO(assign_variable)
#define oct_substitute_variable  OCT_PROTO(substitute_variable)  
#define oct_add_constraint       OCT_PROTO(add_constraint)
#define oct_interv_assign_variable     OCT_PROTO(interv_assign_variable)
#define oct_interv_add_constraint      OCT_PROTO(interv_add_constraint)
#define oct_interv_substitute_variable OCT_PROTO(interv_substitute_variable)
#define oct_time_flow                  OCT_PROTO(time_flow)
#define oct_add_dimensions_and_embed   OCT_PROTO(add_dimensions_and_embed)
#define oct_add_dimensions_and_project OCT_PROTO(add_dimensions_and_project)
#define oct_remove_dimensions    OCT_PROTO(remove_dimensions)
#define oct_add_dimensions_and_embed_multi \
 OCT_PROTO(add_dimensions_and_embed_multi)
#define oct_add_dimensions_and_project_multi \
 OCT_PROTO(add_dimensions_and_project_multi)
#define oct_remove_dimensions_multi \
 OCT_PROTO(remove_dimensions_multi)
#define oct_add_permute_dimensions_and_embed \
 OCT_PROTO(add_permute_dimensions_and_embed)
#define oct_add_permute_dimensions_and_project \
 OCT_PROTO(add_permute_dimensions_and_project)
#define oct_permute_remove_dimensions    \
 OCT_PROTO(permute_remove_dimensions)
#define oct_print                OCT_PROTO(print)
#define oct_add_epsilon          OCT_PROTO(add_epsilon)
#define oct_add_epsilon_max      OCT_PROTO(add_epsilon_max)
#define oct_add_epsilon_bin      OCT_PROTO(add_epsilon_bin)
#define oct_m_empty              OCT_PROTO(m_empty)
#define oct_m_from_oct           OCT_PROTO(m_from_oct)
#define oct_m_to_oct             OCT_PROTO(m_to_oct)
#define oct_m_free               OCT_PROTO(m_free)
#define oct_m_is_equal           OCT_PROTO(m_is_equal)
#define oct_m_print              OCT_PROTO(m_print)
#define oct_m_dimension          OCT_PROTO(m_dimension)
#define oct_m_is_empty           OCT_PROTO(m_is_empty)
#define oct_serialize            OCT_PROTO(serialize)
#define oct_deserialize          OCT_PROTO(deserialize)
#define oct_m_serialize          OCT_PROTO(m_serialize)
#define oct_m_deserialize        OCT_PROTO(m_deserialize)
#define oct_to_poly              OCT_PROTO(to_poly)
#define oct_from_poly            OCT_PROTO(from_poly)
#define oct_random_init          OCT_PROTO(random_init)
#define oct_chrono_reset         OCT_PROTO(chrono_reset)
#define oct_chrono_start         OCT_PROTO(chrono_start)
#define oct_chrono_stop          OCT_PROTO(chrono_stop)
#define oct_chrono_get           OCT_PROTO(chrono_get)
#define oct_chrono_print         OCT_PROTO(chrono_print)
#define oct_timing_enter         OCT_PROTO(timing_enter)
#define oct_timing_exit          OCT_PROTO(timing_exit)
#define oct_timing_print         OCT_PROTO(timing_print)
#define oct_timing_print_all     OCT_PROTO(timing_print_all)
#define oct_timing_reset         OCT_PROTO(timing_reset)
#define oct_timing_reset_all     OCT_PROTO(timing_reset_all)
#define oct_timing_clear         OCT_PROTO(timing_clear)


/**********/
/* Assert */
/**********/

#ifdef OCT_ENABLE_ASSERT

/* it is very convinient when debugging to make the program core dump at the
   very place a check fails, this is why there is a kill(getpid(),SIGABRT)
*/
#define OCT_ASSERT(t,s) if (!(t)) { fprintf(stderr,"Assert failure in file %s at line %i:\n%s (%s)\n",__FILE__,__LINE__,s,#t); fflush(stderr); kill(getpid(),SIGABRT); }

#else

#define OCT_ASSERT(t,s) ;

#endif


/**********/
/* Memory */
/**********/

/* oct_mm_alloc   as malloc
   oct_mm_free    as free
   oct_mm_realloc as realloc
   new_t(t)   returns a pointer t* on a buffer of the size sizeof(t)
   new_n(t,n) returns a pointer t* on a buffer of the size sizeof(t)*n
   renew_n(c,t,n) like new_n, but call mm_realloc

   if ENABLE_MALLOC_MONITORING if defined, allows memory usage monitoring:

   . a monitor is allocated by mm=oct_mmalloc_new()

   . monitors count the number of oct_mm_malloc/oct_mm_realloc/oct_mm_free, 
      memory and max memory consumption
     malloc, realloc and free are unchanged

   . after a oct_mmalloc_use(mm), all blocks mm_malloced belong to monitor mm

   . if you then oct_mm_realloc/oct_mm_free this block, it is monitored by 
     the same monitor used when it was oct_mm_malloced, not the current monitor

   . use oct_mmalloc_print(mm) to print infos

   . oct_mmalloc_reset(mm) resets counters to 0 and forget about all blocks it
     monitored

   . monitors MUST NOT be deallocated (blocks may be still monitored by them !)

   . before any call to oct_mmalloc_use, a default global monitor is used,
     use oct_mmalloc_get_current to get it

   if ENABLE_MALLOC_MONITORING is not defined, oct_mm_alloc, oct_mm_realloc 
   and oct_mm_free are simply malloc, realloc and free

   YOU SHOULD NOT MIX POINTERS USED BY malloc/realloc/free ANS THOSE USED BY
   oct_mm_malloc/oct_mm_realloc/oct_mm_free/new_t/new_n/renew_n

 */

struct mmalloc_tt;
typedef struct mmalloc_tt mmalloc_t;

/* monitor manipulation */
mmalloc_t* OCT_PROTO(mmalloc_new)          (void);
void       OCT_PROTO(mmalloc_print)        (mmalloc_t* mm);
void       OCT_PROTO(mmalloc_use)          (mmalloc_t* mm);
mmalloc_t* OCT_PROTO(mmalloc_get_current)  ();
void       OCT_PROTO(mmalloc_reset)        (mmalloc_t* mm);

#ifdef OCT_ENABLE_MALLOC_MONITORING
/* monitored malloc/realloc/free */
void* OCT_PROTO(mm_malloc)  (size_t t);
void* OCT_PROTO(mm_realloc) (void* p, size_t t);
void  OCT_PROTO(mm_free)    (void* p);
#else

static inline void* OCT_PROTO(mm_malloc)  (size_t t) 
{ void* p = malloc(t);
  OCT_ASSERT(p || !t, "mm_malloc returns NULL pointer");
  return p; }

static inline void* OCT_PROTO(mm_realloc) (void* p, size_t t)
{ p = realloc(p,t);
  OCT_ASSERT(p || !t, "mm_realloc returns NULL pointer");
  return p; }

static inline void  OCT_PROTO(mm_free)    (void* p) { free(p); }

#endif

#define new_t(t)       ((t*) oct_mm_malloc  (sizeof(t)))
#define new_n(t,n)     ((t*) oct_mm_malloc  (sizeof(t)*(n)))
#define renew_n(c,t,n) ((t*) oct_mm_realloc (c,sizeof(t)*(n)))



/************/
/* Octagons */
/************/

/* initialization */
int OCT_PROTO(init) ();


struct oct_tt;
typedef struct oct_tt oct_t;


/* unary/binary constraint type */
typedef enum { 
  px   = 0,  /*    x <= c  (y ignored) */
  mx   = 1,  /*   -x <= c  (y ignored) */
  pxpy = 2,  /*  x+y <= c */
  pxmy = 3,  /*  x-y <= c */
  mxpy = 4,  /* -x+y <= c */
  mxmy = 5   /* -x-y <= c */
} oct_cons_type;

typedef struct {
  var_t         x;
  var_t         y;
  num_t         c;
  oct_cons_type type;
} oct_cons;

/* Bertrand Jeannet's way to specify insertion / deletion of dimensions,
   not necessarily at the end
 */
#ifndef OCT_HAS_NEW_POLKA
typedef struct {
  var_t pos;
  var_t nbdims;
} dimsup_t;
#endif

/* octagon creation/destruction */
oct_t* OCT_PROTO(empty)     (var_t  n);   /* empty domain, c not allocated */
oct_t* OCT_PROTO(universe)  (var_t  n);   /* full domain */
oct_t* OCT_PROTO(copy)      (oct_t* m);   /* increase ref count */
void   OCT_PROTO(free)      (oct_t* m);   /* decrease ref count & free if 0 */

/* query functions */
var_t  OCT_PROTO(dimension)     (oct_t* m);
size_t OCT_PROTO(nbconstraints) (oct_t* m); /* number of non infinitary constraints */

/* interval functions */
num_t* OCT_PROTO(get_box)  (oct_t* m); /* get bounds for all variables */

oct_t* OCT_PROTO(from_box) (var_t  n, 
			    const num_t* b); /* construct an octagon from a box */

void   OCT_PROTO(get_bounds) (oct_t* m,  var_t  k, /* get bounds for one variable */
			      num_t* up, num_t* down);

oct_t* OCT_PROTO(set_bounds) (oct_t* m, var_t  k, /* set bounds for one variable */
			      const num_t* up, const num_t* down,
			      bool  destructive);


/* tests */
bool  OCT_PROTO(is_empty )            (oct_t* m);
tbool OCT_PROTO(is_empty_lazy)        (oct_t* m);
bool  OCT_PROTO(is_universe)          (oct_t* m);
bool  OCT_PROTO(is_included_in)       (oct_t* ma, oct_t* mb);
tbool OCT_PROTO(is_included_in_lazy)  (oct_t* ma, oct_t* mb);
bool  OCT_PROTO(is_equal)             (oct_t* ma, oct_t* mb);
tbool OCT_PROTO(is_equal_lazy)        (oct_t* ma, oct_t* mb);
bool  OCT_PROTO(is_in)                (oct_t* a, const num_t* v);

/* operators */
typedef enum 
{
  OCT_WIDENING_FAST = 0,   /* fast convergence, less precision */
  OCT_WIDENING_ZERO = 1,   /* elements<0 are first set to 0 */
  OCT_WIDENING_UNIT = 2,   /* elemets are set to -1, 0, and 1 before +oo */

  /* Not a widening, but a degenerate hull (precisely, a hull without
     closure of the left argument).
     It is tantalizing to interleave widenings and hulls to improve the
     precision of fix-point computations but, unfortunately, this destroys
     the converge property and makes analyses loop forever.
     The PRE_WIDENING is a middle-ground.
     It does not ensure convergence by itself, but can be safely interleaved 
     with widenings.
     As long as proper widenings occur infinitely often, the interleaved
     sequence will converge. Also, it converges more slowly, and so, gives
     a better precision.
   */
  OCT_PRE_WIDENING = 3
} oct_widening_type;

oct_t* OCT_PROTO(intersection)    (oct_t* ma, oct_t* mb, bool destructive);

oct_t* OCT_PROTO(convex_hull)     (oct_t* ma, oct_t* mb, bool destructive);

oct_t* OCT_PROTO(widening)        (oct_t* ma, oct_t* mb, bool destructive,
				   oct_widening_type type);

oct_t* OCT_PROTO(widening_steps)  (oct_t* ma, oct_t* mb, bool destructive,
				   int nb_steps, num_t* steps);

oct_t* OCT_PROTO(narrowing)       (oct_t* ma, oct_t* mb, bool destructive);

/* transfer functions */
oct_t* OCT_PROTO(forget)              (oct_t* m, var_t  k, bool destructive);

oct_t* OCT_PROTO(add_bin_constraints) (oct_t*           m,
				       unsigned int     nb,
				       const oct_cons*  cons,
				       bool             destructive);

oct_t* OCT_PROTO(assign_variable)     (oct_t*       m,
				       var_t        x,
				       const num_t* tab,
				       bool         destructive);

oct_t* OCT_PROTO(substitute_variable) (oct_t*       m,
				       var_t        x,
				       const num_t* tab,
				       bool         destructive);
  
oct_t* OCT_PROTO(add_constraint)      (oct_t*       m,
				       const num_t* tab,
				       bool         destructive);


oct_t* OCT_PROTO(interv_assign_variable)     (oct_t*       m,
					      var_t        x,
					      const num_t* t,
					      bool         destructive);

oct_t* OCT_PROTO(interv_add_constraint)      (oct_t*       m,
					      const num_t* tab,
					      bool         destructive);


oct_t* OCT_PROTO(interv_substitute_variable)     (oct_t*       m,
						  var_t        x,
						  const num_t* t,
						  bool         destructive);

oct_t* OCT_PROTO(time_flow) (oct_t* m, 
			     const num_t *nmin, 
			     const num_t *nmax, 
			     const num_t *tab,
			     bool destructive);

/* change of dimensions */
oct_t* OCT_PROTO(add_dimensions_and_embed)   (oct_t* m,
					      var_t  dimsup,
					      bool   destructive);

oct_t* OCT_PROTO(add_dimensions_and_project) (oct_t* m, 
					      var_t  dimsup, 
					      bool   destructive);

oct_t* OCT_PROTO(remove_dimensions)          (oct_t* m,
					      var_t  dimsup,
					      bool   destructive);


oct_t* OCT_PROTO(add_dimensions_and_embed_multi)  (oct_t*          m,
						   const dimsup_t* tab,
						   size_t          size_tab,
						   bool            destructive);

oct_t* OCT_PROTO(add_dimensions_and_project_multi)(oct_t*          m,
						   const dimsup_t* tab,
						   size_t          size_tab,
						   bool            destructive);

oct_t* OCT_PROTO(remove_dimensions_multi)         (oct_t*          m,
						   const dimsup_t* tab,
						   size_t          size_tab,
						   bool            destructive);

oct_t* OCT_PROTO(add_permute_dimensions_and_embed)   (oct_t*       m,
						      var_t        dimsup,
						      const var_t* permutation,
						      bool         destructive);

oct_t* OCT_PROTO(add_permute_dimensions_and_project) (oct_t*       m,
						      var_t        dimsup,
						      const var_t* permutation,
						      bool         destructive);

oct_t* OCT_PROTO(permute_remove_dimensions)          (oct_t*       m,
						      var_t        diminf,
						      const var_t* permutation,
						      bool         destructive);


/* perturbation */

oct_t* OCT_PROTO(add_epsilon) (oct_t*        m,
			       const num_t*  epsilon,
			       bool          destructive);

oct_t* OCT_PROTO(add_epsilon_max) (oct_t*        m,
				   const num_t*  epsilon,
				   bool          destructive);

oct_t* OCT_PROTO(add_epsilon_bin) (oct_t*        ma,
				   oct_t*        mb,
				   const num_t*  epsilon,
				   bool          destructive);


/* utilities */
void OCT_PROTO(print) (const oct_t* m); /* print in the form a constrain set */

/* minimal form */

struct moct_tt;
typedef struct moct_tt moct_t;

moct_t* OCT_PROTO(m_empty)        (var_t   n);
moct_t* OCT_PROTO(m_from_oct)     (oct_t*  m);
oct_t*  OCT_PROTO(m_to_oct)       (moct_t* a);
void    OCT_PROTO(m_free)         (moct_t* a);

bool    OCT_PROTO(m_is_equal)     (moct_t* ma, moct_t* mb);
void    OCT_PROTO(m_print)        (moct_t* m);
var_t   OCT_PROTO(m_dimension)    (moct_t* m);
bool    OCT_PROTO(m_is_empty)     (moct_t* m);


/* serialization */
void*    OCT_PROTO(serialize)     (oct_t* m, size_t* size);
oct_t*   OCT_PROTO(deserialize)   (void* d);
void*    OCT_PROTO(m_serialize)   (moct_t* m, size_t* size);
moct_t*  OCT_PROTO(m_deserialize) (void* d);



/****************************/
/* Interface with New Polka */
/****************************/
#ifdef OCT_HAS_NEW_POLKA

poly_t* OCT_PROTO(to_poly)   (oct_t*  m);
oct_t*  OCT_PROTO(from_poly) (poly_t* p);

#endif



/**********/
/* Chrono */
/**********/


typedef struct
{
  struct timeval begin;
  long usec;
  long sec;
  int  start;
} chrono_t;


void OCT_PROTO(chrono_reset) (chrono_t* c);
void OCT_PROTO(chrono_start) (chrono_t* c);
void OCT_PROTO(chrono_stop)  (chrono_t* c);
void OCT_PROTO(chrono_get)   (chrono_t* c, 
			      long* hour, long* min, long* sec, long* usec);
void OCT_PROTO(chrono_print) (chrono_t* c);

/* if ENABLE_TIMING is enabled, each library function use the following macros
   for basic profiling: number of calls and time elapsed in each function

   should not be used to 
 */


#ifdef OCT_ENABLE_TIMING

#define OCT_ENTER(s,k) oct_timing_enter(s,k)
#define OCT_EXIT(s,k)  oct_timing_exit(s,k)

#else

#define OCT_ENTER(s,k) 
#define OCT_EXIT(s,k)  

#endif

void OCT_PROTO(timing_enter)     (const char* name, unsigned key);
void OCT_PROTO(timing_exit)      (const char* name, unsigned key);
void OCT_PROTO(timing_print)     (const char* name);
void OCT_PROTO(timing_print_all) (void);
void OCT_PROTO(timing_reset)     (const char* name);
void OCT_PROTO(timing_reset_all) (void);
void OCT_PROTO(timing_clear)     (void);

#ifdef __cplusplus
}
#endif

#endif
