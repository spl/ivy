/* oct_num.h
   Defines all underlying numerical domains as macros / inline functions.
   This is automatically included by oct.h.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#ifndef OCT_NUM_H__
#define OCT_NUM_H__

#include <stdio.h>
#include <string.h>
#include <math.h>
#include <oct_config_2.h>

#ifdef OCT_HAS_GMP
#include <gmp.h>
#endif

#ifdef OCT_HAS_MPFR
#include <mpfr.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* zra */
#define OCT_NUM_INT 1

/* here, exactely one of the following must be defined */
/*  OCT_NUM_INT         un-saturated integers (int) */
/*  OCT_NUM_FLOAT       floats (double) */
/*  OCT_NUM_LONGDOUBLE  floats (long double) */
/*  OCT_NUM_FRAC        rationals */
/*  OCT_NUM_GMP_INT     GMP integers */
/*  OCT_NUM_GMP_FRAC    GMP fractions */
/*  OCT_NUM_MPFR_FLOAT  MPFR floats */


/* All numerical types suppose perfect numbers: no treatement of modulo
   arithmetic or overflow-as-error is done.

   Numerical types are *sound approximations* of perfect numbers:
   a number that cannont be exactely represented is approximated by a
   number this is greater, a number that cannot be overapproximated by
   a finite number is approximated by +oo.
   
   Tests are either correct (integer, fractionnals) or semi-correct (floats).
   In the later case, true means "really true" and "false" means "maybee
   not true". If this is the case, operators on octagons are also
   semi-correct.
*/


/* WARNING

   the GMP / MPFR types has not been tested much
   especially, conversion functions may not be correct!

*/

typedef enum {
  OCT_DOMAIN_INT   = 0,   /* numbers represent integers */
  OCT_DOMAIN_FRAC  = 1,   /* numbers represent rationals */
  OCT_DOMAIN_REAL  = 2    /* numbers rerpesent reals */
} num_domain_t;

static const char* oct_domain_string[] = {"integers","rationals","reals"};


/* generic functions */

#ifdef WORDS_BIGENDIAN

static inline void swap_word(void* dst, const void* src, size_t t)
{ 
  unsigned char *s = (unsigned char*)src+t-1, *d = (unsigned char*) dst;
  size_t i;
  for (i=0;i<t;i++,s--,d++) *d = *s;
}

#else

static inline void swap_word(void* dst, const void* src, size_t t)
{ 
  memcpy(dst,src,t);
}

#endif

static inline void dump16(unsigned char * c, unsigned i)
{
  c[0] = (i>>8)&0xff;
  c[1] = i&0xff;
}

static inline unsigned undump16(const unsigned char * c)
{
  return (unsigned)c[1]+(((unsigned)c[0])<<8);
}

static inline void dump32(unsigned char * c, unsigned long i)
{
  c[0] = (i>>24)&0xff;
  c[1] = (i>>16)&0xff;
  c[2] = (i>>8)&0xff;
  c[3] = i&0xff;
}

static inline unsigned long undump32(const unsigned char * c)
{
  return (unsigned long)c[3]+(((unsigned long)c[2])<<8)+
         (((unsigned long)c[1])<<16)+(((unsigned long)c[0])<<24);
}



/********************/
/* Machine-integers */
/********************/
  
/* unsafe in case of an overflow */
  
#ifdef OCT_NUM_INT

#ifdef OCT_NUM
#error "only one OCT_NUM_ must be defined in oct_num.h"
#endif
#define OCT_NUM

#define OCT_DOMAIN OCT_DOMAIN_INT
#define OCT_IMPLEMENTATION_STRING "long"

typedef long num_t;

static const num_t num__infty = (unsigned)(1<<(sizeof(num_t)*8-1))-1;

/* constructors */

#define num_init(a)
#define num_init_n(a,n)
#define num_init_set(a,b)        num_set((a),(b))
#define num_init_set_n(a,b,n)    num_set_n((a),(b),(n))
#define num_init_set_int(a,b)    num_set_int((a),(b))
#define num_init_set_float(a,b)  num_set_float((a),(b))
#define num_init_set_frac(a,b,c) num_set_frac((a),(b),(c))
#define num_init_set_infty(a)    num_set_infty((a))

/* copy / update */

#define num_set(a,b)     *(a) = *(b)
#define num_set_n(a,b,n) memcpy((a),(b),sizeof(num_t)*(n));

static inline void num_set_int(num_t* a, long i)
{ *a = (i<-num__infty || i>num__infty) ? num__infty : i; }

static inline void num_set_float(num_t* a, double k)
{ k = ceil(k); *a = (k<-num__infty || k>num__infty) ? num__infty : (num_t)k; }

#define num_set_frac(a,i,j) num_set_float((a),((double)(i))/((double)(j)))
#define num_set_infty(a)    *(a) = num__infty

/* destructors */

#define num_clear(a)
#define num_clear_n(a,n)

/* conversions */

#define num_fits_int(a)   (*(a) != num__infty)
#define num_fits_float(a) (*(a) != num__infty)
#define num_fits_frac(a)  (*(a) != num__infty)

#define num_get_int(a)   ((long)*(a))
#define num_get_float(a) ((double)*(a))
#define num_get_num(a)   ((long)*(a))
#define num_get_den(a)   (1L)

/* tests */

#define num_infty(a)     (*(a)==num__infty)

static inline int num_cmp(const num_t* a, const num_t *b)
{ return (*a==*b)?0:(*a>*b)?1:-1; }

static inline int num_cmp_int(const num_t* a, long b)
{ return (*a==b)?0:((*a>b)?1:-1); }

static inline int num_cmp_zero(const num_t* a)
{ return (*a==0)?0:((*a>0)?1:-1); }

static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a>=*b) ? *a : *b; }

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a<=*b) ? *a : *b; }

static inline void num_add(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a==num__infty || *b==num__infty) ? num__infty : *a + *b; }

static inline void num_sub(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a==num__infty || *b==num__infty) ? num__infty : *a - *b; }

static inline void num_mul(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a==num__infty || *b==num__infty) ? num__infty : *a * *b; }

static inline void num_mul_by_2(num_t* r, const num_t* a)
{ *r = (*a==num__infty) ? num__infty : *a * 2; }

static inline void num_div_by_2(num_t* r, const num_t* a)
{ *r = (*a==num__infty) ? num__infty : (*a>=0) ? (*a+1)/2 : *a/2; }

static inline void num_neg(num_t* r, const num_t* a)
{ *r = (*a==num__infty) ? num__infty : -(*a); }

/* printing */

static inline void num_print(const num_t* a)
{ if (*a!=num__infty) printf("%li",(long)*a); else printf("+oo"); }

static inline void num_snprint(char* s, size_t n, const num_t* a)
{ if (*a!=num__infty) snprintf(s,n,"%li",(long)*a); else snprintf(s,n,"+oo"); }

/* GMP conversion */

#ifdef OCT_HAS_GMP

static inline void num_set_mpz(num_t* a, const mpz_t b)
{ 
  if (mpz_fits_slong_p(b)) num_set_int(a,mpz_get_si(b)); 
  else num_set_infty(a);
}

#define num_get_mpz(a,b) mpz_set_si((a),*(b))

#define num_set_mpq(a,b) num_set_float((a),ceil(mpq_get_d((b)))) /* is it sound ? */

#define num_get_mpq(a,b) mpq_set_si((a),*(b),1)

#endif

#ifdef OCT_HAS_MPFR

static inline void num_set_mpfr(num_t* a, const mpfr_t b)
{ 
  mpfr_t m;
  mpfr_init(m);
  mpfr_ceil(m,b);
  num_set_float(a,mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
			     , GMP_RNDU
#endif
    ));
  mpfr_clear(m);
}

#define num_get_mpfr(a,b) mpfr_set_si((a),*(b),GMP_RNDU)

#endif


#undef  OCT_NUM_CLOSED
#undef  OCT_NUM_EXACT

/* serialization */

#define OCT_NUM_SERIALIZE

static const int num_serialize_id = 0x1000+sizeof(num_t);

static inline size_t num_serialize(const num_t* a, void* c) 
{ swap_word(c,a,sizeof(num_t)); return sizeof(num_t); }

static inline size_t num_deserialize(num_t* a, const void* c) 
{ swap_word(a,c,sizeof(num_t)); return sizeof(num_t); }

static inline size_t num_serialize_size(num_t* a) 
{ return sizeof(num_t); }


#endif



/******************/
/* Machine-floats */
/******************/


/* define OCT_DEBUG_NAN if you want to check that there is no NaN in the
   library
*/

#if defined(OCT_NUM_FLOAT) || defined(OCT_NUM_LONGDOUBLE)

#ifdef OCT_NUM
#error "only one OCT_NUM_ must be defined in oct_num.h"
#endif
#define OCT_NUM

#define OCT_DOMAIN OCT_DOMAIN_REAL

#ifdef OCT_NUM_LONGDOUBLE
#define OCT_IMPLEMENTATION_STRING "long double"
typedef long double num_t;
#else
#define OCT_IMPLEMENTATION_STRING "double"
typedef double num_t;
#endif

#ifdef __INTEL_COMPILER
#define num__infty (1.0/0.0)
#else
static const num_t num__infty =  ((num_t)1.0)/((num_t)0.0);
#endif
static const num_t max_long = (num_t) (((unsigned long)(-1))>>1);

/* constructors */

#define num_init(a)
#define num_init_n(a,n)
#define num_init_set(a,b)        num_set((a),(b))
#define num_init_set_n(a,b,n)    num_set_n((a),(b),(n))
#define num_init_set_int(a,b)    num_set_int((a),(b))
#define num_init_set_float(a,b)  num_set_float((a),(b))
#define num_init_set_frac(a,b,c) num_set_frac((a),(b),(c))
#define num_init_set_infty(a)    num_set_infty((a))

/* copy / update */

#define num_set(a,b)     *(a) = *(b)
#define num_set_n(a,b,n) memcpy((a),(b),sizeof(num_t)*(n));

#define num_set_int(a,i)    *(a) = (num_t)(i)

#ifdef OCT_DEBUG_NAN
#define num_set_float(a,k)  do{ *(a) = (num_t)(k); OCT_ASSERT(!isnan(*(a)),"NaN in num_set_float"); }while(0)
#else
#define num_set_float(a,k)  *(a) = (num_t)(k)
#endif

#define num_set_frac(a,i,j) *(a) = ((num_t)(i))/((num_t)(j))
#define num_set_infty(a)    *(a) = num__infty

/* destructors */

#define num_clear(a)
#define num_clear_n(a,n)

/* conversions */

static inline bool num_fits_int(const num_t* a)
{
  num_t d = ceil(*a);
  return d!=num__infty && d<=max_long  && d>=-max_long;
}

#define num_fits_float(a) (*(a) != num__infty)

#define num_fits_frac(a)  num_fits_int((a))

#define num_get_int(a)   ((long)*(a))
#define num_get_float(a) ((double)*(a))
#define num_get_num(a)   ((long)ceil(*(a)))
#define num_get_den(a)   (1L)

/* tests */

#define num_infty(a)     (*(a)==num__infty)

static inline int num_cmp(const num_t* a, const num_t *b)
{ return (*a==*b) ? 0 : (*a>*b) ? 1 : -1; }

static inline int num_cmp_int(const num_t* a, long b)
{ num_t bb = (num_t)b; return (*a==bb) ? 0 : (*a>bb) ? 1 : -1; }

static inline int num_cmp_zero(const num_t* a)
{ return (*a==0.)?0:((*a>0.)?1:-1); }

/* operations */

#ifdef OLD_MIN_MAX
static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a>=*b) ? *a : *b; }

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a<=*b) ? *a : *b; }

#else
  /* DM: this version compiles to minsd/maxsd on SSE
     (the other version is not equivalent in general because of NaNs ) */
static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a > *b) ? *a : *b; }

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ *r = (*a < *b) ? *a : *b; }
#endif

#ifdef OCT_DEBUG_NAN
#define num_add(r,a,b)    do{ *(r) = *(a) + *(b); OCT_ASSERT(!isnan(*(r)),"NaN in num_add"); }while(0)
#define num_sub(r,a,b)    do{ *(r) = *(a) - *(b); OCT_ASSERT(!isnan(*(r)),"NaN in num_sub"); }while(0)
#define num_mul(r,a,b)    do{ *(r) = *(a) * *(b); OCT_ASSERT(!isnan(*(r)),"NaN in num_mul"); }while(0)
#define num_mul_by_2(r,a) do{ *(r) = *(a) * 2.; OCT_ASSERT(!isnan(*(r)),"NaN in num_mul_by_2"); }while(0)
#define num_div_by_2(r,a) do{ *(r) = *(a) / 2.; OCT_ASSERT(!isnan(*(r)),"NaN in num_div_by_2"); }while(0)
#define num_neg(r,a)      do{ *(r) = - *(a); OCT_ASSERT(!isnan(*(r)),"NaN in num_neg"); }while(0)
#else
#define num_add(r,a,b)    *(r) = *(a) + *(b)
#define num_sub(r,a,b)    *(r) = *(a) - *(b)
#define num_mul(r,a,b)    *(r) = *(a) * *(b)
#define num_mul_by_2(r,a) *(r) = *(a) * 2.
#define num_div_by_2(r,a) *(r) = *(a) / 2.
#define num_neg(r,a)      *(r) = - *(a)
#endif

/* printing */

#ifdef OCT_NUM_LONGDOUBLE

static inline void num_print(const num_t* a)
{ if (*a!=num__infty) printf("%.20Lg",(long double)*a+0.); 
  else printf("+oo"); }

static inline void num_snprint(char* s, size_t n, const num_t* a)
{ if (*a!=num__infty) snprintf(s,n,"%.20Lg",(long double)*a+0.); 
  else snprintf(s,n,"+oo");}

#else

static inline void num_print(const num_t* a)
{ if (*a!=num__infty) printf("%.20g",(double)*a+0.); 
  else printf("+oo"); }

static inline void num_snprint(char* s, size_t n, const num_t* a)
{ if (*a!=num__infty) snprintf(s,n,"%.20g",(double)*a+0.); 
  else snprintf(s,n,"+oo");}


#endif


/* GMP conversion */

#ifdef OCT_HAS_GMP

#define num_set_mpz(a,b) *(a)=mpz_get_d((b)) /* is this sound ? */
#define num_get_mpz(a,b) mpz_set_d((a),ceil(*(b)))
#define num_set_mpq(a,b) *(a)=mpq_get_d((b)) /* is this sound ? */
#define num_get_mpq(a,b) mpq_set_d((a),*(b))

#endif

#ifdef OCT_HAS_MPFR

#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
#define num_set_mpfr(a,b) *(a)=mpfr_get_d((b), GMP_RNDU)
#else
#define num_set_mpfr(a,b) *(a)=mpfr_get_d((b))
#endif

#define num_get_mpfr(a,b) mpfr_set_d((a),*(b),GMP_RNDU)

#endif


#define OCT_NUM_CLOSED
#undef  OCT_NUM_EXACT


/* serialization */

#define OCT_NUM_SERIALIZE

static const int num_serialize_id = 0x1100+sizeof(num_t);

static inline size_t num_serialize(const num_t* a, void* c) 
{ swap_word(c,a,sizeof(num_t)); return sizeof(num_t); }

static inline size_t num_deserialize(num_t* a, const void* c) 
{ swap_word(a,c,sizeof(num_t)); return sizeof(num_t); }

static inline size_t num_serialize_size(num_t* a) 
{ return sizeof(num_t); }

#endif


/********************************/
/* Rationals using machine-ints */
/********************************/

#ifdef OCT_NUM_FRAC

#ifdef OCT_NUM
#error "only one OCT_NUM_ must be defined in oct_num.h"
#endif
#define OCT_NUM

#define OCT_DOMAIN OCT_DOMAIN_FRAC
#define OCT_IMPLEMENTATION_STRING "long"

typedef long coef_t;

/* all rationals are kept in irreductible form  */
typedef struct {
  coef_t n;  /* numerator */
  coef_t d;  /* denominator, >=0 */
} num_t;

static const num_t num__infty = {  1,0 };

static const coef_t coef_overflow = ((coef_t)1<<(sizeof(coef_t)*4-1))-1;

static
inline
void
num_normalize (num_t* r)
{
  if (r->d) {
    /* euclide */
    coef_t pgcd, b;
    pgcd = (r->n<0) ? -r->n : r->n;
    b = r->d;
    while (b) {
      coef_t r = pgcd%b;
      pgcd = b;
      b = r;
    }
    r->n /= pgcd;
    r->d /= pgcd;
    if (r->n<=-coef_overflow || r->n>=coef_overflow || r->d>=coef_overflow) 
      r->d = 0;
  }
}

/* constructors */

#define num_init(a)
#define num_init_n(a,n)
#define num_init_set(a,b)        num_set((a),(b))
#define num_init_set_n(a,b,n)    num_set_n((a),(b),(n))
#define num_init_set_int(a,b)    num_set_int((a),(b))
#define num_init_set_float(a,b)  num_set_float((a),(b))
#define num_init_set_frac(a,b,c) num_set_frac((a),(b),(c))
#define num_init_set_infty(a)    num_set_infty((a))

/* copy / update */

#define num_set(a,b)     *(a) = *(b)
#define num_set_n(a,b,n) memcpy((a),(b),sizeof(num_t)*(n));

static inline void num_set_int(num_t* a, long i)
{ a->n = (coef_t)i; a->d = 1; num_normalize(a); } 

static inline void num_set_float(num_t* a, double k)
{ 
  k = ceil(k); 
  if (k<(double)-coef_overflow || k>(double)coef_overflow) *a = num__infty;
  else { a->n = (coef_t)k; a->d = 1; num_normalize(a); } 
}

static inline void num_set_frac(num_t* a, long i, long j)
{ 
  if (j>=0) { a->n=(coef_t)i; a->d=(coef_t)j; } 
  else { a->n=(coef_t)-i; a->d=(coef_t)-j; } 
  num_normalize(a); 
}

#define num_set_infty(a)    *(a) = num__infty

/* destructors */

#define num_clear(a)
#define num_clear_n(a,n)

/* conversions */

#define num_fits_int(a)   ((a)->d!=0)
#define num_fits_float(a) ((a)->d!=0)
#define num_fits_frac(a)  ((a)->d!=0)

#define num_get_int(a)   ((long)ceil(((double)((a)->n))/((double)((a)->d))))
#define num_get_float(a) (((double)((a)->n))/((double)((a)->d)))
#define num_get_num(a)   ((long)(a)->n)
#define num_get_den(a)   ((long)(a)->d)

/* tests */

#define num_infty(a)     ((a)->d==0)

static inline int num_cmp(const num_t* a, const num_t* b)
{ 
  if (!a->d) {
    if (!b->d) return 0;
    else return 1;
  }
  if (!b->d) return -1;
  else {
    const coef_t aa = a->n*b->d;
    const coef_t bb = a->d*b->n;
    if (aa==bb) return 0;
    if (aa>bb) return 1;
    return -1;
  }
}

static inline int num_cmp_int(const num_t* a, long b)
{ 
  if (!a->d) return 1;
  else if (b<=-coef_overflow) return  1;
  else if (b>= coef_overflow) return -1;
  else {
    const coef_t aa = a->n;
    const coef_t bb = a->d*b;
    if (aa==bb) return 0;
    if (aa>bb) return 1;
    return -1;
  }
}

static inline int num_cmp_zero(const num_t* a)
{ return (!a->d) ? 1 : ((a->n==0) ? 0 : ((a->n>0) ? 1 : -1)); }

/* operations */

static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ *r = (!a->d || !b->d) ? num__infty : (a->n*b->d>=b->n*a->d) ? *a : *b; }

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ *r = (!a->d) ? *b : (!b->d) ? *a : (a->n*b->d<=b->n*a->d) ? *a : *b; }

static inline void num_add(num_t* r, const num_t* a, const num_t* b)
{ coef_t d=a->d*b->d; r->n=a->n*b->d+a->d*b->n; r->d=d; num_normalize(r); }

static inline void num_sub(num_t* r, const num_t* a, const num_t* b)
{ coef_t d=a->d*b->d; r->n=a->n*b->d-a->d*b->n; r->d=d; num_normalize(r); }

static inline void num_mul(num_t* r, const num_t* a, const num_t* b)
{ r->n = a->n*b->n; r->d = a->d*b->d; num_normalize(r); }

static inline void num_mul_by_2(num_t* r, const num_t* a)
{ 
  *r = *a; 
  if (r->d & 1) { 
    r->n *= 2; 
    if (r->n<=-coef_overflow || r->n>=coef_overflow) r->d = 0; 
  }
  else r->d /= 2; 
}

static inline void num_div_by_2(num_t* r, const num_t* a)
{ 
  *r = *a; 
  if (r->n & 1) { r->d *= 2; if (r->d>=coef_overflow) r->d = 0; }
  else r->n /= 2; 
}

static inline void num_neg(num_t* r, const num_t* a)
{ r->n = -a->n; r->d = a->d; }

/* printing */

static
inline
void
num_print(const num_t* a)
{
  if (a->d)
    if (!a->n) printf("0");
    else if (a->d==1) printf("%li",(long)a->n);
    else printf("%li/%li",(long)a->n,(long)a->d); 
  else printf("+oo");
}

static
inline
void
num_snprint(char* s, size_t n, const num_t* a)
{
  if (a->d)
    if (!a->n) snprintf(s,n,"0");
    else if (a->d==1) snprintf(s,n,"%li",(long)a->n);
    else snprintf(s,n,"%li/%li",(long)a->n,(long)a->d); 
  else snprintf(s,n,"+oo");
}

/* GMP conversion */

#ifdef OCT_HAS_GMP

static inline void num_set_mpz(num_t* a, const mpz_t b)
{ 
  if (mpz_fits_slong_p(b)) num_set_int(a,mpz_get_si(b)); 
  else num_set_infty(a);
}

#define num_get_mpz(a,b) mpz_set_si((a),num_get_int((b)))

static inline void num_set_mpq(num_t* a, const mpq_t b)
{ 
  if (mpz_fits_slong_p(mpq_numref(b)) &&
      mpz_fits_slong_p(mpq_denref(b))) 
    num_set_frac(a,mpz_get_si(mpq_numref(b)),mpz_get_si(mpq_denref(b)));
  else num_set_infty(a);
}

#define num_get_mpq(a,b) mpq_set_si((a),(b)->n,(b)->d)

#endif

#ifdef OCT_HAS_MPFR

static inline void num_set_mpfr(num_t* a, const mpfr_t b)
{ 
  mpfr_t m;
  mpfr_init(m);
  mpfr_ceil(m,b);
  num_set_float(a,mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
    ));
  mpfr_clear(m);
}

static inline void num_get_mpfr(mpfr_t a, const num_t* b)
{ mpfr_set_si(a,b->n,GMP_RNDU); mpfr_div_ui(a,a,b->d,GMP_RNDU); }

#endif

#define OCT_NUM_CLOSED
#define OCT_NUM_EXACT

/* serialization */

#define OCT_NUM_SERIALIZE

static const int num_serialize_id = 0x1200+sizeof(coef_t);

static inline size_t num_serialize(const num_t* a, void* c) 
{ 
  swap_word(c,&a->n,sizeof(coef_t)); 
  swap_word((char*)c+sizeof(coef_t),&a->d,sizeof(coef_t)); 
  return 2*sizeof(coef_t); 
}

static inline size_t num_deserialize(num_t* a, const void* c) 
{
  swap_word(&a->n,c,sizeof(coef_t)); 
  swap_word(&a->d,(char*)c+sizeof(coef_t),sizeof(coef_t)); 
  return 2*sizeof(coef_t); 
}

static inline size_t num_serialize_size(num_t* a) 
{ return 2*sizeof(coef_t); }


#endif


/****************/
/* GMP Integers */
/****************/

#ifdef OCT_NUM_GMP_INT

#ifndef OCT_HAS_GMP
#error "the gmpint numerical type requires the GMP library"
#endif

#ifdef OCT_NUM
#error "only one OCT_NUM_ must be defined in oct_num.h"
#endif
#define OCT_NUM

#define OCT_DOMAIN OCT_DOMAIN_INT
#define OCT_IMPLEMENTATION_STRING "GMP mpz"


typedef struct {
  mpz_t num;  /* always allocated, even if inf=1 */
  char  inf;  /* 1 => +oo; 0 => <+oo */
} num_t;

static const double double_infty  =  ((double)1.0)/((double)0.0);
static const double double_minfty = -((double)1.0)/((double)0.0);

/* constructors */

#define num_init(a) mpz_init((a)->num)


static inline void num_init_n(num_t* a, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++) num_init(a); }

static inline void num_init_set(num_t* a, const num_t* b) 
{ a->inf=b->inf; if (a->inf) mpz_init(a->num); else mpz_init_set(a->num,b->num); }

static inline void num_init_set_n(num_t* a, const num_t* b, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++,b++) num_init_set(a,b); }

static inline void num_init_set_int(num_t* a, long i)
{ a->inf=0; mpz_init_set_si(a->num,i); }

static inline void num_init_set_float(num_t* a, double d)
{ a->inf=0; mpz_init_set_d(a->num,ceil(d)); }

#define num_init_set_frac(a,i,j) num_init_set_float((a),((double)(i))/((double)(j)))

static inline void num_init_set_infty(num_t* a) { a->inf=1; mpz_init(a->num); }

/* copy / update */

static inline void num_set(num_t* a, const num_t* b) 
{ a->inf=b->inf; if (!a->inf) mpz_set(a->num,b->num); }

static inline void num_set_n(num_t* a, const num_t* b, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++,b++) num_set(a,b); }

static inline void num_set_int(num_t* a, long i)
{ a->inf=0; mpz_set_si(a->num,i); }

static inline void num_set_float(num_t* a, double d)
{ a->inf=0; mpz_set_d(a->num,ceil(d)); }

#define num_set_frac(a,i,j) num_set_float((a),((double)(i))/((double)(j)))

#define num_set_infty(a) (a)->inf=1

/* destructors */

#define num_clear(a) mpz_clear((a)->num)

static inline void num_clear_n(num_t* a, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++) num_clear(a); }

/* conversions */

static inline bool num_fits_int(const num_t* a)
{ return !a->inf && mpz_fits_slong_p(a->num); }

static inline bool num_fits_float(const num_t* a)
{ 
  double d = mpz_get_d(a->num);
  return !a->inf && d!=double_infty && d!=double_minfty; 
}

#define num_fits_frac(a) num_fits_int(a)

#define num_get_int(a)   mpz_get_si((a)->num)
#define num_get_float(a) mpz_get_d((a)->num)
#define num_get_num(a)   mpz_get_si((a)->num)
#define num_get_den(a)   (1L)


/* GMP conversion */

#define num_get_mpz(a,b) mpz_set((a),(b)->num)
#define num_get_mpq(a,b) mpq_set_z((a),(b)->num)

static inline void num_set_mpz(num_t *a, const mpz_t b) 
{ mpz_set(a->num,b); a->inf=0; }

static inline void num_set_mpq(num_t *a, const mpq_t b) 
{ mpz_cdiv_q(a->num, mpq_numref(b), mpq_denref(b)); }


#ifdef OCT_HAS_MPFR

#define num_get_mpfr(a,b) mpfr_set_z((a),(b)->num,GMP_RNDU)

static inline void num_set_mpfr(num_t *a, const mpfr_t b) 
{ 
  mpfr_t m;
  mpfr_init(m);
  mpfr_ceil(m,b);
  num_set_float(a,mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
    ));
  mpfr_clear(m);
}

#endif

/* tests */

#define num_infty(a) ((a)->inf!=0)

static inline int num_cmp(const num_t* a, const num_t* b)
{
  if (a->inf) {
    if (b->inf) return 0;
    else return 1;
  }
  if (b->inf) return -1;
  return mpz_cmp(a->num,b->num);
}

static inline int num_cmp_int(const num_t* a, long i)
{ if (a->inf) return 1; return mpz_cmp_si(a->num,i); }

static inline int num_cmp_zero(const num_t* a)
{ return num_cmp_int(a,0); }

/* operations */

static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpz_set(r->num,mpz_cmp(a->num,b->num)>0?a->num:b->num); }
}

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf)
    if (b->inf) r->inf=1;
    else { r->inf=0; mpz_set(r->num,b->num); }
  else if (b->inf) { r->inf=0; mpz_set(r->num,a->num); }
  else { r->inf=0; mpz_set(r->num,mpz_cmp(a->num,b->num)<0?a->num:b->num); }
}

static inline void num_add(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpz_add(r->num,a->num,b->num); }
}

static inline void num_sub(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpz_sub(r->num,a->num,b->num); }
}

static inline void num_mul(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpz_mul(r->num,a->num,b->num); }
}

static inline void num_mul_by_2(num_t* r, const num_t* a)
{ 
  if (a->inf) r->inf=1;
  else { r->inf=0; mpz_mul_2exp(r->num,a->num,1); }
}

static inline void num_div_by_2(num_t* r, const num_t* a)
{ 
  if (a->inf) r->inf=1;
  else { r->inf=0; mpz_cdiv_q_2exp(r->num,a->num,1); }
}

static inline void num_neg(num_t* r, const num_t* a)
{ 
  if (a->inf) r->inf=1;
  else { r->inf=0; mpz_neg(r->num,a->num); }
}

/* printing */

static inline void num_print(const num_t* a)
{
  if (a->inf) printf("+oo");
  else mpz_out_str(stdout,10,a->num);
}

static inline void num_snprint(char* s, size_t n, const num_t* a)
{
  if (a->inf) snprintf(s,n,"+oo");
  else if (mpz_sizeinbase(a->num,10)+2>n) 
    if (mpz_sgn(a->num)>0) snprintf(s,n,"+BIG");
    else snprintf(s,n,"-BIG");
  else mpz_get_str(s,10,a->num);
}

#undef  OCT_NUM_CLOSED
#undef  OCT_NUM_EXACT


/* serialization */

#define OCT_NUM_SERIALIZE

static const int num_serialize_id = 0x1300;

static inline size_t num_serialize(const num_t* a, void* c) 
{ 
  size_t count;
  *((char*)c) = a->inf;
  if (a->inf) return 1;
  *((char*)c+1) = mpz_sgn(a->num);
  mpz_export((char*)c+6,&count,1,1,1,0,a->num);
  dump32((unsigned char*)c+2,count);
  return count+6;
}

static inline size_t num_deserialize(num_t* a, const void* c) 
{
  size_t count;
  a->inf = *(char*)c;
  if (a->inf) return 1;
  count = undump32((unsigned char*)c+2);
  mpz_import(a->num,count,1,1,1,0,(char*)c+6);
  if (*((char*)c+1)<0) {
    mpz_neg(a->num,a->num);
  }
  return count+6;
}

/* note: this does not give the exact size of serialized data, but a sound
   overapproximation
*/
static inline size_t num_serialize_size(num_t* a) 
{ 
  if (a->inf) return 1;
  return mpz_sizeinbase(a->num,2)/8+6+sizeof(mp_limb_t);
}


#endif




/*****************/
/* GMP Rationals */
/*****************/

#ifdef OCT_NUM_GMP_FRAC

#ifndef OCT_HAS_GMP
#error "the gmpfrac numerical type requires the GMP library"
#endif

#ifdef OCT_NUM
#error "only one OCT_NUM_ must be defined in oct_num.h"
#endif
#define OCT_NUM

#define OCT_DOMAIN OCT_DOMAIN_FRAC
#define OCT_IMPLEMENTATION_STRING "GMP mpq"

typedef struct {
  mpq_t num;  /* always allocated, even if inf=1 */
  char  inf;  /* 1 => +oo; 0 => <+oo */
} num_t;

static const double double_infty  =   ((double)1.0)/((double)0.0);
static const double double_minfty =  -((double)1.0)/((double)0.0);
static const double max_long = (double) (((unsigned long)(-1))>>1);

/* constructors */

#define num_init(a) mpq_init((a)->num)

static inline void num_init_n(num_t* a, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++) num_init(a); }

static inline void num_init_set(num_t* a, const num_t* b) 
{ a->inf=b->inf; mpq_init(a->num); if (!a->inf) mpq_set(a->num,b->num); }

static inline void num_init_set_n(num_t* a, const num_t* b, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++,b++) num_init_set(a,b); }

static inline void num_init_set_int(num_t* a, long i)
{ a->inf=0; mpq_init(a->num); mpq_set_si(a->num,i,1); }

static inline void num_init_set_float(num_t* a, double d)
{ a->inf=0; mpq_init(a->num); mpq_set_d(a->num,d); }

static inline void num_init_set_frac(num_t* a, long i, long j)
{ 
  if (j<0) { i=-i; j=-j; }
  a->inf=0; mpq_init(a->num); mpq_set_si(a->num,i,j); 
  mpq_canonicalize(a->num); 
}

static inline void num_init_set_infty(num_t* a) 
{ a->inf=1; mpq_init(a->num); }

/* copy / update */

static inline void num_set(num_t* a, const num_t* b) 
{ a->inf=b->inf; if (!a->inf) mpq_set(a->num,b->num); }

static inline void num_set_n(num_t* a, const num_t* b, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++,b++) num_set(a,b); }

static inline void num_set_int(num_t* a, long i)
{ a->inf=0; mpq_set_si(a->num,i,1); }

static inline void num_set_float(num_t* a, double d)
{ a->inf=0; mpq_set_d(a->num,d); }

static inline void num_set_frac(num_t* a, long i, long j)
{ 
  if (j<0) { i=-i; j=-j; }
  a->inf=0; mpq_set_si(a->num,i,j); 
  mpq_canonicalize(a->num); 
}

#define num_set_infty(a) (a)->inf=1

/* destructors */

#define num_clear(a) mpq_clear((a)->num)

static inline void num_clear_n(num_t* a, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++) num_clear(a); }

/* conversions */

static inline bool num_fits_int(const num_t* a)
{
  double d;
  if (a->inf) return false;
  d = ceil(mpq_get_d(a->num));
  return d<=max_long && d>=-max_long;
}

static inline bool num_fits_float(const num_t* a)
{
  double d = mpq_get_d(a->num);
  return !a->inf && d!=double_infty && d!=double_minfty;
}

static inline bool num_fits_frac(const num_t* a)
{ return !a->inf && mpz_fits_slong_p(mpq_numref(a->num))
    && mpz_fits_slong_p(mpq_denref(a->num)); }


static inline long num_get_int(const num_t* a)
{ return (long)ceil(mpq_get_d(a->num)); /* Bad... */ }

#define num_get_float(a) mpq_get_d((a)->num)
#define num_get_num(a)   mpz_get_si(mpq_numref((a)->num))
#define num_get_den(a)   mpz_get_si(mpq_denref((a)->num))


/* GMP conversion */

#define num_get_mpq(a,b) mpq_set((a),(b)->num)

static inline void num_set_mpq(num_t *a, const mpq_t b) 
{ mpq_set(a->num,b); a->inf=0; }

static inline void num_set_mpz(num_t *a, const mpz_t b) 
{ mpq_set_z(a->num,b); a->inf=0; }

static inline void num_get_mpz(mpz_t a, const num_t* b)
{ mpz_cdiv_q(a, mpq_numref(b->num), mpq_denref(b->num)); }



#ifdef OCT_HAS_MPFR

#define num_get_mpfr(a,b) mpfr_set_q((a),(b)->num,GMP_RNDU)

static inline void num_set_mpfr(num_t *a, const mpfr_t b) 
{ 
  mpfr_t m;
  mpfr_init(m);
  mpfr_ceil(m,b);
  num_set_float(a,mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
    ));
  mpfr_clear(m);
}


#endif


/* tests */

#define num_infty(a) ((a)->inf!=0)

static inline int num_cmp(const num_t* a, const num_t* b)
{
  if (a->inf) {
    if (b->inf) return 0;
    else return 1;
  }
  if (b->inf) return -1;
  return mpq_cmp(a->num,b->num);
}

static inline int num_cmp_int(const num_t* a, long i)
{ if (a->inf) return 1; return mpq_cmp_si(a->num,i,1); }

static inline int num_cmp_zero(const num_t* a)
{ return num_cmp_int(a,0); }

/* operations */

static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpq_set(r->num,mpq_cmp(a->num,b->num)>0?a->num:b->num); }
}

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf)
    if (b->inf) r->inf=1;
    else { r->inf=0; mpq_set(r->num,b->num); }
  else if (b->inf) { r->inf=0; mpq_set(r->num,a->num); }
  else { r->inf=0; mpq_set(r->num,mpq_cmp(a->num,b->num)<0?a->num:b->num); }
}

static inline void num_add(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpq_add(r->num,a->num,b->num); }
}

static inline void num_sub(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpq_sub(r->num,a->num,b->num); }
}

static inline void num_mul(num_t* r, const num_t* a, const num_t* b)
{ 
  if (a->inf || b->inf) r->inf=1;
  else { r->inf=0; mpq_mul(r->num,a->num,b->num); }
}

static inline void num_mul_by_2(num_t* r, const num_t* a)
{ 
  if (a->inf) r->inf=1;
  else { r->inf=0; mpq_mul_2exp(r->num,a->num,1); }
}

static inline void num_div_by_2(num_t* r, const num_t* a)
{ 
  if (a->inf) r->inf=1;
  else { r->inf=0; mpq_div_2exp(r->num,a->num,1); }
}

static inline void num_neg(num_t* r, const num_t* a)
{ 
  if (a->inf) r->inf=1;
  else { r->inf=0; mpq_neg(r->num,a->num); }
}

/* printing */

static inline void num_print(const num_t* a)
{
  if (a->inf) printf("+oo");
  else if (!mpz_cmp_si(mpq_denref(a->num),1))
    mpz_out_str(stdout,10,mpq_numref(a->num));
  else mpq_out_str(stdout,10,a->num);
}

static inline void num_snprint(char* s, size_t n, const num_t* a)
{
  if (a->inf) snprintf(s,n,"+oo");
  else if (mpz_sizeinbase(mpq_numref(a->num),10)+
	   mpz_sizeinbase(mpq_denref(a->num),10)+3>n)
    if (mpq_sgn(a->num)>0) snprintf(s,n,"+BIG");
    else snprintf(s,n,"-BIG");
  else 
    if (!mpz_cmp_si(mpq_denref(a->num),1))
      mpz_get_str(s,10,mpq_numref(a->num));
    else {
      mpz_get_str(s,10,mpq_numref(a->num));
      strcat(s,"/");
      mpz_get_str(s+strlen(s),10,mpq_denref(a->num));    
    }
}


#define OCT_NUM_CLOSED
#define OCT_NUM_EXACT


/* serialization */

#define OCT_NUM_SERIALIZE

static const int num_serialize_id = 0x1400;

static inline size_t num_serialize(const num_t* a, void* c) 
{ 
  size_t count1,count2;
  *((char*)c) = a->inf;
  if (a->inf) return 1;
  *((char*)c+1) = mpq_sgn(a->num);
  mpz_export((char*)c+10,&count1,1,1,1,0,mpq_numref(a->num));
  mpz_export((char*)c+10+count1,&count2,1,1,1,0,mpq_denref(a->num));
  dump32((unsigned char*)c+2,count1);
  dump32((unsigned char*)c+6,count2);
  return count1+count2+10;
}

static inline size_t num_deserialize(num_t* a, const void* c) 
{
  size_t count1,count2;
  a->inf = *(char*)c;
  if (a->inf) return 1;
  count1 = undump32((unsigned char*)c+2);
  count2 = undump32((unsigned char*)c+6);
  mpz_import(mpq_numref(a->num),count1,1,1,1,0,(char*)c+10);
  mpz_import(mpq_denref(a->num),count2,1,1,1,0,(char*)c+10+count1);
  if (*((char*)c+1)<0) {
    mpq_neg(a->num,a->num);
  }
  return count1+count2+10;
}

/* note: this does not give the exact size of serialized data, but a sound
   overapproximation
*/
static inline size_t num_serialize_size(num_t* a) 
{ 
  if (a->inf) return 1;
  return 
    (mpz_sizeinbase(mpq_numref(a->num),2)+
     mpz_sizeinbase(mpq_denref(a->num),2))/8+10+2*sizeof(mp_limb_t);
}


#endif



/***************/
/* MPFR Floats */
/***************/

#ifdef OCT_NUM_MPFR_FLOAT

#ifndef OCT_HAS_GMP
#error "the mpfrfloat numerical type requires the GMP library"
#endif

#ifndef OCT_HAS_MPFR
#error "the mpfrfloat numerical type requires the MPFR library"
#endif

#ifdef OCT_NUM
#error "only one OCT_NUM_ must be defined in oct_num.h"
#endif
#define OCT_NUM

#define OCT_DOMAIN OCT_DOMAIN_REAL
#define OCT_IMPLEMENTATION_STRING "GMP mpfr"

typedef struct {
  mpfr_t num;  
} num_t;

static const double double_infty  =  ((double)1.0)/((double)0.0);
static const double double_minfty = -((double)1.0)/((double)0.0);
static const double max_long = (double) (((unsigned long)(-1))>>1);

/* constructors */

#define num_init(a) mpfr_init((a)->num)

static inline void num_init_n(num_t* a, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++) num_init(a); }

#define num_init_set(a,b) mpfr_init_set((a)->num,(b)->num,GMP_RNDU)

static inline void num_init_set_n(num_t* a, const num_t* b, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++,b++) num_init_set(a,b); }

#define num_init_set_int(a,i)   mpfr_init_set_si((a)->num,(i),GMP_RNDU)
#define num_init_set_float(a,d) mpfr_init_set_d ((a)->num,(d),GMP_RNDU)

static inline void num_init_set_frac(num_t* a, long i, long j)
{ 
  if (j<0) { i=-i; j=-j; }
  mpfr_init_set_si(a->num,i,GMP_RNDU); 
  mpfr_div_ui(a->num,a->num,j,GMP_RNDU);
}

#define num_init_set_infty(a) mpfr_init_set_d((a)->num,double_infty,GMP_RNDU)

/* copy / update */

#define num_set(a,b) mpfr_set((a)->num,(b)->num,GMP_RNDU)

static inline void num_set_n(num_t* a, const num_t* b, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++,b++) num_set(a,b); }

#define num_set_int(a,i)   mpfr_set_si((a)->num,(i),GMP_RNDU)
#define num_set_float(a,d) mpfr_set_d ((a)->num,(d),GMP_RNDU)

static inline void num_set_frac(num_t* a, long i, long j)
{ 
  if (j<0) { i=-i; j=-j; }
  mpfr_set_si(a->num,i,GMP_RNDU); 
  mpfr_div_ui(a->num,a->num,j,GMP_RNDU);
}

#define num_set_infty(a) mpfr_set_d((a)->num,double_infty,GMP_RNDU)

/* destructors */

#define num_clear(a) mpfr_clear((a)->num)

static inline void num_clear_n(num_t* a, size_t n) 
{ size_t i; for (i=0;i<n;i++,a++) num_clear(a); }

/* conversions */

static inline bool num_fits_int(const num_t* a)
{ 
  bool b;
  mpfr_t m;
  double d;
  if (mpfr_inf_p(a->num)) return false;
  mpfr_init(m);
  mpfr_ceil(m,a->num);
  d = mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
    );
  b = d<=max_long && d>=-max_long;
  mpfr_clear(m);
  return b;
}

static inline bool num_fits_float(const num_t* a)
{ 
  double d = mpfr_get_d(a->num
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
  );
  return d!=double_infty && d!=double_minfty;
}

#define num_fits_frac(a) num_fits_int(a)

static inline long num_get_int(const num_t* a)
{ 
  mpfr_t m;
  long l;
  mpfr_init(m);
  mpfr_ceil(m,a->num);
  l = (long)ceil(mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
   ));
  mpfr_clear(m);
  return l;
}

#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
#define num_get_float(a) mpfr_get_d((a)->num, GMP_RNDU)
#else
#define num_get_float(a) mpfr_get_d((a)->num)
#endif

#define num_get_num(a)   num_get_int(a)
#define num_get_den(a)   (1L)


/* GMP conversion */

#define num_set_mpz(a,b)  mpfr_set_z((a)->num,(b),GMP_RNDU)
#define num_set_mpq(a,b)  mpfr_set_q((a)->num,(b),GMP_RNDU)
#define num_set_mpfr(a,b) mpfr_set((a)->num,(b),GMP_RNDU)

#define num_get_mpfr(a,b) mpfr_set((a),(b)->num,GMP_RNDU)

static inline void num_get_mpz(mpz_t b, const num_t* a)
{ 
  mpfr_t m;
  long l;
  mpfr_init(m);
  mpfr_ceil(m,a->num);
  l = (long)ceil(mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
   ));
  mpz_set_si(b,l);
  mpfr_clear(m);
}

static inline void num_get_mpq(mpq_t b, const num_t* a)
{ 
  mpfr_t m;
  long l;
  mpfr_init(m);
  mpfr_ceil(m,a->num);
  l = (long)ceil(mpfr_get_d(m
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
    , GMP_RNDU
#endif
   ));
  mpq_set_si(b,l,1);
  mpfr_clear(m);
}



/* tests */

#define num_infty(a)      mpfr_inf_p((a)->num)
#define num_cmp(a,b)      mpfr_cmp((a)->num,(b)->num)
#define num_cmp_int(a,b)  mpfr_cmp_si((a)->num,(b))
#define num_cmp_zero(a)   mpfr_cmp_si((a)->num,0)

/* operations */

static inline void num_max(num_t* r, const num_t* a, const num_t* b)
{ mpfr_set(r->num,mpfr_cmp(a->num,b->num)>0?a->num:b->num,GMP_RNDU); }

static inline void num_min(num_t* r, const num_t* a, const num_t* b)
{ mpfr_set(r->num,mpfr_cmp(a->num,b->num)<0?a->num:b->num,GMP_RNDU); }

#define num_add(r,a,b) mpfr_add((r)->num,(a)->num,(b)->num,GMP_RNDU)
#define num_sub(r,a,b) mpfr_sub((r)->num,(a)->num,(b)->num,GMP_RNDU)
#define num_mul(r,a,b) mpfr_mul((r)->num,(a)->num,(b)->num,GMP_RNDU)
#define num_mul_by_2(r,a)  mpfr_mul_2exp((r)->num,(a)->num,1,GMP_RNDU)
#define num_div_by_2(r,a)  mpfr_div_2exp((r)->num,(a)->num,1,GMP_RNDU)
#define num_neg(r,a)   mpfr_neg((r)->num,(a)->num,GMP_RNDU)

/* printing */

static inline void num_print(const num_t* a)
{ mpfr_out_str(stdout,10,6,a->num,GMP_RNDU); }

static inline void num_snprint(char*s, size_t n, const num_t* a)
{
  char buf[100];
  mp_exp_t ex;
  if (mpfr_inf_p(a->num)) snprintf(s,n,"+oo");
  else {
    /*    mpfr_get_str(buf,&ex,10,(sizeof(buf)>=n)?n:sizeof(buf)-1,a->num,GMP_RNDU);
	  if (ex) snprintf(s,n,"%c.%se%li",buf[0],buf+1,(long)ex);
	  else snprintf(s,n,"%c.%s",buf[0],buf+1); */
    snprintf(s,n,"%f", mpfr_get_d(a->num
#if (__GNU_MP_VERSION >= 4) && (__GNU_MP_VERSION_MINOR >= 1)
	     , GMP_RNDU
#endif
      ));
  }
}


#define OCT_NUM_CLOSED
#undef  OCT_NUM_EXACT


/* serialization */

/* there is currently no _export / _import functions in MPFR
   => we designed our own functions, not very portable and relying on 
   the internal encoding...
 */

#define OCT_NUM_SERIALIZE

static const int num_serialize_id = 
  0x150000 +
  sizeof(mpfr_prec_t) + 16*sizeof(mp_exp_t) + 256*sizeof(mp_limb_t);

static inline size_t num_serialize(const num_t* a, void* c) 
{ 
  size_t i,count=0,bytes;
  swap_word((char*)c+count,&a->num[0]._mpfr_prec,sizeof(mpfr_prec_t));
  count += sizeof(mpfr_prec_t);
  *((char*)c+count) = a->num[0]._mpfr_sign;
  count++;
  swap_word((char*)c+count,&a->num[0]._mpfr_exp,sizeof(mp_exp_t));
  count += sizeof(mp_exp_t);
  bytes = (a->num[0]._mpfr_prec+8*sizeof(mp_limb_t)-1)/(8*sizeof(mp_limb_t));
  for (i=0;i<bytes;i++,count+=sizeof(mp_limb_t))
    swap_word((char*)c+count,&a->num[0]._mpfr_d[i],sizeof(mp_limb_t));
  return count;
}

static inline size_t num_deserialize(num_t* a, const void* c) 
{
  size_t i,count=0,bytes;
  mpfr_prec_t p;
  mp_exp_t e;
  char s;
  swap_word(&p,(char*)c+count,sizeof(mpfr_prec_t));
  count += sizeof(mpfr_prec_t);
  s = *((char*)c+count);
  count++;
  swap_word(&e,(char*)c+count,sizeof(mp_exp_t));
  count += sizeof(mp_exp_t);
  bytes = (p+8*sizeof(mp_limb_t)-1)/(8*sizeof(mp_limb_t));
  mpfr_set_prec(a->num,p);
  for (i=0;i<bytes;i++,count+=sizeof(mp_limb_t))
    swap_word(&a->num[0]._mpfr_d[i],(char*)c+count,sizeof(mp_limb_t));
  a->num[0]._mpfr_sign = s;
  a->num[0]._mpfr_exp = e;
  return count;
}


/* note: this does not give the exact size of serialized data, but a sound
   overapproximation
*/
static inline size_t num_serialize_size(num_t* a) 
{ 
  return 
    sizeof(mpfr_prec_t)+1+sizeof(mp_exp_t)+
    (a->num[0]._mpfr_prec/8)+sizeof(mp_limb_t);
}


#endif



#ifdef __cplusplus
}
#endif

#ifndef OCT_NUM
#error "one OCT_NUM_ must be defined in oct_num.h"
#endif


#endif
