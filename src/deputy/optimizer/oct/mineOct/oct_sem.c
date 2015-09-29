/* oct_sem.c
   Semantics abstract functions.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#include <oct.h>
#include <oct_private.h>

/* define to use simplified closure / incremental closure */
#undef BHMZ05

/*******************/
/* Initialization  */
/*******************/

#if 0
#if defined(__FreeBSD__) || defined(sun)

#include <ieeefp.h>
static int init_fpu() 
{ fpsetround(FP_RP); /*fpsetmask(fpgetmask()|FP_X_INV); */ return 1; }

#elif defined(linux)

#include <fenv.h>
static int init_fpu() 
{ return !fesetround(FE_UPWARD) /*&& feenableexcept(FE_INVALID)!=-1*/; }

#elif defined(__ppc__)

static int init_fpu() { 
  asm volatile ("mtfsfi 7,2");
  /* asm volatile ("mtfsb1 24"); */
  return 1;
}

#else

static int init_fpu() { fprintf(stderr,"Octagon Library Warning: don't know how top set the FPU rounding mode.\n"); return 0; }

#endif
#endif


int
OCT_PROTO(init) ()
{
#if defined(OCT_NUM_FLOAT) || defined(OCT_NUM_LONGDOUBLE)
  return init_fpu();
#else
  return 1;
#endif
}


/********************************/
/* Octagon Creation/Destruction */
/********************************/

/* empty domain, c is not allocated */
inline
oct_t*
OCT_PROTO(empty) (const var_t n)
{
  oct_t* m;
  OCT_ENTER("oct_empty",3); 
  m = new_t(oct_t);
  m->n = n;
  m->ref = 1;
  m->state = OCT_EMPTY;
  m->closed = (oct_t*)NULL;
  m->c = (num_t*)NULL;
  OCT_EXIT("oct_empty",3);
  return m;
}

/* constraints not initialized, it returns an INVALID matrix */
inline
oct_t*
OCT_PROTO(alloc) (const var_t n)
{
  size_t nn = matsize(n);
  oct_t* m;
  m = oct_empty(n);
  m->c = new_n(num_t,nn);
  num_init_n(m->c,nn);
  m->state = OCT_NORMAL;
  m->closed = (oct_t*)NULL;
  return m;
}

/* all constraints are set to +infty, (except m[i][i]=0) */
inline
oct_t*
OCT_PROTO(universe) (const var_t n)
{
  oct_t* m;
  size_t i, nn = matsize(n);
  OCT_ENTER("oct_universe",4);
  m = oct_alloc(n);
  for (i=0;i<nn;i++) num_set_infty(m->c+i);
  for (i=0;i<2*n;i++) num_set_int(m->c+matpos(i,i),0);
  m->state = OCT_CLOSED;
  OCT_EXIT("oct_universe",4);
  return m;
}

/* full copy, except new ref is 1 (oct_copy is preferred for lazy copy) */
inline
oct_t*
OCT_PROTO(full_copy) (oct_t* mm)
{
  oct_t* m;
  OCT_ENTER("oct_full_copy",5);
  m = oct_empty(mm->n);
  m->state = mm->state;
  m->closed = mm->closed;
  if (m->closed) m->closed->ref++;
  if (mm->c) {
    const size_t nn = matsize(mm->n);
    m->c = new_n(num_t,nn);
    num_init_set_n(m->c,mm->c,nn);
  }
  else m->c = (num_t*)NULL;
  OCT_EXIT("oct_full_copy",5);
  return m;
}

/* just add one to ref count */
inline
oct_t*
OCT_PROTO(copy) (oct_t* m)
{
  m->ref++;
  return m;
}

/* really free if ref count reaches 0 */
inline
void
OCT_PROTO(free) (oct_t* m)
{
  m->ref--;
  if (!m->ref) {
    if (m->closed) {
      m->closed->ref--;
      if (!m->closed->ref) { /* free cached closed version */
	if (m->closed->c)  
	  { num_clear_n(m->closed->c,matsize(m->n)); oct_mm_free(m->closed->c); }
	oct_mm_free(m->closed);
      }
    }
    if (m->c) { num_clear_n(m->c,matsize(m->n)); oct_mm_free(m->c); }
    oct_mm_free(m);
  }
}


/*******************/
/* Query Functions */
/*******************/

/* number of variables */
inline
var_t
OCT_PROTO(dimension) (oct_t* m)
{
  return m->n;
}

size_t
OCT_PROTO(nbconstraints) (oct_t* m)
{
  const size_t nn = matsize(m->n);
  size_t i;
  size_t n = 0;
  num_t* c = m->c;
  OCT_ENTER("oct_nbconstraints",6);
  if (m->state==OCT_EMPTY) return 0;
  for (i=0;i<nn;i++,c++)
    if (!num_infty(c)) n++;
  OCT_EXIT("oct_nbconstraints",6);
  return n-2*m->n; /* remove the 2n constraints of the form x_i-x_i<=0 */
}


/******************/
/* Strong Closure */
/******************/


/* 
   strong closure algorithm.
   returns either a CLOSED matrix, or an EMPTY matrix 
   if destructive!=0, the argument is freed and may not be used anymore
   the closure is cached in m->cached if cache=1
   O(n^3) time complexity
   O(n) space complexity (no temporary matrix created!)
*/


#ifndef BHMZ05 /* original version */

oct_t*
OCT_PROTO(close) (oct_t* m,
		  bool   destructive,
		  bool   cache)
{
  var_t  i,j,k;
  oct_t* mm;
  const var_t n2 = m->n*2;
  num_t *buf1, *buf2;
  num_t kk1,kk2,ik1,ik2,ij1,ij2,ij3,ij4;

  OCT_ENTER("oct_close",48);
  /* already closed or empty, we have nothing to do */
  if (m->state==OCT_CLOSED || m->state==OCT_EMPTY) {
    if (destructive) mm=m; else mm = oct_copy(m);
    goto end2;
  }

  /* closed form is cached, we have nothing to do */
  if (m->closed) {
    mm = oct_copy(m->closed);
    if (destructive) oct_free(m);
    goto end2;
  }

  if (destructive)
    if (m->ref==1) mm = m;
    else { mm = oct_full_copy(m); m->ref--; }
  else mm = oct_full_copy(m);
  if (cache && m!=mm) m->closed = oct_copy(mm);

  OCT_ENTER("oct_really_close",49);
  /* these buffers avoid a temporary matrix to be created
     they can also speed up the computation if they stay in the CPU cache!
  */
  buf1 = new_n(num_t,n2); buf2 = new_n(num_t,n2);
  num_init_n(buf1,n2); num_init_n(buf2,n2);
  num_init(&kk1); num_init(&kk2);
  num_init(&ik1); num_init(&ik2);
  num_init(&ij1); num_init(&ij2); num_init(&ij3); num_init(&ij4);

  for (k=0;k<n2;k+=2) {
    
    /* Ck step */
    
    num_t* d = mm->c;   /* xj-xi */
    num_set(&kk1,mm->c+matpos(k+1,k)); /*  xk+xk */
    num_set(&kk2,mm->c+matpos(k,k+1)); /* -xk-xk */
    
    /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
    for (i=0;i<=k;i+=2) {
      num_set(buf1+i  ,mm->c+matpos(k+1,i+1)); /* -xi+xk */
      num_set(buf2+i  ,mm->c+matpos(k  ,i+1)); /* -xi-xk */
      num_set(buf1+i+1,mm->c+matpos(k+1,i  )); /*  xi+xk */
      num_set(buf2+i+1,mm->c+matpos(k  ,i  )); /*  xi-xk */
    }
    for (;i<n2;i+=2) {
      num_set(buf1+i  ,mm->c+matpos(i  ,k  )); /*  xk-xi */
      num_set(buf2+i  ,mm->c+matpos(i  ,k+1)); /* -xk-xi */
      num_set(buf1+i+1,mm->c+matpos(i+1,k  )); /*  xk+xi */
      num_set(buf2+i+1,mm->c+matpos(i+1,k+1)); /* -xk+xi */
    }
    
    for (i=0;i<n2;i++) {
      const var_t ii = i|1;
      num_add(&ik1,buf2+i,&kk1);        /* (-xk-xi) + ( xk+xk) */
      num_add(&ik2,buf1+i,&kk2);        /* ( xk-xi) + (-xk-xk) */
      for (j=0;j<=ii;j++,d++) {
	var_t jj = j^1;
	num_add(&ij1,buf1+i,buf2+jj); num_add(&ij2,&ik1,buf2+jj);
	num_add(&ij3,buf2+i,buf1+jj); num_add(&ij4,&ik2,buf1+jj);
	num_min(&ij1,&ij1,&ij2); num_min(&ij3,&ij3,&ij4);
	num_min(&ij1,&ij1,&ij3);
	num_min(d,d,&ij1);
      }	
    }
 
    /* S step */
    
    d = mm->c;   /* xj-xi */
    /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
    
    for (i=0;i<n2;i+=2) {
      num_div_by_2(buf1+i,  mm->c+matpos(i+1,i)); /* ( xi+xi)/2 */
      num_div_by_2(buf1+i+1,mm->c+matpos(i,i+1)); /* (-xi-xi)/2 */
    }

    for (i=0;i<n2;i++) {
      const var_t ii  = i|1;
      const var_t ii2 = i^1;
      for (j=0;j<=ii;j++,d++) {
	num_add(&ij1,buf1+j,buf1+ii2);
	num_min(d,d,&ij1);
      }
    }
    
    /* emptyness checking */
    for (i=0;i<n2;i+=2)
      if (num_cmp_zero(mm->c+matpos(i,i))<0) {
	mm->state = OCT_EMPTY;
	num_clear_n(mm->c,matsize(mm->n));
	oct_mm_free(mm->c); mm->c = (num_t*)NULL;
	goto end;
      }
  }
  
  mm->state = OCT_CLOSED;
 end:
  num_clear(&kk1); num_clear(&kk2);
  num_clear(&ik1); num_clear(&ik2);
  num_clear(&ij1); num_clear(&ij2); num_clear(&ij3); num_clear(&ij4);
  num_clear_n(buf1,n2); num_clear_n(buf2,n2);
  oct_mm_free(buf1); oct_mm_free(buf2);
  OCT_EXIT("oct_really_close",49);
 end2:
  OCT_EXIT("oct_close",48);
  return mm;
}

#else /* optimized algorithm from BHMZ05 (constant factor improvement) */

oct_t*
OCT_PROTO(close) (oct_t* m,
		  bool   destructive,
		  bool   cache)
{
  var_t  i,j,k;
  oct_t* mm;
  const var_t n2 = m->n*2;
  num_t *c,ik,ik2,ij;

  OCT_ENTER("oct_close",48);
  /* already closed or empty, we have nothing to do */
  if (m->state==OCT_CLOSED || m->state==OCT_EMPTY) {
    if (destructive) mm=m; else mm = oct_copy(m);
    goto end2;
  }

  /* closed form is cached, we have nothing to do */
  if (m->closed) {
    mm = oct_copy(m->closed);
    if (destructive) oct_free(m);
    goto end2;
  }

  if (destructive)
    if (m->ref==1) mm = m;
    else { mm = oct_full_copy(m); m->ref--; }
  else mm = oct_full_copy(m);
  if (cache && m!=mm) m->closed = oct_copy(mm);

  OCT_ENTER("oct_really_close_BHMZ05",49);

  num_init(&ik); num_init(&ik2); num_init(&ij);

  /* Floyd-Warshall */
  for (k=0;k<n2;k++) {
    const var_t k2 = k^1;
    c = mm->c;
    for (i=0;i<n2;i++) {
      const var_t i2 = i|1;
      const var_t br = k<i2 ? k : i2;
      num_set(&ik,mm->c+matpos2(i,k));
      num_set(&ik2,mm->c+matpos2(i,k2));      
      for (j=0;j<=br;j++,c++) {
	num_add(&ij,&ik,mm->c+matpos(k,j));    /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,mm->c+matpos(k2,j));  /* ik2+k2j */
	num_min(c,c,&ij);
      }
      for (;j<=i2;j++,c++) {
	num_add(&ij,&ik,mm->c+matpos(j^1,k2)); /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,mm->c+matpos(j^1,k)); /* ik2+k2j */
	num_min(c,c,&ij);
      }
    }
 
  }
  
  /* lone S step */
  c = mm->c;
  for (i=0;i<n2;i++) {
    const var_t i2 = i|1;
    num_div_by_2(&ij,mm->c+matpos(i,i^1));
    for (j=0;j<=i2;j++,c++) {
      num_div_by_2(&ik,mm->c+matpos(j^1,j)); /* (ii2+j2j)/2 */
      num_add(&ik,&ik,&ij);
      num_min(c,c,&ik);
    }
  }

  /* emptyness checking */
  for (i=0;i<n2;i++) {
    c = mm->c+matpos(i,i);
    if (num_cmp_zero(c)<0) {
      mm->state = OCT_EMPTY;
      num_clear_n(mm->c,matsize(mm->n));
      oct_mm_free(mm->c); mm->c = (num_t*)NULL;
      goto end;
    }
    else num_set_int(c,0);
  }

  mm->state = OCT_CLOSED;
 end:
  num_clear(&ik); num_clear(&ik2); num_clear(&ij);
  OCT_EXIT("oct_really_close_BHMZ05",49);
 end2:
  OCT_EXIT("oct_close",48);
  return mm;
}

#endif


/* returns the closure of m if it is available without computation,
   and m elsewhere
   null cost
*/
inline
oct_t*
OCT_PROTO(close_lazy) (oct_t* m,
		       bool   destructive)
{
  oct_t* r;
  OCT_ENTER("oct_close_lazy",8); 
  if (m->closed) {
    r = oct_copy(m->closed);
    if (destructive) oct_free(m);
  }
  else if (destructive) r = m;
  else r = oct_copy(m);
  OCT_EXIT("oct_close_lazy",8); 
  return r;
}

inline
bool
OCT_PROTO(is_closed) (oct_t* m)
{
  return (m->state==OCT_CLOSED || m->state==OCT_EMPTY)?true:false;
}


/* 
   incremental version of the closure
   the argument matrix must be almost closed, ie, it must be a closed
   matrix except the constraints involving variable v
   always destructive, modify its argument in-place
   O(n^2) time complexity
*/

#ifndef BHMZ05 /* original version */

inline
void
OCT_PROTO(close_incremental) (oct_t* m,
			      var_t  v)
{
  var_t  i,j,k;
  const var_t n2 = m->n*2;
  const var_t v2 = v*2;
  num_t *buf1, *buf2;
  num_t kk1,kk2,ik1,ik2,ij1,ij2,ij3,ij4;

  OCT_ENTER("oct_close_incremental",9);
  OCT_ASSERT(v<m->n,"variable index greater than the number of variables in oct_close_incremental");
  if (m->state==OCT_EMPTY) goto end2;

  buf1 = new_n(num_t,n2); buf2 = new_n(num_t,n2);
  num_init_n(buf1,n2); num_init_n(buf2,n2);
  num_init(&kk1); num_init(&kk2);
  num_init(&ik1); num_init(&ik2);
  num_init(&ij1); num_init(&ij2); num_init(&ij3); num_init(&ij4);
  
  /* try to reduce xv coefficients using xk coefficients */
  OCT_ENTER("oct_close_incremental_1",10);
  {
    num_t* pvpv = m->c+matpos(v2+1,v2);   /*  xv+xv */
    num_t* mvmv = m->c+matpos(v2,v2+1);   /* -xv-xv */

    for (k=0;k<n2;k+=2) {
      
      /* Ck step */
      num_t* pkpk = m->c+matpos (k+1,k);   /*  xk+xk */
      num_t* mkmk = m->c+matpos (k,k+1);   /* -xk-xk */
      num_t* pkpv = m->c+matpos2(v2+1,k  );
      num_t* mkpv = m->c+matpos2(v2+1,k+1);
      num_t* pkmv = m->c+matpos2(v2  ,k  );
      num_t* mkmv = m->c+matpos2(v2  ,k+1);
      for (i=0;i<n2;i++) {
	/*(TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	num_t* imv = m->c + matpos2(v2  ,i); /* xi-xv */
	num_t* ipv = m->c + matpos2(v2+1,i); /* xi+xv */
	num_t* imk = m->c + matpos2(k   ,i); /* xi-xk */
	num_t* ipk = m->c + matpos2(k+1 ,i); /* xi+xk */
	num_add(&ij1,imk,pkpv);
	num_add(&ij2,ipk,mkpv);
	num_add(&ij3,imk,pkpk); num_add(&ij3,&ij3,mkpv);
	num_add(&ij4,ipk,mkmk); num_add(&ij4,&ij4,pkpv);
	num_min(&ij1,&ij1,&ij2); num_min(&ij3,&ij3,&ij4);
	num_min(&ij1,&ij1,&ij3);
	num_min(ipv,ipv,&ij1);
	
	num_add(&ij1,imk,pkmv);
	num_add(&ij2,ipk,mkmv);
	num_add(&ij3,imk,pkpk); num_add(&ij3,&ij3,mkmv);
	num_add(&ij4,ipk,mkmk); num_add(&ij4,&ij4,pkmv);
	num_min(&ij1,&ij1,&ij2); num_min(&ij3,&ij3,&ij4);
	num_min(&ij1,&ij1,&ij3);
	num_min(imv,imv,&ij1);
      }

      /* S step */
      for (i=0;i<v2+2;i++) {
	/*(TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	num_t* imv = m->c + matpos(v2  ,i); /* xi-xv */
	num_t* ipv = m->c + matpos(v2+1,i); /* xi+xv */
	num_t* ii  = m->c + matpos(i^1,i);   /* xi+xi */
	num_add(&ij1,ii,pvpv); num_div_by_2(&ij1,&ij1); num_min(ipv,ipv,&ij1);
	num_add(&ij2,ii,mvmv); num_div_by_2(&ij2,&ij2); num_min(imv,imv,&ij2);
      }
      for (;i<n2;i++) {
	/*(TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	num_t* imv = m->c + matpos(i, v2+1); /* -xi-xv */
	num_t* ipv = m->c + matpos(i, v2  ); /* -xi+xv */
	num_t* ii  = m->c + matpos(i,i^1);    /* -xi-xi */
	num_add(&ij1,ii,pvpv); num_div_by_2(&ij1,&ij1); num_min(ipv,ipv,&ij1);
	num_add(&ij2,ii,mvmv); num_div_by_2(&ij2,&ij2); num_min(imv,imv,&ij2);
      }

      /* emptyness checking */
      if (num_cmp_zero(m->c+matpos(v,v))<0) {
	m->state=OCT_EMPTY;
	num_clear_n(m->c,matsize(m->n));
	oct_mm_free(m->c); m->c = (num_t*)NULL;
	OCT_EXIT("oct_close_incremental_1",10);
	goto end;
      }
    }
  }
  OCT_EXIT("oct_close_incremental_1",10);

  /* try to reduce xk coefficients using xv coefficients */
  OCT_ENTER("oct_close_incremental_2",11);
  {
    num_t* d = m->c;   /* xj-xi */
    k = v2;
    
    /* Ck step */
    
    num_set(&kk1,m->c+matpos(k+1,k)); /*  xk+xk */
    num_set(&kk2,m->c+matpos(k,k+1)); /* -xk-xk */
    
    /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
    for (i=0;i<=k;i+=2) {
      num_set(buf1+i  ,m->c+matpos(k+1,i+1)); /* -xi+xk */
      num_set(buf2+i  ,m->c+matpos(k  ,i+1)); /* -xi-xk */
      num_set(buf1+i+1,m->c+matpos(k+1,i  )); /*  xi+xk */
      num_set(buf2+i+1,m->c+matpos(k  ,i  )); /*  xi-xk */
    }
    for (;i<n2;i+=2) {
      num_set(buf1+i  ,m->c+matpos(i  ,k  )); /*  xk-xi */
      num_set(buf2+i  ,m->c+matpos(i  ,k+1)); /* -xk-xi */
      num_set(buf1+i+1,m->c+matpos(i+1,k  )); /*  xk+xi */
      num_set(buf2+i+1,m->c+matpos(i+1,k+1)); /* -xk+xi */
    }
    
    for (i=0;i<n2;i++) {
      const var_t ii = i|1;
      num_add(&ik1,buf2+i,&kk1);        /* (-xk-xi) + ( xk+xk) */
      num_add(&ik2,buf1+i,&kk2);        /* ( xk-xi) + (-xk-xk) */
      for (j=0;j<=ii;j++,d++) {
	var_t jj = j^1;
	num_add(&ij1,buf1+i,buf2+jj); num_add(&ij2,&ik1,buf2+jj);
	num_add(&ij3,buf2+i,buf1+jj); num_add(&ij4,&ik2,buf1+jj);
	num_min(&ij1,&ij1,&ij2); num_min(&ij3,&ij3,&ij4);
	num_min(&ij1,&ij1,&ij3);
	num_min(d,d,&ij1);
      }	
    }
    
    /* S step */
    
    d = m->c;   /* xj-xi */
    /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
    
    for (i=0;i<n2;i+=2) {
      num_div_by_2(buf1+i,  m->c+matpos(i+1,i)); /* ( xi+xi)/2 */
      num_div_by_2(buf1+i+1,m->c+matpos(i,i+1)); /* (-xi-xi)/2 */
    }
    
    for (i=0;i<n2;i++) {
      const var_t ii  = i|1;
      const var_t ii2 = i^1;
      for (j=0;j<=ii;j++,d++) {
	num_add(&ij1,buf1+j,buf1+ii2);
	num_min(d,d,&ij1);
      }
    }
    
    /* emptyness checking */
    for (i=0;i<n2;i+=2)
      if (num_cmp_zero(m->c+matpos(i,i))<0) {
	m->state=OCT_EMPTY;
	num_clear_n(m->c,matsize(m->n));
	oct_mm_free(m->c); m->c = (num_t*)NULL;
	OCT_EXIT("oct_close_incremental_2",11);
	goto end;
      }
    
  }
  OCT_EXIT("oct_close_incremental_2",11);
  m->state = OCT_CLOSED;
 end:
  num_clear(&kk1); num_clear(&kk2);
  num_clear(&ik1); num_clear(&ik2);
  num_clear(&ij1); num_clear(&ij2); num_clear(&ij3); num_clear(&ij4);
  num_clear_n(buf1,n2); num_clear_n(buf2,n2);
  oct_mm_free(buf1); oct_mm_free(buf2);
 end2:
  OCT_EXIT("oct_close_incremental",9);
}

#else /* optimized algorithm from BHMZ05 (constant factor improvement) */


inline
void
OCT_PROTO(close_incremental) (oct_t* m,
			      var_t  v)
{
  var_t  i,j,k;
  const var_t n2 = m->n*2;
  const var_t v2 = v*2;
  num_t *c;
  num_t ij,ik,ik2;

  OCT_ENTER("oct_close_incremental",9);
  OCT_ASSERT(v<m->n,"variable index greater than the number of variables in oct_close_incremental");
  if (m->state==OCT_EMPTY) goto end2;

  num_init(&ik); num_init(&ik2); num_init(&ij);

  /* incremental Floyd-Warshall : v in end-point position */
  for (k=0;k<n2;k++) {
    const var_t kk = k^1;
    const var_t ii = v2|1;
    const var_t br  = k<ii ? k : ii;
    for (i=v2;i<v2+2;i++) {
      /* v in first end-point position */
      c = m->c+matpos(i,0);
      num_set(&ik,m->c+matpos2(i,k));
      num_set(&ik2,m->c+matpos2(i,kk));
      for (j=0;j<=br;j++,c++) {
	num_add(&ij,&ik,m->c+matpos(k,j));    /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,m->c+matpos(kk,j));  /* ik2+k2j */
	num_min(c,c,&ij);
      }
      for (;j<=ii;j++,c++) {
	num_add(&ij,&ik,m->c+matpos(j^1,kk)); /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,m->c+matpos(j^1,k)); /* ik2+k2j */
	num_min(c,c,&ij);
      }
      /* v in second end-point position */   
      num_set(&ik,m->c+matpos2(k,i));
      num_set(&ik2,m->c+matpos2(kk,i));
      for (j=i;j<k;j++) {
	c = m->c+matpos(j,i);
	num_add(&ij,&ik,m->c+matpos(kk,j^1)); /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,m->c+matpos(k,j^1)); /* ik2+k2j */
	num_min(c,c,&ij);
      }
      for (;j<n2;j++) {
	c = m->c+matpos(j,i);
	num_add(&ij,&ik,m->c+matpos(j,k));    /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,m->c+matpos(j,kk));  /* ik2+k2j */
	num_min(c,c,&ij);
      }
    }
  }
  
  /* incremental Floyd-Warshall : v in pivot position */
  for (k=v2;k<v2+2;k++) {
    const var_t kk = k^1;
    c = m->c;
    for (i=0;i<n2;i++) {
      const var_t ii = i|1;
      const var_t br = k<ii ? k : ii;
      num_set(&ik,m->c+matpos2(i,k));
      num_set(&ik2,m->c+matpos2(i,kk));
      for (j=0;j<=br;j++,c++) {
	num_add(&ij,&ik,m->c+matpos(k,j));    /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,m->c+matpos(kk,j));  /* ik2+k2j */
	num_min(c,c,&ij);
      }
      for (;j<=ii;j++,c++) {
	num_add(&ij,&ik,m->c+matpos(j^1,kk)); /* ik+kj */
	num_min(c,c,&ij);
	num_add(&ij,&ik2,m->c+matpos(j^1,k)); /* ik2+k2j */
	num_min(c,c,&ij);
      }
    } 
  }
  
  /* lone S step */
  c = m->c;
  for (i=0;i<n2;i++) {
    const var_t ii = i|1;
    num_div_by_2(&ij,m->c+matpos(i,i^1));
    for (j=0;j<=ii;j++,c++) {
      num_div_by_2(&ik,m->c+matpos(j^1,j));
      num_add(&ik,&ik,&ij);
      num_min(c,c,&ik);
    }
  }

  /* emptyness checking */
  for (i=0;i<n2;i++) {
    c = m->c+matpos(i,i);
    if (num_cmp_zero(c)<0) {
      m->state = OCT_EMPTY;
      num_clear_n(m->c,matsize(m->n));
      oct_mm_free(m->c); m->c = (num_t*)NULL;
      goto end;
    }
    else num_set_int(c,0);
  }

  m->state = OCT_CLOSED;
 end:
  num_clear(&ik); num_clear(&ik2); num_clear(&ij);
 end2:
  OCT_EXIT("oct_close_incremental",9);
}

#endif


/*********/
/* Tests */
/*********/

/* non-destructively computes the closure to check for emptiness
   calls oct_close with cache=true, so subsequent calls
   to oct_is_empty/oct_close will be very very fast
   cost: the cost of the close operator
*/
inline
bool
OCT_PROTO(is_empty) (oct_t* m)
{  
  oct_t* mm;
  bool r;
  OCT_ENTER("oct_is_empty",12); 
  mm = oct_close(m, false, true);
  r = (mm->state==OCT_EMPTY)?true:false;
  oct_free(mm);
  OCT_EXIT("oct_is_empty",12); 
  return r;
}

/* can return tbool_top if a call to close would be required to answer 
   null cost
 */
inline
tbool
OCT_PROTO(is_empty_lazy) (oct_t* m)
{
  tbool r;
  OCT_ENTER("oct_is_empty_lazy",13); 
  r = (m->state==OCT_EMPTY 
       || (m->closed && m->closed->state==OCT_EMPTY))?tbool_true:
    ((m->state==OCT_CLOSED || m->closed)?tbool_false:tbool_top);
   OCT_EXIT("oct_is_empty_lazy",13); 
  return r;
}

/* calls oct_close with cache=true 
   O(n^2) time cost, on behalf of the cost of closure
 */
bool
OCT_PROTO(is_included_in) (oct_t* ma, 
			   oct_t* mb)
{
  bool r;
  OCT_ENTER("oct_is_included_in",14);
  OCT_ASSERT(ma->n==mb->n,"oct_is_included_in must be called with two octagons of the same dimension.");
  if (ma==mb) r = true;
  else {
    oct_t *ca = oct_close(ma, false, true);
    if (ca->state==OCT_EMPTY) r = true;
    else if (oct_is_empty_lazy(mb)==tbool_true) r = false;
    else {
      const size_t nn = matsize(ma->n);
      size_t i;
      num_t* a = ca->c;
      num_t* b = mb->c;
      r = true;
      for (i=0;i<nn;i++,a++,b++)
	if (num_cmp(a,b)>0) { r=false; break; }
    }
    oct_free(ca);
  }
  OCT_EXIT("oct_is_included_in",14);
  return r;
}

/* can return tbool_top if a call to close would be required to answer 
   O(n^2) time cost
*/
tbool
OCT_PROTO(is_included_in_lazy) (oct_t* ma, 
				oct_t* mb)
{
  tbool r;
  OCT_ENTER("oct_is_included_in_lazy",15);
  OCT_ASSERT(ma->n==mb->n,"oct_is_included_in_lazy must be called with two octagons of the same dimension.");
  if (ma==mb) r = tbool_true;
  else {
    oct_t *ca = oct_close_lazy (ma, false);
    if (ca->state==OCT_EMPTY) r = tbool_true;
    else if (mb->state==OCT_EMPTY) r = tbool_false;
    else {
      const size_t nn = matsize(ma->n);
      size_t i;
      num_t* a = ca->c;
      num_t* b = mb->c;
      
      r = tbool_true;
      for (i=0;i<nn;i++,a++,b++)
	if (num_cmp(a,b)>0) { r=tbool_false; break; }
    }
    if (r==tbool_false && !oct_is_closed(ca)) r = tbool_top;
    oct_free(ca);
  }
  OCT_EXIT("oct_is_included_in_lazy",15);
  return r;
}

/* calls oct_close with cache=true 
   O(n^2) time cost, on behalf of the cost of closure
 */
bool
OCT_PROTO(is_equal) (oct_t* ma, 
		     oct_t* mb)
{
  bool r;
  OCT_ENTER("oct_is_equal",16);
  OCT_ASSERT(ma->n==mb->n,"oct_is_equal must be called with two octagons of the same dimension.");
  if (ma==mb) r = true; 
  else {
    oct_t *ca = oct_close(ma, false, true);
    oct_t *cb = oct_close(mb, false, true);
    if (ca->state==OCT_EMPTY && cb->state==OCT_EMPTY) r = true;
    else if (ca->state==OCT_EMPTY || cb->state==OCT_EMPTY) r = false;
    else {
      const size_t nn = matsize(ma->n);
      size_t i;
      num_t* a = ca->c;
      num_t* b = cb->c;
      r = true;
      for (i=0;i<nn;i++,a++,b++)
	if (num_cmp(a,b)) { r=false; break; }
    }
    oct_free(ca);
    oct_free(cb);
  }
  OCT_EXIT("oct_is_equal",16);
  return r;
}

/* can return tbool_top if a call to close would be required to answer 
   O(n^2) time cost
*/
tbool
OCT_PROTO(is_equal_lazy)(oct_t* ma, 
			 oct_t* mb)
{
  tbool r;
  OCT_ENTER("oct_is_equal_lazy",17);
  OCT_ASSERT(ma->n==mb->n,"oct_is_equal_lazy must be called with two octagons of the same dimension.");
  if (ma==mb) r = tbool_true;
  else {
    oct_t *ca = oct_close_lazy (ma, false);
    oct_t *cb = oct_close_lazy (mb, false);
    if (ca->state==OCT_EMPTY && cb->state==OCT_EMPTY) r = tbool_true;
    else  if (ca->state==OCT_EMPTY || cb->state==OCT_EMPTY) r = tbool_false;
    else {
      const size_t nn = matsize(ma->n);
      size_t i;
      num_t* a = ca->c;
      num_t* b = cb->c;
      
      r = tbool_true;
      for (i=0;i<nn;i++,a++,b++)
	if (num_cmp(a,b)) { r = tbool_false; break; }
    }
    if (r==tbool_false && 
	(!oct_is_closed(ca) || !oct_is_closed(ca))) r = tbool_top;
    oct_free(ca);
    oct_free(cb);
  }
  OCT_EXIT("oct_is_equal_lazy",17);
  return r;
}

/* return true if v is in the domain of a, false elsewhere 
   O(n^2) time cost
*/
bool
OCT_PROTO(is_in) (oct_t*       a,
		  const num_t* v)
{
  bool r = true;
  var_t i,j;
  num_t w;
  OCT_ENTER("oct_is_in",18);
  if (oct_is_empty_lazy(a)==tbool_true) { r = false; goto end2; }
  num_init(&w);
  for (i=0;i<a->n;i++) 
    for (j=0;j<=i;j++) {
      num_add(&w,v+i,a->c+matpos(2*i,2*j));
      if (num_cmp(v+j,&w)>0) { r = false; goto end; }

      num_add(&w,v+j,a->c+matpos(2*i+1,2*j+1));
      if (num_cmp(v+i,&w)>0){ r = false; goto end; }

      num_add(&w,v+i,v+j);
      if (num_cmp(&w,a->c+matpos(2*i+1,2*j))>0)	{ r = false; goto end; }

      num_add(&w,v+i,v+j); num_add(&w,&w,a->c+matpos(2*i,2*j+1));
      if (num_cmp_zero(&w)<0) { r = false; goto end; }
    }
 end:
  num_clear(&w);
 end2:
  OCT_EXIT("oct_is_in",18);
  return r;
}

/* return true if the octagon has a full domain
   O(n^2) time cost
*/
bool
OCT_PROTO(is_universe) (oct_t* m)
{
  bool r = true;
  const var_t n2 = m->n*2;
  var_t i,j;
  num_t* c = m->c;
  OCT_ENTER("oct_is_universe",19);
  if (m->state==OCT_EMPTY) { r = false; goto end; }
  for (i=0;i<n2;i++) {
    const var_t ii = i|1;
    for (j=0;j<=ii;j++,c++)
      if (!num_infty(c) && i!=j) 
	{ r = false; goto end; }
  }
 end:
  OCT_EXIT("oct_is_universe",19);
  return r;
}

/*************/
/* Operators */
/*************/

/* exact intersection 
   O(n^2) time cost
*/
oct_t*
OCT_PROTO(intersection) (oct_t* ma, 
			 oct_t* mb, 
			 bool   destructive)
{
  oct_t* r;
  OCT_ENTER("oct_intersection",20);
  OCT_ASSERT(ma->n==mb->n,"oct_intersection must be called with two octagons of the same dimension.");
  if (ma==mb) r = oct_copy(ma);
  /* ma empty => intersection equals ma */
  else if (oct_is_empty_lazy(ma)==tbool_true) r = oct_copy(ma);
  /* mb empty => intersection equals mb */
  else if (oct_is_empty_lazy(mb)==tbool_true) r = oct_copy(mb);
  else {
    const size_t nn = matsize(ma->n);
    size_t i;
    num_t* a = ma->c;
    num_t* b = mb->c;
    num_t* c;
    /* result is computed in ma, or mb, or a new octagon */  
    if (destructive) { 
      if (ma->ref==1) r = oct_copy(ma);
      else if (mb->ref==1) r = oct_copy(mb);
      else r = oct_alloc(ma->n);
    }
    else r = oct_alloc(ma->n);
    r->state = OCT_NORMAL;
    if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
    /* change the result matrix */
    c = r->c;
    for (i=0;i<nn;i++,a++,b++,c++) num_min(c,a,b);
  }
  if (destructive) { oct_free(ma); oct_free(mb); }
  OCT_EXIT("oct_intersection",20);
  return r;
}

/* best apprixomation of the union 
   both arguments are closed (but with cache=false)    
   O(n^2) time cost, on behalf of the cost of closure
*/
oct_t*
OCT_PROTO(convex_hull) (oct_t* ma, 
			oct_t* mb, 
			bool   destructive)
{
  oct_t* r;
  OCT_ENTER("oct_convex_hull",21);
  OCT_ASSERT(ma->n==mb->n,"oct_convex_hull must be called with two octagons of the same dimension.");
  if (ma==mb) { 
    if (destructive) { r = ma; oct_free(ma); }
    else r = oct_copy(ma);
  }
  else {
    oct_t* ca = oct_close(ma, destructive, true);
    oct_t* cb = oct_close(mb, destructive, true);
    /* ca empty => hull equals cb */
    if (ca->state==OCT_EMPTY) r = oct_copy(cb);
    /* cb empty => hull equals ca */
    else if (cb->state==OCT_EMPTY) r = oct_copy(ca);
    else {
      const size_t nn = matsize(ca->n);
      size_t i;
      num_t* a = ca->c;
      num_t* b = cb->c;
      num_t* c;
      /* result is computed in ca, or cb, or a new octagon */  
      if (destructive) { 
	if (ca->ref==1) r = oct_copy(ca);
	else if (cb->ref==1) r = oct_copy(cb);
	else r = oct_alloc(ca->n);
      }
      else r = oct_alloc(ca->n);
      r->state = OCT_CLOSED;
      /* change the result matrix */
      c = r->c;
      for (i=0;i<nn;i++,a++,b++,c++) num_max(c,a,b);
    }
    oct_free(ca);
    oct_free(cb);
  }
  OCT_EXIT("oct_convex_hull",21);
  return r;
}

/* convergence acceleration operator: jump to a post fixpoint after finite
   iteration
   right argument is closed (but with cache=false)  
   O(n^2) time cost, on behalf of the cost of closure
*/
oct_t*
OCT_PROTO(widening) (oct_t*            ma, 
		     oct_t*            mb, 
		     bool              destructive,
		     oct_widening_type type)
{
  oct_t* r;
  OCT_ENTER("oct_widening",22);
  OCT_ASSERT(ma->n==mb->n,"oct_widening must be called with two octagons of the same dimension.");
  if (ma==mb) { 
    if (destructive) { r = ma; oct_free(ma); }
    else r = oct_copy(ma);
  }
  /* ma empty => widening equals cb */
  else if (oct_is_empty_lazy(ma)==tbool_true) {
    if (destructive) { r = mb; oct_free(ma); }
    else r = oct_copy(mb);
  }
  else {
    oct_t* cb = oct_close(mb, destructive, true);
    /* cb empty => widening equals ma */
    if (cb->state==OCT_EMPTY) r = oct_copy(ma);
    else {
      const size_t nn = matsize(ma->n);
      size_t i;
      num_t* a = ma->c;
      num_t* b = cb->c;
      num_t* c;
      /* result is computed in ma, or cb, or a new octagon */  
      if (destructive) { 
	if (ma->ref==1) r = oct_copy(ma);
	else if (cb->ref==1) r = oct_copy(cb);
	else r = oct_alloc(ma->n);
      }
      else r = oct_alloc(ma->n);
      r->state = OCT_NORMAL;
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
      /* change the result matrix */
      c = r->c;
      switch (type) {
	
	/* 0, +oo */
      case OCT_WIDENING_ZERO:
	for (i=0;i<nn;i++,a++,b++,c++)
	  if (num_cmp(b,a)<=0) num_set(c,a); 
	  else if (num_cmp_zero(b)<=0) num_set_int(c,0);
	  else num_set_infty(c);
	break;
	
	/* -1, 0, 1, +oo */
      case OCT_WIDENING_UNIT:
	for (i=0;i<nn;i++,a++,b++,c++)
	  if (num_cmp(b,a)<=0) num_set(c,a); 
	  else if (num_cmp_int(b,-1)<=0) num_set_int(c,-1);
	  else if (num_cmp_zero(b)  <=0) num_set_int(c, 0);
	  else if (num_cmp_int(b, 1)<=0) num_set_int(c, 1);
	  else num_set_infty(c);
	break;
	
	/* degenerate hull: NOT A PROPER WIDENING, use with care */
      case OCT_PRE_WIDENING:
        for (i=0;i<nn;i++,a++,b++,c++)
          num_max(c,a,b);
        break;

	/* +oo */
      case OCT_WIDENING_FAST:
      default:
	for (i=0;i<nn;i++,a++,b++,c++)
	  if (num_cmp(b,a)<=0) num_set(c,a); else num_set_infty(c);
	break;
      }
    }
    if (destructive) oct_free(ma);
    oct_free(cb);
  }
  OCT_EXIT("oct_widening",22);
  return r;
}

/* this widening takes as an argument an array (in increasing order) of
   thresholds
   right argument is closed (but with cache=false)  
   O(n^2) time cost, on behalf of the cost of closure
*/
oct_t*
OCT_PROTO(widening_steps) (oct_t*            ma, 
			   oct_t*            mb, 
			   bool              destructive,
			   int               nb_steps,
			   num_t*            steps)
{
  oct_t* r;
  OCT_ENTER("oct_widening_steps",47);
  OCT_ASSERT(ma->n==mb->n,"oct_widening_steps must be called with two octagons of the same dimension.");
  if (ma==mb) { 
    if (destructive) { r = ma; oct_free(ma); }
    else r = oct_copy(ma);
  }
  /* ma empty => widening equals cb */
  else if (oct_is_empty_lazy(ma)==tbool_true) {
    if (destructive) { r = mb; oct_free(ma); }
    else r = oct_copy(mb);
  }
  else {
    oct_t* cb = oct_close(mb, destructive, true);
    /* cb empty => widening equals ma */
    if (cb->state==OCT_EMPTY) r = oct_copy(ma);
    else {
      const size_t nn = matsize(ma->n);
      size_t i;
      int j;
      num_t* a = ma->c;
      num_t* b = cb->c;
      num_t* c;
      /* result is computed in ma, or cb, or a new octagon */  
      if (destructive) { 
	if (ma->ref==1) r = oct_copy(ma);
	else if (cb->ref==1) r = oct_copy(cb);
	else r = oct_alloc(ma->n);
      }
      else r = oct_alloc(ma->n);
      r->state = OCT_NORMAL;
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
      /* change the result matrix */
      c = r->c;
      for (i=0;i<nn;i++,a++,b++,c++)
	if (num_cmp(b,a)<=0) num_set(c,a); 
	else {
	  num_set_infty(c);
	  for (j=0;j<nb_steps;j++)
	    if (num_cmp(b,steps+j)<=0) { num_set(c,steps+j); break; }
	}
    }
    if (destructive) oct_free(ma);
    oct_free(cb);
  }
  OCT_EXIT("oct_widening_steps",47);
  return r;
}


/* information restoration operator: stay above least fixpoint
   right argument is closed (but with cache=false)  
   O(n^2) time cost, on behalf of the cost of closure
*/
oct_t*
OCT_PROTO(narrowing) (oct_t* ma, 
		      oct_t* mb, 
		      bool   destructive)
{
  oct_t* r;
  OCT_ENTER("oct_narrowing",23);
  OCT_ASSERT(ma->n==mb->n,"oct_narrowing must be called with two octagons of the same dimension.");
  if (ma==mb) { 
    if (destructive) { r = ma; oct_free(ma); }
    else r = oct_copy(ma);
  }
  else {
    oct_t* ca = oct_close(ma, destructive, true);
    oct_t* cb = oct_close(mb, destructive, true);
    /* ca empty => narrowing equals cb */
    if (ca->state==OCT_EMPTY) r = oct_copy(cb);
    /* cb empty => narrowing equals ca */
    else if (cb->state==OCT_EMPTY) r = oct_copy(ca);
    else {
      const size_t nn = matsize(ca->n);
      size_t i;
      num_t* a = ca->c;
      num_t* b = cb->c;
      num_t* c;
      /* result is computed in ca, or cb, or a new octagon */  
      if (destructive) { 
	if (ca->ref==1) r = oct_copy(ca);
	else if (cb->ref==1) r = oct_copy(cb);
	else r = oct_alloc(ca->n);
      }
      else r = oct_alloc(ca->n);
      r->state = OCT_NORMAL; 
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }

      /* change the result matrix */
      c = r->c;
      for (i=0;i<nn;i++,a++,b++,c++)
	if (num_infty(a)) num_set(c,b); else num_set(c,a);
    }
    oct_free(ca);
    oct_free(cb);
  }
  OCT_EXIT("oct_narrowing",23);
  return r;
}


/**********************/
/* Transfer Functions */
/**********************/

/* forget all informations about the variable k 
   O(n) time cost, on behalf of the cost of closure and copy
   if the result is not empty, it is always a newly allocated matrix
   that can be safely modified in-place
*/
inline
oct_t*
OCT_PROTO(forget) (oct_t* m, 
		   var_t  k,
		   bool   destructive)
{
  oct_t *mm;
  oct_t* r;
  const var_t k2 = 2*k;
  const var_t n2 = 2*m->n;
  var_t i;
  OCT_ENTER("oct_forget",24);
  mm = oct_close(m, destructive, true);
  OCT_ASSERT(k<mm->n,"variable index greater than the number of variables in oct_forget");
  /* mm empty => return mm */
  if (mm->state==OCT_EMPTY) { r = mm; goto end; }
  /* result is computed in mm, or in a new octagon */
  if (mm->ref==1) r = mm;
  else { r = oct_full_copy(mm); mm->ref--; }
  /* change the result matrix */
  for (i=0;i<k2;i++) {
    /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
    num_set_infty(r->c+matpos(k2  ,i));
    num_set_infty(r->c+matpos(k2+1,i));
  }
  for (i=k2+2;i<n2;i++) {
    /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
    num_set_infty(r->c+matpos(i,k2  ));
    num_set_infty(r->c+matpos(i,k2+1));
  }
  num_set_infty(r->c+matpos(k2,k2+1));
  num_set_infty(r->c+matpos(k2+1,k2));
 end:
  OCT_EXIT("oct_forget",24); 
  return r;
}


/* intersects the domain with constraints of the form 
   x<=c, -x<=c, x-y<=c, +x+y<=c or -x-y<=c
   if the result is not empty, it is always a newly allocated matrix
   that can be safely modified in-place
   O(nb) time cost
*/
inline
oct_t*
OCT_PROTO(add_bin_constraints) (oct_t*           m,
				unsigned int     nb,
				const oct_cons*  cons,
				bool             destructive)
{
  oct_t* r;
  unsigned int k;
  num_t c;
  var_t changed = 0; // zra = 0
  int nb_changed = 0;
  OCT_ENTER("oct_add_bin_constraints",25);
  /* m empty => return m */
  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end2; }
    else { r = oct_copy(m); goto end2; }
  } // zra braces
  /* result is computed in m, or in a new octagon */
  if (destructive) {
    if (m->ref==1) r = m;
    else { r = oct_full_copy(m); m->ref--; }
  }
  else r = oct_full_copy(m);
  /* change the result matrix */
  num_init(&c);
  for (k=0;k<nb;k++) {
    var_t i,j;
    OCT_ASSERT(cons[k].x<m->n,"variable index greater than the number of variables in oct_add_constraints");
    OCT_ASSERT(cons[k].type==mx || cons[k].type==px || cons[k].y<m->n,"variable index greater than the number of variables in oct_add_constraints");
    switch (cons[k].type) {
    case mx:   
      j=2*cons[k].x+1; i=2*cons[k].x;   num_mul_by_2(&c,&cons[k].c); 
      if (num_cmp(&c,r->c+matpos2(i,j))<0) {
	num_set(r->c+matpos2(i,j),&c);
	if (nb_changed==0 ) { nb_changed=1; changed=cons[k].x; }
	else if (changed!=cons[k].x) nb_changed++;
      }
      break;

    case px:   
      j=2*cons[k].x;   i=2*cons[k].x+1; num_mul_by_2(&c,&cons[k].c); 
      if (num_cmp(&c,r->c+matpos2(i,j))<0) {
	num_set(r->c+matpos2(i,j),&c);
	if (nb_changed==0 ) { nb_changed=1; changed=cons[k].x; }
	else if (changed!=cons[k].x) nb_changed++;
      }
      break;

    case mxmy: 
      j=2*cons[k].x+1; i=2*cons[k].y;   num_set(&c,&cons[k].c); 
      if (num_cmp(&c,r->c+matpos2(i,j))<0) {
	num_set(r->c+matpos2(i,j),&c);
	if (nb_changed==0 ) { nb_changed=1; changed=cons[k].x; }
	else if (changed!=cons[k].x && changed!=cons[k].y) nb_changed++;
      }
      break;

    case mxpy: 
      j=2*cons[k].x+1; i=2*cons[k].y+1; num_set(&c,&cons[k].c);
      if (num_cmp(&c,r->c+matpos2(i,j))<0) {
	num_set(r->c+matpos2(i,j),&c);
	if (nb_changed==0 ) { nb_changed=1; changed=cons[k].x; }
	else if (changed!=cons[k].x && changed!=cons[k].y) nb_changed++;
      }
      break;

    case pxmy: 
      j=2*cons[k].x;   i=2*cons[k].y;   num_set(&c,&cons[k].c);
      if (num_cmp(&c,r->c+matpos2(i,j))<0) {
	num_set(r->c+matpos2(i,j),&c);
	if (nb_changed==0 ) { nb_changed=1; changed=cons[k].x; }
	else if (changed!=cons[k].x && changed!=cons[k].y) nb_changed++;
      }
      break;

    case pxpy: 
      j=2*cons[k].x;   i=2*cons[k].y+1; num_set(&c,&cons[k].c);
      if (num_cmp(&c,r->c+matpos2(i,j))<0) {
	num_set(r->c+matpos2(i,j),&c);
	if (nb_changed==0 ) { nb_changed=1; changed=cons[k].x; }
	else if (changed!=cons[k].x && changed!=cons[k].y) nb_changed++;
      }
      break;

    default: 
      OCT_ASSERT(false,"invalid constraint type in oct_add_constraints");
    }
  }
  if (nb_changed==1 && r->state==OCT_CLOSED) oct_close_incremental(r,changed);
  else if (nb_changed>0) {
    r->state = OCT_NORMAL;
    if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
  }
  num_clear(&c);
 end2:
  OCT_EXIT("oct_add_bin_constraints",25);
  return r;
}



/* transfer funciton modeling forward semantics of assignment x <- e
   e = tab[0]v0 + tab[1]v1 + ... + tab[N-1]v(N-1) + tab[N]
   the operation is exact for assignments of the form
      x <-  c
      x <-  x + c
      x <- -x + c
      x <-  y + c (x!=y)
      x <- -y + c (x!=y)

   for other assignments x <- e, leads to the constraints m <= x <= M, where
   m and M are computed using a simple interval arithmetic on e
   if the coefficient of y in e is >= 1, then bounds for x-y are also derived
   if the coefficient of y in e is <=-1, then bounds for x+y are also derived

   if the result is not empty, it is always a newly allocated matrix
   that can be safely modified in-place

   often need to close its argument
   returns a closed result whenever possible
 */
oct_t*
OCT_PROTO(assign_variable) (oct_t*       m,
			    var_t        x,
			    const num_t* tab,
			    bool         destructive)
{
  oct_t* r;
  var_t  i, y = 0, N = 0;
  const var_t n  = m->n;
  const var_t n2 = n*2;
  const var_t x2 = 2*x;
  const num_t* c = tab+n;
  OCT_ENTER("oct_assign_variable",26);
  OCT_ASSERT(x<m->n,"variable index greater than the number of variables in oct_assign_variable");

  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  if (num_infty(c)) { r = oct_forget (m, x, destructive); goto end; }
  for (i=0;i<n;i++)
    if (num_infty(tab+i)) { r = oct_forget (m, x, destructive); goto end; }
    else if (num_cmp_zero(tab+i)) { y=i; N++; }

  if (N==0) { /* x <- c */
    r = oct_forget (m, x, destructive);
    if (r->state==OCT_EMPTY) goto end;
    num_mul_by_2(r->c+matpos(x2+1,x2),c);
    num_neg(r->c+matpos(x2,x2+1),r->c+matpos(x2+1,x2));
    /* the following is only here to ensure matrix closedness
       with a O(n) cost; does it worth it ? */
    for (i=0;i<x2;i++) {
      /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
      num_t* i1 = r->c+matpos(x2,i);
      num_t* i2 = r->c+matpos(x2+1,i);
      const num_t* i3 = r->c+matpos(i^1,i);
      num_div_by_2(i1,i3); num_sub(i1,i1,c);
      num_div_by_2(i2,i3); num_add(i2,i2,c);
    }
    for (i=x2+2;i<n2;i++) {
      /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
      num_t* i1 = r->c+matpos(i,x2);
      num_t* i2 = r->c+matpos(i,x2+1);
      const num_t* i3 = r->c+matpos(i,i^1);
      num_div_by_2(i1,i3); num_add(i1,i1,c);
      num_div_by_2(i2,i3); num_sub(i2,i2,c);
    }
  }

  else if (N==1 && (!num_cmp_int(tab+y,1) || !num_cmp_int(tab+y,-1)))
    /* x <- +/- y + c */

    if (y!=x) { /* x <- +/- y + c, x!=y */
      r = oct_forget (m, x, destructive);
      if (r->state==OCT_EMPTY) goto end;
      if (!num_cmp_int(tab+y,1)) {          /* x <- y + c,   y!=x */
	num_set(r->c+matpos2(2*y,x2),c);
	num_neg(r->c+matpos2(x2,2*y),c);
      }
      else {                                /* x <- -y + c,  y!=x */
	num_set(r->c+matpos2(2*y+1,x2),c);
	num_neg(r->c+matpos2(x2,2*y+1),c);
      }
      oct_close_incremental(r,x);
    }

    else {  /* x <- +/- x + c; respects closure */

      m = oct_close_lazy(m,destructive);
      if (m->ref==1) r = m;
      else { r = oct_full_copy(m); m->ref--; }
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }

      /* modify the result matrix */
      if (!num_cmp_int(tab+x,-1)) { /* x <- -x + c */
	num_t w,ww;
	num_init(&w); num_init(&ww);
	num_mul_by_2(&ww,c);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_set(&w,xi);
	  num_sub(xi,ix,c);
	  num_add(ix,&w,c);
	}
	num_set(&w,r->c+matpos(x2,x2+1));
	num_sub(r->c+matpos(x2,x2+1),r->c+matpos(x2+1,x2),&ww);
	num_add(r->c+matpos(x2+1,x2),&w                  ,&ww);
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_set(&w,xi);
	  num_sub(xi,ix,c);
	  num_add(ix,&w,c);
	}
	num_clear(&w); num_clear(&ww);
      } 
      else {                         /* x <- x + c */
	num_t ww;
	num_init(&ww);
	num_mul_by_2(&ww,c);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_sub(xi,xi,c);
	  num_add(ix,ix,c);
	}
	num_add(r->c+matpos(x2+1,x2),r->c+matpos(x2+1,x2),&ww);
	num_sub(r->c+matpos(x2,x2+1),r->c+matpos(x2,x2+1),&ww);
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_sub(xi,xi,c);
	  num_add(ix,ix,c);
	}
	num_clear(&ww);
      }
    }

  else { /* general case */
    var_t j;
    num_t* buf;              /* bounds for each variable */
    num_t Cb,cb;             /* global upper / lower bounds */
    int   Cinf, cinf;        /* number of infinite coef in up/lw bounds */
    var_t Ci = 0, ci = 0;            /* var leading to infinite coef in up/lw bounds */
    num_t w;
    int changed = 0;
    r = oct_close (m,destructive,false);
    if (r->state==OCT_EMPTY) goto end;
    buf = new_n(num_t,n2);
    num_init(&Cb); num_init(&cb); num_init(&w);
    num_mul_by_2(&Cb,c); num_neg(&cb,&Cb);
    Cinf = cinf = 0;
    for (i=0,j=0;i<n2;i+=2,j++) { 
      /* get variable bounds, ignoring components leading to +oo */
      num_t* px = r->c+matpos(i+1,i); /*  xj+xj */
      num_t* mx = r->c+matpos(i,i+1); /* -xj-xj */
      num_init_set(buf+i  ,px);
      num_init_set(buf+i+1,mx);
      if (num_cmp_zero(tab+j)>0) {
	if (num_infty(px)) { Cinf++; Ci = j; }
	else { num_mul(&w,tab+j,px); num_add(&Cb,&Cb,&w); }
	if (num_infty(mx)) { cinf++; ci = j; }
	else { num_mul(&w,tab+j,mx); num_add(&cb,&cb,&w); }
      }
      else if (num_cmp_zero(tab+j)<0) {
	if (num_infty(mx)) { Cinf++; Ci = j; }
	else { num_neg(&w,tab+j); num_mul(&w,&w,mx); num_add(&Cb,&Cb,&w); }
	if (num_infty(px)) { cinf++; ci = j; }
	else { num_neg(&w,tab+j); num_mul(&w,&w,px); num_add(&cb,&cb,&w); }
      }
    }
    r = oct_forget (r,x,true);
    /* upper bounds */
    switch (Cinf) {
    case 0:
      /* bound is not infinite */
      num_set(r->c+matpos(x2+1,x2),&Cb);        /* bound for x */
      for (i=0;i<n;i++)
      	if (i!=x) {
      	  if (num_cmp_int(tab+i,1)>=0 && !num_infty(buf+2*i)) {        
	    /* bound for x-y */
	    num_sub(&w,&Cb,buf+2*i);
	    num_div_by_2(r->c+matpos2(2*i,  x2),&w);
	  }
      	  else if (num_cmp_int(tab+i,-1)<=0 && !num_infty(buf+2*i+1)) {  
	    /* bound for x+y */
	    num_sub(&w,&Cb,buf+2*i+1);
	    num_div_by_2(r->c+matpos2(2*i+1,x2),&w);
	  }      
	}
      changed = 1;
      break;
    case 1:
      /* bound has only one infinite coef, for var y of index Ci =>
	 we may still have a finite bound for x-y, or x+y            */
      if (Ci!=x) {
      	if (!num_cmp_int(tab+Ci,1)) num_div_by_2(r->c+matpos2(Ci*2  ,x2),&Cb);
      	else if (!num_cmp_int(tab+Ci,-1)) num_div_by_2(r->c+matpos2(Ci*2+1,x2),&Cb);
      }
      changed = 1;
      break;
    }
    /* lower bounds */
    switch (cinf) {
    case 0:
      /* bound is not infinite */
      num_set(r->c+matpos(x2,x2+1),&cb);        /* bound for -x */
      for (i=0;i<n;i++)
	if (i!=x) {
      	  if (num_cmp_int(tab+i,1)>=0 && !num_infty(buf+2*i+1)) {        
	    /* bound for -x+y */
	    num_sub(&w,&cb,buf+2*i+1);
	    num_div_by_2(r->c+matpos2(2*i+1,x2+1),&w);
	  }
      	  else if (num_cmp_int(tab+i,-1)<=0 && !num_infty(buf+2*i)) {  
	    /* bound for -x-y */
	    num_sub(&w,&cb,buf+2*i);
	    num_div_by_2(r->c+matpos2(2*i,  x2+1),&w);
	  }
	}
      changed = 1;
      break;
    case 1:
      /* bound has only one infinite coef, for var y of index ci =>
	 we may still have a finite bound for -x+y, or -x-y            */
      if (ci!=x) {
	if (!num_cmp_int(tab+ci,1)) num_div_by_2(r->c+matpos2(x2,ci*2  ),&cb);
      	else if (!num_cmp_int(tab+ci,-1)) num_div_by_2(r->c+matpos2(x2,ci*2+1),&cb);
      }
      changed = 1;
      break;
    }
    num_clear_n(buf,n2);  oct_mm_free (buf);
    num_clear(&cb); num_clear(&Cb); num_clear(&w);
    if (changed) oct_close_incremental(r,x);
  } 
 end:
  OCT_EXIT("oct_assign_variable",26);
  return r;  
}



/* transfer function modeling backward semantics of assignment x -> e
   e = tab[0]v0 + tab[1]v1 + ... + tab[N-1]v(N-1) + tab[N]
   the operation is exact for assignments of the form
      x ->  c
      x ->  x + c
      x -> -x + c
      x ->  y + c (x!=y)
      x -> -y + c (x!=y)
   for other assignments, this call is equivalent to oct_forget!
   THE GENERAL CASE COULD BE IMPROVED

   if the result is not empty, it is always a newly allocated matrix
   that can be safely modified in-place

   often need to close its argument
   returns a closed result whenever possible
 */
oct_t*
OCT_PROTO(substitute_variable) (oct_t*       m,
				var_t        x,
				const num_t* tab,
				bool         destructive)
{
  oct_t* r;
  var_t  i, y = 0, N = 0;
  const var_t n2 = m->n*2;
  const var_t x2 = 2*x;
  const num_t* c = tab+m->n;
  OCT_ENTER("oct_substitute_variable",27);
  OCT_ASSERT(x<m->n,"variable index greater than the number of variables in oct_substitute_variable");

  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  if (num_infty(c)) { r = oct_forget (m, x, destructive); goto end; }
  for (i=0;i<m->n;i++)
    if (num_infty(tab+i)) { r = oct_forget (m, x, destructive); goto end; }
    else if (num_cmp_zero(tab+i)) { y=i; N++; }

  if (N==0) { /* x -> c */
    oct_t* mm;
    num_t w1,w2;
    mm = oct_close (m,destructive,false);
    num_init(&w1); num_init(&w2);
    /* result is empty */
    if (mm->state==OCT_EMPTY) { r = mm; goto end0; }
    num_mul_by_2(&w1,c);
    num_neg(&w2,&w1);
    if (num_cmp(&w1,mm->c+matpos(x2+1,x2))>0 ||
        num_cmp(&w2,mm->c+matpos(x2,x2+1))>0) 
      { r = oct_empty(mm->n); oct_free(mm); goto end0; }
    /* result is computed in mm, or in a new octagon */
    if (mm->ref==1) r = mm;
    else { r = oct_full_copy(mm); mm->ref--; }
    r->state = OCT_NORMAL;     
    if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }

    /* change the result matrix */
    for (i=0;i<x2;i++) {
      /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
      num_t* xi = r->c+matpos(x2  ,i);
      num_t* ix = r->c+matpos(x2+1,i);
      num_t* ii = r->c+matpos(i^1,i);
      num_add(&w1,xi,c);
      num_sub(&w2,ix,c);
      num_min(&w1,&w1,&w2);
      num_mul_by_2(&w1,&w1);
      num_min(ii,ii,&w1);
      num_set_infty(xi);
      num_set_infty(ix);
    }
    for (i=x2+2;i<n2;i++) {
      /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
      num_t* xi = r->c+matpos(i,x2+1);
      num_t* ix = r->c+matpos(i,x2  );
      num_t* ii = r->c+matpos(i,i^1);
      num_add(&w1,xi,c);
      num_sub(&w2,ix,c);
      num_min(&w1,&w1,&w2);
      num_mul_by_2(&w1,&w1);
      num_min(ii,ii,&w1);
      num_set_infty(xi);
      num_set_infty(ix);
    }
    num_set_infty(r->c+matpos(x2,x2+1));
    num_set_infty(r->c+matpos(x2+1,x2));
  end0:
    num_clear(&w1); num_clear(&w2);
  }

  else if (N==1 && (!num_cmp_int(tab+y,1) || !num_cmp_int(tab+y,-1)))
    if (y!=x) {  /* x -> +/- y + c, x!=y */
      var_t yy, yy1;
      oct_t* mm;
      num_t w;
      num_init(&w);
      mm = oct_close (m,destructive,false);
      if (!num_cmp_int(tab+y,-1)) yy = 2*y+1; else yy = 2*y;
      yy1 = yy^1;
      /* result is empty */
      if (mm->state==OCT_EMPTY) { r = mm; goto end1; }
      num_neg(&w,c);
      if (num_cmp(c ,mm->c+matpos2(yy,x2))>0 ||
	  num_cmp(&w,mm->c+matpos2(x2,yy))>0)
	{ r = oct_empty(mm->n); oct_free(mm); goto end1; }
      /* result is computed in mm, or in a new octagon */
      if (mm->ref==1) r = mm;
      else { r = oct_full_copy(mm); mm->ref--; }
      /* change the result matrix */
      for (i=0;i<x2;i++) {
	/* TO BE LINEARIZED */
	num_t* xi = r->c+matpos(x2  ,i);
	num_t* ix = r->c+matpos(x2+1,i);
	num_t* yi = r->c+matpos2(yy ,i);
	num_t* iy = r->c+matpos2(yy1,i);
	num_add(xi,xi,c); num_min(yi,yi,xi); num_set_infty(xi);
	num_sub(ix,ix,c); num_min(iy,iy,ix); num_set_infty(ix);
      }
      for (i=x2+2;i<n2;i++) {
	/* TO BE LINEARIZED */
	num_t* xi = r->c+matpos(i,x2+1);
	num_t* ix = r->c+matpos(i,x2  );
	num_t* yi = r->c+matpos2(i,yy1);
	num_t* iy = r->c+matpos2(i,yy );
	num_add(xi,xi,c); num_min(yi,yi,xi); num_set_infty(xi);
	num_sub(ix,ix,c); num_min(iy,iy,ix); num_set_infty(ix);
      }
      {
	num_t* xi = r->c+matpos(x2  ,x2+1);
	num_t* ix = r->c+matpos(x2+1,x2  );
	num_t* yi = r->c+matpos2(yy ,yy1);
	num_t* iy = r->c+matpos2(yy1,yy );
	num_mul_by_2(&w,c);
	num_add(xi,xi,&w); num_min(yi,yi,xi); num_set_infty(xi);
	num_sub(ix,ix,&w); num_min(iy,iy,ix); num_set_infty(ix);
      }
     oct_close_incremental(r,x);
    end1:
      num_clear(&w);
    }
    else {
      /* x ->  x + c is equivalent to x <-  x - c
	 x -> -x + c is equivalent to x <- -x + c
	 they respect closure
       */

      /* result is computed in m, or in a new octagon */
      m = oct_close_lazy(m,destructive);
      if (m->ref==1) r = m;
      else { r = oct_full_copy(m); m->ref--; }
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
      
      /* modify the result matrix */
      if (!num_cmp_int(tab+x,-1)) { /* x -> -x + c */
	num_t w,ww;
	num_init(&w); num_init(&ww);
	num_mul_by_2(&ww,c);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2+1,i);
	  num_t* ix = r->c+matpos(x2  ,i);
	  num_set(&w,xi);
	  num_add(xi,ix,c);
	  num_sub(ix,&w,c);
	}
	{
	  num_t* xi = r->c+matpos(x2+1,x2  );
	  num_t* ix = r->c+matpos(x2  ,x2+1);
	  num_set(&w,xi);
	  num_add(xi,ix,&ww);
	  num_sub(ix,&w,&ww);
	}
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2  );
	  num_t* ix = r->c+matpos(i,x2+1);
	  num_set(&w,xi);
	  num_add(xi,ix,c);
	  num_sub(ix,&w,c);
	}
	num_clear(&w); num_clear(&ww);
      } 
      else {                         /* x -> x + c */
	num_t ww;
	num_init(&ww);
	num_mul_by_2(&ww,c);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_add(xi,xi,c);
	  num_sub(ix,ix,c);
	}
	{
	  num_t* xi = r->c+matpos(x2  ,x2+1);
	  num_t* ix = r->c+matpos(x2+1,x2  );
	  num_add(xi,xi,&ww);
	  num_sub(ix,ix,&ww);
	}
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_add(xi,xi,c);
	  num_sub(ix,ix,c);
	}
	num_clear(&ww);
      }
 
    }

  else { /* general case */
    r = oct_forget (m, x, destructive);
  }
 end:
  OCT_EXIT("oct_substitute_variable",27);
  return r;  
}





/* intersects the domain with a linear constraint
     tab[0]v0 + tab[1]v1 + ... + tab[N-1]v(N-1) + tab[N] >= 0

   if the result is not empty, it is always a newly allocated matrix
   that can be safely modified in-place
 */
oct_t*
OCT_PROTO(add_constraint) (oct_t*       m,
			   const num_t* tab,
			   bool         destructive)
{
  oct_t* r;
  var_t  i, n = 0;
  oct_cons c;
  OCT_ENTER("oct_add_constraint",28);

  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  for (i=0;i<m->n;i++)
    if (num_cmp_zero(tab+i)) { c.x=i; n=1; break; }
  for (i++;i<m->n;i++)
    if (num_cmp_zero(tab+i)) { c.y=i; n++; }

  if (n==0) {
    if (num_cmp_zero(tab+m->n)>=0) r = oct_copy(m);
    else r = oct_empty (m->n);
    if (destructive) oct_free (m);
  }

  else if (n==1 && !num_cmp_int(tab+c.x,1)) {
    c.type = mx;
    num_init_set(&c.c,tab+m->n);
    r = oct_add_bin_constraints (m, 1, &c, destructive);
  }

  else if (n==1 && !num_cmp_int(tab+c.x,-1)) {
    c.type = px;
    num_init_set(&c.c,tab+m->n);
    r = oct_add_bin_constraints (m, 1, &c, destructive);
  }

  else if (n==2 && !num_cmp_int(tab+c.x,1) && !num_cmp_int(tab+c.y,1)) {
    c.type = mxmy;
    num_init_set(&c.c,tab+m->n);
    r = oct_add_bin_constraints (m, 1, &c, destructive);
  }

  else if (n==2 && !num_cmp_int(tab+c.x,1) && !num_cmp_int(tab+c.y,-1)) {
    c.type = mxpy;
    num_init_set(&c.c,tab+m->n);
    r = oct_add_bin_constraints (m, 1, &c, destructive);
  }

  else if (n==2 && !num_cmp_int(tab+c.x,-1) && !num_cmp_int(tab+c.y,1)) {
    c.type = pxmy;
    num_init_set(&c.c,tab+m->n);
    r = oct_add_bin_constraints (m, 1, &c, destructive);
  }

  else if (n==2 && !num_cmp_int(tab+c.x,-1) && !num_cmp_int(tab+c.y,-1)) {
    c.type = pxpy;
    num_init_set(&c.c,tab+m->n);
    r = oct_add_bin_constraints (m, 1, &c, destructive);
  }

  else
    if (destructive) r = m;
    else r = oct_copy (m);
 end:
  OCT_EXIT("oct_add_constraint",28);
  return r;
}



/**************************/
/* Experimental operators */
/**************************/


/* as oct_assign_variable, but with interval instead of constant coefficients
   e = [-t[1];t[0]]v0 + ... + [-t[2N-1];t[2N-2]v(N-1)] + [-t[2N+1;t[2N]]

   beware the sign inversion of the lower bound!
   make sure the lower bound is less than or equal to the higher bound!

   the result is always closed (thanks to calls to oct_close_incremental)
 */
oct_t*
OCT_PROTO(interv_assign_variable) (oct_t*       m,
				   var_t        x,
				   const num_t* t,
				   bool         destructive)
{
  oct_t* r;
  var_t  i, y = 0, N = 0;
  const var_t n  = m->n;
  const var_t n2 = n*2;
  const var_t x2 = 2*x;
  const num_t* c = t+n2;
  num_t tmp;
  OCT_ENTER("oct_interv_assign_variable",29);
  OCT_ASSERT(x<m->n,"variable index greater than the number of variables in oct_interv_assign_variable");

  num_init(&tmp);

  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  for (i=0;i<n;i++) 
    if (num_infty(t+2*i) || num_infty(t+2*i+1))
      { r = oct_forget (m, x, destructive); goto end; } 
    else {
      num_add(&tmp,t+2*i,t+2*i+1);
      if (num_cmp_zero(&tmp)<0) {
	r = oct_empty(m->n);
	if (destructive) oct_free(m);
	goto end;
      }
      if (num_cmp_zero(t+2*i) || num_cmp_zero(t+2*i+1)) { y=i; N++; }
    }

  num_add(&tmp,c,c+1);
  if (num_cmp_zero(&tmp)<0) {
    r = oct_empty(m->n);
    if (destructive) oct_free(m);
    goto end;
  }
  
  if (N==0)  /* x <- [-d,c] */
    r = oct_set_bounds (m, x,c,c+1,destructive);

  else if (N==1 && 
	   ((!num_cmp_int(t+2*y, 1) && !num_cmp_int(t+2*y+1,-1)) || 
	    (!num_cmp_int(t+2*y,-1) && !num_cmp_int(t+2*y+1, 1))))

    /* x <- +/- y + [-d,c] */

    if (y!=x) { /* x <- +/- y + [-d,c], x!=y */
      r = oct_forget (m, x, destructive);
      if (r->state==OCT_EMPTY) goto end;
      if (!num_cmp_int(t+2*y,1)) {          /* x <- y + [-d,c],   y!=x */
	num_set(r->c+matpos2(2*y,x2),c);
	num_set(r->c+matpos2(x2,2*y),c+1);
      }
      else {                                /* x <- -y + [-d,c],  y!=x */
	num_set(r->c+matpos2(2*y+1,x2),c);
	num_set(r->c+matpos2(x2,2*y+1),c+1);
      }
      oct_close_incremental(r,x);
    }

    else {  /* x <- +/- x + [-d,c]  respects closure  */

      /* result is computed in m, or in a new octagon */
      m = oct_close_lazy(m,destructive);
      if (m->ref==1) r = m;
      else { r = oct_full_copy(m); m->ref--; }
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
      
      /* modify the result matrix */
      if (!num_cmp_int(t+2*x,-1)) { /* x <- -x + [-d,c] */
	num_t w,vv,ww;
	num_init(&w); num_init(&vv); num_init(&ww);
	num_mul_by_2(&vv,c); num_mul_by_2(&ww,c+1);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_set(&w,xi);
	  num_add(xi,ix,c+1);
	  num_add(ix,&w,c);
	}
	num_set(&w,r->c+matpos(x2,x2+1));
	num_add(r->c+matpos(x2,x2+1),r->c+matpos(x2+1,x2),&ww);
	num_add(r->c+matpos(x2+1,x2),&w                  ,&vv);
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_set(&w,xi);
	  num_add(xi,ix,c+1);
	  num_add(ix,&w,c);
	}
	num_clear(&w); num_clear(&vv); num_clear(&ww);
      } 
      else {                         /* x <- x + [-d,c] */
	num_t vv,ww;
	num_init(&vv); num_init(&ww);
	num_mul_by_2(&vv,c); num_mul_by_2(&ww,c+1);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_add(xi,xi,c+1);
	  num_add(ix,ix,c);
	}
	num_add(r->c+matpos(x2+1,x2),r->c+matpos(x2+1,x2),&vv);
	num_add(r->c+matpos(x2,x2+1),r->c+matpos(x2,x2+1),&ww);
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_add(xi,xi,c+1);
	  num_add(ix,ix,c);
	}
	num_clear(&vv); num_clear(&ww);
      }
    }

  else { /* general case */
    num_t* buf;              /* 2*bounds for each variable */
    num_t Cb,cb;             /* 2*global upper / lower bound */
    int   Cinf, cinf;        /* number of infinite coef in up/lw bounds */
    var_t Ci = 0, ci = 0;            /* var leading to infinite coef in up/lw bounds */
    num_t ka,kb,kc,kd;
    int changed = 0;
    r = oct_close (m,destructive,false);
    if (r->state==OCT_EMPTY) goto end;
    buf = new_n(num_t,n2);
    num_init(&Cb); num_init(&cb); 
    num_init(&ka); num_init(&kb); num_init(&kc); num_init(&kd);
    num_mul_by_2(&Cb,c); num_mul_by_2(&cb,c+1);
    Cinf = cinf = 0;
    for (i=0;i<n2;i+=2) { 
      /* get variable bounds */
      num_t* px = r->c+matpos(i+1,i); /*  xj+xj */
      num_t* mx = r->c+matpos(i,i+1); /* -xj-xj */

      num_init_set(buf+i  ,px);
      num_init_set(buf+i+1,mx);

      /* compute Cb & cb ignoring components leading to +oo */

      /* max */
      if (!num_cmp_zero(t+i)) num_set_int(&ka,0);
      else {
	num_mul(&ka,t+i  ,px);
	num_neg(&kb,t+i);   
	num_mul(&kb,&kb,mx);
	num_max(&ka,&ka,&kb);
      }
      if (!num_cmp_zero(t+i+1)) num_set_int(&kc,0);
      else {
	num_mul(&kc,t+i+1,mx);
	num_neg(&kd,t+i+1); 
	num_mul(&kd,&kd,px);
	num_max(&kc,&kc,&kd); 
      }
      num_max(&ka,&ka,&kc);
      if (num_infty(&ka)) { Cinf++; Ci=i; } else num_add(&Cb,&Cb,&ka);

      /* -min */
      if (!num_cmp_zero(t+i)) num_set_int(&ka,0);
      else {
	num_mul(&ka,t+i  ,mx);
	num_neg(&kb,t+i);   
	num_mul(&kb,&kb,px);
	num_max(&ka,&ka,&kb);
      }
      if (!num_cmp_zero(t+i+1)) num_set_int(&kc,0);
      else {
	num_mul(&kc,t+i+1,px);
	num_neg(&kd,t+i+1); 
	num_mul(&kd,&kd,mx);
	num_max(&kc,&kc,&kd); 
      }
      num_max(&ka,&ka,&kc);
      if (num_infty(&ka)) { cinf++; ci=i; } else num_add(&cb,&cb,&ka);
    }

    r = oct_forget (r,x,true);

    /* upper bounds */
    if (!num_infty(&Cb))
    switch (Cinf) {
    case 0:
      /* bound is not infinite */
      num_set(r->c+matpos(x2+1,x2),&Cb);        /* bound for x */
      for (i=0;i<n2;i+=2)
      	if (i!=x2) {
      	  if (num_cmp_int(t+i+1,-1)<=0 && !num_infty(buf+i)) {       
	    /* bound for x-y */
	    num_sub(&ka,&Cb,buf+i);
	    num_div_by_2(r->c+matpos2(i,  x2),&ka);
	  }
      	  else if (num_cmp_int(t+i,-1)<=0 && !num_infty(buf+i+1)) {    
	    /* bound for x+y */
	    num_sub(&ka,&Cb,buf+i+1);
	    num_div_by_2(r->c+matpos2(i+1,x2),&ka);
	  }      
	}
      changed = 1;
      break;
    case 1:
      /* bound has only one infinite coef, for var y of index Ci =>
	 we may still have a finite bound for x-y, or x+y            */
      if (Ci!=x2) {
      	if (!num_cmp_int(t+Ci,1) && !num_cmp_int(t+Ci+1,-1)) {
	  num_div_by_2(r->c+matpos2(Ci  ,x2),&Cb);  
	  changed = 1;
	}
      	else if (!num_cmp_int(t+Ci,-1) && !num_cmp_int(t+Ci+1,1)) {
	  num_div_by_2(r->c+matpos2(Ci+1,x2),&Cb);
	  changed = 1;
	}
      }
      break;
    }

    /* lower bounds */
    if (!num_infty(&cb))
    switch (cinf) {
    case 0:
      /* bound is not infinite */
     num_set(r->c+matpos(x2,x2+1),&cb);        /* bound for -x */
     for (i=0;i<n2;i+=2)
       if (i!=x2) {
	 if (num_cmp_int(t+i+1,-1)<=0 && !num_infty(buf+i+1)) {       
	   /* bound for -x+y */
	   num_sub(&ka,&cb,buf+i+1);
	   num_div_by_2(r->c+matpos2(i+1,x2+1),&ka);

	 }
	 else if (num_cmp_int(t+i,-1)<=0 && !num_infty(buf+i)) {    
	   /* bound for -x-y */
	   num_sub(&ka,&cb,buf+i);
	   num_div_by_2(r->c+matpos2(i,  x2+1),&ka);
	 }
       }
     changed = 1;
     break;
    case 1:
      /* bound has only one infinite coef, for var y of index ci =>
	 we may still have a finite bound for -x+y, or -x-y            */
      if (ci!=x2) {
	if (!num_cmp_int(t+ci,1) && !num_cmp_int(t+ci+1,-1)) {
	  num_div_by_2(r->c+matpos2(x2,ci  ),&cb);
	  changed = 1;
	}
      	else if (!num_cmp_int(t+ci,-1) && !num_cmp_int(t+ci+1,1)) {
	  num_div_by_2(r->c+matpos2(x2,ci+1),&cb);
	  changed = 1;
	}
      }
      break;
    }
    num_clear_n(buf,n2);  oct_mm_free (buf);
    num_clear(&cb); num_clear(&Cb); 
    num_clear(&ka); num_clear(&kb); num_clear(&kc); num_clear(&kd);
    if (changed) oct_close_incremental(r,x);
  }
 end:
  num_clear(&tmp);
  OCT_EXIT("oct_interv_assign_variable",29);
  return r;  
}



/* as oct_add_constraint, but with interval instead of constant coefficients
   [-t[1];t[0]]v0 + ... + [-t[2N-1];t[2N-2]v(N-1)] + [-t[2N+1;t[2N]] >= 0
*/
oct_t*
OCT_PROTO(interv_add_constraint) (oct_t*       m,
				  const num_t* t,
				  bool         destructive)
{
  oct_t* r;
  var_t  i, j, k, y1 = 0, y2 = 0, N = 0; // zra = 0 y1, y2
  const var_t n  = m->n;
  const var_t n2 = n*2;
  const num_t* c = t+n2;
  num_t tmp;
  OCT_ENTER("oct_interv_add_constraint",46);

  num_init(&tmp);

  if (oct_is_empty_lazy(m)==tbool_true)
    { if (destructive) r = m; else r = oct_copy(m); goto end; }

  for (i=0;i<n2;i+=2) {
    if (num_infty(t+i) || num_infty(t+i+1))
      { if (destructive) r = m; else r = oct_copy(m); goto end; }
    num_add(&tmp,t+i,t+i+1);
    if (num_cmp_zero(&tmp)<0) 
      { if (destructive) r = m; else r = oct_copy(m); goto end; }
    if (num_cmp_zero(t+i) || num_cmp_zero(t+i+1)) { y2=y1; y1=i; N++; }
  }

  num_add(&tmp,c,c+1);
  if (num_cmp_zero(&tmp)<0) 
    { if (destructive) r = m; else r = oct_copy(m); goto end; }

  if (N==0) { /* [-d,c] >= 0 */
    if (num_cmp_int(c,0)>=0) r = oct_copy(m);
    else r = oct_empty (m->n);
    if (destructive) oct_free(m);
  }

  else if (N==1 &&  /* +/- x + [-d,c] >= 0 */
	   ((!num_cmp_int(t+y1, 1) && !num_cmp_int(t+y1+1,-1)) ||
	    (!num_cmp_int(t+y1,-1) && !num_cmp_int(t+y1+1, 1)))) {
    oct_cons cons;
    cons.x = y1/2;
    num_init_set(&cons.c,c);
    if (!num_cmp_int(t+y1,1)) cons.type = mx; else cons.type = px;
    r = oct_add_bin_constraints(m, 1, &cons, destructive);
    num_clear(&cons.c);
  }


  else if (N==2 && /* +/- x +/-y + [-d,c] >= 0 */
	   ((!num_cmp_int(t+y1, 1) && !num_cmp_int(t+y1+1,-1)) ||
	    (!num_cmp_int(t+y1,-1) && !num_cmp_int(t+y1+1, 1))) &&
	   ((!num_cmp_int(t+y2, 1) && !num_cmp_int(t+y2+1,-1)) ||
	    (!num_cmp_int(t+y2,-1) && !num_cmp_int(t+y2+1, 1)))) {

    oct_cons cons;
    cons.x = y1/2;
    cons.y = y2/2;
    num_init_set(&cons.c,c);
    if (!num_cmp_int(t+y1,1)) {
      if (!num_cmp_int(t+y2,1)) cons.type = mxmy; else cons.type = mxpy;
	}
    else {
      if (!num_cmp_int(t+y2,1)) cons.type = pxmy; else cons.type = pxpy;
    }
    r = oct_add_bin_constraints(m, 1, &cons, destructive);
    num_clear(&cons.c);
  }
  
  /* general case */
  else {
    num_t* buf;            /* 2*bounds for each variable */
    num_t Cb;              /* 2*global upper bound */
    int   Cinf;            /* number of infinite coef in up bound */
    var_t Ci1 = 0;             /* var1 leading to infinite coef in up bound */
    var_t Ci2 = 0;             /* var2 leading to infinite coef in up bound */
    num_t ka,kb = 0,kc,kd;
    int   changed = 0;
    r = oct_close (m,destructive,false);
    if (r->state==OCT_EMPTY) goto end;
    buf = new_n(num_t,n2);
    num_init(&Cb);
    num_init(&ka); num_init(&kb); num_init(&kc); num_init(&kd);
    num_mul_by_2(&Cb,c);
    Cinf = 0;

    for (i=0;i<n2;i+=2) { 
      /* get variable bounds, ignoring components leading to +oo */
      num_t* px = r->c+matpos(i+1,i); /*  xj+xj */
      num_t* mx = r->c+matpos(i,i+1); /* -xj-xj */

      num_init_set(buf+i  ,px);
      num_init_set(buf+i+1,mx);

      /* max */
      if (!num_cmp_zero(t+i)) num_set_int(&ka,0);
      else {
	num_mul(&ka,t+i  ,px);
	num_neg(&kb,t+i);   
	num_mul(&kb,&kb,mx);
	num_max(&ka,&ka,&kb);
      }
      if (!num_cmp_zero(t+i+1)) num_set_int(&kc,0);
      else {
	num_mul(&kc,t+i+1,mx);
	num_neg(&kd,t+i+1); 
	num_mul(&kd,&kd,px);
	num_max(&kc,&kc,&kd); 
      }
      num_max(&ka,&ka,&kc);
      if (num_infty(&ka)) { Cinf++; Ci2=Ci1; Ci1=i; } 
      else num_add(&Cb,&Cb,&ka);
    }
    
    /* get a copy of r to modify in-place */
    oct_free(r);
    r = oct_full_copy(m);
    
    if (!num_infty(&Cb))
    switch (Cinf) {
    case 0:
      /* no infinite bound */
      for (i=0;i<n2;i+=2) {
	if (num_cmp_int(t+i+1,-1)<=0 && !num_infty(buf+i)) {
	  // -x <= expr-x <= max(expr) - max x
	  num_sub(&ka,&Cb,buf+i);
	  num_min(r->c+matpos(i,i+1),r->c+matpos(i,i+1),&ka);
	  k = i+1;
	  changed = 1;
	}  
	else if (num_cmp_int(t+i,-1)<=0 && !num_infty(buf+i+1)) {
	  // x <= expr+x <= max(expr) - max(-x)
	  num_sub(&ka,&Cb,buf+i+1);
	  num_min(r->c+matpos(i+1,i),r->c+matpos(i+1,i),&ka);
	  k = i;
	  changed = 1;
	}
	else k = -1;
	
	if (k!=-1) {
	  for (j=i+2;j<n2;j+=2) {
	    if (num_cmp_int(t+j+1,-1)<=0 && !num_infty(buf+j)) {
	      // (+/-)x -y <= max(expr) - max((+/-)x) - max y
	      num_sub(&kb,&ka,buf+j);
	      num_div_by_2(&kb,&kb);
	      num_min(r->c+matpos(j,k),r->c+matpos(j,k),&kb);
	      changed = 1;
	    }  
	    else if (num_cmp_int(t+j,-1)<=0 && !num_infty(buf+j+1)) {
	      // (+/-)x +y <= max(expr) - max((+/-)x) - max (-y)
	      num_sub(&kb,&ka,buf+j+1);
	      num_div_by_2(&kb,&kb);
	      num_min(r->c+matpos(j+1,k),r->c+matpos(j+1,k),&kb);
	      changed = 1;
	    }
	  }
	}
      }
      break;

    case 1:
      /* we can still infer info on Ci1 */
      if      (!num_cmp_int(t+Ci1, 1) && !num_cmp_int(t+Ci1+1,-1)) k = Ci1+1;
      else if (!num_cmp_int(t+Ci1,-1) && !num_cmp_int(t+Ci1+1, 1)) k = Ci1;
      else goto end0;

      num_min(r->c+matpos(k^1,k),r->c+matpos(k^1,k),&Cb);
      changed = 1;

      for (j=0;j<n2;j+=2) 
	if (Ci1!=j) {
	  if (num_cmp_int(t+j+1,-1)<=0 && !num_infty(buf+j)) {
	    // (+/-)x -y <= max(expr) - max((+/-)x) - max y
	    num_sub(&kb,&Cb,buf+j);
	    num_div_by_2(&kb,&kb);
	    num_min(r->c+matpos2(j,k),r->c+matpos2(j,k),&kb);
	  }  
	  else if (num_cmp_int(t+j,-1)<=0 && !num_infty(buf+j+1)) {
	    // (+/-)x +y <= max(expr) - max((+/-)x) - max (-y)
	    num_sub(&kb,&Cb,buf+j+1);
	    num_div_by_2(&kb,&kb);
	    num_min(r->c+matpos2(j+1,k),r->c+matpos2(j+1,k),&kb);
	  }
	}
      break;

    case 2:
      /* we can still infer info on Ci1 & Ci2 */
      if      (!num_cmp_int(t+Ci1, 1) && !num_cmp_int(t+Ci1+1,-1)) i = Ci1+1;
      else if (!num_cmp_int(t+Ci1,-1) && !num_cmp_int(t+Ci1+1, 1)) i = Ci1;
      else goto end0;

      if      (!num_cmp_int(t+Ci2, 1) && !num_cmp_int(t+Ci2+1,-1)) j = Ci1+1;
      else if (!num_cmp_int(t+Ci2,-1) && !num_cmp_int(t+Ci2+1, 1)) j = Ci1;
      else goto end0;

      num_div_by_2(&ka,&Cb);
      num_min(r->c+matpos2(j^1,i),r->c+matpos2(j^1,i),&kb);
      changed = 1;
      break;
    }

    if (changed) r->state = OCT_NORMAL;
    
  end0:
    num_clear_n(buf,n2);  oct_mm_free (buf);
    num_clear(&Cb); 
    num_clear(&ka); num_clear(&kb); num_clear(&kc); num_clear(&kd);
  }

 end:
  num_clear(&tmp);
  OCT_EXIT("oct_interv_add_constraint",46);
  return r;
}


/* as oct_substitute_variable, but with interval instead of constant coefs
   e -> [-t[1];t[0]]v0 + ... + [-t[2N-1];t[2N-2]v(N-1)] + [-t[2N+1;t[2N]]

   NOTE: the general case is not yet implemented...
*/
oct_t*
OCT_PROTO(interv_substitute_variable) (oct_t*       m,
				       var_t        x,
				       const num_t* t,
				       bool         destructive)
{
  oct_t* r;
  var_t  i, y = 0, N = 0;
  const var_t n  = m->n;
  const var_t n2 = n*2;
  const var_t x2 = 2*x;
  const num_t* c = t+n2;
  num_t tmp;

  OCT_ENTER("oct_interv_substitute_variable",47);
  OCT_ASSERT(x<m->n,"variable index greater than the number of variables in oct_interv_substitute_variable");

  num_init(&tmp);

  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  for (i=0;i<n;i++) 
    if (num_infty(t+2*i) || num_infty(t+2*i+1))
      { r = oct_forget (m, x, destructive); goto end; } 
    else {
      num_add(&tmp,t+2*i,t+2*i+1);
      if (num_cmp_zero(&tmp)<0) {
	r = oct_empty(m->n);
	if (destructive) oct_free(m);
	goto end;
      }
      if (num_cmp_zero(t+2*i) || num_cmp_zero(t+2*i+1)) { y=i; N++; }
    }

  num_add(&tmp,c,c+1);
  if (num_cmp_zero(&tmp)<0) {
    r = oct_empty(m->n);
    if (destructive) oct_free(m);
    goto end;
  }
  
  if (N==0) { /* x -> [-d,c] */
    oct_t* mm;
    num_t w1,w2;
    mm = oct_close (m,destructive,false);
    num_init(&w1); num_init(&w2);
    /* result is empty */
    if (mm->state==OCT_EMPTY) { r = mm; goto end0; }
    num_mul_by_2(&w1,c);   num_neg(&w1,&w1);
    num_mul_by_2(&w2,c+1); num_neg(&w2,&w2);
    if (num_cmp(mm->c+matpos(x2+1,x2),&w2)<0 ||
        num_cmp(mm->c+matpos(x2,x2+1),&w1)<0) 
      { r = oct_empty(mm->n); oct_free(mm); goto end0; }
    /* result is computed in mm, or in a new octagon */
    if (mm->ref==1) r = mm;
    else { r = oct_full_copy(mm); mm->ref--; }
    r->state = OCT_NORMAL; 
    if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }

    /* change the result matrix */
    for (i=0;i<x2;i++) {
      /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
      num_t* xi = r->c+matpos(x2  ,i);
      num_t* ix = r->c+matpos(x2+1,i);
      num_t* ii = r->c+matpos(i^1,i);
      num_add(&w1,xi,c);
      num_add(&w2,ix,c+1);
      num_min(&w1,&w1,&w2);
      num_mul_by_2(&w1,&w1);
      num_min(ii,ii,&w1);
      num_set_infty(xi);
      num_set_infty(ix);
    }
    for (i=x2+2;i<n2;i++) {
      /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
      num_t* xi = r->c+matpos(i,x2+1);
      num_t* ix = r->c+matpos(i,x2  );
      num_t* ii = r->c+matpos(i,i^1);
      num_add(&w1,xi,c);
      num_add(&w2,ix,c+1);
      num_min(&w1,&w1,&w2);
      num_mul_by_2(&w1,&w1);
      num_min(ii,ii,&w1);
      num_set_infty(xi);
      num_set_infty(ix);
    }
    num_set_infty(r->c+matpos(x2,x2+1));
    num_set_infty(r->c+matpos(x2+1,x2));
  end0:
    num_clear(&w1); num_clear(&w2);
  }

  else if (N==1 &&
	   ((!num_cmp_int(t+2*y, 1) && !num_cmp_int(t+2*y+1,-1)) || 
	    (!num_cmp_int(t+2*y,-1) && !num_cmp_int(t+2*y+1, 1)))) {
    if (y!=x) {  /* x -> +/- y + [-d,c], x!=y */
      var_t yy, yy1;
      oct_t* mm;
      num_t w,ww;
      num_init(&w); num_init(&ww);
      mm = oct_close (m,destructive,false);
      if (!num_cmp_int(t+2*y,-1)) yy = 2*y+1; else yy = 2*y;
      yy1 = yy^1;
      /* result is empty */
      if (mm->state==OCT_EMPTY) { r = mm; goto end1; }
      num_neg(&w, c);
      num_neg(&ww,c+1);
      if (num_cmp(&ww ,mm->c+matpos2(yy,x2))>0 ||
	  num_cmp(&w,  mm->c+matpos2(x2,yy))>0)
	{ r = oct_empty(mm->n); oct_free(mm); goto end1; }
      /* result is computed in mm, or in a new octagon */
      if (mm->ref==1) r = mm;
      else { r = oct_full_copy(mm); mm->ref--; }
      /* change the result matrix */
      for (i=0;i<x2;i++) {
	/* TO BE LINEARIZED */
	num_t* xi = r->c+matpos(x2  ,i);
	num_t* ix = r->c+matpos(x2+1,i);
	num_t* yi = r->c+matpos2(yy ,i);
	num_t* iy = r->c+matpos2(yy1,i);
	num_add(xi,xi,c  ); num_min(yi,yi,xi); num_set_infty(xi);
	num_add(ix,ix,c+1); num_min(iy,iy,ix); num_set_infty(ix);
      }
      for (i=x2+2;i<n2;i++) {
	/* TO BE LINEARIZED */
	num_t* xi = r->c+matpos(i,x2+1);
	num_t* ix = r->c+matpos(i,x2  );
	num_t* yi = r->c+matpos2(i,yy1);
	num_t* iy = r->c+matpos2(i,yy );
	num_add(xi,xi,c  ); num_min(yi,yi,xi); num_set_infty(xi);
	num_add(ix,ix,c+1); num_min(iy,iy,ix); num_set_infty(ix);
      }
      {
	num_t* xi = r->c+matpos(x2  ,x2+1);
	num_t* ix = r->c+matpos(x2+1,x2  );
	num_t* yi = r->c+matpos2(yy ,yy1);
	num_t* iy = r->c+matpos2(yy1,yy );
	num_mul_by_2(&w,c);
	num_mul_by_2(&ww,c+1);
	num_add(xi,xi,&w ); num_min(yi,yi,xi); num_set_infty(xi);
	num_add(ix,ix,&ww); num_min(iy,iy,ix); num_set_infty(ix);
      }
     oct_close_incremental(r,x);
    end1:
      num_clear(&w); num_clear(&ww);
    }
    else {
      /* x ->  x + [-d,c] is equivalent to x <-  x - [-d,c]
	 x -> -x + [-d,c] is equivalent to x <- -x + [-d,c]
	 they respect closure
       */

      /* result is computed in m, or in a new octagon */
      m = oct_close_lazy(m,destructive);
      if (m->ref==1) r = m;
      else { r = oct_full_copy(m); m->ref--; }
      if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
      
      /* modify the result matrix */
      if (!num_cmp_int(t+2*x,-1)) { /* x <- -x + [-d,c] */
	num_t w,vv,ww;
	num_init(&w); num_init(&vv); num_init(&ww);
	num_mul_by_2(&vv,c); num_mul_by_2(&ww,c+1);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_set(&w,xi);
	  num_add(xi,ix,c+1);
	  num_add(ix,&w,c);
	}
	num_set(&w,r->c+matpos(x2,x2+1));
	num_add(r->c+matpos(x2,x2+1),r->c+matpos(x2+1,x2),&ww);
	num_add(r->c+matpos(x2+1,x2),&w                  ,&vv);
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_set(&w,xi);
	  num_add(xi,ix,c+1);
	  num_add(ix,&w,c);
	}
	num_clear(&w); num_clear(&vv); num_clear(&ww);
      } 
      else {                         /* x <- x - [-d,c] */
	num_t vv,ww;
	num_init(&vv); num_init(&ww);
	num_mul_by_2(&vv,c); num_mul_by_2(&ww,c+1);
	for (i=0;i<x2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(x2  ,i);
	  num_t* ix = r->c+matpos(x2+1,i);
	  num_add(xi,xi,c);
	  num_add(ix,ix,c+1);
	}
	num_add(r->c+matpos(x2+1,x2),r->c+matpos(x2+1,x2),&ww);
	num_add(r->c+matpos(x2,x2+1),r->c+matpos(x2,x2+1),&vv);
	for (i=x2+2;i<n2;i++) {
	  /* (TO BE LINEARIZED TO AVOID MULTIPLICATION) */
	  num_t* xi = r->c+matpos(i,x2+1);
	  num_t* ix = r->c+matpos(i,x2  );
	  num_add(xi,xi,c);
	  num_add(ix,ix,c+1);
	}
	num_clear(&vv); num_clear(&ww);
      }

    }

  }
  else { /* general case */
    r = oct_forget (m, x, destructive);
    /*  not yet implemented */
  }

 end:
  num_clear(&tmp);
  OCT_EXIT("oct_interv_substitute_variable",47);
  return r;  
}


/* Modify all variables of the octagon simultaneously by the formula
   r_i <- r_i + [nmin,nmax] * [-tab[2*i+1],tab[2*i]]
   This simulates time flow.
   The amout of time t is in [nmin,nmax], and each variable Vi has a change
   rate in [-tab[2*i+1],tab[2*i]].
   We must have 0 <= nmin <= nmax.
   This function has a O(n^2) complexity.
   Original code by Damien Masse.
*/
oct_t*
OCT_PROTO(time_flow) (oct_t* m, 
		      const num_t *nmin, const num_t *nmax, const num_t *tab,
		      bool destructive)
{
  var_t i,j;
  const var_t n2 = m->n*2;
  int a;
  num_t tmp, *c;
  oct_t* r;
  OCT_ENTER("oct_time_flow",56);
  OCT_ASSERT((num_cmp_zero(nmin)>=0) && (num_cmp(nmax,nmin)>=0), 
	     "incorrect range in oct_time_flow");
  /* m empty => return m */
  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  }
  /* result is computed in m, or in a new octagon */
  if (destructive) {
    if (m->ref==1) r = m;
    else { r = oct_full_copy(m); m->ref--; }
  }
  else r = oct_full_copy(m);

  /* change the result matrix */
  r->state = OCT_NORMAL;
  if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }

  num_init(&tmp);
  c = r->c;
  /* we take each constraint once */
  for (i=0;i<n2;i++) {
    const var_t br = i|1;
    const var_t ii = i^1;
    for (j=0;j<=br;j++,c++) {
      if (i==j) continue;
      /* Vj-Vi <= c + [nmin,nmax] * [ -(tab[2i]+tab[2j+1]); tab[2j]+tab[2i+1] ]

	 as 0<=nmin<=nmax we have:

	 Vj-Vi <= c + max( nmin * tab[2j]+tab[2i+1], nmax * tab[2j]+tab[2i+1] )
       */
      num_add(&tmp,tab+ii,tab+j); /* tab[2j]+tab[2i+1] */
      a=num_cmp_zero(&tmp);
      if (a==0) continue; /* no modification */
      num_mul(&tmp,&tmp,(a>0 ? nmax : nmin));
      num_add(c,c,&tmp);
    }
  }
  num_clear(&tmp);
 end:
  OCT_EXIT("oct_time_flow",56);
  return r;
}



/***********************/
/* Change of Dimension */
/***********************/

/* add dimsup variables at the end
   there is no constraints added on the variables: the domain is extruded 
   O(dimsup^2) time cost (plus optionnal copy)
*/
oct_t*
OCT_PROTO(add_dimensions_and_embed) (oct_t* m,
				     var_t  dimsup,
				     bool   destructive)
{
  oct_t* r;
  const size_t n1=matsize(m->n), n2=matsize(m->n+dimsup);
  OCT_ENTER("oct_add_dimensions_and_embed",30);
  if (destructive) {
    if (m->ref==1) r = m;
    else { r = oct_full_copy(m); m->ref--; }
  }
  else r = oct_full_copy(m);

  if (r->state!=OCT_EMPTY) {
    size_t i;
    r->c = renew_n(r->c,num_t,n2);
    for (i=n1;i<n2;i++)  num_init_set_infty(r->c+i);
    for (i=r->n;i<2*(r->n+dimsup);i++) num_set_int(r->c+matpos(i,i),0);
    if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
  }
  r->n += dimsup;
  OCT_EXIT("oct_add_dimensions_and_embed",30);
  return r;
}

/* add dimsup variables at the end
   added variables are initialy constrained to be 0  
   O(dimsup^2) time cost (plus optionnal copy)
*/
oct_t*
OCT_PROTO(add_dimensions_and_project) (oct_t* m,
				       var_t  dimsup,
				       bool   destructive)
{
  const var_t n0 = m->n;
  var_t i;
  oct_t* r;
  OCT_ENTER("oct_add_dimensions_and_project",31);
  r = oct_add_dimensions_and_embed(m,dimsup,destructive);
  if (r->state!=OCT_EMPTY) {
    for (i=n0;i<r->n;i++) {
      num_set_int(r->c+matpos(2*i+1,2*i),0);
      num_set_int(r->c+matpos(2*i,2*i+1),0);
    }
    r->state = OCT_NORMAL;
  }
  OCT_EXIT("oct_add_dimensions_and_project",31);
  return r;
}

/* remove the dimsup last variables  
   O(n^3) cost for closure
*/
oct_t*
OCT_PROTO(remove_dimensions) (oct_t* m,
			      var_t  diminf,
			      bool   destructive)
{
  oct_t* mm;
  oct_t* r;
  const size_t /*n1=matsize(m->n), zra */ n2=matsize(m->n-diminf);
  OCT_ENTER("oct_remove_dimensions",32);
  OCT_ASSERT(m->n>=diminf,"removing too many dimensions in oct_remove_dimensions");
  mm = oct_close(m, destructive, true);
  if (mm->ref==1) r = mm;
  else { r = oct_full_copy(mm); mm->ref--; }

  if (r->state!=OCT_EMPTY) {
    num_clear_n(r->c+n2,n1-n2);
    r->c = renew_n(r->c,num_t,n2);
  }
  r->n -= diminf;
  OCT_EXIT("oct_remove_dimensions",32);
  return r;
}


/* add variables, not necessarily at the end
   there is no constraints added on the variables: the domain is extruded 
   O(newsize^2) time cost
   copies elements by bunch for improved efficiency
   always returns a new octagon
*/
oct_t*
OCT_PROTO(add_dimensions_and_embed_multi) (oct_t*          m,
					   const dimsup_t* tab,
					   size_t          size_tab,
					   bool            destructive)
{
  size_t i,j,org_j,new_j;
  size_t new_n;
  oct_t* r;
  OCT_ENTER("oct_add_dimensions_and_embed_multi",53);
  new_n = m->n;
  for (i=0;i<size_tab;i++) {
    OCT_ASSERT((!i || tab[i].pos>=tab[i-1].pos) &&
	       tab[i].pos<=m->n,
	       "invalid dimension array in oct_add_dimensions_and_embed_multi");
    new_n += tab[i].nbdims;
  }
  if (m->state==OCT_EMPTY) r = oct_empty(new_n);
  else {
    r = oct_universe(new_n);
    r->state = m->state;

    /* copy first lines */    
    new_j = org_j = tab[0].pos*2;
    num_set_n(r->c,m->c,matsize(tab[0].pos));

    for (j=0;j<size_tab;j++) {
      /* skip lines */
      new_j += tab[j].nbdims*2;

      /* copy lines */
      {
	num_t* org_c = m->c + matsize(org_j/2);
	num_t* new_c = r->c + matsize(new_j/2);
	size_t last_org_j = ((j<size_tab-1) ? tab[j+1].pos : m->n)*2;
	for (;org_j<last_org_j;org_j++,new_j++) {
	  size_t size_org_line = org_j+2-(org_j&1);
	  size_t size_new_line = new_j+2-(new_j&1);
	  size_t org_i = 0;
	  size_t new_i = 0;
	  for (i=0;i<size_tab;i++) {
	    /* copy elems */
	    size_t last_org_i = tab[i].pos*2;
	    if (last_org_i>=size_org_line) break; /* partial block */
	    num_set_n(new_c+new_i,org_c+org_i,last_org_i-org_i);
	    new_i += last_org_i-org_i;
	    org_i = last_org_i;

	    /* skip elems */
	    new_i += tab[i].nbdims*2;
	  }

	  /* copy remaining elems */
	  num_set_n(new_c+new_i,org_c+org_i,size_org_line-org_i);

	  /* next line */
	  org_c += size_org_line;
	  new_c += size_new_line;
	}
      }
    }
  }
  if (destructive) oct_free(m);
  OCT_EXIT("oct_add_dimensions_and_embed_multi",53);
  return r;
}


/* (always returns a new octagon) */
oct_t*
OCT_PROTO(add_dimensions_and_project_multi) (oct_t*          m,
					     const dimsup_t* tab,
					     size_t          size_tab,
					     bool            destructive)
{
  oct_t* r;
  OCT_ENTER("oct_add_dimensions_and_project_multi",54);
  r = oct_add_dimensions_and_embed_multi(m,tab,size_tab,destructive);
  if (r->state!=OCT_EMPTY) {
    size_t i,ii;
    size_t accum = 0;
    /* modify r in-place */
    for (i=0;i<size_tab;i++) 
      for (ii=0;ii<tab[i].nbdims;ii++,accum++) {
	size_t v = 2*(tab[i].pos+accum);
	num_set_int(r->c+matpos(v+1,v),0);
	num_set_int(r->c+matpos(v,v+1),0);
      }
    r->state = OCT_NORMAL;
  }
  OCT_EXIT("oct_add_dimensions_and_project_multi",54);
  return r;
}

/* (always returns a new octagon) */
oct_t*
OCT_PROTO(remove_dimensions_multi) (oct_t*          m,
				    const dimsup_t* tab,
				    size_t          size_tab,
				    bool            destructive)
{
  oct_t* r;
  size_t i,j,org_j,new_j;
  size_t new_n;
  OCT_ENTER("oct_remove_dimensions_multi",55);
  new_n = m->n;
  for (i=0;i<size_tab;i++) {
    OCT_ASSERT((!i || tab[i].pos>=tab[i-1].pos+tab[i-1].nbdims) &&
	       tab[i].pos+tab[i].nbdims<=m->n,
	       "invalid dimension array in oct_remove_dimensions_multi");
    new_n -= tab[i].nbdims;
  }
  m = oct_close(m,destructive,true);
  if (m->state==OCT_EMPTY) r = oct_empty(new_n);
  else {
    r = oct_alloc(new_n);
    r->state = OCT_CLOSED;

    /* copy first lines */    
    new_j = org_j = tab[0].pos*2;
    num_set_n(r->c,m->c,matsize(tab[0].pos));

    for (j=0;j<size_tab;j++) {
      /* skip lines */
      org_j += tab[j].nbdims*2;

      /* copy lines */
      {
	num_t* org_c = m->c + matsize(org_j/2);
	num_t* new_c = r->c + matsize(new_j/2);
	size_t last_org_j = ((j<size_tab-1) ? tab[j+1].pos : m->n)*2;
	for (;org_j<last_org_j;org_j++,new_j++) {
	  size_t size_org_line = org_j+2-(org_j&1);
	  size_t size_new_line = new_j+2-(new_j&1);
	  size_t org_i=0;
	  size_t new_i=0;
	  for (i=0;i<size_tab;i++) {
	    /* copy elems */
	    size_t last_org_i = tab[i].pos*2;
	    if (last_org_i>=size_org_line) break; /* partial block */
	    num_set_n(new_c+new_i,org_c+org_i,last_org_i-org_i);
	    new_i += last_org_i-org_i;
	    org_i = last_org_i;

	    /* skip elems */
	    org_i += tab[i].nbdims*2;
	  }

	  /* copy remaining elems */
	  if (size_org_line>org_i)
	    num_set_n(new_c+new_i,org_c+org_i,size_org_line-org_i);

	  /* next line */
	  org_c += size_org_line;
	  new_c += size_new_line;
	}
      }
    }
  }
  oct_free(m);
  OCT_EXIT("oct_remove_dimensions_multi",55);
  return r;
}


/* add variables at the end, then apply permutation
   O(newsize^2) time cost
   in practice, less efficient than add_dimensions_and_embed and
   add_dimensions_and_embed_multi
   (always returns a new octagon)
*/
oct_t*
OCT_PROTO(add_permute_dimensions_and_embed) (oct_t*          m,
					     var_t           dimsup,
					     const var_t*    permutation,
					     bool            destructive)
{
  const var_t old_n = m->n;
  const var_t new_n = old_n+dimsup;
  oct_t* r;
  OCT_ENTER("oct_add_permute_dimensions_and_embed",57);
  if (m->state==OCT_EMPTY) r = oct_empty(new_n);
  else {
    var_t i,j;
    num_t* n = m->c;
    for (i=0;i<new_n;i++)
      OCT_ASSERT(permutation[i]<new_n,"invalid permutation in oct_add_permute_dimensions_and_embed");
    r = oct_universe(new_n);
    r->state = m->state;
    for (i=0;i<old_n;i++) {
      const var_t new_ii = 2*permutation[i];
      for (j=0;j<=i;j++,n+=2) {
	const var_t new_jj = 2*permutation[j];
	num_set(r->c+matpos2(new_ii,new_jj),n);
	num_set(r->c+matpos2(new_ii,new_jj+1),n+1);
	num_set(r->c+matpos2(new_ii+1,new_jj),n+2*(i+1));
	num_set(r->c+matpos2(new_ii+1,new_jj+1),n+2*(i+1)+1);
      }
      n+=2*(i+1);
    }
  }
  if (destructive) oct_free(m);
  OCT_EXIT("oct_add_permute_dimensions_and_embed",57);
  return r;
}

oct_t*
OCT_PROTO(add_permute_dimensions_and_project) (oct_t*          m,
					       var_t           dimsup,
					       const var_t*    permutation,
					       bool            destructive)
{
  const var_t old_n = m->n;
  const var_t new_n = old_n+dimsup;
  oct_t* r;
  OCT_ENTER("oct_add_permute_dimensions_and_project",58);
  if (m->state==OCT_EMPTY) r = oct_empty(new_n);
  else {
    var_t i,j;
    num_t* n = m->c;
    for (i=0;i<new_n;i++)
      OCT_ASSERT(permutation[i]<new_n,"invalid permutation in oct_add_permute_dimensions_and_project");
    r = oct_universe(new_n);
    r->state = OCT_NORMAL;
    for (i=0;i<old_n;i++) {
      const var_t new_ii = 2*permutation[i];
      for (j=0;j<=i;j++,n+=2) {
	const var_t new_jj = 2*permutation[j];
	num_set(r->c+matpos2(new_ii,new_jj),n);
	num_set(r->c+matpos2(new_ii,new_jj+1),n+1);
	num_set(r->c+matpos2(new_ii+1,new_jj),n+2*(i+1));
	num_set(r->c+matpos2(new_ii+1,new_jj+1),n+2*(i+1)+1);
      }
      n+=2*(i+1);
    }
    for (i=old_n;i<new_n;i++) {
      const var_t new_ii = 2*permutation[i];
      num_set_int(r->c+matpos(new_ii+1,new_ii),0);
      num_set_int(r->c+matpos(new_ii,new_ii+1),0);
    }
  }
  if (destructive) oct_free(m);
  OCT_EXIT("oct_add_permute_dimensions_and_project",58);
  return r;
}

/* permute, then remove dimensions */
oct_t*
OCT_PROTO(permute_remove_dimensions) (oct_t*          m,
				      var_t           diminf,
				      const var_t*    permutation,
				      bool            destructive)
{
  const var_t old_n = m->n;
  const var_t new_n = old_n-diminf;
  const var_t new_n2 = new_n*2;
  oct_t* r;
  OCT_ENTER("oct_remove_permute_dimensions",59);
  m = oct_close(m,destructive,true);
  if (m->state==OCT_EMPTY) r = oct_empty(new_n);
  else {
    var_t i,j;
    num_t* n = m->c;
    for (i=0;i<new_n;i++)
      OCT_ASSERT(permutation[i]<old_n,"invalid permutation in oct_remove_permute_dimensions");
    r = oct_universe(new_n);
    r->state = m->state;
    for (i=0;i<old_n;i++) {
      const var_t new_ii = 2*permutation[i];
      if (new_ii<new_n2) {
	for (j=0;j<=i;j++,n+=2) {
	  const var_t new_jj = 2*permutation[j];
	  if (new_jj<new_n2) {
	    num_set(r->c+matpos2(new_ii,new_jj),n);
	    num_set(r->c+matpos2(new_ii,new_jj+1),n+1);
	    num_set(r->c+matpos2(new_ii+1,new_jj),n+2*(i+1));
	    num_set(r->c+matpos2(new_ii+1,new_jj+1),n+2*(i+1)+1);
	  }
	}
	n+=2*(i+1);
      }
      else n+=4*(i+1);
    }
  }
  oct_free(m);
  OCT_EXIT("oct_remove_permute_dimensions",59);
  return r;
}

/**************************/
/* Interval Manipulations */
/**************************/

/* get bounds for all variables in a fresh array r
      -r[2i+1] <= v_i <= r[2i]
   O(n) time cost
*/
num_t*
OCT_PROTO(get_box) (oct_t* m)
{
  //num_t* t; zra
  oct_t* mm;
  num_t* r = (num_t*)NULL;
  OCT_ENTER("oct_get_box",33);
  mm = oct_close(m, false, true);
  if (mm->state!=OCT_EMPTY) {
    var_t i;
    r = new_n(num_t,m->n*2);
    num_init_n(r,m->n*2);
    for (i=0;i<m->n;i++) {
      num_div_by_2(r+2*i  ,mm->c+matpos(2*i+1,2*i)); /* ( xi+xi)/2 */
      num_div_by_2(r+2*i+1,mm->c+matpos(2*i,2*i+1)); /* (-xi-xi)/2 */
    }
  }
  oct_free (mm);
  OCT_EXIT("oct_get_box",33);
  return r;
}

/* get bounds for only one variable 
    - *down <= v_k <= *up
   O(n) time cost
*/
void
OCT_PROTO(get_bounds) (oct_t* m, 
		       const var_t  k,
		       num_t* up,
		       num_t* down)
{
  oct_t* mm;
  OCT_ENTER("oct_get_bounds",34);
  OCT_ASSERT(k<m->n,"variable index greater than the number of variables in oct_get_bounds");
  mm = oct_close(m, false, true);
  if (mm->state!=OCT_EMPTY) {
    num_div_by_2(up  ,mm->c+matpos(2*k+1,2*k)); /* ( xk+xk)/2 */
    num_div_by_2(down,mm->c+matpos(2*k,2*k+1)); /* (-xk-xk)/2 */
  }
  oct_free (mm);
  OCT_EXIT("oct_get_bounds",34);
}

/* set bounds for one variable:
    - down <= v_k <= up
    O(n) time cost
 */
oct_t*
OCT_PROTO(set_bounds)  (oct_t*        m,
			const var_t   k, 
			const num_t*  up, 
			const num_t*  down,
			bool          destructive)
{
  oct_t* mm;
  num_t tmp;
  const var_t k2 = k*2;
  OCT_ENTER("oct_set_bounds",35);
  OCT_ASSERT(k<m->n,"variable index greater than the number of variables in oct_set_bounds");
  num_init(&tmp);

  num_add(&tmp,up,down);
  if (num_cmp_zero(&tmp)<0) {
    mm = oct_empty(m->n);
    if (destructive) oct_free(m);
    goto end;
  }

  mm = oct_forget(m, k, destructive);
  if (mm->state!=OCT_EMPTY) {
    var_t i;
    const var_t n2 = mm->n*2;
     
    num_mul_by_2(mm->c+matpos(k2+1,k2),up);   /* ( xk+xk)/2 */
    num_mul_by_2(mm->c+matpos(k2,k2+1),down); /* (-xk-xk)/2 */
    
    /* enforce closure */
     for (i=0;i<k2;i++) {
      num_div_by_2(&tmp,mm->c+matpos(i^1,i)); /* (xi+xi)/2 */
      num_add(mm->c+matpos(k2  ,i),&tmp,down);  /* xi-xk */
      num_add(mm->c+matpos(k2+1,i),&tmp,up);    /* xi+xk */
    }
    for (i=k2+2;i<n2;i++) {
      num_div_by_2(&tmp,mm->c+matpos(i,i^1)); /* (xi+xi)/2 */
      num_add(mm->c+matpos(i,k2+1),&tmp,down); /* xi-xk */
      num_add(mm->c+matpos(i,k2  ),&tmp,up);   /* xi+xk */
    }
   }

 end:
  num_clear(&tmp);
  OCT_EXIT("oct_set_bounds",35);
  return mm;
}

/* create an octagon from a list of bounds b
      -b[2i+1] <= v_i <= b[2i]
   O(n) time cost
 */
oct_t*
OCT_PROTO(from_box) (const var_t  n,
		     const num_t* b)
{
  oct_t* m;
  var_t i;
  num_t tmp;
  OCT_ENTER("oct_from_box",36);

  num_init(&tmp);

  m = oct_universe (n);
  for (i=0;i<n;i++) {
    num_add(&tmp,b+2*i,b+2*i+1);
    if (num_cmp_zero(&tmp)<0) {
      oct_free(m);
      m = oct_empty(n);
      goto end;
    }
    num_mul_by_2(m->c+matpos(2*i+1,2*i),b+2*i  );   /* ( xi+xi)/2 */
    num_mul_by_2(m->c+matpos(2*i,2*i+1),b+2*i+1);   /* (-xi-xi)/2 */
  }  
  m->state = OCT_NORMAL;

 end:
  num_clear(&tmp);
  OCT_EXIT("oct_from_box",36);
  return m;
}


/****************/
/* Perturbation */
/****************/

/* return an octagon where each contraint coefficient a is enlarged
   by epsilon |a| (thus resulting in a slightly bigger octagon)
   normal form is lost
   O(n^2) time cost
*/
oct_t*
OCT_PROTO(add_epsilon) (oct_t*        m,
			const num_t*  epsilon,
			bool          destructive)
{
  oct_t* r;
  size_t i;
  num_t* a;
  num_t aa;
  const size_t n = matsize(m->n);
  OCT_ENTER("oct_add_epsilon",50);
  /* m empty => return m */
  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  /* result is computed in m, or in a new octagon */
  if (destructive) {
    if (m->ref==1) r = m;
    else { r = oct_full_copy(m); m->ref--; }
  }
  else r = oct_full_copy(m);  
  r->state = OCT_NORMAL;
  if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
  num_init(&aa);
  for (i=0,a=r->c;i<n;i++,a++)
    if (num_cmp_zero(a)>=0) {
      num_mul(&aa,a,epsilon);
      num_add(a,a,&aa);
    } 
    else {
      num_neg(&aa,a);
      num_mul(&aa,&aa,epsilon);
      num_add(a,a,&aa);
    }
  num_clear(&aa);
 end:
  OCT_EXIT("oct_add_epsilon",50);
  return r;
}

/* return an octagon where each contraint coefficient is enlarged
   by (epsilon * max { |m| | x_i-x_j <= m, m!=+oo }) 
   (thus resulting in a slightly bigger octagon)
   normal form is lost
   O(n^2) time cost
*/
oct_t*
OCT_PROTO(add_epsilon_max) (oct_t*        m,
			    const num_t*  epsilon,
			    bool          destructive)
{
  oct_t* r;
  size_t i;
  num_t* a;
  num_t  abs,max;
  const size_t n = matsize(m->n);
  OCT_ENTER("oct_add_epsilon_max",51);
  /* m empty => return m */
  if (oct_is_empty_lazy(m)==tbool_true) {
    if (destructive) { r = m; goto end; }
    else { r = oct_copy(m); goto end; }
  } // zra braces
  /* result is computed in m, or in a new octagon */
  if (destructive) {
    if (m->ref==1) r = m;
    else { r = oct_full_copy(m); m->ref--; }
  }
  else r = oct_full_copy(m);  
  r->state = OCT_NORMAL;
  if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
  num_init_set_infty(&max); num_init(&abs);
  /* get abs of first non +oo coef */
  for (i=0,a=r->c;i<n;i++,a++)
    if (!num_infty(a)) { 
      if (num_cmp_zero(a)<0) num_neg(&max,a); else num_set(&max,a);
      i++; a++;
      break; 
    }
  /* get max abs of non +oo coefs */
  for (;i<n;i++,a++)
    if (!num_infty(a)) {
      if (num_cmp_zero(a)<0) {
	num_neg(&abs,a);
	num_max(&max,&max,&abs);
      }
      else num_max(&max,&max,a);
    } // zra braces
  num_mul(&max,epsilon,&max);
  /* change result matrix */
  for (i=0,a=r->c;i<n;i++,a++) num_add(a,a,&max);
  num_clear(&abs);  num_clear(&max);
 end:
  OCT_EXIT("oct_add_epsilon_max",51);
  return r;
}

/* convergence acceleration operator with perturbation
   constraints in ma that are not stable in mb are replaced by
   mb + (epsilon * max { |mb| | x_i-x_j<=m, m != +oo })
   (thus resulting in an octagon that is slightly bigger than the union)
   normal form is lost
   O(n^2) time cost
*/
oct_t*
OCT_PROTO(add_epsilon_bin) (oct_t*        ma,
			    oct_t*        mb,
			    const num_t*  epsilon,
			    bool          destructive)
{
  oct_t* r;
  size_t i;
  num_t *a, *b, *c;
  num_t  abs,max;
  const size_t n = matsize(ma->n);
  OCT_ASSERT(ma->n==mb->n,"oct_add_epsilon_bin must be called with two octagons of the same dimension.");
  OCT_ENTER("oct_add_epsilon_bin",52);
  /* ma empty => return mb */
  if (oct_is_empty_lazy(ma)==tbool_true) {
    if (destructive) { r = mb; goto end; }
    else { r = oct_copy(mb); goto end; }
  } // zra braces
  /* mb empty => return ma */
  if (oct_is_empty_lazy(mb)==tbool_true) {
    if (destructive) { r = ma; goto end; }
    else { r = oct_copy(ma); goto end; }
  } // zra braces
  /* result is computed in ma, mb, or in a new octagon */
  if (destructive) {
    if (ma->ref==1) r = ma;
    else if (mb->ref==1) r = mb;
    else r = oct_alloc(ma->n);
  }
  else r = oct_alloc(ma->n);
  r->state = OCT_NORMAL;
  if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
  num_init_set_infty(&max); num_init(&abs);
  /* get abs of first non +oo coef */
  for (i=0,b=mb->c;i<n;i++,b++)
    if (!num_infty(b)) { 
      if (num_cmp_zero(b)<0) num_neg(&max,b); else num_set(&max,b);
      i++; b++;
      break; 
    }
  /* get max abs of non +oo coefs */
  for (;i<n;i++,b++)
    if (!num_infty(b)) {
      if (num_cmp_zero(b)<0) {
	num_neg(&abs,b);
	num_max(&max,&max,&abs);
      }
      else num_max(&max,&max,b);
    } // zra braces
  num_mul(&max,epsilon,&max);
  /* change result matrix */
  for (i=0,a=ma->c,b=mb->c,c=r->c;i<n;i++,a++,b++,c++) 
    if (num_cmp(a,b)<0) { num_set(c,b); num_add(c,c,&max); }
    else num_set(c,a);
  num_clear(&abs);  num_clear(&max);
 end:
  OCT_EXIT("oct_add_epsilon_bin",52);
  return r;
}

/*************/
/* Utilities */
/*************/

/* print as a constraint list */
void
OCT_PROTO(print) (const oct_t* m)
{
  var_t i, j;
  num_t w;
  OCT_ENTER("oct_print",37);
  num_init(&w);
  if (m->state==OCT_EMPTY) { printf("[ empty ]\n"); OCT_EXIT("oct_print",37); return; }
  printf("[");
  if (m->state==OCT_CLOSED) printf(" (closed)");
  for (i=0;i<m->n;i++) {
    if (num_cmp_zero(m->c+matpos(2*i,2*i))) {
      printf("\n   v%02i-v%02i <= ",i,i); 
      num_print(m->c+matpos(2*i,2*i)); 
    }
    if (num_cmp_zero(m->c+matpos(2*i+1,2*i+1))) {
      printf("\n  -v%02i+v%02i <= ",i,i); 
      num_print(m->c+matpos(2*i+1,2*i+1));
    } 
    if (!num_infty(m->c+matpos(2*i+1,2*i))) {  
      printf("\n   v%02i     <= ",i); 
      num_div_by_2(&w,m->c+matpos(2*i+1,2*i));
      num_print(&w); 
    }
    if (!num_infty(m->c+matpos(2*i,2*i+1))) { 
      printf("\n  -v%02i     <= ",i);
      num_div_by_2(&w,m->c+matpos(2*i,2*i+1));
      num_print(&w); 
    }
  }
  
  for (i=0;i<m->n;i++)
    for (j=i+1;j<m->n;j++) {
      if (!num_infty(m->c+matpos(2*j,2*i))) { 
	printf("\n   v%02i-v%02i <= ",i,j); 
	num_print(m->c+matpos(2*j,2*i));
      }
      if (!num_infty(m->c+matpos(2*j,2*i+1))) { 
	printf("\n  -v%02i-v%02i <= ",i,j); 
	num_print(m->c+matpos(2*j,2*i+1)); 
      }
      if (!num_infty(m->c+matpos(2*j+1,2*i))) { 
	printf("\n   v%02i+v%02i <= ",i,j); 
	num_print(m->c+matpos(2*j+1,2*i));
      }
      if (!num_infty(m->c+matpos(2*j+1,2*i+1)))	{ 
	printf("\n   v%02i-v%02i <= ",j,i); 
	num_print(m->c+matpos(2*j+1,2*i+1));
      }
      
    }
  printf("  ]\n");
  num_clear(&w);
  OCT_EXIT("oct_print",37); 
}


/* usefull to debug the strong closure algorithm 
   O(n^3) time cost, not optimized at all
 */
bool
OCT_PROTO(check_closed) (const oct_t* m,
			 bool         quiet)
{
  bool r = true;
  var_t i,j,k;
  const var_t n = m->n;
  num_t w;
  OCT_ENTER("oct_check_closed",38);
  num_init(&w);
  if (m->state==OCT_EMPTY) {
    if (!quiet) printf("Empty\n");
  }
  else {
    for (i=0;i<2*n;i++)
      for (j=0;j<2*n;j++)
	for (k=0;k<2*n;k++) {
	  num_add(&w,m->c+matpos2(i,k),m->c+matpos2(k,j));
	  if (num_cmp(m->c+matpos2(i,j),&w)>0) {
	    if (!quiet) {
	      printf("Bueargh #1 %i-%i-%i ",i,j,k);
	      num_print(m->c+matpos2(i,j));
	      printf(" > ");
	      num_print(m->c+matpos2(i,k));
	      printf("+");
	      num_print(m->c+matpos2(k,j));
	      printf("\n");
	    }
	    r = false; goto end;
	}
      }
    
    for (i=0;i<2*n;i++)
      for (j=0;j<2*n;j++)
	if (num_cmp(m->c+matpos2(i,j), m->c+matpos2(j^1,i^1))>0) {
	  if (!quiet) {
	    printf("Bueargh #2 %i-%i ",i,j);
	    num_print(m->c+matpos2(i,j));
	    printf(" != ");
	    num_print(m->c+matpos2(j^1,i^1));
	    printf("\n");		
	  }    
	  r = false; goto end;
	}
    
    for (i=0;i<2*n;i++)
      for (j=0;j<2*n;j++) {
	num_add(&w,m->c+matpos2(i,i^1),m->c+matpos2(j^1,j));
	num_div_by_2(&w,&w);
	if (num_cmp(m->c+matpos2(i,j),&w)>0) {
	  if (!quiet) {
	    printf("Bueargh #3 %i-%i ",i,j);
	    num_print(m->c+matpos2(i,j));
	    printf(" > (");
	    num_print(m->c+matpos2(i,i^1));
	    printf("+");
	    num_print(m->c+matpos2(j^1,j));
	    printf(")/2\n");
	  }
	r = false; goto end;
	}
      }
  }
  if (!quiet) printf("OK\n");
 end:
  num_clear(&w);
  OCT_EXIT("oct_check_closed",38);
 return r;
}


/****************/
/* Minimal form */
/****************/

moct_t*
OCT_PROTO(m_empty) (var_t n)
{
  moct_t* a;
  OCT_ENTER("oct_m_empty",39);
  a = new_t(moct_t);
  a->n = n;
  a->bol = (size_t*)NULL;
  a->col = (var_t*)NULL;
  a->data = (num_t*)NULL;
  OCT_EXIT("oct_m_empty",39);
  return a;
}

moct_t*
OCT_PROTO(m_from_oct) (oct_t* m)
{
  moct_t* a;
  oct_t* cm;
  OCT_ENTER("oct_m_from_oct",40);
  a = oct_m_empty (m->n);
  cm = oct_close (m,false,false);
  if (cm->state!=OCT_EMPTY) {
    const var_t n2 = m->n*2;
    var_t* rep   = new_n(var_t,n2);
    var_t* next  = new_n(var_t,n2);
    var_t* first = new_n(var_t,n2);
    var_t i,j,k,nb;
    size_t n;
    num_t c1,c2;
    /* compute equivalence classes xi<->xj iff m[i][j]+m[j][i]=0 
       next[i] is the smallest index j>i such that xi<->xj (or -1 at the end)
       first[i] is the smallest index j such that xi<->xj
       rep[i] is the last index in the ith equivalence class
     */
    /* maybee we could use union-find instead here ? */
    num_init(&c1); num_init(&c2);
    nb = 0;
    for (i=0;i<n2;i++) {
      for (j=0;j<nb;j++) {
	num_add(&c1,cm->c+matpos(i,rep[j]),cm->c+matpos(i^1,rep[j]^1));
	if (!num_cmp_zero(&c1)) {
	  first[i] = first[rep[j]];
	  next[rep[j]] = i;
	  rep[j] = i;
	  goto notnew;
	}
      }
      rep[nb++] = i;
      first[i] = i;
    notnew:
      next[i] = 0;
    }
    /* make rep monotonic: rep[i]<rep[j] if i<j */
    for (j=0,i=0;i<n2;i++) if (!next[i]) rep[j++] = i;
    /* alloc */
    a->bol = new_n(size_t,n2+1);
    a->col = new_n(var_t,matsize(cm->n));
    a->data = new_n(num_t,matsize(cm->n));
    n = 0;
    for (i=0;i<n2;i++) {
      a->bol[i] = n;
      if (next[i]) {
	a->col[n] = next[i];
	num_init_set(a->data+n,cm->c+matpos(next[i]^1,i^1));
	n++;
      } 
      else {
	const var_t ii = i|1;
	num_div_by_2(&c1,cm->c+matpos(i,i^1));
	for (j=0;j<=ii;j++) {
	  if (j!=i && (j==first[i] || !next[j])) {
	    const num_t* cij = cm->c+matpos(i,j);
	    if (num_infty(cij)) goto redund;
	    if (j==first[i]) goto noredund;
	    num_div_by_2(&c2,cm->c+matpos(j^1,j));
	    num_add(&c2,&c1,&c2);
	    if ((i^1)!=j && !num_cmp(cij,&c2) &&
	    	first[i]!=first[i^1] && first[j]!=first[j^1]) goto redund;
	    for (k=0;k<nb;k++) {
	      const var_t kk = rep[k];
	      if (kk!=i && kk!=j) {
		/* CAN THIS BE LINEARIZED ? (rep is monotonic) */
		num_add(&c2,cm->c+matpos2(i,kk),cm->c+matpos2(kk,j));
		if (!num_cmp(cij,&c2)) goto redund;
	      }
	    }
	  noredund:
	    a->col[n]  = j;
	    num_init_set(a->data+n,cij);
	    n++;
	  redund:;
	  }
	}
      }
    }
    a->bol[i] = n;
    oct_mm_free(rep); oct_mm_free(next); oct_mm_free(first);
    num_clear(&c1); num_clear(&c2);
    a->col = renew_n(a->col,var_t,n+1);
    /* we alloc 1 to size to be sure that a->data is not NULL */
    a->data = renew_n(a->data,num_t,n+1);
  }
  oct_free (cm);
  OCT_EXIT("oct_m_from_oct",40);
  return a;
}


oct_t*
OCT_PROTO(m_to_oct) (moct_t* a)
{
  oct_t* r;
  var_t i;
  size_t n;
  const var_t n2 = a->n*2;
  OCT_ENTER("oct_m_to_oct",41);
  if (!a->col) { r = oct_empty (a->n); goto end; }
  r = oct_universe (a->n);
  for (n=0,i=0;i<n2;i++)
    for (;n<a->bol[i+1];n++) 
      if (!num_infty(a->data+n))
	num_set(r->c+matpos2(i,a->col[n]),a->data+n);
  r->state = OCT_NORMAL;
  if (r->closed) { oct_free(r->closed); r->closed = (oct_t*)NULL; }
 end:
  OCT_EXIT("oct_m_to_oct",41);
  return r;
}

void
OCT_PROTO(m_free) (moct_t* a)
{
  OCT_ENTER("oct_m_free",42);
  if (a->data) { num_clear_n(a->data,a->bol[a->n*2]); oct_mm_free (a->data); }
  if (a->col)  oct_mm_free (a->col);
  if (a->bol)  oct_mm_free (a->bol);
  oct_mm_free (a);
  OCT_EXIT("oct_m_free",42);
}

/* number of variables */
inline
var_t
OCT_PROTO(m_dimension) (moct_t* m)
{
  return m->n;
}

bool
OCT_PROTO(m_is_empty) (moct_t* m)
{
  if (m->data) return false;
  return true;
}


/* print as a constraint list */
void
OCT_PROTO(m_print) (moct_t* a)
{
  var_t i;
  size_t n;
  const var_t n2 = a->n*2;
  OCT_ENTER("oct_m_print",43);
  if (!a->col) printf("[ empty ]\n");
  else {
    printf("[");
    for (n=0,i=0;i<n2;i++)
      for (;n<a->bol[i+1];n++)
	if (!num_infty(a->data+n)) {
	  const var_t j = a->col[n];
	  if (i==(j^1))
	    if (i&1) 
	      { printf("\n   2v%02i    <= ",i/2); num_print(a->data+n); }
	    else     
	      { printf("\n  -2v%02i    <= ",i/2); num_print(a->data+n); }
	  else
	    if (i&1)
	      if (j&1) { 
		printf("\n  -v%02i+v%02i <= ",j/2,i/2); 
		num_print(a->data+n); 
	      }
	      else {
		printf("\n   v%02i+v%02i <= ",j/2,i/2); 
		num_print(a->data+n); 
	      }
	    else
	      if (j&1) { 
		printf("\n  -v%02i-v%02i <= ",j/2,i/2); 
		num_print(a->data+n); 
	      }
	      else { 
		printf("\n   v%02i-v%02i <= ",j/2,i/2); 
		num_print(a->data+n); 
	      }
	}
    printf("  ]\n");
  }
  OCT_EXIT("oct_m_print",43); 
}


/* using binary search on a row: O(log n) time cost */
num_t*
OCT_PROTO(m_elem) (moct_t* a,
		   var_t   i,
		   var_t   j)
{
  num_t* r;
  size_t lo,hi;
  OCT_ENTER("oct_m_elem",44); 
  OCT_ASSERT(a->data,"empty hollow matrix in oct_m_elem");
  OCT_ASSERT(i<a->n*2 && j<a->n*2,"invalid index in oct_m_elem");
  if (j>i) { var_t t = i; i = j^1; j = t^1; }
  lo = a->bol[i];
  hi = a->bol[i+1];
  while (lo<hi) { /* col[lo] <= j < col[hi] */
    size_t mid = (lo+hi)/2;
    if (j==a->col[mid]) { r = a->data+mid; goto end; }
    else if (j<a->col[mid]) hi = mid; else lo = mid+1;
  }
  r = (num_t*) NULL;
 end:
  OCT_EXIT("oct_m_elem",44);
  return r;
}


/* O(n^2) time cost as minimized octagons are also a normal form */
bool
OCT_PROTO(m_is_equal) (moct_t* ma, 
		       moct_t* mb)
{
  bool r = true;
  OCT_ENTER("oct_m_is_equal",45);
  OCT_ASSERT(ma->n==mb->n,"oct_m_is_equal must be called with two octagons of the same dimension.");
  if (!ma->data && !mb->data) r = true;
  else if (!ma->data || !mb->data) r = false;
  else {
    const var_t n2 = ma->n*2;
    const size_t nn = ma->bol[n2];
    size_t i;
    for (i=1;i<=n2;i++)
      if (ma->bol[i]!=mb->bol[i]) { r = false; goto end; }
    for (i=0;i<nn;i++)
      if (ma->col[i]!=mb->col[i]) { r = false; goto end; }    
    for (i=0;i<nn;i++)
      if (num_cmp(ma->data+i,mb->data+i)) { r = false; goto end; }    
    r = true;
  }  
 end:
  OCT_EXIT("oct_m_is_equal",45);
  return r;
}


/*****************/
/* Serialization */
/*****************/

/* this only works for a few underlying numerical domains! */
/* octagon serialized on an architecture with a numerical type may not be
   deserialized on another architecture, or with a different numerical type */

#ifdef OCT_NUM_SERIALIZE

void*
OCT_PROTO(serialize) (oct_t* m, size_t* size)
{
  size_t sz = 16, max = 100;
  unsigned char* data;
  if (m->closed) m=m->closed;
  data = new_n(unsigned char,max);
  dump32(data,num_serialize_id);
  dump32(data+4,m->n);
  dump32(data+8,m->state);
  if (m->state!=OCT_EMPTY) {
    const size_t nn = matsize(m->n);
    size_t i;
    for (i=0;i<nn;i++) {
      int s = num_serialize_size(m->c+i);
      while (s+sz>=max) { max*=2; data = renew_n(data,unsigned char,max); }
      sz += num_serialize(m->c+i,data+sz);
    }
  }
  *size = sz;
  return data;
}

oct_t*
OCT_PROTO(deserialize) (void* d)
{
  unsigned char* data = (unsigned char*)d;
  int id;
  var_t n;
  int state;
  size_t pos = 16;
  id = undump32(data);
  OCT_ASSERT(id==num_serialize_id,"oct_deserialize: incompatible serialized octagon");
  n = undump32(data+4);
  state = undump32(data+8);
  if (state==OCT_EMPTY) return(oct_empty(n));
  else {
    const size_t nn = matsize(n);
    size_t i;
    oct_t* m = oct_alloc(n);
    m->state = state;
    for (i=0;i<nn;i++)
      pos += num_deserialize(m->c+i,data+pos);
    return(m);
  }
}

void*
OCT_PROTO(m_serialize) (moct_t* m, size_t* size)
{
  size_t sz = 16, max = 100;
  unsigned char* data;
  data = new_n(unsigned char,max);
  dump32(data,num_serialize_id);
  dump32(data+4,m->n);
  if (!m->bol) {
    /* empty */
    dump32(data+8,0);
  }
  else {
    /* non-empty */
    const var_t  n2 = m->n*2;
    const size_t nn = m->bol[n2];
    size_t i;
    dump32(data+8,1);
    dump32(data+12,nn);
    max += 2*(nn+n2);
    data = renew_n(data,unsigned char,max);
    for (i=1;i<=n2;i++,sz+=2)  dump16(data+sz,m->bol[i]-m->bol[i-1]);
    for (i=0;i<nn;i++,sz+=2)   dump16(data+sz,m->col[i]);
    for (i=0;i<nn;i++) {
      int s = num_serialize_size(m->data+i);
      while (s+sz>=max) { max*=2; data = renew_n(data,unsigned char,max); }
      sz += num_serialize(m->data+i,data+sz);
    }
  }
  *size = sz;
  return data;
}

moct_t*
OCT_PROTO(m_deserialize) (void* d)
{
  unsigned char* data = (unsigned char*)d;
  int id;
  var_t n;
  int state;
  size_t pos = 16;
  id = undump32(data);
  OCT_ASSERT(id==num_serialize_id,"oct_m_deserialize: incompatible serialized octagon");
  n = undump32(data+4);
  state = undump32(data+8);
  if (state) {
    const var_t n2 = n*2;
    const size_t nn = undump32(data+12);
    size_t i;
    moct_t* m;
    m = new_t(moct_t);
    m->n = n;
    m->bol = new_n(size_t,n2+1);
    m->col = new_n(var_t,nn);
    m->data = new_n(num_t,nn);
    m->bol[0] = 0;
    num_init_n(m->data,nn);
    for (i=1;i<=n2;i++,pos+=2) m->bol[i] = m->bol[i-1] + undump16(data+pos);
    for (i=0;i<nn;i++,pos+=2)  m->col[i] = undump16(data+pos);
    for (i=0;i<nn;i++)
      pos += num_deserialize(m->data+i,data+pos);
    return m;
  }
  else return(oct_m_empty(n));
}

#else

void*
OCT_PROTO(serialize) (oct_t* m, size_t* size)
{
  OCT_ASSERT(0,"oct_serialize: serialization not supported for this underlying numerical domain.");
}

oct_t*
OCT_PROTO(deserialize) (void* data)
{
  OCT_ASSERT(0,"oct_deserialize: serialization not supported for this underlying numerical domain.");
}

void*
OCT_PROTO(m_serialize) (moct_t* m, size_t* size)
{
  OCT_ASSERT(0,"oct_m_serialize: serialization not supported for this underlying numerical domain.");
}

moct_t*
OCT_PROTO(m_deserialize) (void* data)
{
  OCT_ASSERT(0,"oct_m_deserialize: serialization not supported for this underlying numerical domain.");
}


#endif
