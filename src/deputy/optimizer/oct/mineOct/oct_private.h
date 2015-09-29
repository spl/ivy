/* oct_private.h
   Include this in order to access to low-level octagon data structures.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */
#ifndef OCT_PRIVATE_H__
#define OCT_PRIVATE_H__

#include <oct.h>

#ifdef __cplusplus
extern "C" {
#endif


/* Shortcuts */
/* --------- */

#define oct_alloc               OCT_PROTO(alloc)
#define oct_full_copy           OCT_PROTO(full_copy)
#define oct_close               OCT_PROTO(close)
#define oct_is_closed           OCT_PROTO(is_closed)
#define oct_close_lazy          OCT_PROTO(close_lazy)
#define oct_check_closed        OCT_PROTO(check_closed)
#define oct_m_elem              OCT_PROTO(m_elem)
#define oct_close_incremental   OCT_PROTO(close_incremental)


/************/
/* Octagons */
/************/

/*
  Unlike the presentation of the article "The Octagonal Abstract Domain",
  there is no redundancy in the internal representation of the invariants.
  This is achevied by storing m[i][j] only if i>=j or i=j^1.
  There is no loss of information because, by coherence, m[j^1][i^1]=m[i][j].
  In memory, the matrix has approximately the form of a triangle:

      j ->  0 1 2 3 4 5
            ___
        0  |_|_|
        1  |_|_|___
  i ->  2  |_|_|_|_|
        3  |_|_|_|_|___
        4  |_|_|_|_|_|_|
        5  |_|_|_|_|_|_|

  In the following we will use the term 'matrix' even if the representation
  no longer has a matrix form.
  The elements are stored in a flat array with m[i][j] beeing stored in
  c[j+((i+1)*(i+1))/2].

  There is no longer an emptyness test as emptyness is tested during the
  closure.

  Memory managment is a little complex in order to avoid unnecessary copy,
  closure or emptyness checking.
  All operators come in 2 forms: a copy form that protects all arguments,
  and a in-place form that destroys the arguments and is more efficient.
  There is also reference counting so that copy versions of operators can
  return the one of the argument without having to copy it (union when one
  argument is empty, for example).
  This results in a lazy copy-on-write policy saying that we must perform
  an actual copy only when modifing in-place a matrix that have a
  reference count > 1.
  The last mechanism is remembering of closure form. When the argument of
  an operator must be closed, but must stay accessible in its original form
  (either we use the copy form of the operator, or the argument has a
  reference count > 1); we keep the closed form in memory and add a pointer
  from the original unchanged argument to its closed form we just computed.
  If the arguement is used again with an operator requiring the normal form,
  the stored form is reused and no extra closure algorithm is performed.
  (this mechanism can be turned off manually if we are short of memory,
  this can result in time inefficiency).

*/

/* nb of elements in a matrix with n variables */
#define matsize(n)   (2*(size_t)(n)*((size_t)(n)+1))

/* xj - xi <= m->c[matpos(i,j)], if j/2 <= i/2 */
#define matpos(i,j)  ((size_t)(j)+(((size_t)(i)+1)*((size_t)(i)+1))/2)

/* xj - xi <= m->c[matpos2(i,j)] for all i,j */
#define matpos2(i,j) ((j)>(i)?matpos(((j)^1),((i)^1)):matpos(i,j))

/* state of a matrix representing an octagon */
typedef enum {
  OCT_EMPTY  = 0,         /* empty domain */
  OCT_NORMAL = 1,           
  OCT_CLOSED = 2
} oct_state;


/* octagon data structure */
struct oct_tt {
  var_t          n;       /* number of variables, aka dimension */

  int            ref;     /* reference counting */

  oct_state      state;   /* is it empty, closed, etc. ? */
  struct oct_tt* closed;  /* pointer to the closed version, or NULL */

  num_t*         c;       /* the matrix, contains matsize(n) elements */
};

/* private because not really useful for user */
oct_t* OCT_PROTO(alloc)     (var_t  n);   /* c allocated but not initialized */
oct_t* OCT_PROTO(full_copy) (oct_t* m);   /* new copy with ref=1 */

/* strong closure */
oct_t* OCT_PROTO(close)      (oct_t* m, bool destructive, bool cache); 
bool   OCT_PROTO(is_closed)  (oct_t* m);
oct_t* OCT_PROTO(close_lazy) (oct_t* m, bool destructive);

bool   OCT_PROTO(check_closed) (const oct_t* m, bool quiet);  /* for debugging purpose */
void OCT_PROTO(close_incremental)  (oct_t* m, var_t v);


/* low-level access to an element 
   get the element m[i][j]            */
static inline
num_t*
oct_elem (oct_t* m,
	  var_t  i,
	  var_t  j)
{
  OCT_ASSERT(m->c,"matrix not allocated in oct_elem");
  OCT_ASSERT(i<2*m->n && j<2*m->n,"invalid index in oct_elem");
  return m->c+matpos2(i,j);
}


/* Octagon in hollow form, 
   cannot be modified in-place !
*/

struct moct_tt {
  var_t     n;     /* number of variables */
  
  size_t*   bol;   /* begin-of-line indices, array of n*2+1 indices */
  var_t*    col;   /* column indices, array of bol[n*2] elements */
  num_t*    data;  /* constraint array of bol[n*2] elements */
  /* data[i] contains the original matrix element at position
       col[i],
       line l, such that bol[l] <= i < bol[l+1]
   */
  /* all fields are NULL if the octagon is empty */
};


/* no direct access, O(log n) time cost */
num_t* OCT_PROTO(m_elem) (moct_t* a, var_t i, var_t j);


/**********/
/* Memory */
/**********/

/* a memory monitor */
struct mmalloc_tt
{
  int    id;         /* incremented after a reset */

  int    nb_alloc;   /* nb of calls to malloc */
  int    nb_realloc; /* nb of calls to realloc */
  int    nb_free;    /* nb of calls to free */

  size_t rem;        /* memory consumption */
  size_t max;        /* max memory consumption */
  size_t tot;        /* total allocated */

};




#ifdef __cplusplus
}
#endif

#endif
