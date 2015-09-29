#include <stdio.h>
#include <hslib.h>
#define MAXVARS 100

#ifndef	MINIT

typedef struct {
	int len;
 	/* The sign is stored in len, which leads to a rather strange and
	   complex bound.
	   The good: you can use complex expressions here :-)
	   The bad: performance suffers - it would probably be better to just 
	     use a separate sign bit */
        short *COUNT(len + (len < 0) * 2 * -len) val;
} MINT;

/* Users should avoid these in general	*/
#define vfree(u) free(u)
#define valloc(x,i) (((x) = HS_ARRAYALLOC(short, 2 * (i))) == 0 ? valerr() : 0)

/*	Initialization macros--every new variable 
	be initialized with one of these macros	*/
#define MINIT(x) ((x)->len=0)
static inline void MSET(short c, MINT *x)
{
  x->val = NULL;

  if (c == 0)
    x->len = 0;
  else if (c > 0)
    {
      x->len = 1;
      valloc(x->val, 1);
      *x->val = c;
    }
  else
    {
      x->len = -1;
      valloc(x->val, 1);
      *x->val = -c;
    }
}

#define MMOVE(x,y) (MMOVEFREE(x,y), MINIT(x))
#define MCOPY(x,y) (MINIT(y), mcopy(x,y))

/* Every MINT should be garbage collected with one of these before being 
	abandoned */
#define MFREE(x) (((x)->len!=0) ? (HS_ZFREE((x)->val), (x)->len = 0) : 0)
#define MMOVEFREE(x,y) (*(y) = *(x))

/* Other useful statement macros */
#define mmove(x,y) (MFREE(y), MMOVE(x,y))
#define mset(c,x) (MFREE(x), MSET(c,x))
#define mnegate(x) ((x)->len = -(x)->len)

/*	Sign testing macro 	*/
#define mtest(x)	((x)->len)

/* 	Test if a MINT and a short have same value */
#define meqshort(p,q) (((p)->len!=1) ? 					     \
				(((p)->len!=(-1)) ? 0:((p)->val[0]==(-(q)))) \
				 : ((p)->val[0]==(q)))

/*	Bit test macro */
#define modd(x)		(((x)->len != 0) ? ((x)->val[0] & 0x1) : 0)
#define	mlowbits(x)	(((x)->len != 0) ? ((x)->val[0]) : 0)
			/* guaranteed 15 bits */


/*
 * HISTORY
 *
 *  3 DEC 93 Soumen. #define flag for interrupt or poll. All .c files updated.
 *  7 JUL 92 Soumen. Renamed calls to malloc and free as xalloc and xfree so
 *           that mark-release memory allocation can be used. For grobner basis.
 *
 * 9-June-87 Jean-Philippe Vidal at Carnegie-Mellon University changed malloc
 *           and free in (*malloc_f) and (*free_f) to test several allocation
 *           policies.
 *
 * 14-Apr-87  Jean-Philippe Vidal at Carnegie-Mellon University
 *      Added the macro meqshort()
 *
 * 07-Dec-87  Bennet Yee (bsy) at Carnegie-Mellon University
 *	Added mlowbits().
 *
 * 22-Jan-87  Bennet Yee (byee) at Carnegie-Mellon University
 *	Added #ifndef MINIT to prevent multiple inclusion.
 *	Added htonm (host-to-network-mint, ala byteorder(3N)).
 *
 * 03-Dec-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created.  Based in part on existing mp package.
 * 09-apr-92
 */

void valerr(void);

int expoequal(short int *COUNT(nvars + 1) exp1, 
	      short int *COUNT(nvars + 1) exp2, int nvars) hs_nofree;
void expocopy (short int *COUNT(nvars + 1) exp1, 
	       short int *COUNT(nvars + 1) exp2, int nvars) hs_nofree;
int expozero(short int *exp, int nvars) hs_nofree;
void exposub(short int *COUNT(nvars + 1) exp1, 
	     short int *COUNT(nvars + 1) exp2, 
	     short int *COUNT(nvars + 1) exp3, int nvars) hs_nofree;
void expoadd(short int *COUNT(nvars + 1) exp1, 
	     short int *COUNT(nvars + 1) exp2,
	     short int *COUNT(nvars + 1) exp3, int nvars) hs_nofree;
void expomax(short int *COUNT(nvars + 1) exp1,
	     short int *COUNT(nvars + 1) exp2,
	     short int *COUNT(nvars + 1) exp3, int nvars) hs_nofree;
int expodiv (register short int *COUNT(nvars + 1) exp1, 
	     register short int *COUNT(nvars + 1) exp2, int nvars) hs_nofree;
int expostrictdiv(short int *COUNT(nvars + 1) exp1,
		  short int *COUNT(nvars + 1) exp2, int nvars) hs_nofree;
void expofactor(short int *COUNT(nvars + 1) exp1, 
		short int *COUNT(nvars + 1) exp2,
		short int *COUNT(nvars + 1) exp3, int nvars) hs_nofree;
int expocrit2(short int *COUNT(nvars + 1) exp1,
	      short int *COUNT(nvars + 1) exp2, int nvars) hs_nofree;

void m_add (MINT *a, MINT *b, MINT *c);
void madd (MINT *a, MINT *b, MINT *c);
void m_sub (MINT *a, MINT *b, MINT *c);
void msub (MINT *a, MINT *b, MINT *c);
void mdiv (MINT *a, MINT *b, MINT *q, MINT *r);
void mpfatal (char *NTS s);
int mtod (MINT *a, MINT *b, double *d);
int mlog (MINT *a);
void mshiftl (MINT *a, int b);
void mshiftr (MINT *a, int b);
void mgcd (MINT *a, MINT *b, MINT *c);
void minvert (MINT *a, MINT *b, MINT *c);
void mmult (MINT *a, MINT *b, MINT *c);
int m_in (MINT *a, int b, FILE *f);
int m_in_b (MINT *a, int b, FILE *f, int blanks);
static int slog (int n);
void m_out (MINT *a, int b, FILE *f);
void m_out_b (MINT *a, int b, FILE *f, int blanks);
void sdiv (MINT *a, int n, MINT *q, short *r);
int gmin (MINT *a);
int omin (MINT *a);
void mout (MINT *a);
void omout (MINT *a);
void hexmout (MINT *a);
void fmout (MINT *a, FILE *f);
int hexmin (MINT *a);
int fmin2 (MINT *a, FILE *f);
void Sm_out_b (char *NTS s, MINT *a, int b, int blanks);
void Sm_out (char *NTS s, MINT *a, int b);
void Smout (char *NTS s, MINT *a);
void mstrtoul (MINT *a, char *NTS s, char *NTS *p, short int b);
void mcopy (MINT *a, MINT *b);
int mcmp (MINT *a, MINT *b);

void	(*PollPtr)();

void init_order_exp(void);
int (*cmp_exp)(short int *COUNT(nvars + 1) exp1,
	       short int *COUNT(nvars + 1) exp2, int nvars) hs_nofree;

#endif

