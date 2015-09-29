#define INTR 1 /* 0: poll, 1: intr */

/* We want to use different representations for the polynomials and be able
** to choose it by a switch in the program.
**
** The exponents are given by an array of integers whose first member is
**  the total degree of the exponent.
**
** The only variation in the representation is the order according to which 
** the monomials are sorted ? The parameter is order_exp. We have the following 
** possibilitites :
**		- lexicographic ordering : order_exp = 0
**		- total degree ordering refined by lexicographic : 
**						order_exp = 1
**		- total degree ordering refined by reverse lexicographic :
**						order_exp = 2
**		- we split the variables in two groups. The size of the first
**		  group is determined by the parameter first_group.
**		  We use the total degree ordering refined by reverse 
**		  lexicographic ordering on the variables of the first group.
**	  	  In case of equality, we do the same thing with the second
**		  group :			order_exp = 3
*/

#define MAX_VARS 50                  /* maximum number of variables */
extern short nvars;                  /* actual number of variables  */
extern int order_exp, first_group;
extern char *NTS (COUNT(nvars) varnames)[];

/* -------------------- Type declaration of MPOL -------------------------- */
typedef struct mpt{
	int			owner;		/* generator of the mpol */
	int			ppid;		/* pe-wise unique id number */
	int			compact;	/* whether in compact form or not */
	struct mpt	*next;		/* next pointer */

	short		nterms;
	short		maxterms;	/* Set by POL_ALLOC to size of alloc space */
	short		nvp1;
	MINT		*COUNT(maxterms) coefs;
	short		*COUNT(maxterms * nvp1) expos;
	int		reducible;
} MPOL;


/* Initialization macros--every new variable should be initialized with one of these macros */

#define MPOLINIT(p) { (p)->nterms = (p)->maxterms = (p)->compact = 0; }

#define MPOLMONSET(coef,expo,p) \
	if ((coef)->len==0) { \
		(p)->nterms = 0; \
		(p)->maxterms = 0; \
	} else { \
		(p)->nterms = 1; \
		POL_ALLOC(p,1); \
		MCOPY(coef,&((p)->coefs[0])); \
		expocopy(expo,(p)->expos,(p)->nvp1-1);  \
	}

#define MPOLMONMOVE(coef,expo,p) \
	if ((coef)->len==0) {  \
		(p)->nterms = 0; \
		(p)->maxterms = 0; \
	} else { \
		(p)->nterms = 1; \
		POL_ALLOC(p,1); \
		MMOVE(coef,&((p)->coefs[0])); \
		expocopy(expo,(p)->expos,(p)->nvp1-1);  \
	}

#define MPOLMOVE(p,q) (MPOLMOVEFREE(p,q),MPOLINIT(p))

/* Other useful statement macros */

#define mpolmonset(coef,expo,p)  mpolfree(p);MPOLMONSET(coef,expo,p)
#define mpolmonmove(coef,expo,p) mpolfree(p);MPOLMONMOVE(coef,expo,p)
			      
                             
/* Every MPOL should be garbage collected with mpolfree or one of these before
   being abandoned */

#define MPOLMOVEFREE(p,q) (*(q) = *(p))

/* Test : is the polynomial equal to zero ? */
#define MPOLZERO(p) ((p)->nterms == 0)

/* Users should avoid these. */

static inline void POL_ALLOC(MPOL *p, short size)
{
  p->coefs = NULL;
  p->expos = NULL;
  p->maxterms = size;
  p->nvp1 = nvars + 1;
  p->coefs = HS_ARRAYALLOC(MINT, size);
  p->expos =HS_ARRAYALLOC(short, size * (nvars + 1));
  if (!p->coefs || !p->expos) 
    valerr();
}

#define MEXPO(p, it) (short *) ((p)->expos + (p)->nvp1 * (it))
#define MPOW(p, it, ivar) (short *) ((p)->expos + (p)->nvp1 * (it) + (ivar) + 1)

#define	_proto_multpol_
#ifdef	_proto_multpol_

void	mpoladd ( MPOL *p, MPOL *q, MPOL *r );
void	mpolcopy ( MPOL *p, MPOL *q );
void	mpolfree ( MPOL *p );
int		mpolin ( MPOL *p );
void	mpolmult ( MPOL *p, MPOL *q, MPOL *r );
void	mpolout ( MPOL *p );
void	Smpolout ( char *NTS s, MPOL *p );
void	mpolsub ( MPOL *p, MPOL *q, MPOL *r );
void	mpolunit ( MPOL *p, MINT *c, MPOL *q );

void	(*PollPtr)();

#endif


