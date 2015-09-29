/* ----------------------new definitions to avoid LMPOLs--------------------------------- */
typedef struct{
	int npols;
	MPOL *polp;
} polsettype;

typedef struct{
  MPOL *p1, *p2;
} polpairtype;

typedef struct{
  int npairs, maxpairs;
  polpairtype *COUNT(maxpairs) polpair;
} polpairsettype;

#define lpp_lbd_pair(p1,p2,exp) expomax(MEXPO((p1),0), MEXPO((p2),0),(exp), nvars)
#ifndef NULL
#define NULL 0
#endif

void new_mpolsetadd(polsettype *s, MPOL *p);
void new_update_pairs(polpairsettype *spair, polsettype *spol, MPOL *p);
void new_choose_pair(polpairsettype *sp, MPOL **p1, MPOL **p2);
MPOL *new_redfast2(MPOL *p, MPOL *nextp);
void spolfast(MPOL *p, MPOL *q, MPOL *r);
void itimerinit(int timerid, int setval);
