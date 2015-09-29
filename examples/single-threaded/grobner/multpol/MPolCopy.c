#include"cmump.h"
#include "multpol.h"


void mpolcopy(MPOL *p, MPOL *q)
{ 
  MPOL temp;
  int i;

  MPOLINIT(&temp);
  temp = *p;
  temp.nterms = p->nterms;
  POL_ALLOC(&temp,p->nterms);
  for (i=0;i<(p->nterms)*p->nvp1;i++) temp.expos[i]=(p->expos[i]);
  for (i=0;i<p->nterms;i++){
	MINIT(&(temp.coefs[i]));
	mcopy(&(p->coefs[i]),&(temp.coefs[i]));
  };
  mpolfree(q);
  MPOLMOVEFREE(&temp,q);
};
