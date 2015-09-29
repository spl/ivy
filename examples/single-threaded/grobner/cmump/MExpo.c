#include "cmump.h"
#include "multpol.h"

int expoequal(short int *exp1, short int *exp2, int nv) hs_nofree
{
	register i;

	if(exp1[0]!=exp2[0])
		return(0);
	for(i=1;i<=nv;i++)
		if(exp1[i]!=exp2[i])
			return(0);
	return(1);
}


void expocopy (short int *exp1, short int *exp2, int nv) hs_nofree
{
	bcopy ( exp1, exp2, (nv+1)*sizeof(short) );
}


int expozero(short int *exp, int nv) hs_nofree
{
	return((exp[0]==0) ? 1 : 0);
}


void exposub(short int *exp1, short int *exp2, short int *exp3, int nv) hs_nofree
{
  register short *p1,*p2;
  register i;

  p1=exp1;
  p2=exp2;
  for (i=0;i<=nv;i++) exp3[i]=(*(p1++)-(*(p2++)));
}



void expoadd(short int *exp1, short int *exp2, short int *exp3, int nv) hs_nofree
{
  register short *p1,*p2;
  register i;

  p1=exp1;
  p2=exp2;
  for (i=0;i<=nv;i++) exp3[i]=(*(p1++)+(*(p2++)));
}


void expomax(short int *exp1, short int *exp2, short int *exp3, int nv) hs_nofree
{
  register i;

  exp3[0]=0;
  for (i=1;i<=nv;i++) 
	exp3[0] += (exp3[i]= (exp1[i]>exp2[i]) ? exp1[i] : exp2[i]);
}


int expodiv (register short int *_exp1, register short int *_exp2, int nv) hs_nofree
{
	short *exp1 = _exp1, *exp2 = _exp2;
	register short *last = exp1 + (int)(nv+1);

	while ( exp1 < last )
		if ( *(exp1++) > *(exp2++) )
			return 0;
	return 1;
}



/* expostrictdiv : returns 1 if exp1[i] <= exp2[i] for all i 
and exp1[i] < exp2[i] for at least one i. */

int expostrictdiv(short int *exp1, short int *exp2, int nv) hs_nofree
{
  register i;

  if (exp1[0]>=exp2[0]) return(0);
  for (i=1;(i<=nv) && (exp1[i]<=exp2[i]);i++);
  return (i==(nv+1)) ? 1 : 0;
}


/* expofactor : find exp3 such that exp1 + exp3 = sup(exp1,exp2) */

void expofactor(short int *exp1, short int *exp2, short int *exp3, int nv) hs_nofree
{
  register i;

  exp3[0]=0;  
  for (i=1;i<=nv;i++) {
	exp3[i]= exp2[i]-exp1[i];
	if (exp3[i]<0) exp3[i]=0;
	exp3[0]+=exp3[i];
  }
}


/* tests if the two power products do not have any factor in common */

int expocrit2(short int *exp1, short int *exp2, int nv) hs_nofree
{
  register i;

  for (i=1;(i<=nv) && ((exp1[i]==0)||(exp2[i]==0));i++);
  return (i==(nv+1));
}



/* Now come all the different orders. One or the other will be chosen, depending on
** the value of the parameter order_exp. This will be done in the function order_init
** which must be called before any use of this package.
*/


static int cmp_lex_exp(short int *COUNT(nv + 1) exp1,
		       short int *COUNT(nv + 1) exp2, int nv)  hs_nofree

/* cmp_lex_exp -- integer function returning 1 (resp -1,0) if the exponent 
pointed to by the first pointer is greater than (resp less than, equal to) the 
exponent pointed to by the second pointer in the lexicographical ordering. */

{
  register i;

  for (i=1;(i<=nv) && (exp1[i]==exp2[i]);i++);
  if (i==nv+1) return(0);
  return((exp1[i]>=exp2[i])?1:-1);}




static int cmp_td_exp(short int *COUNT(nv + 1) exp1,
		      short int *COUNT(nv + 1) exp2, int nv) hs_nofree

/* cmp_td_exp -- integer function returning 1 (resp -1,0) if the exponent 
pointed to by the first pointer is greater than (resp less than, equal to) the 
exponent pointed to by the second pointer in the total order refined by the 
lexicographic order. */

{
  register i;

  for (i=0;(i<nv+1) && (exp1[i]==exp2[i]);i++);
  if (i==nv+1) return(0);
  return((exp1[i]>=exp2[i])?1:-1);}



static int cmp_revlex_exp(short int *COUNT(nv + 1) exp1,
			  short int *COUNT(nv + 1) exp2, int nv) hs_nofree

/* cmp_revlex_exp -- integer function returning 1 (resp -1,0) if the exponent 
pointed to by the first pointer is greater than (resp less than, equal to) the 
exponent pointed to by the second pointer in the total order refined by the 
reverse lexicographic order. */

{
  register i;

  if (exp1[0]!=exp2[0])
	return((exp1[0]>exp2[0])?1:-1);
  else {
  	for (i=nv;(i>0) && (exp1[i]==exp2[i]);i--);
  if (i==0) return(0);
  return((exp1[i]<=exp2[i])?1:-1);}
}


static int cmp_double_revlex_exp(short int *COUNT(nv + 1) exp1,
				 short int *COUNT(nv + 1) exp2, int nv) hs_nofree

/* cmp_double_revlex_exp -- integer function returning 1 (resp -1,0) if the exponent 
pointed to by the first pointer is greater than (resp less than, equal to) the 
exponent pointed to by the second pointer in the following order : total order 
refined by the reverse lexicographic order on the first "first_group" variables 
refined by the same order on the other variables. */

{
  register i,f1,f2;

  f1=0;f2=0;
  for (i=1;i<first_group+1;i++){ f1 += exp1[i]; f2 += exp2[i];}
  if (f1!=f2)
	return((f1>f2)?1:-1);
  for (i=first_group+1;(i>0) && (exp1[i]==exp2[i]);i--);
  if (i!=0) return((exp1[i]<exp2[i]) ? 1 : -1);
  if ((exp1[0]-f1) != (exp2[0]-f2)) 
	return (((exp1[0]-f1)> (exp2[0]-f2))?1:-1);
  for (i=nv;(i>first_group+1) && (exp1[i]==exp2[i]);i--);
  if (i==first_group+1) return(0);
  return ((exp1[i]<=exp2[i])?1:-1);
}


int (*cmp_exp)(short int *exp1, short int *exp2, int nv) hs_nofree;

void init_order_exp(void)
{
	switch(order_exp){
	case 0 : cmp_exp = cmp_lex_exp;
		 break;
	case 1 : cmp_exp = cmp_td_exp;
		 break;
	case 2 : cmp_exp = cmp_revlex_exp;
		 break;
	case 3 : cmp_exp = cmp_double_revlex_exp;
		 break;
	}
}


