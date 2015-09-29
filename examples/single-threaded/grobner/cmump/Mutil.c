#include <stdio.h>
#include "cmump.h"

void mcopy(MINT *a, MINT *b)
{	register i,j;
	register short *aval, *bval;

	MFREE(b);
	b->len = i = a->len;
	if (i==0) return;
	else if (i<0) i = -i;

	aval = a->val;	
	valloc(bval,i);
	for (j=i; (--j)>=0;) bval[j] = aval[j];
	b->val = bval;
	return;
}

void valerr(void) {
	mpfatal("cmump: no free space");
}

int mcmp(MINT *a, MINT *b)
{	register neg,p,q,i;
	register short *aval, *bval;

	p = a->len;
	q = b->len;
	if (p != q) return (p-q);
	if (p == 0) return (0);
	if (p < 0) {neg = 1; p = -p;}
	else neg = 0;

	aval = a->val;
	bval = b->val;
	for (i=p; (--i)>=0;) {
		p = aval[i];
		q = bval[i];
		if (p != q) break;
	}
	if (neg) return(q-p);
	else return(p-q);

}

/* HISTORY
 *
 * 23-Apr-87  Bennet Yee (byee) at Carnegie-Mellon Unviersity
 *	Moved fatal to Mfatal.c to allow user to supply own.
 *
 * 18-May-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created from code in existing mp package. *
 *	Debugged, cleaned up, and sped up. *
 */
