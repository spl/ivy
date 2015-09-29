#include <stdio.h>
#include "cmump.h"

#define S2	x += aval[i-j] * bval[j];	\
		if (x & 020000000000)		\
		{	x &= 017777777777;	\
			carry += 1;		\
		}

#define S5	cval[i]= x & 077777;	\
		x>>=15;			\
		carry <<= 16;		\
		x |= carry;

void mmult(MINT *a, MINT *b, MINT *c)
{
    register  carry,i,j,x;
    register short *aval, *bval;
    short *cval;
    int alen, blen, clen, sign;
#ifdef DEBUG
    if (1) {printf("\n"); mout(a); printf(" * ");mout(b);printf(" = ");}
#endif

    alen = a->len;
    blen = b->len;
    if (alen == 0 || blen == 0) {
	mset(0,c);
	return;
    }

    sign = 1;
    if (alen < 0) { alen = -alen; sign = -1; }
    if (blen < 0) { blen = -blen; sign = -sign; }

    if (alen < blen) {
	i = alen;  alen = blen;  blen = i;
	bval = a->val; aval = b->val;
    }
    else { aval = a->val; bval = b->val; }

    clen = alen+blen;
    valloc(cval, clen);

    if (blen == 1) {
	/*  We eliminate a lot of loop overhead on this common case. */
	x = 0;
	j = bval[0];
	bval = cval;
	for (i=0; i<alen; i++) {
	    x += j * aval[i];
	    bval[i] = x & 077777;
	    x >>= 15;
#if (! INTR)
	    (*PollPtr)();
#endif
	}
	bval[i] = x;
	if (x == 0) clen = i;    /* clen = alen+blen-1 == alen */
    }
    else {
	x = 0;
	for(i=0;i<blen;i++) {
#if (! INTR)
	  (*PollPtr)();
#endif
	  carry=0;
	  for(j= i+1; (--j) >= 0;) { S2 }
	  S5
	}
	for(;i<alen;i++) {
#if (! INTR)
	  (*PollPtr)();
#endif
	  carry=0;
	  for(j=blen; (--j) >= 0;) { S2 }
	  S5
	}
	for(;i<clen; i++) {
#if (! INTR)
	  (*PollPtr)();
#endif
	  carry=0;
	  for(j=i-alen+1; j<blen; j++) { S2 }
	  S5
	}
	if(cval[--i]==0) clen = i;  /* clen = alen+blen-1 */
    }
    MFREE(c);
    c->len = sign * clen;
    c->val = cval;

#ifdef DEBUG
    if (1) { mout(c); printf("; %d ", blen); putchar('\n'); }
#endif
}



/* HISTORY
 * 07-Dec-84  Rex Dwyer (rad) at Carnegie-Mellon University
 *	Created.  Based in part on existing mp package.
 */
