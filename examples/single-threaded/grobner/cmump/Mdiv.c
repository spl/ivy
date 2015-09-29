#include <stdio.h>
#include "cmump.h"
#include "multpol.h"

static int m_dsb(int qq, int nn, short int *COUNT(nn) aa, short int *COUNT(nn + 1) bb)  hs_nofree
{
	register short *a, *b;
	register x,q,j,n;

	q = qq; a = aa; b = bb; n = nn;
	/* Step D4: Multiply and subtract. */
	x=0;
	for (j = 0; j < n; j++ ) {
		x += *b - *a++ * q;
		*b++ = x & 077777;
		x >>= 15;
#if (! INTR)
		(*PollPtr)();
#endif
	}
	x	+= *b;
	*b	= x&077777;
	/* Step D5: Test Remainder. */
	if (x >> 15 == 0) { return 0;}
	/* Step D6: Add back. */
	x=0; a = aa; b = bb;
	for (j = 0; j < n; j++) {
		x += *a++ + *b;
		*b++ = x & 077777;
		x >>= 15;
#if (! INTR)
		(*PollPtr)();
#endif
	}
	return 1;
}

#define NEGQ 2
#define NEGR 1

/*  See Knuth, Vol. 2 for an explanation of this algorithm   */

void mdiv(MINT *a, MINT *b, MINT *q, MINT *r)
{
	MINT		u,v;
	short		*qval, rr;
	register	v1,v2,j;
	register short	*uj;
	int		sign, alen, blen, qlen, i, shift, v12;

#ifdef DEBUG
	printf("\n%d / %d = %d , %d", (int) a, (int) b, (int) q, (int) r);
	printf("\n"); mout(a); printf(" (%d) / ", a->len);
	mout(b);printf(" (%d)",b->len);
#endif
	alen = a->len;
	sign = 0;
	if (alen < 0) { sign = NEGQ|NEGR ; alen = -alen; }
	blen = b->len;
	if (blen < 0) { sign ^= NEGQ; blen = -blen;}

	if (blen == 0) { mpfatal("mdiv divide by zero");
	} else if (alen < blen) {
		if (a != r) mcopy(a,r);
		/*
		 * this stmt must come before zeroing q since a and q may be
		 * identical
		 */
		mset(0,q);
	} else if (blen == 1) {
		MINIT(&u);
		v.len = alen; v.val = a->val;
		sdiv(&v,b->val[0],&u,&rr);
		mset(rr, r);
		mmove(&u, q);
		if (sign & NEGQ) mnegate(q);
		if (sign & NEGR) mnegate(r);
	} else {
		/* Step D1: Normalize */
		/* Make u be one word longer than a, but equal */
		{
			register short *av, *uv;
			u.len = alen+1;
			valloc(u.val, u.len);
			uv = u.val;
			av = a->val;
			for (j = alen, uv[j]=0; --j >= 0;) *uv++ = *av++;
		}
		v.len	= blen;
		v.val	= b->val;

		v1	= v.val[blen-1];
		j	= 14;
		while (v1 >>= 1)  --j;
		shift = j;
		mshiftl(&u, j);
		mshiftl(&v, j);
	
		/* Step D2: Initialize */
		v1	= v.val[blen-1];
		v2	= v.val[blen-2];
		v12	= (v1<<15) | v2;
		qlen	= alen-blen+1;
		valloc(qval, qlen);

		for (i = qlen, uj = &u.val[alen]; --i >= 0;  uj--) {
			/* Step D3: Calculate qhat. */
			register qhat, uj01;
			j = *uj;
			uj01 = (j<<15) | *(uj-1);
			qhat = (j == v1) ? 077777 : (uj01 / v1);
			/*
			 * j = (uj0,uj1,uj2) - qhat * (v1,v2) within 32 bits.
			 */
			j = uj01 - qhat * v1;	 /* < v1 !! */
			j = ((j<<15) | *(uj-2)) - qhat * v2;
			if (j < 0) {
				qhat--;
				if ((j + v12) < 0) qhat--;
			}
			/* Steps D4 through D6 in m_dsb. */
			if (m_dsb(qhat,blen,v.val,(uj-blen))) qhat--;
			qval[i]=qhat;
#if (! INTR)
			(*PollPtr)();
#endif
		}
		/*  Step D8: Unnormalize. */
		/*
		 * Adjust length of u.  This used to be done by calling
		 * mcan.
		 */
		uj = u.val;
		for (j=v.len; --j >= 0;) if (uj[j] != 0) break;
		if (++j == 0) HS_ZFREE(u.val);
		u.len = j;

		if ((b != q) && (b != r)) mshiftr(&v, shift);  /* unshift b */
		/* Unnormalize remainder. */
		mshiftr(&u, shift);
		mmove(&u, r);

		/* Fix up quotient. */
                u.val = v.val = NULL;
		MFREE(q);
		if (qval[qlen-1] == 0) qlen--;
		q->len	= qlen;
       		if (qlen == 0) {
                    vfree(qval);
                }else{
                    q->val = qval;
                }
		if (sign & NEGQ) mnegate(q);
		if (sign & NEGR) mnegate(r);
	}
#ifdef DEBUG
	printf(" = "); mout(q); printf(" (%d) , ",q->len);
	mout(r); printf(" (%d)\n", r->len);
#endif
}

/*
 * HISTORY
 *
 * 21-Jun-89  Jean-Philippe Vidal (jpv) at CMU
 *	BugFix : division should work properly on shared-memory 
 *		multiprocessors.
 *
 * 10-Jan-86  Bennet Yee (bsy) at CMU
 *	BugFix:  signed divisions now give correctly signed results.
 *
 * 07-Dec-84  Rex Dwyer (rad) at Carnegie-Mellon University
 *	Created.  Based in part on existing mp package.
 */
