#include "cmump.h"

mtod (MINT *a, MINT *b, double *d)
{
	MINT q,r;
	double d2;
	int i,bits,exp,sign;
	double frexp(double, int *),ldexp(double, int);

	if (mtest(b) == 0) return (-1);
	if (mtest(a) == 0) {*d = 0.0; return(0);}	

	MINIT(&r);
	MCOPY (a, &q);
	mshiftl (&q, 135);

	mdiv (&q, b, &q, &r);
	MFREE(&r);

	if (mtest(&q) == 0) {*d = 0.0; return(0);}
	if (mtest(&q) < 0) {sign = -1; mnegate(&q);}
	else sign = 1;

	bits = mlog(&q);

	exp = -135;

	if (bits > 53) {
		i = bits - 53;
		mshiftr (&q,i);
		exp += i;
	}
	
	*d = 0;
	for (i=q.len-1; i>=0; --i) *d = *d * (1<<15) +  q.val[i];
	MFREE (&q);

	if (*d == 0) return(0);
	d2 = frexp(*d, &i);
	exp += i;
	if (exp > 127) return (-2);
	if (exp < -128) {*d = 0; return (0);}
	*d = ldexp(d2,exp);
	if (sign < 0) *d = - *d;
	return (0);
}

mlog(MINT *a)
{
	register bits, hi, alen;

	alen = a->len;

	if (alen == 0) return(0);
	else if (alen < 0) alen = -alen;

	bits = (alen-1) * 15;
	hi = a->val[alen-1];
	while (hi) {
		bits++;
		hi >>= 1;
	}
	return (bits);
}

void mshiftl (MINT *a, int b)
{	register big, q, p, bits;
	register short *aval, *cval;
	int alen, words, neg, clen, rest;

	bits = b;

	if (bits == 0) return;
	else if (bits < 0) {mshiftr(a,-bits); return;}

	alen = a->len;
	aval = a->val;

	if (alen == 0) return;
	if (alen > 0) neg = 0;
	else {alen = -alen; neg = 1;}

	words = bits/15;
	bits = bits%15;
	rest = 15 - bits;

	q = alen-1;
	big = aval[q--]<<bits;

	if (big>>15) {
		clen = alen + words + 1;
		valloc(cval,clen);
		p = clen - 1;
		cval[p--] = big >> 15;
		big &= 077777;
	}
	else {
		clen = alen + words;
		p = clen - 1;
		if (words == 0) cval = aval;
		else valloc (cval, clen);
	}

	while (q >= 0) {
		big <<= rest;
		big |= (int)aval[q--];
		big <<= bits;
		cval[p--] = big>>15;
		big &= 077777;
	}

	if (p >= 0) cval[p--] = big;

	while (p >= 0) cval[p--] = 0;

	if (cval != aval) {MFREE(a); a->len = clen; a->val = cval; }
	if (neg) mnegate(a);
}

void mshiftr (MINT *a, int b)
{
	register bits, big, p, q, alen;
	register short *aval;
	int neg, words, rest;

	bits = b;

	if (bits == 0) return;
	else if (bits < 0) {mshiftl(a,-bits); return;}

	alen = a->len;
	aval = a->val;

	if (alen == 0) return;
	else if (alen > 0) neg = 0;
	else {alen = -alen; neg = 1;}

	words = bits / 15;
	bits = bits % 15;
	rest = 15 - bits;
	if (words >= alen) {mset(0,a); return;}
	
	q = words;
	p = 0;

	if (bits == 0)
		while (q < alen) aval[p++] = aval[q++];
	else {
		big = aval[q++];
		while (q < alen) {
			big |= ((int)aval[q++]) << 15;
			big >>= bits;
			aval[p++] = big & 077777;
			big >>= rest;
		}
		big >>= bits;
		if (big) aval[p++] = big;
		else if (p == 0) {mset(0,a); return;}
	}

	if (neg) p = -p;
	a->len = p;
}

/* HISTORY
 * 03-Dec-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created.
 */
