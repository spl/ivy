#include <stdio.h>
#include <ctype.h>
#include "cmump.h"

#undef	DEBUG

m_in(MINT *a, int b, FILE *f)
{
	return m_in_b(a,b,f,1);
}

m_in_b(MINT *a, int b, FILE *f, int blanks)
{
	MINT	y, base;
	int	sign, c, dectop, alphatop = 0;
	short	qy;
	int	flag;

	mset(0,a);
	sign	= 1;
	MSET(b,&base);
	y.len	= 1;
	y.val	= &qy;
	flag	= 0;
	dectop = (b <= 10) ? '0' + b - 1 : '9';
	if (b > 10) alphatop = 'a' + b - 10;

	while ((c=getc(f)) != EOF) switch(c) {
	case '\\':
		if (getc(f) == EOF) goto end;
		continue;
	case ' ':
	case '\t':
		if (blanks) continue;
		/* else fall through */
	case '\n':
		if (flag) {
			a->len *= sign;
			return 0;
		}
		continue;
	case '-':
		sign = -sign;
		continue;
	default:
		if (isupper(c)) c = c - 'A' + 'a';
		if (c >= '0' && c <= dectop) {
			qy = c - '0';
			mmult(a,&base,a);
			if (qy != 0) madd(a,&y,a);
			flag = 1;
			continue;
		} if (b > 10 && (c >= 'a' && c <= alphatop)) {
			qy = c - 'a' + 10;
			mmult(a,&base,a);
			madd(a,&y,a);
			flag = 1;
			continue;
		} else {
			(void) ungetc(c,stdin);
			a->len *= sign;
			return 0;
		}
	}
end:
	return EOF;
}

/* pre: n > 0;	out: integer part of base 2 log of n */

static int slog(int n)
{
	int i = 0;
	while (n >>= 1) ++i;
	return i;
}

void m_out(MINT *a, int b, FILE *f)
{
	m_out_b(a,b,f,0);
}

void m_out_b(MINT *a, int b, FILE *f, int blanks)
{
	int		sign, i;
	short		r;
	MINT		x;
	char		*obuf;
	register char	*bp;
	int		regionsize;

	if (b < 2) return;

	MINIT (&x);
	mcopy(a,&x);
	if (mtest(&x) == 0) { fprintf(f,"0"); return; }
	else if (mtest(&x) > 0) sign = 1;
	else {mnegate(&x); sign = -1;}

	regionsize = slog(b);
	regionsize = ((8 * sizeof(short) - 1) * x.len + (regionsize - 1)) / regionsize;
	/* round up */
	if (blanks) regionsize += regionsize/10;
	/* a blank every 10 digits */
	regionsize += 2;
	/* null and opt sign */

#ifdef	DEBUG
	fprintf(stderr,"ALLOCATING:  regionsize = %d\n",regionsize);
#endif
	if ((obuf = HS_ARRAYALLOC(char, regionsize)) == 0) valerr();
	bp = obuf + regionsize - 1;
	*bp--=0;			/* sentinel */

	while (mtest(&x) > 0) {
		for (i = 0; i<10 && mtest(&x) > 0; i++) {
			sdiv(&x,b,&x,&r);
			if (r < 10)	*bp-- = r + '0';
			else		*bp-- = r - 10+'A';
		}
		if (blanks && mtest(&x) > 0) *bp--=' ';
	}
	if (sign == -1) *bp--='-';
#ifdef	DEBUG
	fprintf(stderr,"OUTPUTSTRINGSIZE: %d\n",strlen(bp+1));
#endif
	fprintf(f,"%s",bp+1);
	free(obuf);
	MFREE(&x);
}

void sdiv (MINT *a, int n, MINT *q, short int *r)
{
	register qlen,i,x,y;
	register short *aval, *qval;
	int neg;

	qlen = a->len;
	if (qlen == 0) {mset(0,q); *r = 0; return;}
	if (qlen > 0) neg = 0;
	else { qlen = -qlen; neg = 1;}
	if (n < 0) {n = -n; neg = 1 - neg;}

	aval = a->val;
	valloc(qval,qlen);
	x = 0;
	for (i=qlen; (--i)>=0;) {
		x <<= 15;
		x += aval[i];
		qval[i] = y = x/n;
		x -= y*n;
	}
	if (qval[qlen-1] == 0) qlen--;
	MFREE (q);
	if (neg) {qlen = -qlen; x = -x;}
	q->len = qlen;
	if (qlen==0) vfree(qval);
	else q->val = qval;
	*r = x;
}

/* simple routines */
int gmin(MINT *a) {
	return m_in(a,10,stdin);
}
omin(MINT *a) {
	return m_in(a,8,stdin);
}
void mout(MINT *a) {
	m_out(a,10,stdout);
}
void omout(MINT *a) {
	m_out(a,8,stdout);
}
void hexmout(MINT *a) {
	m_out(a,16,stdout);
}
void fmout(MINT *a, FILE *f) {
	m_out(a,10,f);
}
int hexmin(MINT *a) {
	return m_in(a,16,stdin);
}
fmin2(MINT *a, FILE *f) {
	return m_in(a,10,f);
}

/*
 * HISTORY
 *
 * 22-Jan-87  Bennet Yee (byee) at Carnegie-Mellon University
 *	Modified m_in and m_out to handle arbitrary bases.
 *	Added hexmin, m_in_b, and m_out_b.
 *
 * 18-May-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created from code in existing mp package. *
 *	Debugged, cleaned up, and sped up. *
 */



void Sm_out_b(char *s, MINT *a, int b, int blanks)
{
	int		sign, i;
	short		r;
	MINT		x;
	char		*obuf;
	register char	*bp;
	int		regionsize;

	if (b < 2) return;

	MINIT (&x);
	mcopy(a,&x);
	if (mtest(&x) == 0) { sprintf(s+strlen(s),"0"); return; }
	else if (mtest(&x) > 0) sign = 1;
	else {mnegate(&x); sign = -1;}

	regionsize = slog(b);
	regionsize = ((8 * sizeof(short) - 1) * x.len + (regionsize - 1)) / regionsize;
	/* round up */
	if (blanks) regionsize += regionsize/10;
	/* a blank every 10 digits */
	regionsize += 2;
	/* null and opt sign */

#ifdef	DEBUG
	fprintf(stderr,"ALLOCATING:  regionsize = %d\n",regionsize);
#endif
	if ((obuf = HS_ARRAYALLOC(char, regionsize)) == 0) valerr();
	bp = obuf + regionsize - 1;
	*bp--=0;			/* sentinel */

	while (mtest(&x) > 0) {
		for (i = 0; i<10 && mtest(&x) > 0; i++) {
			sdiv(&x,b,&x,&r);
			if (r < 10)	*bp-- = r + '0';
			else		*bp-- = r - 10+'A';
		}
		if (blanks && mtest(&x) > 0) *bp--=' ';
	}
	if (sign == -1) *bp--='-';
#ifdef	DEBUG
	fprintf(stderr,"OUTPUTSTRINGSIZE: %d\n",strlen(bp+1));
#endif
	sprintf(s+strlen(s),"%s",bp+1);
	free(obuf);
	MFREE(&x);
}

void Sm_out(char *s, MINT *a, int b)
{
	Sm_out_b(s,a,b,0);
}

void Smout(char *s, MINT *a) {
	Sm_out(s,a,10);
}

