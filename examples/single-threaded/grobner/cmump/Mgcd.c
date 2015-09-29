#include "cmump.h"
#define FN

void mgcd(MINT *a, MINT *b, MINT *c)
{	MINT x,y,z,w;

	MCOPY(a,&x);
	MCOPY(b,&y);
	MINIT(&z);
	MINIT(&w);

	while( mtest(&y) != 0)
	{	mdiv(&x,&y,&w,&z);
		mmove(&y,&x);
		mmove(&z,&y);
#if (! INTR)
		(*PollPtr)();
#endif
	}
	mmove(&x,c);
	MFREE(&y);
	MFREE(&z);
	MFREE(&w);
	return;
}

/* calculated a^-1 in ring Z sub b and places result in c */

void minvert(MINT *a, MINT *b, MINT *c)
{	MINT x, y, z, w, Anew, Aold;
	int i = 0;
	static MINT one;
	static int oneinit = 1;

	if (oneinit) {
		oneinit = 0;
		MSET(1,&one);
	}
	MINIT(&x);
	MINIT(&y);
	MINIT(&z);
	MINIT(&w);
	MINIT(&Aold);
	MSET (1,&Anew);

	mcopy(b, &x);
	mcopy(a, &y);
	/*
	 * Loop invariant:
	 *
	 * y = -1^i * Anew * a  mod b
	 */
	while(mtest(&y) != 0)
	{	mdiv(&x, &y, &w, &z);
		mcopy(&Anew, &x);
		mmult(&w, &Anew, &Anew);
		madd(&Anew, &Aold, &Anew);
		mmove(&x, &Aold);
		mmove(&y, &x);
		mmove(&z, &y);
		i++;
	}
	if (mcmp(&one,&x)) {
		mcopy(&one,c);
	} else {
		mmove(&Aold, c);
		if( (i&01) == 0) msub(b, c, c);
	}

	MFREE(&x);
	MFREE(&y);
	MFREE(&z);
	MFREE(&w);
	MFREE(&Aold);
	MFREE(&Anew);
}

/* HISTORY
 * 18-May-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created from code in existing mp package. *
 *	Debugged, cleaned up, and sped up. *
 *
 * 11-Dec-86  Bennet Yee (bsy) at Carnegie-Mellon University
 *	Un-commented-out minvert and put in comments.
 *
 * 28-Jan-88  Bennet Yee (bsy) at Carnegie-Mellon University
 *	Fixed storage leak bug pointed out by guy@th.
 */
