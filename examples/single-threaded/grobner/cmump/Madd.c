#include "cmump.h"
#include <stdio.h>

/* M_ADD --	adds a and b, yielding c
	Pre:  c != a;  c != b;  a->len >= b->len >= 0 = c->len
*/

void m_add(MINT *a, MINT *b, MINT *c)
{	register i,x;
	register short *aval, *bval, *cval;

	aval = a->val;
	bval = b->val;
	valloc(cval,a->len+1);
	x=0;

	for(i=0;i<b->len;i++)
	{	x += aval[i] + bval[i];
		cval[i] = x&077777;
		x >>= 15;
#if (! INTR)
		(*PollPtr)();
#endif
	}
	for(;i<a->len;i++)
	{	x += aval[i];
		cval[i] = x&077777;
		x >>= 15;
#if (! INTR)
		(*PollPtr)();
#endif
	}
	if(x == 1)
	{	cval[i]=1;
		c->len=i+1;
	}
	else c->len=a->len;
	c->val=cval;
	if(c->len==0) vfree(cval);
}

void madd(MINT *a, MINT *b, MINT *c)
{	MINT x,y,z;
	register sign;

	x.len=a->len;
	x.val=a->val;
	y.len=b->len;
	y.val=b->val;
	z.len=0;
	sign=1;

	if(x.len>=0)
		if(y.len>=0)
			if(x.len>=y.len) m_add(&x,&y,&z);
			else m_add(&y,&x,&z);
		else
		{	y.len= -y.len;
			if (mcmp(&x,&y)>=0) m_sub(&x,&y,&z);
			else 
			{ 
				sign = -1; 
				m_sub(&y,&x,&z);
			}
		}
	else	if(y.len<=0)
		{	x.len = -x.len;
			y.len= -y.len;
			sign= -1;
			if (x.len >= y.len) m_add(&x,&y,&z);
			else m_add(&y,&x,&z);
		}
		else
		{	x.len= -x.len;
			if (mcmp(&y,&x)>=0) m_sub(&y,&x,&z);
			else
			{
				sign = -1;
				m_sub(&x,&y,&z);
			}
		}
        x.val = y.val = NULL;
	MFREE(c);
	c->len=sign*z.len;
	c->val=z.val;
	return;
}

/* M_SUB --	subtracts a and b, yielding c
	Pre:  c != a;  c != b;  a->len >= b->len >= 0 == c->len
*/

void m_sub(MINT *a, MINT *b, MINT *c)
{	register i,x;
	register short *aval, *bval, *cval;

	aval = a->val;
	bval = b->val;
	valloc(cval,a->len);
	x=0;

	for(i=0;i<b->len;i++)
	{	x += aval[i] - bval[i];
		cval[i] = x&077777;
		x >>= 15;
#if (! INTR)
		(*PollPtr)();
#endif
	}
	for(;i<a->len;i++)
	{	x += aval[i];
		cval[i] = x&077777;
		x >>= 15;
#if (! INTR)
		(*PollPtr)();
#endif
	}
	for (i=a->len; (--i)>=0;) if (cval[i]!=0) break;
	if ((c->len = i+1)==0) vfree(cval);
	else c->val = cval;
}

void msub(MINT *a, MINT *b, MINT *c)
{	MINT x,y,z;
	register sign;

	x.len=a->len;
	y.len=b->len;
	x.val=a->val;
	y.val=b->val;
	z.len=0;
	sign=1;
	if(x.len>=0)
		if(y.len>=0)
			if(mcmp(&x,&y)>=0) m_sub(&x,&y,&z);
			else
			{	sign= -1;
				m_sub(&y,&x,&z);
			}
		else
		{	y.len= -y.len;
			if (x.len >=y.len) m_add(&x,&y,&z);
			else m_add(&y,&x,&z);
		}
	else	if(y.len<=0)
		{	x.len= -x.len;
			y.len= -y.len;
			if (mcmp(&y,&x)>=0) m_sub(&y,&x,&z);
			else
			{
				sign = -1;
				m_sub(&x,&y,&z);
			}
		}
		else
		{	x.len= -x.len;
			if (x.len >= y.len) m_add(&x,&y,&z);
			else m_add(&y,&x,&z);
			sign= -1;
		}
        x.val = y.val = NULL;
	MFREE(c);
	c->len=sign*z.len;
	c->val=z.val;
}

/* HISTORY
 * 18-May-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created from code in existing mp package. *
 *	Debugged, cleaned up, and sped up. *
 */
