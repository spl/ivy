#include "cmump.h"
#include "multpol.h"
#include "gbas.h"

extern short nvars;
extern int order_on_pols;

void new_mpolsetadd(polsettype *s, MPOL *p)
{
	register MPOL *pt1,*pt2;
	register short *pexp;
	
	pexp = MEXPO(p,0);
	pt1 = s->polp;
	switch (order_on_pols) {
		case 0:		/* No special order */
			p->next=NULL;
			if (s->polp==NULL) 
				s->polp=p;
			else{
				while((pt1->next)!=NULL)
					pt1=pt1->next;
				pt1->next=p; 
			}
			break;
		case 1:		/* Descending order */
			pt2=pt1;
			while((pt1!=NULL)&& ((*cmp_exp)(pexp,MEXPO(pt1,0),nvars)<0)){
				pt2=pt1;
				pt1=pt1->next;
			}
			p->next=pt1;
			if(pt1!=pt2)
				pt2->next=p;
			else
				(s->polp)=p;
			break;
		case 2:		/* Ascending order */
			pt2=pt1;
			while((pt1!=NULL)&& ((*cmp_exp)(pexp,MEXPO(pt1,0),nvars)>0)){
				pt2=pt1;
				pt1=pt1->next;
			}
			p->next=pt1;
			if(pt1!=pt2)
				pt2->next=p;
			else
				(s->polp)=p;
			break;
		case 3:		/* by ascending number of terms. */
			pt2=pt1;
			while((pt1!=NULL)&& (p->nterms>pt1->nterms)){
				pt2=pt1;
				pt1=pt1->next;
			}
			p->next=pt1;
			if(pt1!=pt2)
				pt2->next=p;
			else
				(s->polp) =p;
			break;
	}
	s->npols++;
	return;
}	

