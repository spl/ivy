#ifdef CM5
#	include <cm/cmna.h>
#	include <cmsys/ni_interface.h>
#	include <cm/cmmd.h>
#	include <cm/timers.h>
#endif

#include "cmump.h"
#include "multpol.h"
#include "gbas.h"
#include <stdio.h>

#define MSIZE(x) ((x)->len>0 ? (x)->len : - ((x)->len))
extern short nvars;

#ifdef cmu_
extern long arith_cost[MAX_WORKERS];
extern int nbumps[MAX_WORKERS];
extern int dead_time[MAX_WORKERS];
extern int state[MAX_WORKERS];
#endif /* cmu_ */

extern int spy, redgcd;
extern int zero_poly_count;

#if	eager_kills
extern	LMPOL *current_pair[MAX_WORKERS][2];
extern  int kill_pair[MAX_WORKERS];
extern  int valid_pair[MAX_WORKERS];
extern  int nworkers,co_workers;
#endif	/* eager_kills */

#if	TIME_REDUCTION

/*	time_ stuff is used to record intervals for reductions delays using 
	the microsecond timer.  */

#define	TIME_SIZE	32768

extern unsigned	*microtime;
extern int		time_log_start[TIME_SIZE];
extern int		time_log_end[TIME_SIZE];
extern int		time_who[TIME_SIZE];
extern int		time_what[TIME_SIZE];
extern int		time_index;

#define		TIME_WHAT_READY 5
#define		TIME_WHAT_START 6
#define		TIME_WHAT_SEARCH 7

#endif	/* TIME_REDUCTION */

extern int primitive_reduction_count;

#if LOCKCOUNT
extern int lockcount;
#endif

extern int deque();

void new_redonefast(MPOL *p, MPOL *q, MPOL *r, short int *COUNT(2 * (nv + 1)) scratch, MPOL *nextp, int nv);

MPOL *new_redfast2(MPOL *p, MPOL *nextp)
{
	MPOL *temp;
	MPOL *pmpol;
	static short *COUNT(2 * MAXVARS) scratch;

	if (!scratch)
	  scratch = HS_ARRAYALLOC(short, 2 * MAXVARS);

	for (;;) {
		extern double maxRedTime, minRedTime, totRedTime;
		double thisTime;

		if(p->nterms==0)
			return(p);
		pmpol=nextp;
		while(
		    (pmpol!=NULL)&&
		    (!expodiv(MEXPO(pmpol,0),MEXPO(p,0),nvars))
		)
			pmpol=pmpol->next;

		if (pmpol==NULL)
			return( p );

		pmpol->reducible++;
		temp = HS_ALLOC(MPOL);
		temp->nterms = 0;

		/* printf("reduced by: ");
		hexout(pmpol->puid); mpolout(pmpol); printf("\n"); */

#		if 0 && defined(CM5)
			CMMD_node_timer_clear ( T_RED );
			CMMD_node_timer_start ( T_RED );
#		endif
			new_redonefast(p,pmpol,temp,scratch,nextp,nvars);
#		if 0 && defined(CM5)
			CMMD_node_timer_stop ( T_RED );
			thisTime = CMMD_node_timer_busy(T_RED);
			pmpol->owner = pmpol->owner + (int)(1e6*thisTime);
			if ( thisTime > maxRedTime )
				maxRedTime = thisTime;
			if ( thisTime < minRedTime )
				minRedTime = thisTime;
			totRedTime += thisTime;
#		endif

		mpolfree(p);
		free ( p ); /* <<<<--------- */
		/* free(scratch); */
		p = temp;
	}
}


void new_redonefast(MPOL *p, MPOL *q, MPOL *r, short int *scratch, MPOL *nextp, int nv)
{

	MINT coef1,coef2,rem;
	register int ip,iq,ires;
	short *pow,*lpp;
	int flag;


	pow = scratch;
	lpp = scratch + nv + 1;
	MINIT(&coef1); 
	MINIT(&coef2);
	MINIT(&rem);

	/* This code should never execute. */
	while ( p->nterms == 0 ) { /* What if p has 0 terms? */
		printf("yucco\n");
	}

	exposub(MEXPO(p,0),MEXPO(q,0),scratch,nv);
	mgcd(&(p->coefs[0]),&(q->coefs[0]),&coef1);
	mdiv(&(p->coefs[0]),&coef1,&coef2,&rem);
	mdiv(&(q->coefs[0]),&coef1,&coef1,&rem);
	if (mtest(&coef1)<0){
		mnegate(&coef1); 
		mnegate(&coef2);
	}

	ip=1;
	iq=1;
	ires=0;

	/* Make sure that there is enough space */

	POL_ALLOC(r,(int)(p->nterms+q->nterms-1));

	if (iq<q->nterms) {
		expoadd(pow,MEXPO(q,1),lpp,nv);
	}
	flag = 0;
	while ( flag == 0 ) {
		if ((ip<p->nterms)&&(iq<q->nterms)) {
			switch((*cmp_exp)(MEXPO(p,ip),lpp,nv)){
			case 1 : 
				expocopy(MEXPO(p,ip),MEXPO(r,ires),nv);
				MINIT(&(r->coefs[ires]));
				mmult(&(p->coefs[ip]),&coef1,&(r->coefs[ires]));
				ip++;
				ires++;
				r->nterms++;
				break;
			case -1 : 
				expocopy(lpp,MEXPO(r,ires),nv);
				MINIT(&(r->coefs[ires]));
				mmult(&(q->coefs[iq]), &coef2, &(r->coefs[ires]));
				mnegate(&(r->coefs[ires]));
				iq++;
				ires++;
				r->nterms++;
				if (iq<q->nterms) expoadd(pow,MEXPO(q,iq),lpp,nv);
				break;
			case 0 : 
				MINIT(&(r->coefs[ires]));
				mmult(&(p->coefs[ip]),&coef1,&(r->coefs[ires]));
				mmult(&(q->coefs[iq]),&coef2,&rem);
				msub(&(r->coefs[ires]),&rem,&(r->coefs[ires]));
				if (mtest(&(r->coefs[ires]))){
					expocopy(lpp,MEXPO(r,ires),nv);
					ires++;
					r->nterms++;
				};
				ip++;
				iq++;
				if (iq<q->nterms) expoadd(pow,MEXPO(q,iq),lpp,nv);
			}
		}
		else if ( iq == q->nterms ) { 
			flag = 1; 
		}
		else if ( ip == p->nterms ) { 
			flag = 1; 
		}
		else {
			if ( (ip >= p->nterms) ) { 
				flag = 1; 
			}
		}
	}
	flag = 0;
	while ( flag == 0 ) {
		if (ip<p->nterms) {
			expocopy(MEXPO(p,ip),MEXPO(r,ires),nv);
			MINIT(&(r->coefs[ires]));
			mmult(&(p->coefs[ip]),&coef1,&(r->coefs[ires]));
			ip++;
			ires++;
			r->nterms++;
		}
		else if (1) {
			if (ip >= p->nterms) { 
				flag = 1; 
			}
		}
		else {
			if ( (ip >= p->nterms) ) { 
				flag = 1; 
			}
		}
	}
	while (iq<q->nterms){
		expoadd(pow,MEXPO(q,iq),MEXPO(r,ires),nv);
		MINIT(&(r->coefs[ires]));
		mmult(&(q->coefs[iq]), &coef2, &(r->coefs[ires]));
		mnegate(&(r->coefs[ires]));
		iq++;
		ires++;
		r->nterms++;
	}

	if (ires==0){
		HS_ZFREE(r->coefs);
		HS_ZFREE(r->expos);
	};

	MFREE(&rem);
	MFREE(&coef1);
	MFREE(&coef2);
}




void spolfast(MPOL *p, MPOL *q, MPOL *r)
{
	MINT coef1,coef2,rem;
	register ip,iq,ires;
	short *expofactp,*expofactq,*lpp_p,*lpp_q;
	int flag,flag2;

	expofactp = HS_ARRAYALLOC(short, 4 * (nvars+1));
	expofactq = expofactp + nvars + 1;
	lpp_p = expofactq + nvars + 1;
	lpp_q = lpp_p + nvars + 1;

	MPOLINIT(r);
	MINIT(&coef1); 
	MINIT(&coef2);
	MINIT(&rem);

	expofactor(MEXPO(p,0),MEXPO(q,0),expofactp,nvars);
	expofactor(MEXPO(q,0),MEXPO(p,0),expofactq,nvars);

	mgcd(&(p->coefs[0]),&(q->coefs[0]),&coef1);
	mdiv(&(p->coefs[0]),&coef1,&coef2,&rem);
	mdiv(&(q->coefs[0]),&coef1,&coef1,&rem);

	ip=1;
	iq=1;
	ires=0;

	POL_ALLOC(r,p->nterms+q->nterms-1);

	flag = 0;
	while (flag == 0) {
		if ((ip<p->nterms)&&(iq<q->nterms)){
			expoadd(expofactp,MEXPO(p,1),lpp_p,nvars);
			expoadd(expofactq,MEXPO(q,1),lpp_q,nvars);
			flag = 1;
		}
		else if (ip>=p->nterms) {
			flag = 1;
		}
		else if (iq>=q->nterms) {
			flag = 1;
		}
	}
	flag = 0;
	while ( flag == 0 ) {
		if ((ip<p->nterms)&&(iq<q->nterms)) {
			switch((*cmp_exp)(lpp_p,lpp_q,nvars)){
			case 1 : 
				expocopy(lpp_p,MEXPO(r,ires),nvars);
				MINIT(&(r->coefs[ires]));
				mmult(&(p->coefs[ip]),&coef1,&(r->coefs[ires]));
				ip++;
				ires++;
				r->nterms++;
				flag2 = 0;
				while ( flag2 == 0) {
					if (ip<p->nterms) {
						expoadd(expofactp,MEXPO(p,ip),lpp_p,nvars);
						flag2 = 1;
					}
					else if (ip >= p->nterms) {
						flag2 = 1;
					}
				}
				break;
			case -1 : 
				expocopy(lpp_q,MEXPO(r,ires),nvars);
				MINIT(&(r->coefs[ires]));
				mmult(&(q->coefs[iq]),
				    &coef2,
				    &(r->coefs[ires]));
				mnegate(&(r->coefs[ires]));
				iq++;
				ires++;
				r->nterms++;
				flag2 = 0;
				while ( flag2 == 0) {
					if (iq<q->nterms) {
						expoadd(expofactq,MEXPO(q,iq),lpp_q,nvars);
						flag2 = 1;
					}
					else if (iq >= q->nterms) {
						flag2 = 1;
					}
				}
				break;
			case 0 : 
				MINIT(&(r->coefs[ires]));
				mmult(&(p->coefs[ip]),&coef1,&(r->coefs[ires]));
				mmult(&(q->coefs[iq]),&coef2,&rem);
				msub(&(r->coefs[ires]),&rem,&(r->coefs[ires]));
				if (mtest(&(r->coefs[ires]))){
					expocopy(lpp_p,MEXPO(r,ires),nvars);
					ires++;
					r->nterms++;
				}
				ip++;
				iq++;
				flag2 = 0;
				while ( flag2 == 0) {
					if (ip<p->nterms) {
						expoadd(expofactp,MEXPO(p,ip),lpp_p,nvars);
						flag2 = 1;
					}
					else if (ip >= p->nterms) {
						flag2 = 1;
					}
				}
				flag2 = 0;
				while ( flag2 == 0) {
					if (iq<q->nterms) {
						expoadd(expofactq,MEXPO(q,iq),lpp_q,nvars);
						flag2 = 1;
					}
					else if (iq >= q->nterms) {
						flag2 = 1;
					}
				}
			}
		}
		else if (ip >= p->nterms) { 
			flag = 1; 
		}
		else if (iq >= q->nterms) { 
			flag = 1; 
		}
		else {
			if ( ip >= p->nterms ) {
				flag = 1; 
			}
			if ( iq >= q->nterms ) {
				flag = 1; 
			}
		}
	}
	flag = 0;
	while ( flag == 0 ) {
		if (ip<p->nterms) {
			expoadd(expofactp,MEXPO(p,ip),MEXPO(r,ires),nvars);
			MINIT(&(r->coefs[ires]));
			mmult(&(p->coefs[ip]),&coef1,&(r->coefs[ires]));
			ip++;
			ires++;
			r->nterms++;
		}
		else if ( 1 ) {
			if (ip >= p->nterms) { 
				flag = 1; 
			}
		}
		else {
			while ( 0 /*(ip >= p->nterms) && (p->done == 0)*/ ) {
			}
			if ( (ip >= p->nterms)/* && (p->done == 1)*/ ) { 
				flag = 1; 
			}
		}
	}
	flag = 0;
	while ( flag == 0) {
		if (iq<q->nterms){
			expoadd(expofactq,MEXPO(q,iq),MEXPO(r,ires),nvars);
			MINIT(&(r->coefs[ires]));
			mmult(&(q->coefs[iq]),
			    &coef2,
			    &(r->coefs[ires]));
			mnegate(&(r->coefs[ires]));
			iq++;
			ires++;
			r->nterms++;
		}
		else if ( 1 ) {
			if (iq >= q->nterms) { 
				flag = 1; 
			}
		}
		else {
			if (iq >= q->nterms) { 
				flag = 1; 
			}
		}
	}
	r->nterms = ires;

	MFREE(&rem);
	MFREE(&coef1);
	MFREE(&coef2);
	free(expofactp);
}


/* ------------------------ end of 294-3 modifications ------------------------------ */

