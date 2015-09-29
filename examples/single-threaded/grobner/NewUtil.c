/*#include	<malloc.h>*/
#include	<stdio.h>
#include	"cmump.h"
#include	"multpol.h"
#include	"gbas.h"

/* ------------- malloc statistics ----------------- */
#define	BINS	12
double freq[BINS];
int whichbin (int bytes)
{
	register int shift=bytes, answer=-1;
	while ( shift ) {
		shift = shift >> 1;
		answer++;
	}
	return answer<BINS?answer:(BINS-1);
}

void prbins (void) {
	int i;
	double total=0;
	for ( i=0; i<BINS; i++ )
		total += freq[i];
	printf ( "\n\n\n" );
	for ( i = 0; i < BINS-1; i++ ) {
		printf ( "%d\t%f\n", 1 << i, freq[i]/total );
		printf ( "%d\t%f\n", 1 << (i+1), freq[i]/total );
	}
	printf ( "\n\n\n" );
	return;
}

/* ------------------------------------------------- */

int debt = 0;

void show_basis(polsettype b)
{
	MPOL *v;
	printf("# %d\n",b.npols);
	for(v=b.polp;v!=NULL;v=v->next){
		mpolout(v);
		printf("\n");
	}
	return;
}

void beep(void)
{
	printf("%c",(char)7); fflush(stdout);
	return;
}

