#undef DO_TIME
#define DO_TIME
	/* define DO_TIME to use timers */

/* --------------------- includes ---------------------------------------- */
#include <stdio.h>
#include <signal.h>
#include <string.h>
#include <sys/time.h>
#include "cmump.h"
#include "multpol.h"
#include "gbas.h"

/* ------------------------ globals ------------------------------------ */

int order_exp = 1;	/* 0:lex, 1:deglex, 2:? */

static void Empty (void) {};
void (*PollPtr)() = Empty;

short nvars;
char *varnames[100];
int first_group=0;
int zero_poly_count = 0;
int redgcd = 0;
int order_on_pols=0;
int order_on_pairs=0;
int reduction_first=0;
int deletion=1;
int allow_same_lpp=0;
int spy = 0;

#if ( defined(DO_TIME) && !defined(NODE) )
extern float itimerread(int timerid);
#endif

polsettype s, pols;
polpairsettype pairs;

/* ------------------------ instrumentatiion ---------------------------- */

typedef enum {
  T_ALL,
  T_RED
} TimeType;

float
  addcnt = 0, zero = 0;

/* see when malloc gives up */
int
  memheld=0;

int
  intercnt = 0;

extern int debt;

/* ------------------------------ main ---------------------------------- */

int main(int argc, char *NTS *NT COUNT(argc) argv)
{
#ifdef STATS
  char *sb = (char *)sbrk(0);
#endif
  int a, pflag=0, oflag=0, aflag=0, wflag=0;
  /* print action, old basis, answer output, add-warn */
  MPOL *p, *v, *w;
  int vn, npolyin, cp;
  float oldt, newt;
  int initdebt=0;
  int pidx=0;

#ifdef TIMING
  timing_init();
#endif

#ifdef STATS
  setbuf(stdin, NULL);
#endif

  for(a=0;a<argc;a++){
    if ( argv[a][0] == '-' ) {
      switch(argv[a][1]){
      case 'p':
	pflag = 1;
	break;
      case 'o':
	oflag = 1;
	break;
      case 'a':
	aflag = 1;
	break;
      case 'w':
	wflag = 1;
	break;
      }
    }
  }

  init_order_exp();

  /* get variables */
# ifdef out
  {
    printf("# vars: ");
  }
# endif
  scanf("%hd",&nvars);
# ifdef out
  {
    printf("variables: ");
  }
# endif

  for(vn=0;vn<nvars;vn++){
    char tbuf[32];
    scanf("%s",tbuf);
    varnames[vn] = HS_ARRAYALLOC(char, strlen(tbuf)+1);
    initdebt+= strlen(tbuf)+1;
    strcpy(varnames[vn],tbuf);
  }

  s.npols = 0;
  
  /* get input poly set */
# ifdef out
  {
    printf("# input poly: ");
  }
# endif
  scanf("%d", &npolyin);
  for(cp=0;cp<npolyin;cp++){
    p = HS_ALLOC(MPOL);
    MPOLINIT(p);
    do{
#     ifdef out
      {
	printf("[%d] ",(int)s.npols+1);
      }
#     endif
    } while(mpolin(p)!=0);
    p->compact = 0;
    p->owner = 0;
    p->ppid = pidx++;
    p->next = NULL;
    new_mpolsetadd(&s,p);
    initdebt+= howbig(p);
  }

# ifdef out
  {
    printf("\n");
  }
# endif
  {
    MPOL *y;
    pols.npols = 0;
    pairs.npairs = 0;
    y = s.polp;
    while ( y ) {
      MPOL *z;
      z = y;
      y = z->next;
      z->next = 0;
      z->owner = z->reducible = 0;
      new_mpolsetadd ( &pols, z );
      memheld += howbig ( z );
      if ( pols.npols > 1 )
	new_update_pairs ( &pairs, &pols, z );
    }
  }

# ifdef DO_TIME
    {
      /* start timer */
      itimerinit(ITIMER_VIRTUAL, 1<<20);
      oldt = itimerread(ITIMER_VIRTUAL);
    }
# endif


  pidx = 1000;

  /* main while loop */
  while(pairs.npairs>0){
    MPOL *new;

    if( 0 && pflag)
      show_basis(pols);

    new_choose_pair(&pairs, &v, &w);
    if(pflag){
      printf("chosen pair:\n");
      mpolout(v); printf("\n");
      mpolout(w); printf("\n");
    }

    /* compute s poly */
    new = HS_ALLOC(MPOL);
    spolfast(v,w,new);

    if(pflag){
      printf("s-poly: ");  mpolout(new); printf("\n");
    }

    /* reduce the s-poly */
    {
      int size = new->nterms;
      float red, redend;
      
#     if ( defined(DO_TIME) && !defined(NODE) )
      red = itimerread ( ITIMER_VIRTUAL );
#     endif

      if(oflag)
	new = (MPOL*) new_redfast2(new, s.polp);
      else
	new = (MPOL*) new_redfast2(new, pols.polp);
      
#     if ( defined(DO_TIME) && !defined(NODE) )
      redend = itimerread ( ITIMER_VIRTUAL );
#     endif
    }

    if(pflag){
      printf("reduced poly: "); mpolout(new); printf("\n\n");
    }

    new->ppid = pidx++;
    new->next = NULL;
    new->compact = 0;
    new->owner = new->reducible = 0;

    /* add to basis */
    if(new->nterms!=0){

      memheld += howbig(new);
      new_mpolsetadd(&pols,new);
      /* sparselog ( new ); */
      new_update_pairs(&pairs,&pols,new);
      
      addcnt = addcnt  +  1.0;
      if ( wflag ) {
	printf ( "added poly: "); mpolout (new); printf ("\n\n");
      }

      if (0) {
	printf ( "A-%d-%d-->  ", new->owner, new->ppid );
	mpolout ( new );
	printf ( "\n\n" );
      }

      intercnt++;
      if ( intercnt%10 == 0 )
	/*inter_reduce ( &pols, &pairs )*/;
    }
    else {
      free ( new );
      zero = zero + 1;
    }
  }
  
# ifdef DO_TIME
    {
      newt = itimerread(ITIMER_VIRTUAL);
    }
# endif

  /* output statistics */
# ifdef DO_TIME
  printf("t%f a%.0f z%.0f\n", oldt-newt, addcnt, zero );
# else
  printf("a%.0f z%.0f\n", addcnt, zero );
# endif

  if(aflag) {
    int w;
    printf ( "\n\n%d\n", (int)nvars);
    for ( w=0; w<(int)nvars; w++ )
      printf ( "%s ", varnames[w] );
    printf ( "\n%d\n", pols.npols );
    for(v=pols.polp;v!=NULL;v=v->next){
      mpolout(v); printf(" ;\n");
    }
  }
# if 0
    extern float sparseout();
    printf ( "density = %f\n", sparseout() );
# endif

#ifdef BWGC
  fprintf(stderr, "heap size %d\n", GC_get_heap_size());
#else
#ifdef STATS
  malloc_stats();
#endif
#endif
  return 0;
}

/* ---------------------- size of polys ----------- */

#define abs(x) ((x>0)?(x):(-(x)))

int howbig (MPOL *p)
{
	register int tp, ans;

	ans = sizeof(MPOL) + (p->maxterms)* ( sizeof(short)*((int)nvars+1) + sizeof(MINT) );
	for ( tp=0; tp < p->nterms; tp++ )
		ans += sizeof(short)*abs(p->coefs[tp].len);
	return ans;
}

void report (char *NTS s)
{
	printf ( "%s: debt %d, held %d\n", s, debt, memheld );
}

