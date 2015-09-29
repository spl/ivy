#include <stdio.h>
#include "cmump.h"
#include "multpol.h"


#define NBUF 1000

/* I don't know how to use yacc in a less ugly way */

static MPOL tempmon,temp;
static MINT coef;
static short expo[1000];
static int status;
static char *NTS numbers[NBUF];

#include "y.tab.c"

/* returns 0 if the input is correct
	   1 if the input is empty
           2 if there is a syntax error
	   3 if there is an unknown 
	   4 if the buffer is too small */

int mpolin(MPOL *p)
{
  MPOLINIT(&tempmon);
  MPOLINIT(&temp);
  MINIT(&coef);
  status = 0;
  initall();

  yyparse();
  coef.val = NULL;
  mpolfree(&tempmon);
  if (status==0)
    MPOLMOVEFREE(&temp,p);
  else{
    mpolfree(&temp);
    mpolfree(p);
  };
  clean_num();
  return(status);
};


void clean1(void)
{
  int i;
  for (i=0;i<=nvars;i++) expo[i]=0;
}

void initall(void)
{
  int i;

  clean1();
  for (i=0;i<NBUF;i++)numbers[i]=NULL;
}

void clean_num(void)
{
	register i;

	for (i=0;i<NBUF;i++)
		if (numbers[i]!=NULL) {
			free(numbers[i]);
			numbers[i]=NULL;
		}
}

