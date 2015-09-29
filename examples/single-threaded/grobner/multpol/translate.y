%{
#include <string.h>
%}

%token NUMBER,SYMBOL,POWER,PLUS,MINUS,STOP,TIMES,SEP,UNKNOWN,FULBUF

%%

read	:	pol STOP	{YYACCEPT;}
		|	STOP  		{status=1;YYACCEPT;}
		|	error		{status=2;YYACCEPT;}
		|	FULBUF		{status=4;YYACCEPT;}
		|	SEP read
		;

pol		:	pol sgnterm
			{
				mpoladd(&temp,&tempmon,&temp);
			}
		|	first
			{
				mpoladd(&temp,&tempmon,&temp);
			}
		;


first	:	sgnterm			
		|	unsterm			
		;

sgnterm	:	PLUS unsterm
		|	MINUS unsterm
			{
				mnegate(&(tempmon.coefs[0]));
			}
		;
	
unsterm	:	powprod	
			{
				MFREE(&coef);MSET(1,&coef);
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			}
		|	NUMBER TIMES powprod
			{
				MFREE(&coef);
				mstrtoul(&coef,numbers[$1],NULL,10);
				HS_ZFREE(numbers[$1]);numbers[$1]=NULL;
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			}
		|	NUMBER SEP powprod
			{
				MFREE(&coef);
				mstrtoul(&coef,numbers[$1],NULL,10);
				HS_ZFREE((numbers[$1]));numbers[$1]=NULL;
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			}
		|	NUMBER
			{
				MFREE(&coef);
				mstrtoul(&coef,numbers[$1],NULL,10);
				HS_ZFREE(numbers[$1]);numbers[$1]=NULL;
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			}
		;

powprod	:	powprod TIMES power
		|	powprod SEP power
		|	power
		;

power	:	SYMBOL POWER NUMBER
			{
				expo[0]+=(expo[$1+1]+= (short)atoi(numbers[$3],NULL,10));
				HS_ZFREE(numbers[$3]);
				numbers[$3]=NULL;
			}
		|	SYMBOL
			{
				expo[0]+=(expo[$1+1]+=1);
			}
		|	UNKNOWN POWER NUMBER   
		|	UNKNOWN		       
		;

%%
#include "lex.yy.c"

void yyerror(s)          {printf("%s\n",s);}

