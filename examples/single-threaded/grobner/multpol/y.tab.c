
# line 2 "translate.y"
#include <string.h>
# define NUMBER 257
# define SYMBOL 258
# define POWER 259
# define PLUS 260
# define MINUS 261
# define STOP 262
# define TIMES 263
# define SEP 264
# define UNKNOWN 265
# define FULBUF 266
#define yyclearin yychar = -1
#define yyerrok yyerrflag = 0
extern int yychar;
extern short yyerrflag;
#ifndef YYMAXDEPTH
#define YYMAXDEPTH 150
#endif
#ifndef YYSTYPE
#define YYSTYPE int
#endif
YYSTYPE yylval, yyval;
# define YYERRCODE 256

# line 89 "translate.y"

#include "lex.yy.c"

void yyerror(char *NTS s) {printf("%s\n",s);}

short yyexca[] ={
-1, 1,
	0, -1,
	-2, 0,
	};
# define YYNPROD 23
# define YYLAST 54
short yyact[]={

   4,  13,  15,  33,  10,  11,   3,  15,   6,  16,
   5,  13,  15,  32,  16,  22,  23,  27,  26,  16,
  24,  25,  10,  11,  17,  12,   9,   1,   8,  14,
   7,  18,   2,   0,  19,   0,   0,  20,  21,   0,
   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,
  30,  31,  28,  29 };
short yypact[]={

-256,-1000,-238,-1000,-1000,-1000,-256,-1000,-1000,-1000,
-246,-246,-248,-243,-1000,-241,-242,-1000,-1000,-1000,
-1000,-1000,-251,-251,-251,-251,-244,-254,-1000,-1000,
-248,-248,-1000,-1000 };
short yypgo[]={

   0,  27,  32,  28,  30,  26,  25,  29 };
short yyr1[]={

   0,   1,   1,   1,   1,   1,   2,   2,   4,   4,
   3,   3,   5,   5,   5,   5,   6,   6,   6,   7,
   7,   7,   7 };
short yyr2[]={

   0,   2,   1,   1,   1,   2,   2,   1,   1,   1,
   2,   2,   1,   3,   3,   1,   3,   3,   1,   3,
   1,   3,   1 };
short yychk[]={

-1000,  -1,  -2, 262, 256, 266, 264,  -4,  -3,  -5,
 260, 261,  -6, 257,  -7, 258, 265, 262,  -3,  -1,
  -5,  -5, 263, 264, 263, 264, 259, 259,  -7,  -7,
  -6,  -6, 257, 257 };
short yydef[]={

   0,  -2,   0,   2,   3,   4,   0,   7,   8,   9,
   0,   0,  12,  15,  18,  20,  22,   1,   6,   5,
  10,  11,   0,   0,   0,   0,   0,   0,  16,  17,
  13,  14,  19,  21 };
#ifndef lint
static char yaccpar_sccsid[] = "@(#)yaccpar	4.1	(Berkeley)	2/11/83";
#endif

#
# define YYFLAG -1000
# define YYERROR goto yyerrlab
# define YYACCEPT return(0)
# define YYABORT return(1)

/*	parser for yacc output	*/

#ifdef YYDEBUG
int yydebug = 0; /* 1 for debugging */
#endif
YYSTYPE yyv_[YYMAXDEPTH + 1]; /* where the values are stored */
#define yyv (&yyv_[1])
int yychar = -1; /* current input token number */
int yynerrs = 0;  /* number of errors */
short yyerrflag = 0;  /* error recovery flag */

yyparse() {

        short yys_[1+YYMAXDEPTH];
#define yys (&yys_[1])
	short yyj, yym;
	register YYSTYPE *yypvt;
	register short yystate, *yyps, yyn;
	register YYSTYPE *yypv;
	register short *yyxi;

	yystate = 0;
	yychar = -1;
	yynerrs = 0;
	yyerrflag = 0;
	yyps= &yys[-1];
	yypv= &yyv[-1];

 yystack:    /* put a state and value onto the stack */

#ifdef YYDEBUG
	if( yydebug  ) printf( "state %d, char 0%o\n", yystate, yychar );
#endif
		if( ++yyps> &yys[YYMAXDEPTH] ) { yyerror( "yacc stack overflow" ); return(1); }
		*yyps = yystate;
		++yypv;
		*yypv = yyval;

 yynewstate:

	yyn = yypact[yystate];

	if( yyn<= YYFLAG ) goto yydefault; /* simple state */

	if( yychar<0 ) if( (yychar=yylex())<0 ) yychar=0;
	if( (yyn += yychar)<0 || yyn >= YYLAST ) goto yydefault;

	if( yychk[ yyn=yyact[ yyn ] ] == yychar ){ /* valid shift */
		yychar = -1;
		yyval = yylval;
		yystate = yyn;
		if( yyerrflag > 0 ) --yyerrflag;
		goto yystack;
		}

 yydefault:
	/* default state action */

	if( (yyn=yydef[yystate]) == -2 ) {
		if( yychar<0 ) if( (yychar=yylex())<0 ) yychar = 0;
		/* look through exception table */

		for( yyxi=yyexca; (*yyxi!= (-1)) || (yyxi[1]!=yystate) ; yyxi += 2 ) ; /* VOID */

		while( *(yyxi+=2) >= 0 ){
			if( *yyxi == yychar ) break;
			}
		if( (yyn = yyxi[1]) < 0 ) return(0);   /* accept */
		}

	if( yyn == 0 ){ /* error */
		/* error ... attempt to resume parsing */

		switch( yyerrflag ){

		case 0:   /* brand new error */

			yyerror( "syntax error" );
		yyerrlab:
			++yynerrs;

		case 1:
		case 2: /* incompletely recovered error ... try again */

			yyerrflag = 3;

			/* find a state where "error" is a legal shift action */

			while ( yyps >= yys ) {
			   yyn = yypact[*yyps] + YYERRCODE;
			   if( yyn>= 0 && yyn < YYLAST && yychk[yyact[yyn]] == YYERRCODE ){
			      yystate = yyact[yyn];  /* simulate a shift of "error" */
			      goto yystack;
			      }
			   yyn = yypact[*yyps];

			   /* the current yyps has no shift onn "error", pop stack */

#ifdef YYDEBUG
			   if( yydebug ) printf( "error recovery pops state %d, uncovers %d\n", *yyps, yyps[-1] );
#endif
			   --yyps;
			   --yypv;
			   }

			/* there is no state on the stack with an error shift ... abort */

	yyabort:
			return(1);


		case 3:  /* no shift yet; clobber input char */

#ifdef YYDEBUG
			if( yydebug ) printf( "error recovery discards char %d\n", yychar );
#endif

			if( yychar == 0 ) goto yyabort; /* don't discard EOF, quit */
			yychar = -1;
			goto yynewstate;   /* try again in the same state */

			}

		}

	/* reduction by production yyn */

#ifdef YYDEBUG
		if( yydebug ) printf("reduce %d\n",yyn);
#endif
		yyps -= yyr2[yyn];
		yypvt = yypv;
		yypv -= yyr2[yyn];
		yyval = yypv[1];
		yym=yyn;
			/* consult goto table to find next state */
		yyn = yyr1[yyn];
		yyj = yypgo[yyn] + *yyps + 1;
		if( yyj>=YYLAST || yychk[ yystate = yyact[yyj] ] != -yyn ) yystate = yyact[yypgo[yyn]];
		switch(yym){
			
case 1:
# line 9 "translate.y"
{YYACCEPT;} break;
case 2:
# line 10 "translate.y"
{status=1;YYACCEPT;} break;
case 3:
# line 11 "translate.y"
{status=2;YYACCEPT;} break;
case 4:
# line 12 "translate.y"
{status=4;YYACCEPT;} break;
case 6:
# line 17 "translate.y"
{
				mpoladd(&temp,&tempmon,&temp);
			} break;
case 7:
# line 21 "translate.y"
{
				mpoladd(&temp,&tempmon,&temp);
			} break;
case 11:
# line 33 "translate.y"
{
				mnegate(&(tempmon.coefs[0]));
			} break;
case 12:
# line 39 "translate.y"
{
				MFREE(&coef);MSET(1,&coef);
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			} break;
case 13:
# line 45 "translate.y"
{
				MFREE(&coef);
				mstrtoul(&coef,numbers[yypvt[-2]],NULL,10);
				HS_ZFREE(numbers[yypvt[-2]]);numbers[yypvt[-2]]=NULL;
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			} break;
case 14:
# line 53 "translate.y"
{
				MFREE(&coef);
				mstrtoul(&coef,numbers[yypvt[-2]],NULL,10);
				HS_ZFREE(numbers[yypvt[-2]]);numbers[yypvt[-2]]=NULL;
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			} break;
case 15:
# line 61 "translate.y"
{
				MFREE(&coef);
				mstrtoul(&coef,numbers[yypvt[-0]],NULL,10);
				HS_ZFREE(numbers[yypvt[-0]]);numbers[yypvt[-0]]=NULL;
				mpolmonmove(&coef,expo,&tempmon);
				clean1();
			} break;
case 19:
# line 76 "translate.y"
{
				expo[0]+=(expo[yypvt[-2]+1]+= (short)strtol(numbers[yypvt[-0]],NULL,10));
				HS_ZFREE(numbers[yypvt[-0]]);
				numbers[yypvt[-0]]=NULL;
			} break;
case 20:
# line 82 "translate.y"
{
				expo[0]+=(expo[yypvt[-0]+1]+=1);
			} break; 
		}
		goto yystack;  /* stack new state and value */

	}
