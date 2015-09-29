/* regular definitions */
%START COMMENT

beg_com \/\*
end_com \*\/
sep_pol	; 
ws	[ \t\n]*
mult    \*
plus	\+
minus	\-
power	\^
letter	[A-Za-z]
digit	[0-9]
symbol	{letter}({letter}|{digit})*
number	({digit})+
%%

{ws}			{return(SEP);}
{ws}?{sep_pol}		{return(STOP); }
{ws}?{mult}{ws}?	{return(TIMES);}
{power}			{return(POWER);}
{symbol}		{if((yylval = id_var())>=0) return(SYMBOL); else return(UNKNOWN);}
{number}		{if((yylval = id_num())>=0) return(NUMBER); else return(FULBUF);}
{ws}?{plus}{ws}?	{return(PLUS);}
{ws}?{minus}{ws}?	{return(MINUS);}
{ws}?{beg_com}		{BEGIN COMMENT	;}

<COMMENT>([^\*]|\*[^\/])*	{}
<COMMENT>{end_com}{ws}?		{BEGIN 0;return(SEP);}

%%

int id_var(void)
{
	int i;

	for (i=0;i<nvars;i++){
		if (!strcmp(yytext,varnames[i]))
			return(i);
	}
	/* when it finds an unknown ...*/
	printf("Unknown variable : %s\n", yytext);
	status=3;
	return(-1);
};


int id_num(void)
{
	int i;
	
	for ( i=0; (i<NBUF) && (numbers[i]!=NULL); i++ )
		;
	if (i==NBUF)
		return(-1);
	else {
		/* printf("call malloc: %d\n",sizeof(char)*(yyleng+1)); */
		char *tmp = malloc(sizeof(char)*(yyleng+1)) ; 
		strncpy(tmp,yytext,yyleng);
		tmp[yyleng]='\0';
		numbers[i] = (char *NTS)TC(tmp);
		return(i);
	}
};

int yywrap(void) {
	return 0;
}

