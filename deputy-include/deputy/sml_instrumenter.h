
#ifndef _SML_INSTRUMENTER_H_
#define _SML_INSTRUMENTER_H_

#include <deputy/lwcalls.h>

typedef unsigned int u32;


/* XXX: Add codes for each instr type, interpret in SML code */
#define INSTR_WIDTH  15
#define INSTR_MAX    2200000

#define ASSIGNBASIC   0
#define ASSIGNBOP    10
#define ASSIGNUOP    20
#define ASSIGNCAST   30
#define RETBASIC     40
#define RETBOP       50
#define RETUOP       60
#define RETVOID      70
#define IFBASIC      80
#define IFBOP        90
#define IFUOP       100
#define SWITCHBASIC 110
#define SWITCHBOP   120
#define SWITCHUOP   130

#define PUSHARG     140
#define POPARG      150
#define FUNSTART    160
#define RETPOP      170
#define RETNORET    180

#define UNREGLOCAL  190

#define TAINT       200
#define CONDT       210

#define CLEQCODE    220

#define CLEQSUM     230
#define CSUMLEQ     240

struct funInstrList {
	u32 *instrs;
	u32 next;
	u32 max;
};

#define BOP_PLUSA   0
#define BOP_PLUSPI  1
#define BOP_INDEXPI 2
#define BOP_MINUSA  3
#define BOP_MINUSPI 4
#define BOP_MINUSPP 5
#define BOP_MULT    6
#define BOP_DIV     7
#define BOP_MOD     8
#define BOP_SHIFTL  9
#define BOP_SHIFTR  10
#define BOP_LT      11
#define BOP_GT      12
#define BOP_LE      13
#define BOP_GE      14
#define BOP_EQ      15
#define BOP_NE      16
#define BOP_BAND    17
#define BOP_BXOR    18
#define BOP_BOR     19
#define BOP_LAND    20
#define BOP_LOR     21

#define UOP_NEG     0
#define UOP_BNOT    1
#define UOP_LNOT    2


#ifndef IN_GLOB_STATE_C

#define NULL (void *)0;
#define INLINE inline __attribute__((always_inline))
//#define INLINE

extern struct funInstrList fil;

#define APPARGS1 u32 a1
#define APPARGS2 APPARGS1, u32 a2
#define APPARGS3 APPARGS2, u32 a3
#define APPARGS4 APPARGS3, u32 a4
#define APPARGS5 APPARGS4, u32 a5
#define APPARGS6 APPARGS5, u32 a6
#define APPARGS7 APPARGS6, u32 a7
#define APPARGS8 APPARGS7, u32 a8
#define APPARGS9 APPARGS8, u32 a9
#define APPARGS10 APPARGS9, u32 a10
#define APPARGS11 APPARGS10, u32 a11
#define APPARGS12 APPARGS11, u32 a12
#define APPARGS13 APPARGS12, u32 a13
#define APPARGS14 APPARGS13, u32 a14
#define APPARGS15 APPARGS14, u32 a15

#define FILLINSTR1 fil.instrs[ri] = a1
#define FILLINSTR2 FILLINSTR1; fil.instrs[ri+1] = a2
#define FILLINSTR3 FILLINSTR2; fil.instrs[ri+2] = a3
#define FILLINSTR4 FILLINSTR3; fil.instrs[ri+3] = a4
#define FILLINSTR5 FILLINSTR4; fil.instrs[ri+4] = a5
#define FILLINSTR6 FILLINSTR5; fil.instrs[ri+5] = a6
#define FILLINSTR7 FILLINSTR6; fil.instrs[ri+6] = a7
#define FILLINSTR8 FILLINSTR7; fil.instrs[ri+7] = a8
#define FILLINSTR9 FILLINSTR8; fil.instrs[ri+8] = a9
#define FILLINSTR10 FILLINSTR9; fil.instrs[ri+9] = a10
#define FILLINSTR11 FILLINSTR10; fil.instrs[ri+10] = a11
#define FILLINSTR12 FILLINSTR11; fil.instrs[ri+11] = a12
#define FILLINSTR13 FILLINSTR12; fil.instrs[ri+12] = a13
#define FILLINSTR14 FILLINSTR13; fil.instrs[ri+13] = a14
#define FILLINSTR15 FILLINSTR14; fil.instrs[ri+14] = a15

#define FUNINSTRLISTAPP(N) \
INLINE static void funInstrListApp##N(APPARGS##N)\
{\
	int ri;\
	if (fil.next == fil.max) {\
		process_instrs(fil.instrs,fil.max,INSTR_WIDTH);\
		fil.next = 0;\
	}\
	ri = fil.next * INSTR_WIDTH;\
	FILLINSTR##N;\
	fil.next++;\
	return;\
}

FUNINSTRLISTAPP(1);
FUNINSTRLISTAPP(2);
FUNINSTRLISTAPP(3);
FUNINSTRLISTAPP(4);
FUNINSTRLISTAPP(5);
FUNINSTRLISTAPP(6);
FUNINSTRLISTAPP(7);
FUNINSTRLISTAPP(8);
FUNINSTRLISTAPP(9);
FUNINSTRLISTAPP(10);
FUNINSTRLISTAPP(11);
FUNINSTRLISTAPP(12);
FUNINSTRLISTAPP(13);
FUNINSTRLISTAPP(14);
FUNINSTRLISTAPP(15);

/*
INLINE static void
funInstrListPush()
{
	struct funInstrList *new = malloc(sizeof(struct funInstrList));
	new->instrs = malloc(100000 * sizeof(u32) * INSTR_WIDTH);
	new->max = 100000;
	new->next = 0;
	new->lnext = fil_stack;
	fil_stack = new;
	return;
}

INLINE static void
funInstrListPop()
{
	struct funInstrList *tmp = fil_stack;
	if (tmp) {
		if (tmp->instrs) {
			process_instrs(tmp->instrs, tmp->next, INSTR_WIDTH);
			free(tmp->instrs);
		}
		fil_stack = tmp->lnext;
		free(tmp);
	}
	return;
}
*/

#define BOP_PLUSA   0
#define BOP_PLUSPI  1
#define BOP_INDEXPI 2
#define BOP_MINUSA  3
#define BOP_MINUSPI 4
#define BOP_MINUSPP 5
#define BOP_MULT    6
#define BOP_DIV     7
#define BOP_MOD     8
#define BOP_SHIFTL  9
#define BOP_SHIFTR  10
#define BOP_LT      11
#define BOP_GT      12
#define BOP_LE      13
#define BOP_GE      14
#define BOP_EQ      15
#define BOP_NE      16
#define BOP_BAND    17
#define BOP_BXOR    18
#define BOP_BOR     19
#define BOP_LAND    20
#define BOP_LOR     21

#define UOP_NEG     0
#define UOP_BNOT    1
#define UOP_LNOT    2

/************** Printing */

static void print_bop(unsigned int bop)
{
	switch(bop) {
		case BOP_PLUSA:
		case BOP_PLUSPI:
		case BOP_INDEXPI: printf(" + "); break;
		case BOP_MINUSA:
		case BOP_MINUSPI:
		case BOP_MINUSPP: printf(" - "); break;
		case BOP_MULT:    printf(" * "); break;
		case BOP_DIV:     printf(" / "); break;
		case BOP_MOD:     printf(" \% "); break;
		case BOP_SHIFTL:  printf(" << "); break;
		case BOP_SHIFTR:  printf(" >> "); break;
		case BOP_LT:      printf(" < "); break;
		case BOP_GT:      printf(" > "); break;
		case BOP_LE:      printf(" <= "); break;
		case BOP_GE:      printf(" >= "); break;
		case BOP_EQ:      printf(" == "); break;
		case BOP_NE:      printf(" != "); break;
		case BOP_BAND:    printf(" & "); break;
		case BOP_BXOR:    printf(" ^ "); break;
		case BOP_BOR:     printf(" | "); break;
		case BOP_LAND:    printf(" && "); break;
		case BOP_LOR:     printf(" || "); break;
		default:          printf(" ?? "); break;
	}
}

static void print_uop(unsigned int uop)
{
	switch(uop) {
		case UOP_NEG:  printf(" - "); break;
		case UOP_BNOT: printf(" ~ "); break;
		case UOP_LNOT: printf(" ! "); break;
		default:       printf(" ?? "); break;
	}
}


#define VOIDARGS0
#define VOIDARGS1 unsigned int a1
#define VOIDARGS2 VOIDARGS1, unsigned int a2
#define VOIDARGS3 VOIDARGS2, unsigned int a3
#define VOIDARGS4 VOIDARGS3, unsigned int a4
#define VOIDARGS5 VOIDARGS4, unsigned int a5
#define VOIDARGS6 VOIDARGS5, unsigned int a6
#define VOIDARGS7 VOIDARGS6, unsigned int a7
#define VOIDARGS8 VOIDARGS7, unsigned int a8
#define VOIDARGS9 VOIDARGS8, unsigned int a9
#define VOIDARGS10 VOIDARGS9, unsigned int a10
#define VOIDARGS11 VOIDARGS10, unsigned int a11
#define VOIDARGS12 VOIDARGS11, unsigned int a12
#define VOIDARGS13 VOIDARGS12, unsigned int a13
#define VOIDARGS14 VOIDARGS13, unsigned int a14
#define VOIDARGS15 VOIDARGS14, unsigned int a15
#define VOIDARGS16 VOIDARGS15, unsigned int a16
#define VOIDARGS17 VOIDARGS16, unsigned int a17

#define DINSTRFun(name, args) INLINE static void DINSTR_##name(VOIDARGS##args)

INLINE static unsigned int
negate_bop(unsigned int bop)
{
	switch(bop) {
		case BOP_LT: return BOP_GE;
		case BOP_GT: return BOP_LE;
		case BOP_LE: return BOP_GT;
		case BOP_GE: return BOP_LT;
		default: return bop;
	}
}


/*
INLINE static in isNeg(struct exp *e)
{
	return (e != NULL) && (e->type == BASICTYP) && (e->e.basic->neg == 1);
}
*/

DINSTRFun(Assign,5)
{

	funInstrListApp6(ASSIGNBASIC,a1,a2,a3,a4,a5);
	return;
}


DINSTRFun(Bop,10)
{
	funInstrListApp11(ASSIGNBOP,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10);
	return;
}

DINSTRFun(Uop,6)
{
	funInstrListApp7(ASSIGNUOP,a1,a2,a3,a4,a5,a6);
	return;
}


DINSTRFun(PushArg,4)
{
	funInstrListApp5(PUSHARG,a1,a2,a3,a4);
	return;
}

DINSTRFun(PopArg,1)
{
	funInstrListApp2(POPARG,a1);
    return;
}

DINSTRFun(UnRegLocal,3)
{
	funInstrListApp4(UNREGLOCAL,a1,a2,a3);
	return;
}

DINSTRFun(FunStart,1)
{
	funInstrListApp2(FUNSTART,a1);
	return;
}

/* a1 - symbolic op
 * a2 - type(pointer/scalar)
 * a3 - size
 */
DINSTRFun(RegisterField, 3)
{
	return;
}

/* make sure memory range [p,p+sz] is all zero */
INLINE static unsigned int
DINSTR_IsNull(unsigned int p, unsigned int sz)
{
	char *c = (char *)p;
	int i = 0;
	while(c < p + sz) {
		if(*c) return 0;
		c++;
	}
	return 1;
}

/*
 * a1 - start address
 * a2 - element size
 * a3 - number of elements. -1 => Nullterm
 * a4 - pointer to element registration function
 */
DINSTRFun(RegisterArray, 4)
{
	return;
}

DINSTRFun(Cast,5)
{
	funInstrListApp6(ASSIGNCAST,a1,a2,a3,a4,a5);
	return;
}

DINSTRFun(RetBasic,4)
{
	funInstrListApp5(RETBASIC,a1,a2,a3,a4);
	return;
}

DINSTRFun(RetBop,9)
{
	funInstrListApp10(RETBOP,a1,a2,a3,a4,a5,a6,a7,a8,a9);
	return;
}

DINSTRFun(RetUop,5)
{
	funInstrListApp6(RETUOP,a1,a2,a3,a4,a5);
	return;
}

DINSTRFun(RetVoid,0)
{
	funInstrListApp1(RETVOID);
	return;
}


DINSTRFun(RetPop,5)
{
	funInstrListApp6(RETPOP,a1,a2,a3,a4,a5);
	return;
}

DINSTRFun(RetNoRet,1)
{
	funInstrListApp2(RETNORET,a1);
	return;
}

DINSTRFun(IfBasic,6)
{
	funInstrListApp7(IFBASIC,a1,a2,a3,a4,a5,a6);
	return;
}

DINSTRFun(IfBop,11)
{
	funInstrListApp12(IFBOP,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11);
	return;
}

DINSTRFun(IfUop,7)
{
	funInstrListApp8(IFUOP,a1,a2,a3,a4,a5,a6,a7);
	return;
}

DINSTRFun(SwitchBasic,5)
{
	funInstrListApp6(SWITCHBASIC,a1,a2,a3,a4,a5);
	return;
}

DINSTRFun(SwitchBop,10)
{
	funInstrListApp11(SWITCHBOP,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10);
	return;
}

DINSTRFun(SwitchUop,6)
{
	funInstrListApp7(SWITCHUOP,a1,a2,a3,a4,a5,a6);
	return;
}

DINSTRFun(CNonNull,4) {return;}
DINSTRFun(CEq,8) {return;}
DINSTRFun(CMult,8) {return;}
DINSTRFun(CPtrArith,17){return;}
DINSTRFun(CPtrArithNT,17) {return;}
DINSTRFun(CPtrArithAccess,17) {return;}
DINSTRFun(CLeqInt,8) {return;}
DINSTRFun(CLeq,10)
{
	funInstrListApp11(CLEQCODE,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10);
	return;
}

DINSTRFun(CLeqSum,14)
{
	funInstrListApp15(CLEQSUM,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14);
	return;
}
DINSTRFun(CSumLeq,14)
{
	funInstrListApp15(CSUMLEQ,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14);
	return;
}
DINSTRFun(CLeqNT,9) {return;}
DINSTRFun(CNullOrLeq,12) {return;}
DINSTRFun(CNullOrLeqNT,13) {return;}
DINSTRFun(CWriteNT,13) {return;}
DINSTRFun(CNullUnionOrSelected,8) {return;}
DINSTRFun(CSelected,4) {return;}
DINSTRFun(CNotSelected,4) {return;}

DINSTRFun(taint,5)
{
	funInstrListApp6(TAINT,a1,a2,a3,a4,a5);
	return;
}

DINSTRFun(ctaint,8)
{
	funInstrListApp9(CONDT,a1,a2,a3,a4,a5,a6,a7,a8);
	return;
}

DINSTRFun(Argv,4)
{
	int argc = a1, i;
	char **argv = a2;

	for(i = 0; i < argc; i++)
		funInstrListApp6(TAINT,argv[i],1,strlen(argv[i])+1,a3,a4);

	return;
}

INLINE static void DINSTR_init()
{
	fil.instrs = malloc(INSTR_MAX * sizeof(u32) * INSTR_WIDTH);
	fil.max = INSTR_MAX;
	fil.next = 0;
	return;
}

INLINE static void DINSTR_end()
{
	process_instrs(fil.instrs,fil.next,INSTR_WIDTH);
	free(fil.instrs);
	return;
}
INLINE static void DINSTR_nop()  { return; }

#endif
#endif /* _SML_INSTRUMENTER_H_ */
