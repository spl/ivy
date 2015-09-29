/*
 * instr_glob_state.c
 *
 * global state for the instrumenter.
 *
 */

#define IN_GLOB_STATE_C

#include <oct/oct.h>
#include <deputy/sml_instrumenter.h>

struct funInstrList fil;

#define CAST(t,sz,e) ((t) == 0 ? ((sz) == 8 ? ((unsigned char)e) :\
                               ((sz) == -8 ? ((char)e) :\
                               ((sz) == 16 ? ((unsigned short)e) :\
                               ((sz) == -16 ? ((short)e) :\
                               ((sz) == 32 ? ((unsigned int)e) :\
                               ((sz) == -32 ? ((int)e) :\
                               ((sz) == 64 ? ((unsigned long long)e) :\
                               ((sz) == -64 ? ((long long)e) : (e))))))))) :\
                               (e))

#define SCALE(sz,e) ((sz)*(e))

unsigned int
c_eval_bop(unsigned int bop,
           unsigned int o1, unsigned int t1, unsigned int sz1,
           unsigned int o2, unsigned int t2, unsigned int sz2)
{
	switch(bop) {
		case BOP_PLUSA:   return CAST(t1,sz1,o1) + CAST(t2,sz2,o2);
		case BOP_PLUSPI:  return o1 + SCALE(sz1,CAST(t2,sz2,o2));
		case BOP_INDEXPI: return o1 + SCALE(sz1,CAST(t2,sz2,o2));
		case BOP_MINUSA:  return CAST(t1,sz1,o1) - CAST(t2,sz2,o2);
		case BOP_MINUSPI: return o1 - SCALE(sz1,CAST(t2,sz2,o2));
		case BOP_MINUSPP: return o1 - o2;
		case BOP_MULT:    return CAST(t1,sz1,o1) * CAST(t2,sz2,o2);
		case BOP_DIV:     return CAST(t1,sz1,o1) / CAST(t2,sz2,o2);
		case BOP_MOD:     return CAST(t1,sz1,o1) % CAST(t2,sz2,o2);
		case BOP_SHIFTL:  return CAST(t1,sz1,o1) << CAST(t2,sz2,o2);
		case BOP_SHIFTR:  return CAST(t1,sz1,o1) >> CAST(t2,sz2,o2);
		case BOP_LT:      return CAST(t1,sz1,o1) < CAST(t2,sz2,o2);
		case BOP_GT:      return CAST(t1,sz1,o1) > CAST(t2,sz2,o2);
		case BOP_LE:      return CAST(t1,sz1,o1) <= CAST(t2,sz2,o2);
		case BOP_GE:      return CAST(t1,sz1,o1) >= CAST(t2,sz2,o2);
		case BOP_EQ:      return CAST(t1,sz1,o1) == CAST(t2,sz2,o2);
		case BOP_NE:      return CAST(t1,sz1,o1) != CAST(t2,sz2,o2);
		case BOP_BAND:    return CAST(t1,sz1,o1) & CAST(t2,sz2,o2);
		case BOP_BXOR:    return CAST(t1,sz1,o1) ^ CAST(t2,sz2,o2);
		case BOP_BOR:     return CAST(t1,sz1,o1) | CAST(t2,sz2,o2);
		case BOP_LAND:    return CAST(t1,sz1,o1) && CAST(t2,sz2,o2);
		case BOP_LOR:     return CAST(t1,sz1,o1) || CAST(t2,sz2,o2);
		default:          return -1;
	}
}

unsigned int
c_eval_uop(unsigned int uop, unsigned int op, unsigned int t, unsigned int sz)
{
	switch(uop) {
		case UOP_NEG:  return -CAST(t,sz,op);
		case UOP_BNOT: return ~CAST(t,sz,op);
		case UOP_LNOT: return !CAST(t,sz,op);
		default:       return -1;
	}
}

unsigned int
c_int32_hash(unsigned int w, unsigned int mask)
{
	w = (w+0x7ed55d16) + (w<<12);
	w = (w^0xc761c23c) ^ (w>>19);
	w = (w+0x165667b1) + (w<<5);
	w = (w+0xd3a2646c) ^ (w<<9);
	w = (w+0xfd7046c5) + (w<<3);
	w = (w^0xb55a4f09) ^ (w>>16);
	return w & mask;
}

void
c_print_loc(const char *file, unsigned int line)
{
	printf("%s:%d",file,line);
	fflush((void *)0);
	return;
}

/* From here down are wrappers for Mine's octagon library */

int c_oct_init() {return oct_init();}
oct_t *c_oct_empty(unsigned int n) {return oct_empty(n);}
oct_t *c_oct_universe(unsigned int n) {return oct_universe(n);}
oct_t *c_oct_copy(oct_t *o) {return oct_copy(o);}
void c_oct_print(oct_t *o) {oct_print(o);return;}
void c_oct_free(oct_t *o) {oct_free(o);return;}
unsigned int c_oct_dimension(oct_t *o) {return oct_dimension(o);}
unsigned int c_oct_is_empty(oct_t *o) {return oct_is_empty(o);}
unsigned int c_oct_is_universe(oct_t *o) {return oct_is_universe(o);}
unsigned int c_oct_is_included_in(oct_t *o1, oct_t *o2)
	{return oct_is_included_in(o1,o2);}
unsigned int c_oct_is_equal(oct_t *o1, oct_t *o2)
	{return oct_is_equal(o1,o2);}

oct_t *c_oct_add_constraint(oct_t *o, unsigned int *coefs, unsigned int nb)
{
	int i;
	oct_t *newo;

	num_t *ncs = new_n(num_t,nb);
	num_init_n(ncs,nb);

	for (i = 0; i < nb; i++) {
		num_set_int(&ncs[i],coefs[i]);
	}

	newo = oct_add_constraint(o, ncs, true);
	oct_mm_free(ncs);

	return newo;
}

void c_oct_get_box(oct_t *o, int *box, int *valid)
{
	int i;
	int dim = oct_dimension(o);
	num_t *nbox = oct_get_box(o);

	if (!nbox) {
		for (i = 0; i < 2 * dim; i++)
			valid[i] = 0;
		return;
	}

	for (i = 0; i < 2 * dim; i++) {
		if (num_fits_int(&nbox[i])) {
			box[i] = num_get_int(&nbox[i]);
			valid[i] = 1;
		}
		else
			valid[i] = 0;
	}

	oct_mm_free(nbox);
	return;
}

oct_t *c_oct_add_dimension(oct_t *o, unsigned int num)
{
	return oct_add_dimensions_and_embed(o, num, true);
}


#undef IN_GLOB_STATE_C
