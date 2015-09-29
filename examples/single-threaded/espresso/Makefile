INC = ansi.h copyright.h espresso.h main.h mincov.h mincov_int.h port.h sparse.h sparse_int.h stdlib.h utility.h

SRC =  cofactor.c cols.c compl.c contain.c cubestr.c cvrin.c cvrm.c cvrmisc.c cvrout.c dominate.c equiv.c espresso.c essen.c exact.c expand.c gasp.c getopt.c gimpel.c globals.c hack.c indep.c irred.c main.c map.c matrix.c mincov.c opo.c pair.c part.c primes.c reduce.c rows.c set.c setc.c sharp.c sminterf.c solution.c sparse.c unate.c utility.c verify.c # dlmalloc28.c

ifeq ($(OS),Windows_NT)
CC = cl
CFLAGS = /DNDEBUG /Ox /MD /DWIN32 # -DHEAP_CHECKS=1
.SUFFIXES: .obj
OBJS=$(SRC:.c=.obj)
%.obj: %.c
	$(CC) $(CFLAGS) -c $< 
else
CC = ivycc --heapsafe
CFLAGS = -DNDEBUG -g -O3 $(EXTRACFLAGS)
OBJS=$(SRC:.c=.o)
.c.o:
	$(CC) $(CFLAGS) -c $<
endif

espresso: $(SRC) $(OBJS) $(INC)
	$(CC) $(CFLAGS) $(OBJS) -o espresso -lm $(EXTRALIBS)

espresso-winhard: $(SRC) $(OBJS) $(INC)
	$(CC) $(CFLAGS) $(OBJS) usewinhard.obj winhard.lib -o espresso-hard

espresso-winhard-adaptive: $(SRC) $(OBJS) $(INC)
	$(CC) $(CFLAGS) $(OBJS) usewinhard-adaptive.obj winhard-adaptive.lib -o espresso-hard-adaptive

espresso-winhard-doa: $(SRC) $(OBJS) $(INC)
	$(CC) $(CFLAGS) $(OBJS) usewinhard-adaptive.obj winhard-diefast.lib -o espresso-hard-diefast

espresso-hoard: $(SRC) $(OBJS) $(INC)
	$(CC) $(CFLAGS) $(OBJS) usewinhoard.obj winhoard.lib -o espresso-hoard

espresso-hard: $(SRC) $(OBJS) $(INC)
	$(CC) $(CFLAGS) $(OBJS) usewinhard.obj winhard.lib -o espresso-hard

clean:
	-rm -f $(OBJS) espresso

