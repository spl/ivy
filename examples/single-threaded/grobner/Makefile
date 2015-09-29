# use gmake

EXEC	:= og
BINDIR	:= bin
INCDIR	:= include

CC	   :=	ivycc --heapsafe --deputy
FLAGS	:= -g -O3 $(EXTRACFLAGS)

SRC	:= Time.c NewPairs.c NewAddPol.c NewRed.c \
	   NewUtil.c og.c 

LIB	:= -Llib -lmultpol -lcmump $(EXTRALIBS) -lm
# - ----- no need to change the following

INCSTR	:= ${addprefix -I, ${INCDIR}}
LIBSTR	:= ${addprefix -L, ${LIBDIR}}
OBJ	:= ${addprefix ${BINDIR}/, ${addsuffix .o, ${basename ${SRC}}}}

${EXEC}	:  ${BINDIR} ${OBJ} makelib
	   ${CC} -g -o $@ ${OBJ} ${LIBSTR} ${LIB}

makelib:
	(cd cmump;make EXTRACFLAGS="$(EXTRACFLAGS)" CC="$(CC)")
	(cd multpol;make EXTRACFLAGS="$(EXTRACFLAGS)" CC="$(CC)")

${BINDIR}:
	   mkdir ${BINDIR}

${BINDIR}/%.o: %.c
	   ${CC} ${FLAGS} ${INCSTR} -o $@ -c $*.c

clean	: cleantarget
	sh mclean

cleantarget:
	rm -f ${EXEC}

tags:
	etags *.c include/*.h cmump/*.c multpol/*.c
