CFLAGS=-I../../heapsafe-include -g -O3 --param max-inline-insns-single=1000 -DNDEBUG -fomit-frame-pointer

all: setjmp.o _setjmp.o csetjmp.o sigsetjmp.o conccsetjmp.o concsigsetjmp.o

setjmp.o: setjmp.s
	$(CC) -c -m32 -I. setjmp.s

_setjmp.o: _setjmp.s
	$(CC) -c -m32 -I. _setjmp.s

csetjmp.o: csetjmp.c
	$(CC) $(CFLAGS) -D__HS_NOCONCRC__ -c -o csetjmp.o csetjmp.c

sigsetjmp.o: sigsetjmp.c
	$(CC) $(CFLAGS) -D__HS_NOCONCRC__ -c -o sigsetjmp.o sigsetjmp.c

conccsetjmp.o: csetjmp.c
	$(CC) $(CFLAGS) -c -o conccsetjmp.o csetjmp.c

concsigsetjmp.o: sigsetjmp.c
	$(CC) $(CFLAGS) -c -o concsigsetjmp.o sigsetjmp.c
