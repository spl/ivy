CFLAGS=-I../../heapsafe-include -g -O3 --param max-inline-insns-single=1000 -DNDEBUG -fomit-frame-pointer -fno-strict-aliasing -Wall

all: bsd-_setjmp.o longjmp.o sigjmp.o clongjmp.o csigjmp.o

bsd-_setjmp.o: bsd-_setjmp.S
	$(CC) -c -m32 bsd-_setjmp.S

longjmp.o: longjmp.c
	$(CC) $(CFLAGS) -D__HS_NOCONCRC__ -c -o longjmp.o longjmp.c

sigjmp.o: sigjmp.c
	$(CC) $(CFLAGS) -D__HS_NOCONCRC__ -c -o sigjmp.o sigjmp.c

clongjmp.o: longjmp.c
	$(CC) $(CFLAGS) -c -o clongjmp.o longjmp.c

csigjmp.o: sigjmp.c
	$(CC) $(CFLAGS) -c -o csigjmp.o sigjmp.c
