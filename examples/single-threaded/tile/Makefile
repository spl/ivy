CC=	ivycc --heapsafe --deputy
CFLAGS  = -g -O3 -I.. $(EXTRACFLAGS)
OBJS=	tile.o main.o token.o common.o
LEX=	flex

tile: $(OBJS)
	$(CC) -g -o htile $(OBJS) $(EXTRALIBS) -lm -lfl

common.c: mkcommon
	sh ./mkcommon > common.c

#token.c: token.l
#	flex -otoken.c token.l

clean:
	rm -f *.o htile common.c

cleantarget:
	rm htile
