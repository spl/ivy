# EnderUNIX Aget Makefile
# http://www.enderunix.org/aget/

OBJS = main.o Aget.o Misc.o Head.o Signal.o Download.o Resume.o
CFLAGS = -g -Wall -W 
CC = ivycc --sharc --heapsafe --deputy --sc-infer-sharing=$$PWD
STRIP = strip

all: $(OBJS)
	$(CC) -o aget $(OBJS) $(LDFLAGS)

strip: $(all)
	$(STRIP) aget
	
install:
	cp -f aget /usr/local/bin/aget

clean: 
	rm -rf aget *.o core.* *~ .ppatches *.cil.c *.i

c:
	rm -f *core* *~ *log
