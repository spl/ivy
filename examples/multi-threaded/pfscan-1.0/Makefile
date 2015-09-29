# Makefile for pfscan

DESTDIR=/usr/local

BINDIR=$(DESTDIR)/bin
MANDIR=$(DESTDIR)/man
MAN1DIR=$(MANDIR)/man1

TAR=tar
GZIP=gzip
MAKE=make
INSTALL=./install-sh


## Solaris 8 with Gcc 3.0
GSO_CC=gcc -Wall -g -O -pthreads
GSO_LDOPTS=
GSO_LIBS= -lnsl -lsocket

## Solaris 8 with Forte C 6.2
SOL_CC=cc -mt -O
SOL_LDOPTS=
SOL_LIBS= -lpthread -lnsl -lsocket

## Linux 2.4 with Gcc 2.96
LNX_CC=ivycc --heapsafe --sharc --deputy -Wall -g -O --sc-infer-sharing=$$PWD -include hslib.h
#LNX_CC=ivycc -Wall -g --heapsafe --hs-debug -include hslib.h
LNX_LDOPTS=#-Wl,-s 
LNX_LIBS=-lpthread -lnsl

## Darwin
APL_CC=ivycc --heapsafe --sharc --deputy -Wall -g -O --sc-infer-sharing=$$PWD -include hslib.h
#APL_CC=ivycc -Wall -g --heapsafe --hs-debug -include hslib.h
APL_LDOPTS=#-Wl,-s 
APL_LIBS=-lpthread


OBJS = pfscan.o bm.o version.o pqueue.o


help:
	@echo 'Use "make SYSTEM" where SYSTEM may be:'
	@echo '   lnx      (Linux with GCC)'
	@echo '   gso      (Solaris with GCC v3)'
	@echo '   sol      (Solaris with Forte C)'
	@echo 'Note: this program does not work on Darwin (some problem with ftw)'

lnx linux:
	@$(MAKE) all CC="$(LNX_CC)" LIBS="$(LNX_LIBS)" LDOPTS="$(LNX_LDOPTS)"

apl apple:
	@$(MAKE) all CC="$(APL_CC)" LIBS="$(APL_LIBS)" LDOPTS="$(APL_LDOPTS)"

gso:
	@$(MAKE) all CC="$(GSO_CC)" LIBS="$(GSO_LIBS)" LDOPTS="$(GSO_LDOPTS)"

sol solaris:
	@$(MAKE) all CC="$(SOL_CC)" LIBS="$(SOL_LIBS)" LDOPTS="$(SOL_LDOPTS)"

sol64:
	@$(MAKE) all CC="$(SOL_CC) -xarch=v9" LIBS="$(SOL_LIBS)" LDOPTS="$(SOL_LDOPTS)"


all: pfscan

man: pfscan.1

pfscan.1:	pfscan.sgml
	docbook2man pfscan.sgml

pfscan: $(OBJS)
	$(CC) $(LDOPTS) -o pfscan $(OBJS) $(LIBS)


version:
	(PACKNAME=`basename \`pwd\`` ; echo 'char version[] = "'`echo $$PACKNAME | cut -d- -f2`'";' >version.c)

clean distclean:
	-killall ivy.asm.exe
	-rm -rf *.o *~ pfscan core manpage.* \#* *.cil.c *.i .ppatches

dist:	distclean version
	(PACKNAME=`basename \`pwd\`` ; cd .. ; $(TAR) cf - $$PACKNAME | $(GZIP) -9 >$$PACKNAME.tar.gz)


install: all
	$(INSTALL) -c -m 755 pfscan $(BINDIR)

install-man: man
	$(INSTALL) -c -m 644 pfscan.1 $(MAN1DIR)


install-all install-distribution: install install-man
