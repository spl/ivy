prefix = /usr/local
exec_prefix = ${prefix}
libdir = ${exec_prefix}/lib
pkglibdir = $(libdir)/ivy

IVYLIBSRC = pthread_wrappers.c
LIB_FILES = pthread_wrappers.o

CFLAGS=-g -O3 --param max-inline-insns-single=1000 -DNDEBUG -fomit-frame-pointer -fno-strict-aliasing

LIBRARIES = ivy_libc.a

ivy_libc.a: $(IVYLIBSRC)
	$(CC) -c $(CFLAGS) $(IVYLIBSRC)
	rm -f $@; ar r $@ $(LIB_FILES)

clean:
	rm -f *.o *.a

INSTALL = /usr/bin/install -c
INSTALL_DATA = ${INSTALL} -m 644
INSTALL_PROGRAM = ${INSTALL}

INSTALL_FILES = $(LIBRARIES)

install: $(INSTALL_FILES)
	$(INSTALL_DATA) $(INSTALL_FILES) $(DESTDIR)$(pkglibdir)/lib

# Look out for outdated Makefiles; if it's out of date, this will automatically
# re-run ./config.status, then re-exec make with the same arguments.
Makefile: ../config.status Makefile.in
	@echo "Rebuilding the Makefile"
	(cd ..;./config.status)
