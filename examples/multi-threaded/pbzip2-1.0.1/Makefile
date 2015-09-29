# Make file for parallel BZIP2
SHELL=/bin/sh
BZ2DIR=../bzip2-1.0.4

# Compiler to use
CC=ivycc --heapsafe --sharc --sc-infer-sharing=$$PWD -include hslib.h

# Where you want pbzip2 installed when you do 'make install'
PREFIX=/usr

all: pbzip2

# Made static version standard
pbzip2: $(BZ2DIR)/libbz2.a pbzip2.c
	$(CC) -g -D_LARGEFILE64_SOURCE -D_FILE_OFFSET_BITS=64 -o pbzip2 pbzip2.c \
	  -lpthread -I. -L$(BZ2DIR) -lbz2 `pkg-config --libs --cflags glib-2.0`

# Choose this if you want to compile pbzip2 without load average support for
# systems that do not support it
pbzip2-noloadavg: $(BZ2DIR)/libbz2.a pbzip2.c
	$(CC) -O3 -D_LARGEFILE64_SOURCE -D_FILE_OFFSET_BITS=64 -DPBZIP_NO_LOADAVG \
	  -o pbzip2 pbzip2.c -pthread -lpthread -L$(BZ2DIR) -lbz2 `pkg-config --libs --cflags glib-2.0`

# Compatability mode for 32bit file sizes (less than 2GB) and systems
# that have compilers that treat int as 64bit natively (ie: modern AIX)
pbzip2-compat: $(BZ2DIR)/libbz2.a pbzip2.c
	$(CC) -O3 -o pbzip2 pbzip2.c -pthread -lpthread  -L$(BZ2DIR) -lbz2 \
	  `pkg-config --libs --cflags glib-2.0`

# Install the binary pbzip2 program and man page
install: pbzip2
	if ( test ! -d $(PREFIX)/bin ) ; then mkdir -p $(PREFIX)/bin ; fi
	if ( test ! -d $(PREFIX)/man ) ; then mkdir -p $(PREFIX)/man ; fi
	if ( test ! -d $(PREFIX)/man/man1 ) ; then mkdir -p $(PREFIX)/man/man1 ; fi
	cp -f pbzip2 $(PREFIX)/bin/pbzip2
	chmod a+x $(PREFIX)/bin/pbzip2
	cp -f pbzip2.1 $(PREFIX)/man/man1
	chmod a+r $(PREFIX)/man/man1/pbzip2.1

clean:
	-killall ivy.asm.exe
	rm -rf .ppatches *.o pbzip2 *.i *.cil.c
	(cd ../bzip2-1.0.4;make clean)

$(BZ2DIR)/libbz2.a:
	make -C $(BZ2DIR)
