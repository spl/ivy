SharC notes: this program gets one sharing error at exit time, when it 
accesses a protected-by-lock object without holding the lock. However,
there's only a single thread at that time.

=====================================================================

pfscan - a Parallell File Scanner

Copyright (c) 2002 Peter Eriksson <pen@lysator.liu.se>

----------------------------------------------------------------------

This program is free software; you can redistribute it and/or
modify it as you wish - as long as you don't claim that you wrote
it.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

----------------------------------------------------------------------

INTRODUCTION

Pfscan is a tool that sort-of functions as a parallellised version
of find + xargs + fgrep all-in-one - with some slight deviations.

Please note that the parallellism is not really useful (you might
be able to use 2 or 3 threads and see an improvement in search times,
but not much more) since most file systems and disks are inherently
sequential. 

However - if you have a highly parallell file system spread out over
multiple disks and a multi-CPU machine then this tool might be 
really fast. If you have such a system - please let me know of
your performance numbers :-) 

The latest version of pfscan can always be downloaded
from:

	ftp://ftp.lysator.liu.se/pub/unix/pfscan

There is also a small web page about it at:

	http://www.lysator.liu.se/~pen/pfscan


If you like it then I'd gladly accept a nice bottle of whisky,
some free beer or even just a "Thank you!" email :-)



INSTALLATION

Possibly edit the "Makefile" and the run 'make <SYSTEM>' where <SYSTEM>
currently may be:

	lnx	Linux with GCC v2
	gso	Solaris with GCC v3
	sol	Solaris with Forte C
	sol64   Solaris with Forte C generating 64bit code

(To be able to scan files larger than 2GB you must build
it as a 64 bit binary)

When it has been built you can install it with "make install".
It will by default install in /usr/local/bin and /usr/local/man/man1


USAGE

Start "pfscan" with the "-h" option for online help.

EXAMPLES

# Scan for the word "nobody" in the /usr/share/man tree
pfscan -n2 nobody /usr/share/man

# Scan (singlethreaded, case insensitive) for "gazonk" in /etc and /var
pfscan -n1 gazonk /etc /var
