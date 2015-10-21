# Introduction

Ivy is a compiler and runtime library for an extended dialect of C that checks
type, memory, and concurrency safety. Ivy relies on a small number of
lightweight annotations in the source code to keep time and space overheads
reasonable. Ivy is implemented as a C-to-C compiler using gcc as its backend.

[This repository](https://github.com/spl/ivy) is an attempt by [Sean
Leather](https://github.com/spl) to resurrect the code. The [old
website](http://ivy.cs.berkeley.edu) is no longer updated, and this project has
not seen an update since 2008.

# Building

Ivy builds on Linux and Mac OS X, in the usual Unix fashion:

    ./configure --prefix=<installation-path>
    make
    make install
