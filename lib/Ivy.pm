#
#
# Copyright (c) 2001-2002, 
#  George C. Necula    <necula@cs.berkeley.edu>
#  Scott McPeak        <smcpeak@cs.berkeley.edu>
#  Wes Weimer          <weimer@cs.berkeley.edu>
# All rights reserved.
# 
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# 1. Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer.
#
# 2. Redistributions in binary form must reproduce the above copyright
# notice, this list of conditions and the following disclaimer in the
# documentation and/or other materials provided with the distribution.
#
# 3. The names of the contributors may not be used to endorse or promote
# products derived from this software without specific prior written
# permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
# IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
# TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
# PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
# OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
# PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#

# This package is used from an environment when CilConfig.pm has been loaded
package Ivy;
use strict;

$::version_major = 1;
$::version_minor = 0;
$::version_sub = 0;

use Cilly;

# NOTE: If perl chokes, complaining about 'our', or
# "Array found where operator expected", it's because
# you need perl version 5.6.0 or later.
our @ISA = qw(Cilly);

sub new {
    my ($proto, @args) = @_;
    my $class = ref($proto) || $proto;

    # Select the directory containing Ivy's executables.  We look in
    # both places in order to accomodate the build and distribution
    # directory layouts.
    my $bin;
    my $lib;
    if (-x "$::ivyhome/obj/$::archos/ivy.asm.exe") {
        $bin = "$::ivyhome/obj/$::archos";
        $lib = "$::ivyhome/obj/$::archos";
    } elsif (-x "$::ivyhome/bin/ivy.asm.exe") {
        $bin = "$::ivyhome/bin";
        $lib = "$::ivyhome/lib";
    } else {
        die "Couldn't find directory containing Ivy executables.\n" .
            "Please ensure that Ivy is compiled and installed properly.\n";
    }

    # Select the most recent executable
    my $mtime_asm = int((stat("$bin/ivy.asm.exe"))[9]);
    my $mtime_byte = int((stat("$bin/ivy.byte.exe"))[9]);
    my $use_debug = 
            grep(/--bytecode/, @args) ||
            grep(/--ocamldebug/, @args) ||
            ($mtime_asm < $mtime_byte);
    if ($use_debug) { 
        $ENV{"OCAMLRUNPARAM"} = "b" . $ENV{"OCAMLRUNPARAM"}; # Print back trace
    } 

    # Save choice in global vars for printHelp (can be called from Cilly::new)
    $Ivy::compiler = "$bin/ivy" . ($use_debug ? ".byte.exe" : ".asm.exe");

    my $self = Ivy->Cilly::new(@args);

    # New variables for Ivy
    $self->{COMPILER} = $Ivy::compiler;
    $self->{LIBBASE} = $lib;

    $self->{DARWIN} = `uname` =~ /Darwin/;

    # Tools default to off
    $self->{DEPUTY} = 0;
    $self->{HEAPSAFE} = 0;
    $self->{SHARC} = 0;

    push @{$self->{CPP}}, $self->{INCARG} . $::ivyhome . "/include";
    my $v = $::version_major * 1000 + $::version_minor * 100 + $::version_sub;
    push @{$self->{CPP}}, $self->{DEFARG} . (sprintf "__IVY__=%d", $v);

    # Override Cilly's default
    $self->{SEPARATE} = 1;

    bless $self, $class;
}

sub processArguments {
    my ($self) = @_;
    my @args = @{$self->{ARGV}};
    my $lib = $self->{LIBBASE};

    # Scan and process the arguments
    $self->setDefaultArguments;
    $self->collectArgumentList(@args);

    # Resolve conflicting and partially conflicting options, pick
    # appropriate options for the various stages
    if (!$self->{HEAPSAFE} && $self->{SHARC}) {
	print STDERR "SharC requires the use of Heapsafe - reenabling HeapSafe\n";
	$self->{HEAPSAFE} = 1;
    }

    $self->{CONCRC} = $self->{SHARC} || ($self->{HEAPSAFE} && $self->{DOCONCRC});

    if ($self->{HSDEBUG} && $self->{CONCRC} && !$self->{NOLIBS}) {
	print STDERR "--hs-debug not supported for multithreaded code -- disabling\n";
	$self->{HSDEBUG} = 0;
    }

    push @{$self->{CPP}}, $self->{DEFARG} . "__DEPUTY__=1" if $self->{DEPUTY};
    push @{$self->{CPP}}, $self->{DEFARG} . "__HEAPSAFE__=1" if $self->{HEAPSAFE};
    push @{$self->{CPP}}, $self->{DEFARG} . "__SHARC__=1" if $self->{SHARC};

    push @{$self->{CILARGS}}, "--hs-norc" unless $self->{HEAPSAFE};
    push @{$self->{CILARGS}}, "--nosharc" unless $self->{SHARC};
    push @{$self->{CILARGS}}, "--nodeputy" unless $self->{DEPUTY};

    if ($self->{CONCRC}) {
        push @{$self->{CILARGS}}, "--hs-concrc";
    }
    elsif ($self->{HEAPSAFE}) {
        push @{$self->{CPP}}, $self->{DEFARG} . "__HS_NOCONCRC__=1";
    }

    if ($self->{HSDEBUG}) {
        push @{$self->{CILARGS}}, "--hs-debug";
	push @{$self->{CPP}}, $self->{DEFARG} . "__HS_DEBUG__=1";
    }

    if ($self->{HSDEBUG}) { 
	$self->{HSLIB} = "$lib/heapsafe_libc_debug.$self->{LIBEXT}";
    }
    elsif ($self->{CONCRC}) {
 	$self->{HSLIB} = "$lib/heapsafe_libc_conc.$self->{LIBEXT}";
    }
    else {
	$self->{HSLIB} = "$lib/heapsafe_libc.$self->{LIBEXT}";
    }

    $self->{DEPUTYLIB} = "$lib/deputy_libc.$self->{LIBEXT}";

    if ($self->{SHARC}) {
        $self->{SHARCLIB} = "$lib/sharc_libc.$self->{LIBEXT}";
    }
    else {
    	$self->{SHARCLIB} = "$lib/nosharc_libc.$self->{LIBEXT}";
    }

    if($self->{CONCRC}) {
        $self->{PTHREADLIB} = "$lib/pthread_wrappers.$self->{LIBEXT}";
    }    

    unless ($self->{NOPATCH}) {
	push @{$self->{CILARGS}}, "--patch", "$::ivyhome/include/libc_patch.i";
	push @{$self->{CILARGS}}, "--patch", "$::ivyhome/include/sharc_libc_patch.i" if $self->{SHARC};
    }

    return $self;
}

sub setDefaultArguments {
    my ($self) = @_;
    $self->{TRACE_COMMANDS} = 0;
    push @{$self->{CILARGS}}, "--home", $::ivyhome;
    return $self->SUPER::setDefaultArguments;
}

sub collectOneArgument {
    my ($self, $arg, $pargs) = @_;
    my $res = 1;
    if ($self->compilerArgument($self->{OPTIONS}, $arg, $pargs)) {
        # do nothing
    } elsif ($arg eq "--help" || $arg eq "-help") {
        $self->printVersion();
        $self->printHelp();
        exit 0;
    } elsif ($arg eq "--version" || $arg eq "-version") {
        $self->printVersion();
        exit 0;
    } elsif ($arg eq "--trace") {
        $self->{TRACE_COMMANDS} = 1;
    } elsif ($arg eq "--nopatch") {
        $self->{NOPATCH} = 1;
    } elsif ($arg eq "--nolibs") {
        $self->{NOLIBS} = 1;
    } elsif ($arg =~ m|--ivylib=(.+)$|) {
        push @{$self->{IVYLIBS}}, "$self->{LIBBASE}/$1.$self->{LIBEXT}";
    } elsif ($arg =~ m|--hs-debug$|) {
        $self->{HSDEBUG} = 1;
    } elsif ($arg eq "--sharc") {
        $self->{SHARC} = 1;
    } elsif ($arg eq "--deputy") {
        $self->{DEPUTY} = 1;
    } elsif ($arg eq "--heapsafe") {
        $self->{HEAPSAFE} = 1;
    } elsif ($arg eq "--hs-concrc") {
        $self->{DOCONCRC} = 1;
    } elsif ($arg eq "--bytecode") {
        $self->{NATIVECAML} = 0;
    } elsif ($arg =~ m|--save-temps=(.+)$|) {
        if (!-d $1) {
            die "Cannot find directory $1";
        }
        $self->{SAVE_TEMPS} = $1;
    } elsif ($arg eq '--save-temps') {
        $self->{SAVE_TEMPS} = '.';
    } elsif ($arg =~ m|--sc-infer-sharing=(.+)$|) {
        if (!-d $1) {
            die "Cannot find directory $1";
        }
        $self->{SAVE_TEMPS} = '.';
	push @{$self->{CILARGS}}, "--sc-infer-sharing", $1;
    } elsif ($arg =~ m|--includedir=(.+)$|)  {
        push @{$self->{INCLUDEDIR}}, $1;
    } elsif ($arg =~ m|^--out=(\S+)$|) {
        # Intercept the --out argument
        $self->{CILLY_OUT} = $1;
        push @{$self->{CILARGS}}, "--out", $1;
    } elsif ($arg =~ m|^--|) {
        # All other arguments starting with -- are passed to CIL
        # Split the ==
        if ($arg =~ m|^(--\S+)=(.+)$|) {
            push @{$self->{CILARGS}}, $1, $2;
        } else {
            push @{$self->{CILARGS}}, $arg;
        }
    } else {
        # We fail!
        $res = 0;
    }
    return $res;
}

sub preprocess_before_cil {
    my($self, $src, $dest, $ppargs) = @_;
    my @args = @{$ppargs};
    unshift @args,
    $self->forceIncludeArg("$::ivyhome/include/deputy/annots.h");
    unshift @args, $self->{INCARG} . $::ivyhome . "/include";
    return $self->SUPER::preprocess_before_cil($src, $dest, \@args);
}


## We do not preprocess after CIL, to save time and files
sub preprocessAfterOutputFile {
    my ($self, $src) = @_;
    return $src; # Do not preprocess after CIL
}

sub preprocess_after_cil {
    my ($self, $src, $dest, $ppargs) = @_;
    if($src ne $dest) { die "I thought we are not preprocessing after CIL";}
    return $dest;
}

sub compile_cil {
    my ($self, $src, $dest, $ppargs, $ccargs) = @_;
    my @args = @{$ppargs};
    my @newargs;
    my $i;

    # Filter out -include options
    for ($i = 0; $i <= $#args; $i++) {
	$_ = $args[$i];
	if (/^-include/) {
	    $i++;
	}
	else {
	    push @newargs, $_;
	}
    }
    push @newargs, "$self->{INCARG}$::ivyhome/include";
    push @newargs, $self->{DEFARG} . "__HS_DEBUG__=1" if $self->{HSDEBUG};
    push @newargs, $self->{DEFARG} . "__HS_NOCONCRC__=1" if !$self->{CONCRC};
    push @newargs, "-fno-strict-aliasing" if $self->{CONCRC};
    return $self->SUPER::compile_cil($src, $dest, \@newargs, $ccargs);
}


sub link_after_cil {
    my ($self, $psrcs, $dest, $ppargs, $ccargs, $ldargs) = @_;
    my @srcs = @{$psrcs};
    my @libs = @{$ldargs};
    my @cargs = @{$ccargs};
    if ($self->{DARWIN}) {
	push @libs, "-Wl,-multiply_defined", "-Wl,suppress";
    }
    if (scalar @srcs == 0) {
        print STDERR "ivycc: no input files\n";
        return 0;
    } else {
	push @libs, @{$self->{IVYLIBS}} if defined $self->{IVYLIBS};
	if (!$self->{NOLIBS}) {
	    push @srcs, $self->{DEPUTYLIB} if $self->{DEPUTY};
	    push @srcs, $self->{HSLIB} if $self->{HEAPSAFE};
	    push @srcs, $self->{SHARCLIB} if $self->{CONCRC};
        push @srcs, $self->{PTHREADLIB} if $self->{CONCRC};
        push @libs, ("-ldl","-lpthread") if $self->{CONCRC};
	}
        return $self->SUPER::link_after_cil(\@srcs, $dest, $ppargs,
                                            \@cargs, \@libs);
    }
}

sub linktolib {
    my ($self, $psrcs, $dest, $ppargs, $ccargs, $ldargs) = @_;
    my @srcs = @{$psrcs};
    my @libs = @{$ldargs};
    if (scalar @srcs == 0) {
        print STDERR "ivycc: no input files\n";
        return 0;
    } else {
	push @libs, @{$self->{IVYLIBS}};
	if (!$self->{NOLIBS}) {
	    push @srcs, $self->{DEPUTYLIB} if $self->{DEPUTY};
	    push @srcs, $self->{HSLIB} if $self->{HEAPSAFE};
	    push @srcs, $self->{SHARCLIB} if $self->{CONCRC};
        push @srcs, $self->{PTHREADLIB} if $self->{CONCRC};
        push @libs, ("-ldl","-lpthread") if $self->{CONCRC};
	}
        return $self->SUPER::linktolib(\@srcs, $dest, $ppargs,
                                       $ccargs, $ldargs);
    }
}

sub CillyCommand {
    my ($self, $ppsrc, $dest) = @_;

    my @cmd = ($self->{COMPILER});
    my $aftercil = $self->cilOutputFile($dest, 'cil.c');
    return ($aftercil, @cmd, '--out', $aftercil);
}

sub printVersion {
    printf "ivycc: %d.%d.%d\n", $::version_major, $::version_minor, $::version_sub;
}

sub printHelp {
    my ($self) = @_;
    my @cmd = ($self->{COMPILER}, '-help');
    print <<EOF;

Usage: ivycc [options] <source-files>...

Front end:

  --deputy              Enable Deputy (type checks)
  --heapsafe            Enable Heapsafe (deallocation checks)
  --sharc               Enable SharC (shared memory checks)
  --ivylib=<file>       Use a specific Ivy runtime library.
  --nolibs              Disable auto-linking with Ivy runtime libraries
                        (you should provide your own and/or use --ivylib to
                        link with appropriate libraries)
  --nopatch             Disable automatic libc patching (for Deputy, SharC)

  --trace               Print commands invoked by the front end.
  --save-temps[=<dir>]  Save intermediate files (target directory optional).
  --version             Print version number and exit.
  --includedir          Add the specified directory to the beginning of
                        the include path.
  --gcc                 Use the specified executable instead of gcc as the
                        final C compiler (see also the --envmachine option)

EOF
    $self->runShell(@cmd); 
}

1;
