This directory contains the source code for the ZipCPU tool-chain--the
GCC back end, assembler, and linker.  The directory also has the patches
necessary to build the C-library, newlib.  This tool-chain is kept in a series
of patch files--primarily because I found the patch files for the eco32
CPU *very* helpful to me when I needed to know where to start when building
the back end for the ZipCPU.

You'll also find within this directory the [Makefile](Makefile) used to
direct the build of this tool-chain, together with basic scripts for building
[GCC](gcc-script.sh), [binutils](gas-script.sh), and [newlib](nlib-script.sh).

If you run into trouble building these components, know this: the
[Makefile](Makefile) works off of the existence of nonce.txt files to know
how to proceed from one step to the next.  Hence, as an example, when building
the binutils components, it will start by applying patches to the binutils
repository found within here.  Once completed, it will place a nonce.txt
file into the resulting (patched) directory.  It will then attempt to
configure binutils.  Once done, there will be a `build-gas` directory with
a `nonce.txt` file within it.  This will be `make`s indication to move forward
and build the compiler.  If you have any problems with building, or if you want
to start the build over, feel free to either remove the patched directories,
or even to just remove the (empty) `nonce.txt` files and have `make`
start over.

## Common problems building the toolchain

The most common problem people have had is the result of not having the
pre-requisites properly installed on your computer.  Sadly, in this case,
the makefile will exit with some confusing error.  You'll need to find the
`config.log` file of the component that didn't build to find out what is
missing.

Another common error is that GCC needs the cross-built GCC to build it's
libraries.  Hence, you may need to make certain that the install'ed binary
directory is in your path.  I've tried to clean this up so that the
tool-chain Makefile doesn't require this, but certainly the builds of any
assembly or C related files will require it.

## Installed location

Currently, the tool-chain as configured does not install into your system
directories, but rather into an `install` directory that will be built as a
subset of this one.  This behavior is controlled by the `prefix` flags within
the various build scripts, which in turn is set by a Makefile variable.
Should you wish to change this behavior, just remember that the install
to the system directory will require sys-admin privileges, and it may also
require you to build the various components manually rather than via the
make script.  (It's not something I've tested.)

