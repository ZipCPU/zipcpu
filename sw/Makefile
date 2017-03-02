################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	This makefile attempts to build the ZipCPU toolchain.  This 
#		includes binutils and GCC.  (Eventually, it will include the
#	standard library as well ...)  Configuration options for binutils, GCC,
#	and newlib can be found (and set) in the gas-script.sh, gcc-script.sh,
#	and nlib-script.sh files respectively.
#
# Targets:
#
#	make all:
#		Includes the install target, but also the pdf documentation
#		files that come with binutils and gcc.  Building this target
#		will require a LaTeX distribution in addition to the needs of
#		the other targets.  Since the PDFs can be found on line,
#		building them is not really necessary, but may be quite useful.
#
#	make install
#		Attempts to build binutils, gcc, and newlib, and to install 
#		them into the local install directory.
#
#		This is the default target
#
#	make binutils
#	make gcc
#	make newlib
#		Builds the respective packages
#
#	make binutils-install
#	make gcc-install
#	make newlib-install
#		Installs the respective packages into the install directory,
#		building them first if necessary.
#
#	make clean
#		Removes all build products--to include the source directories
#		that are built from patched tarballs.
#
#
# Creator:	Dan Gisselquist, Ph.D.
#		Gisselquist Technology, LLC
#
################################################################################
#
# Copyright (C) 2015-2017, Gisselquist Technology, LLC
#
# This program is free software (firmware): you can redistribute it and/or
# modify it under the terms of  the GNU General Public License as published
# by the Free Software Foundation, either version 3 of the License, or (at
# your option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.
#
# License:	GPL, v3, as defined and found on www.gnu.org,
#		http://www.gnu.org/licenses/gpl.html
#
#
################################################################################
#
.PHONY: all basic-install install build
install: basic-install
all: basic-install binutils-pdf-install gcc-pdf-install
basic-install: gas-install gcc-install newlib-install
build: gas gcc-all nlib
CC: gcc

BINUTILSD=binutils-2.27
GCCD=gcc-6.2.0
NLIBD=newlib-2.5.0
INSTALL=`pwd`/install
PDFD=$(INSTALL)/usr/doc
ZASMD=zasm
BUILDGASD=build-gas
BUILDGCCD=build-gcc
BUILDNLIB=build-nlib
SUBMAKE=$(MAKE) --no-print-directory
ZIPINCD=$(INSTALL)/cross-tools/zip/include

$(BINUTILSD)-zip/nonce.txt: $(BINUTILSD).tar.bz2 gas-zippatch.patch
	rm -rf $(BINUTILSD)-zip/
	tar -xjf ./$(BINUTILSD).tar.bz2 --transform s,$(BINUTILSD),$(BINUTILSD)-zip,
	-bash -c "cd $(BINUTILSD)-zip; patch -p1 <../gas-zippatch.patch"
	rm -rf $(BUILDGASD)
	touch $(BINUTILSD)-zip/nonce.txt

$(BUILDGASD)/nonce.txt: $(BINUTILSD)-zip/nonce.txt
	bash -c "if [ ! -e build-gas ]; then bash gas-script.sh; fi"
	touch $(BUILDGASD)/nonce.txt

.PHONY: binutils
binutils: $(BUILDGASD)/nonce.txt
	$(SUBMAKE) --directory=$(BUILDGASD)

.PHONY: binutils-install
binutils-install: binutils
	$(SUBMAKE) --directory=$(BUILDGASD) install
	cp ../bench/zipsim.ld install/cross-tools/zip/lib/ldscripts

.PHONY: binutils-pdf
binutils-pdf: binutils
	$(SUBMAKE) --directory=$(BUILDGASD) pdf

$(PDFD)/:
	bash -c "if [[ ! -d $(PDFD) ]]; then mkdir -p $(PDFD); fi"

.PHONY:
pdfd: $(PDFD)/

.PHONY: binutils-pdf-install
binutils-pdf-install: binutils-pdf $(PDFD)/
	find $(BUILDGASD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;

.PHONY: gas
gas: binutils

.PHONY: gas-install
gas-install: binutils-install

# We can also set the environment variable DEJAGNU to point to our site .exp
# file.
gas-check: binutils-install
	+$(SUBMAKE) --directory=$(BUILDGASD) check RUNTESTFLAGS="--target_board=zip-sim"
#
#
# Now let's try the same thing for GCC
#
#
$(GCCD)-zip/nonce.txt: $(GCCD).tar.bz2 gcc-zippatch.patch
	rm -rf $(GCCD)-zip/
	tar -xjf ./$(GCCD).tar.bz2 --transform s,$(GCCD),$(GCCD)-zip,
	-bash -c "cd $(GCCD)-zip; patch -p1 <../gcc-zippatch.patch"
	rm -rf $(BUILDGCCD)
	touch $(GCCD)-zip/nonce.txt

genzipops: $(GCCD)-zip/gcc/config/zip/genzipops.c $(GCCD)-zip/nonce.txt
	$(CC) $< -o $@
$(GCCD)-zip/gcc/config/zip/zip-ops.md: genzipops
	genzipops > $@

$(BUILDGCCD)/nonce.txt: $(GCCD)-zip/nonce.txt $(GCCD)-zip/gcc/config/zip/zip-ops.md gas-install
	bash -c "if [[ ! -e $(BUILDGCCD) ]]; then bash gcc-script.sh; fi"
	touch $(BUILDGCCD)/nonce.txt

#
#
# GCC must be done in two parts: The host files first, which don't depend
# upon a built compiler, and then all the libraries that depend upon the
# built compiler.
#
#
gcc-host: $(BUILDGCCD)/nonce.txt
	+$(SUBMAKE) --directory=$(BUILDGCCD) all-host
.PHONY: zip-gcc
zip-gcc: gcc-host

gcc-install-host: $(BUILDGCCD)/nonce.txt gcc-host
	+$(SUBMAKE) --directory=$(BUILDGCCD) install-host

.PHONY: zip-gcc-install
zip-gcc-install: gcc-install-host

$(INSTALL)/cross-tools/bin/zip-gcc: zip-gcc-install

$(INSTALL)/cross-tools/bin/zip-cc: zip-gcc-install
	bash -c "cd $(INSTALL)/cross-tools/bin; if [[ ! -e zip-cc ]]; then ln -s zip-gcc zip-cc; fi"

.PHONY: gcc-pdf-install
#
#
# Now for the second part of GCC.  This part depends upon newlib as well as
# GCC proper.
#
#
.PHONY: gcc
gcc: $(BUILDGCCD)/nonce.txt gas-install newlib-install
	+$(SUBMAKE) --directory=$(BUILDGCCD)

.PHONY: gcc-install
gcc-install: gcc
	+$(SUBMAKE) --directory=$(BUILDGCCD) install

.PHONY: gcc-pdf
gcc-pdf: $(BUILDGCCD)/nonce.txt
	+$(SUBMAKE) --directory=$(BUILDGCCD) pdf

gcc-pdf-install: gcc-pdf $(PDFD)/
	find $(BUILDGCCD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;

#
#
# And repeat for newlib
#
#
$(NLIBD)-zip/nonce.txt: $(NLIBD).tar.gz nlib-zippatch.patch
	rm -rf $(NLIBD)-zip/
	tar -xzf ./$(NLIBD).tar.gz --transform s,$(NLIBD),$(NLIBD)-zip,
	-bash -c "cd $(NLIBD)-zip; patch -p1 <../nlib-zippatch.patch"
	rm -rf $(BUILDNLIB)
	touch $(NLIBD)-zip/nonce.txt

$(BUILDNLIB)/nonce.txt: $(NLIBD)-zip/nonce.txt $(BUILDGASD)/nonce.txt
	bash nlib-script.sh
	touch $(BUILDNLIB)/nonce.txt

.PHONY: newlib
newlib: $(BUILDNLIB)/nonce.txt zip-gcc-install
newlib: $(INSTALL)/cross-tools/bin/zip-cc
	+$(SUBMAKE) --directory=$(BUILDNLIB)

.PHONY: newlib-install
newlib-install: newlib
	+$(SUBMAKE) --directory=$(BUILDNLIB) install


# Some abbreviations for targets
.PHONY: nlib nlib-install
nlib: newlib
nlib-install: newlib-install

#
#
# Finally, can we build and install zasm?
#
#
# zasm:
#	$(SUBMAKE) --directory=$(ZASMD) all

# zasm-install: zasm
#	$(SUBMAKE) --directory=$(ZASMD) install

#
#
# The clean target
#
#
.PHONY: clean
clean:
	rm -rf $(INSTALL)
	rm -rf $(BINUTILSD)-zip/ $(GCCD)-zip/ $(NLIBD)-zip/
	rm -rf $(BUILDGASD) $(BUILDGCCD) $(BUILDNLIB)
	# $(SUBMAKE) --no-print-directory --directory=$(ZASMD) clean

