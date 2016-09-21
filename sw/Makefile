################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	This makefile attempts to build the ZipCPU toolchain.  This 
#		includes binutils and GCC.  (Eventually, it will include the
#	standard library as well ...)  Configuration options for binutils and
#	GCC can be found in the gas-script.sh and gcc-script.sh files
#	respectively.
#
# Targets:
#	make basic-install
#		Attempts to build binutils, gcc, and the (now obsolete) zasm
#		assembler, and to install them into INSTALL directory.  This is
#		also the default target.
#
#	make all:
#		Includes the basic-install target, but also the pdf
#		documentation files that come with binutils and gcc.  Building
#		this target will require a LaTeX distribution in addition to the
#		needs of the other targets.  (These documents may also be found
#		online, and have not been edited as part of the ZipCPU toolchain
#		... (yet).)
#
#	make clean
#
#
# Creator:	Dan Gisselquist, Ph.D.
#		Gisselquist Technology, LLC
#
################################################################################
#
# Copyright (C) 2015, Gisselquist Technology, LLC
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
basic-install: binutils-install gcc-install zasm-install
all: basic-install binutils-pdf-install gcc-pdf-install

BINUTILSD=binutils-2.25
BUILDGASD=build-gas
BUILDGCCD=build-gcc
INSTALL=`pwd`/install
PDFD=$(INSTALL)/usr/doc
ZASMD=zasm

binutils-2.25: binutils-2.25.tar.bz2 binutils-2.25.patch
	rm -rf binutils-2.25/
	tar -xjf ./binutils-2.25.tar.bz2
	bash -c "cd binutils-2.25; patch -p1 <../binutils-2.25.patch"
	rm -rf $(BUILDGASD)

.PHONY: binutils
binutils: binutils-2.25
	bash -c "if [ ! -e build-gas ]; then bash gas-script.sh; fi"
	$(MAKE) --no-print-directory --directory=$(BUILDGASD)

.PHONY: binutils-install
binutils-install: binutils
	$(MAKE) --no-print-directory --directory=$(BUILDGASD) install

.PHONY: binutils-pdf
binutils-pdf: binutils
	$(MAKE) --no-print-directory --directory=$(BUILDGASD) pdf

.PHONY: binutils-pdf-install
binutils-pdf-install: binutils-pdf
	mkdir -p $(PDFD)
	find $(BUILDGASD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;


#
#
# Now let's try the same thing for GCC
#
#
gcc-5.3.0-zip: gcc-5.3.0.tar.bz2 gcc-5.3.0-specs-1.patch gcc-zippatch.patch
	rm -rf gcc-5.3.0-zip/
	tar -xjf ./gcc-5.3.0.tar.bz2 --transform s,gcc-5.3.0,gcc-5.3.0-zip,
	bash -c "cd gcc-5.3.0-zip; patch -p1 <../gcc-5.3.0-specs-1.patch"
	rm gcc-5.3.0-zip/gcc/config/rs6000/sysv4.h.orig
	bash -c "cd gcc-5.3.0-zip; patch -p1 <../gcc-zippatch.patch"
	rm -rf $(BUILDGCCD)
	
.PHONY: gcc
gcc: gcc-5.3.0-zip
	bash -c "if [[ ! -e $(BUILDGCCD) ]]; then bash gcc-script.sh; fi"
	$(MAKE) --no-print-directory --directory=$(BUILDGCCD)/gcc

.PHONY: gcc-install
gcc-install: gcc
	$(MAKE) --no-print-directory --directory=$(BUILDGCCD)/gcc install

.PHONY: gcc-pdf
gcc-pdf: gcc
	$(MAKE) --no-print-directory --directory=$(BUILDGCCD) pdf

.PHONY: gcc-pdf-install
gcc-pdf-install: gcc-pdf
	mkdir -p $(PDFD)
	find $(BUILDGCCD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;

#
#
# Finally, can we build and install zasm?
#
#
zasm:
	$(MAKE) --no-print-directory --directory=$(ZASMD)

zasm-install: zasm
	$(MAKE) --no-print-directory --directory=$(ZASMD) install

#
#
# The clean target
#
#
.PHONY: clean
clean:
	rm -rf $(INSTALL)
	rm -rf binutils-2.25 gcc-5.3.0-zip
	rm -rf $(BUILDGASD) $(BUILDGCCD)
	$(MAKE) --no-print-directory --directory=$(ZASMD) clean

