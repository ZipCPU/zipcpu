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
#	make install
#		Attempts to build binutils, gcc, and newlib, and to install 
#		hem into INSTALL directory.  This is also the default target.
#
#	make all:
#		Includes the basic-install target, but also the pdf
#		documentation files that come with binutils and gcc.  Building
#		this target will require a LaTeX distribution in addition to the
#		needs of the other targets.
#
#	make clean
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
bypass:
	echo "This Makefile has not yet been updated as part of 8-bit support."
	echo "Neither are the scripts, gas-script.sh, gcc-script.sh, and nlib-script.sh"
	echo "ready for prime-time: they dont yet handle creating and adjusting"
	echo "the required directories automatically (yet)."
	echo
	echo "Please debug this Makefile first, before trying to automatically run it"

basic-install: binutils-install gcc-install nlib-install
all: basic-install binutils-pdf-install gcc-pdf-install

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

$(BINUTILSD)-zip: $(BINUTILSD).tar.bz2 gas-zippatch.patch
	rm -rf $(BINUTILSD)-zip/
	tar -xjf ./$(BINUTILSD).tar.bz2 --transform s,$(BINUTILSD),$(BINUTILSD)-zip
	bash -c "cd $(BINUTILSD)-zip; patch -p1 <../gas-zippatch.patch"
	rm -rf $(BUILDGASD)

.PHONY: binutils-zip
binutils: $(BINUTILSD)
	bash -c "if [ ! -e build-gas ]; then bash gas-script.sh; fi"
	$(SUBMAKE) --directory=$(BUILDGASD)

.PHONY: binutils-install
binutils-install: binutils
	$(SUBMAKE) --directory=$(BUILDGASD) install

.PHONY: binutils-pdf
binutils-pdf: binutils
	$(SUBMAKE) --directory=$(BUILDGASD) pdf

.PHONY: binutils-pdf-install
binutils-pdf-install: binutils-pdf
	mkdir -p $(PDFD)
	find $(BUILDGASD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;


#
#
# Now let's try the same thing for GCC
#
#
$(GCCD)-zip: $(GCCD).tar.bz2 gcc6-zippatch.patch
	rm -rf $(GCCD)-zip/
	tar -xjf ./$(GCCD).tar.bz2 --transform s,$(GCCD),$(GCCD)-zip,
	bash -c "cd $(GCCD)-zip; patch -p1 <../gcc-zippatch.patch"
	rm -rf $(BUILDGCCD)
	
.PHONY: gcc
gcc: $(GCCD)-zip
	bash -c "if [[ ! -e $(BUILDGCCD) ]]; then bash gcc-script.sh; fi"
	$(SUBMAKE) --directory=$(BUILDGCCD)/gcc

.PHONY: gcc-install
gcc-install: gcc
	$(SUBMAKE) --directory=$(BUILDGCCD)/gcc install

.PHONY: gcc-pdf
gcc-pdf: gcc
	$(SUBMAKE) --directory=$(BUILDGCCD) pdf

.PHONY: gcc-pdf-install
gcc-pdf-install: gcc-pdf
	mkdir -p $(PDFD)
	find $(BUILDGCCD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;


#
#
# And repeat for newlib
#
#
$(NLIBD)-zip: $(NLIBD).tar.bz2 gcc6-zippatch.patch
	rm -rf $(NLIBD)-zip/
	tar -xjf ./$(NLIBD).tar.bz2 --transform s,$(NLIBD),$(NLIBD)-zip,
	bash -c "cd $(NLIBD)-zip; patch -p1 <../gcc-zippatch.patch"
	rm -rf $(BUILDNLIB)
	
.PHONY: newlib
newlib: $(NLIBD)-zip
	bash -c "if [[ ! -e $(BUILDNLIB) ]]; then bash gcc-script.sh; fi"
	$(SUBMAKE) --directory=$(BUILDNLIB)/gcc

.PHONY: newlib-install
newlib-install: newlib
	$(SUBMAKE) --directory=$(BUILDGCCD)/gcc install

# .PHONY: newlib-pdf
# newlib-pdf: gcc
#	$(SUBMAKE) --directory=$(BUILDGCCD) pdf

# .PHONY: gcc-pdf-install
# gcc-pdf-install: gcc-pdf
#	mkdir -p $(PDFD)
#	find $(BUILDGCCD) -name "*.pdf" -exec cp \{\} $(PDFD)/ \;



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

