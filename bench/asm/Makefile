################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	To direct and simplify the build of a variety of simple assembly
#		language test programs which will use one (or both) of the
#	ZipCPU simulators.
#
# Targets include:
#
#	hellosim
#		Using the SIM instruction, prints Hello World to the screen.
#
#	simuart
#		Same as hellosim, but without using the SIM instruction.  This
#		*should* be able to run successfully on a verilated or
#		synthesized hardware, although I hvae yet to test it there.
#
#	simtest
#		A set of simple tests designed to demonstrate if the simulator
#		works or not.
#
#	clean
#		Removes the object file directory and any executables that have
#		been created.
#
#	None of the files/targets below have any dependencies, or if they did,
#	GCC can't determine them, so thus there is no make depends step.
#
#	To actually run one of these programs, list the program on the command
#	line with the ZipCPU simulator, zsim.
#
#
#
# Creator:	Dan Gisselquist, Ph.D.
#		Gisselquist Technology, LLC
#
################################################################################
#
# Copyright (C) 2017, Gisselquist Technology, LLC
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
# You should have received a copy of the GNU General Public License along
# with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
# target there if the PDF file isn't present.)  If not, see
# <http://www.gnu.org/licenses/> for a copy.
#
# License:	GPL, v3, as defined and found on www.gnu.org,
#		http://www.gnu.org/licenses/gpl.html
#
#
################################################################################
#
.PHONY: all
all:
PROGRAMS := hellosim simuart simtest cmptest
all: $(PROGRAMS)

CC      := zip-gcc
CPP     := zip-cpp
AS      := zip-as
LD      := zip-ld
OBJDUMP := zip-objdump
OBJDIR := obj-zip
CFLAGS := -O3
LIBD   := ../../sw/install/cross-tools/zip/lib
LIBS   := -L$(LIBD) -lzipbasic
LDSCRIPT:= ./simscript.ld

$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@

$(OBJDIR)/%.o: %.s
	$(mk-objdir)
	$(AS) $< -o $@

%.txt: %
	$(OBJDUMP) -dr $< > $@

#
# hellosim
#
# This is an assembly version of Hello World that uses the new SIM instructions.
# It should fail with an illegal instruction error if it is ever tried on an
# RTL-synthesized implementation
#
hellosim: $(OBJDIR)/hellosim.o
	$(LD) -T $(LDSCRIPT) $< -o $@

#
# simuart
#
# This is an assembly version of Hello World that uses the UART in the 
# process.  It doesn't use newlib or any other support tools, just binutils.
#
simuart: $(OBJDIR)/simuart.o
	$(LD) -T $(LDSCRIPT) $< -o $@

#
# simtest
#
# This is just a simple series of instruction tests that should be able to be
# used to determine whether the simulator has a basic amount of functionality.
# Because the test includes #define, #ifdef, and #endif statements, though, it
# needs to be run through the C pre-processor before it can go through the
# assembler.  Hence the build is a tocuh trickier, but still simple enough.
#
$(OBJDIR)/simtest.o: simtest.s
	$(mk-objdir)
	$(CPP) $< > $(OBJDIR)/simtest.s
	$(AS) $(OBJDIR)/simtest.s -o $@

simtest: $(OBJDIR)/simtest.o
	$(LD) -T $(LDSCRIPT) $< -o $@

cmptest: $(OBJDIR)/cmptest.o
	$(LD) -T $(LDSCRIPT) -Map=map.txt $< -o $@


define	mk-objdir
	@bash -c "if [[ ! -e $(OBJDIR) ]]; then mkdir -p $(OBJDIR)/; fi"
endef

tags: $(wildcard *.c) $(wildcard *.h) $(wildcard *.cpp)
	@echo "Generating tags"
	@ctags $(wildcard *.c) $(wildcard *.h)

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/
	rm -rf $(PROGRAMS)
