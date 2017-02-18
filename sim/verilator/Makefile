################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	This makefile builds the final verilator simulation of the
#		zipsystem.  Specifically, it builds the final C++ portion
#	of the simulator, and thus the final simulator executable.
#
#	This simulator depends upon the ncurses library.
#
#	Useful targets of this makefile include:
#
#	zippy_tb (default)
#		This is the test bench program / simulator that is built by
#		this directory.
#
#	test
#		Runs the simulator on a test program found in the trunk/sw/zasm
#		directory.  That program needs to be built via 'make test' in
#		that directory before this make test will work.  Changes to the
#		test itself will require a 'make test' in trunk/sw/zasm as well
#		as 'make test' in this directory.
#
#		The test itself consists of two tests.  The first, the "step"
#		test, tests whether the test works via "step"ing the CPU.
#		This would be the interface to the CPU were the CPU placed in
#		a device.
#
#		The second test is an internal test which works by just running
#		the CPU without step instructions.
#
#		In either case the test is over upon reaching either a HALT
#		or a BUSY instruction.  A HALT instruction indicates success,
#		BUSY a failure.
#
#	stest
#		Runs the test in "step" mode as described above.
#
#	itest
#		Runs the test file in interactive mode.  The CPU will not
#		execute any instructions without user interaction.  This is
#		useful for actually debugging the test.  The other two modes
#		are useful for quickly determining that the CPU does (or
#		doesn't) work.
#
#	dhrystone
#		Runs a hand-optimized version of the dhrystone benchmark.
#		Using the instructions at the top of the dhrystone assembly
#		file, you should be able to convert the result to DMIPS or even
#		DMIPS/MHz.
#
#	div_tb
#		A raw test bench to test the divide unit separate from the
#		rest of the CPU.  This test will fail with a failed assert()
#		if unsuccessful, or complete with no error (but lots of
#		debugging output) if successful.  To actually run this test,
#		you'll need to run ./div_tb (no arguments necessary).
#
#	mpy_tb
#		A raw test bench to test the multiply instructions within the
#		cpuops (ALU) unit separate from the rest of the CPU.  For more
#		details, look at the usage statement wtihin mpy_tb.
#
#	pfcache_tb
#
#	zipmmu_tb
#		Like div_tb, this is another raw component test bench.  In this
#		case, zipmmu_tb tests whether or not the MMU works when
#		separated from the rest of the CPU.
#
#	pdump
#		zippy_tb can be configured to produce a profile output that is
#		very useful when debugging the Dhrystone benchmark.  (It is
#		so configured by default.)  This file will be name pfile.bin.
#		pdump is a very simple program designed to read this file and
#		produce some (very raw) information from it.  To use this,
#		type pdump and the name of the executable file, such as
#		../asm/zipdhry.z, and examine how many times each instruction
#		was executed, and how many stalls took place between each
#		instruction and the next.
#
#	clean
#		Removes all products of compilation--specifically zippy_tb,
#		pdump and div_tb.
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
all: zippy_tb pdump div_tb mpy_tb pfcache_tb # zipmmu_tb

CXX	:= g++
CFLAGS	:= -Wall -Og -g
OBJDIR  := obj-pc
ZASM	:= ../../sw/zasm
RTLD	:= ../../rtl
RTLOBJD := $(RTLD)/obj_dir
BENCHOBJD:= ../../bench/rtl/obj_dir
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
VROOT   := $(VERILATOR_ROOT)
VINCS	:= -I$(VROOT)/include -I$(VROOT)/include/vltstd
INCS	:= -I$(RTLOBJD) -I$(RTLD) -I$(ZASM) $(VINCS)
ZLIBSRCS:= zipelf.cpp twoc.cpp byteswap.cpp
SOURCES := $(ZLIBSRCS) pdump.cpp zippy_tb.cpp memsim.cpp
ZDSMSRCS:= zopcodes.cpp
ZOBJS   := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(ZLIBSRCS) $(ZDSMSRCS)))
SIMSRCS := zippy_tb.cpp memsim.cpp $(ZLIBSRCS) $(ZDMSRCS)
SIMOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSRCS) $(ZDSMSRCS)))
VLSRCS	:= verilated.cpp verilated_vcd_c.cpp
VLOBJS := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o
VLIB	:= $(addprefix $(VROOT)/include/,$(VLSRCS))
RAWLIB	:= $(RTLOBJD)/Vzipsystem__ALL.a
LIBS	:= $(RAWLIB) -lncurses -lelf
TESTF	:= $(ZASM)/z.out
DHRYSTONEF := ../asm/zipdhry.z

$(OBJDIR)/%.o: %.cpp
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(ZASM)/%.cpp
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VROOT)/include/%.cpp
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

zippy_tb: $(SIMOBJS) $(VLOBJS) $(RAWLIB)
	$(CXX) $(CFLAGS) $(INCS) $(SIMOBJS) $(VLOBJS) $(RAWLIB) $(LIBS) -o $@

div_tb: div_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vdiv__ALL.a testb.h
	$(CXX) $(CFLAGS) $(INCS) div_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vdiv__ALL.a -o $@

mpy_tb: mpy_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vcpuops__ALL.a testb.h
	$(CXX) $(CFLAGS) $(INCS) mpy_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vcpuops__ALL.a -o $@

zipmmu_tb: zipmmu_tb.cpp $(VLIB) $(BENCHOBJD)/Vzipmmu_tb__ALL.a
	$(CXX) $(CFLAGS) $(INCS) -I$(BENCHOBJD) zipmmu_tb.cpp $(VLIB) $(BENCHOBJD)/Vzipmmu_tb__ALL.a -o $@

pfcache_tb: $(OBJDIR)/pfcache_tb.o $(OBJDIR)/memsim.o $(OBJDIR)/byteswap.o
pfcache_tb: $(VLIB) $(RTLOBJD)/Vpfcache__ALL.a
	$(CXX) $(CFLAGS) $(INCS) -I$(RTLOBJD) $(OBJDIR)/pfcache_tb.o $(OBJDIR)/memsim.o $(OBJDIR)/byteswap.o $(VLIB) $(RTLOBJD)/Vpfcache__ALL.a -o $@

pdump: pdump.cpp $(ZOBJS) $(OBJDIR)/zopcodes.o $(OBJDIR)/pdump.o
pdump: $(ZASM)/zopcodes.h testb.h byteswap.h zipelf.h
	$(CXX) $(CFLAGS) $(INCS) $(OBJDIR)/pdump.o $(ZOBJS) -lelf -o $@

.PHONY: stest
stest: zippy_tb
	./zippy_tb -s $(TESTF)

.PHONY: itest
itest: zippy_tb
	./zippy_tb $(TESTF)

.PHONY: test
test: zippy_tb stest
	./zippy_tb -a $(TESTF)

.PHONY: dhrystone
dhrystone: zippy_tb
	./zippy_tb -a $(DHRYSTONEF)

define	build-depends
	@echo "Building dependencies"
	@$(CXX) $(CPPFLAGS) $(INCS) -MM $(VLIB) $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(VLIB) $(SOURCES)
	@ctags $(SOURCES) $(VLIB)

.PHONY: depends
depends: tags $(OBJDIR)/
	$(build-depends)

$(OBJDIR)/:
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"

$(OBJDIR)/depends.txt: $(OBJDIR)/ depends

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/
	rm -rf ./zippy_tb pdump div_tb mpy_tb

-include $(OBJDIR)/depends.txt
