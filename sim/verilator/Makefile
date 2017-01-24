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
# Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
all: zippy_tb pdump div_tb mpy_tb

CXX	:= g++
FLAGS	:= -Wall -Og -g
OBJDIR  := obj-pc
ZASM	:= ../../sw/zasm
RTLD	:= ../../rtl
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
VROOT   := $(VERILATOR_ROOT)
INCS	:= -I$(RTLD)/obj_dir/ -I$(RTLD) -I$(VROOT)/include -I$(ZASM)
ZSOURCES:= zippy_tb.cpp zipelf.cpp memsim.cpp twoc.cpp
ZDSMSRCS:= zopcodes.cpp zparser.cpp
ZOBJS   := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(ZSOURCES) $(ZDSMSRCS)))
VLSRCS	:= verilated.cpp verilated_vcd_c.cpp
VLOBJS := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o
VLIB	:= $(addprefix $(VROOT)/include/,$(VLSRCS))
RAWLIB	:= $(RTLD)/obj_dir/Vzipsystem__ALL.a
LIBS	:= $(RAWLIB) -lncurses -lelf
TESTF	:= $(ZASM)/z.out
DHRYSTONEF := ../asm/zipdhry.z

$(OBJDIR)/%.o: %.cpp
	$(CXX) $(FLAGS) $(INCS) -c $^ -o $@

$(OBJDIR)/%.o: $(ZASM)/%.cpp
	$(CXX) $(FLAGS) $(INCS) -c $^ -o $@

$(OBJDIR)/%.o: $(VROOT)/include/%.cpp
	$(CXX) $(FLAGS) $(INCS) -c $^ -o $@

zippy_tb: $(ZOBJS) $(VLOBJS) $(RAWLIB)
zippy_tb: $(ZASM)/zopcodes.h $(ZASM)/zparser.h testb.h $(RTLD)/cpudefs.h
	$(CXX) $(FLAGS) $(INCS) $(ZOBJS) $(VLOBJS) $(LIBS) -o $@

div_tb: div_tb.cpp twoc.cpp $(VLIB) $(RTLD)/obj_dir/Vdiv__ALL.a testb.h
	$(CXX) $(FLAGS) $(INCS) div_tb.cpp twoc.cpp $(VLIB) $(RTLD)/obj_dir/Vdiv__ALL.a -o $@

mpy_tb: mpy_tb.cpp twoc.cpp $(VLIB) $(RTLD)/obj_dir/Vcpuops__ALL.a testb.h
	$(CXX) $(FLAGS) $(INCS) mpy_tb.cpp twoc.cpp $(VLIB) $(RTLD)/obj_dir/Vcpuops__ALL.a -o $@

zipmmu_tb: zipmmu_tb.cpp $(VLIB) ../rtl/obj_dir/Vzipmmu_tb__ALL.a
	$(CXX) $(FLAGS) $(INCS) -I ../rtl/obj_dir zipmmu_tb.cpp $(VLIB) ../rtl/obj_dir/Vzipmmu_tb__ALL.a -o $@

pdump: pdump.cpp $(ZASM)/zopcodes.cpp $(ZASM)/zparser.cpp 
pdump: $(ZASM)/zopcodes.h $(ZASM)/zparser.h testb.h twoc.cpp
	$(CXX) $(FLAGS) $(INCS) pdump.cpp $(ZASM)/zopcodes.cpp $(ZASM)/zparser.cpp twoc.cpp -lelf -o $@

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
	@$(CXX) $(CPPFLAGS) $(INCS) -MM $(VLIB) $(ZSOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
endef

tags: $(VLIB) $(ZSOURCES)
	@ctags $(ZSOURCES) $(VLIB)

.PHONY: depends
depends: tags $(OBJDIR)/
	$(build-depends)

$(OBJDIR)/:
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"

$(OBJDIR)/depends.txt: $(OBJDIR)/ depends

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/
	rm ./zippy_tb pdump div_tb mpy_tb

-include $(OBJDIR)/depends.txt
