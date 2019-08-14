################################################################################
##
## Filename:	Makefile
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	This makefile builds the final verilator simulation of the
##		zipsystem.  Specifically, it builds the final C++ portion
##	of the simulator, and thus the final simulator executable.
##
##	This simulator depends upon the libelf and ncurses libraries.
##
##	Useful targets of this makefile include:
##
##	zipsys_tb (default)
##		This is the test bench program / simulator that is built by
##		this directory.  This is based upon the ZipSystem.
##
##	zipbones_tb (default)
##		This is the test bench program / simulator that is built by
##		this directory--save that this ones uses the ZipBones.
##
##	test
##		Runs the simulator on a test program found in the trunk/sw/zasm
##		directory.  That program needs to be built via 'make test' in
##		that directory before this make test will work.  Changes to the
##		test itself will require a 'make test' in trunk/sw/zasm as well
##		as 'make test' in this directory.
##
##		The test itself consists of two tests.  The first, the "step"
##		test, tests whether the test works via "step"ing the CPU.
##		This would be the interface to the CPU were the CPU placed in
##		a device.
##
##		The second test is an internal test which works by just running
##		the CPU without step instructions.
##
##		In either case the test is over upon reaching either a HALT
##		or a BUSY instruction.  A HALT instruction indicates success,
##		BUSY a failure.
##
##	stest
##		Runs the test in "step" mode as described above.
##
##	itest
##		Runs the test file in interactive mode.  The CPU will not
##		execute any instructions without user interaction.  This is
##		useful for actually debugging the test.  The other two modes
##		are useful for quickly determining that the CPU does (or
##		doesn't) work.
##
##	dhrystone
##		Runs a hand-optimized version of the dhrystone benchmark.
##		Using the instructions at the top of the dhrystone assembly
##		file, you should be able to convert the result to DMIPS or even
##		DMIPS/MHz.
##
##	div_tb
##		A raw test bench to test the divide unit separate from the
##		rest of the CPU.  This test will fail with a failed assert()
##		if unsuccessful, or complete with no error (but lots of
##		debugging output) if successful.  To actually run this test,
##		you'll need to run ./div_tb (no arguments necessary).
##
##	mpy_tb
##		A raw test bench to test the multiply instructions within the
##		cpuops (ALU) unit separate from the rest of the CPU.  For more
##		details, look at the usage statement wtihin mpy_tb.
##
##	pfcache_tb
##
##	zipmmu_tb
##		Like div_tb, this is another raw component test bench.  In this
##		case, zipmmu_tb tests whether or not the MMU works when
##		separated from the rest of the CPU.
##
##	pdump
##		zipsys_tb can be configured to produce a profile output that is
##		very useful when debugging the Dhrystone benchmark.  (It is
##		so configured by default.)  This file will be name pfile.bin.
##		pdump is a very simple program designed to read this file and
##		produce some (very raw) information from it.  To use this,
##		type pdump and the name of the executable file, such as
##		../asm/zipdhry.z, and examine how many times each instruction
##		was executed, and how many stalls took place between each
##		instruction and the next.
##
##	clean
##		Removes all products of compilation--specifically zipsys_tb,
##		pdump and div_tb.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2015-2017, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
all: zipsys_tb zipbones_tb pdump div_tb mpy_tb pfcache_tb # zipmmu_tb

CXX	:= g++
#
# Add the -DVM_COVERAGE flag as shown below if you are running coverage
# tests with Verilator.  You'll also need to adjust VLSRCS and the Makefile
# in the rtl directory
# CFLAGS	:= -Wall -Og -g -D__WORDSIZE=64 -DVM_COVERAGE=1
#
CFLAGS	:= -Wall -Og -g -D__WORDSIZE=64
OBJDIR  := obj-pc
ZASM	:= ../../sw/zasm
RTLD	:= ../../rtl
RTLOBJD := $(RTLD)/obj_dir
BENCHOBJD:= ../../bench/rtl/obj_dir
ifneq ($(VERILATOR_ROOT),)
VERILATOR:=$(VERILATOR_ROOT)/bin/verilator
else
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
endif
export	$(VERILATOR)
VROOT   := $(VERILATOR_ROOT)
VDEFS   := $(shell ./vversion.sh)
VINCS	:= -I$(VROOT)/include -I$(VROOT)/include/vltstd
INCS	:= -I$(RTLOBJD) -I$(RTLD) -I$(ZASM) $(VINCS)
ZLIBSRCS:= zipelf.cpp twoc.cpp byteswap.cpp
SOURCES := $(ZLIBSRCS) pdump.cpp zipcpu_tb.cpp memsim.cpp
ZDSMSRCS:= zopcodes.cpp
ZOBJS   := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(ZLIBSRCS) $(ZDSMSRCS)))
SIMSRCS := memsim.cpp $(ZLIBSRCS) $(ZDMSRCS)
SIMOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSRCS) $(ZDSMSRCS)))
SYSOBJS := $(OBJDIR)/zipsys_tb.o   $(SIMOBJS)
BONOBJS := $(OBJDIR)/zipbones_tb.o $(SIMOBJS)
VLSRCS	:= verilated.cpp verilated_vcd_c.cpp
#
# Use the verilated_cov.cpp source when you want to run Verilator coverage
# (The CPU is covered better by the formal proofs ...)
# VLSRCS	:= verilated.cpp verilated_vcd_c.cpp verilated_cov.cpp
VLOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(VLSRCS)))
VLIB	:= $(addprefix $(VROOT)/include/,$(VLSRCS))
RAWSYSLIB := $(RTLOBJD)/Vzipsystem__ALL.a
RAWBONLIB := $(RTLOBJD)/Vzipbones__ALL.a
SYSLIBS	:= $(RAWSYSLIB) -lncurses -lelf
BONLIBS	:= $(RAWBONLIB) -lncurses -lelf
TESTF	:= ../../bench/asm/simtest
DHRYSTONEF := ../asm/zipdhry.z

$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -c $< -o $@

$(OBJDIR)/zipsys_tb.o: zipcpu_tb.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -c $< -o $@

$(OBJDIR)/zipbones_tb.o: zipcpu_tb.cpp
	$(mk-objdir)
	$(CXX) -DZIPBONES $(VDEFS) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(ZASM)/%.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VROOT)/include/%.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

zipsys_tb: $(SYSOBJS) $(VLOBJS) $(RAWSYSLIB)
	$(CXX) $(CFLAGS) $(INCS) $(SYSOBJS) $(VLOBJS) $(SYSLIBS) -o $@

zipbones_tb: $(BONOBJS) $(VLOBJS) $(RAWBONLIB)
	$(CXX) $(CFLAGS) $(INCS) $(BONOBJS) $(VLOBJS) $(BONLIBS) -o $@

div_tb: div_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vdiv__ALL.a testb.h
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) div_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vdiv__ALL.a -o $@

mpy_tb: mpy_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vcpuops__ALL.a testb.h
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) mpy_tb.cpp twoc.cpp $(VLIB) $(RTLOBJD)/Vcpuops__ALL.a -o $@

zipmmu_tb: zipmmu_tb.cpp $(VLIB) $(BENCHOBJD)/Vzipmmu_tb__ALL.a
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -I$(BENCHOBJD) zipmmu_tb.cpp $(VLIB) $(BENCHOBJD)/Vzipmmu_tb__ALL.a -o $@

pfcache_tb: $(OBJDIR)/pfcache_tb.o $(OBJDIR)/memsim.o $(OBJDIR)/byteswap.o
pfcache_tb: $(VLIB) $(RTLOBJD)/Vpfcache__ALL.a
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -I$(RTLOBJD) $(OBJDIR)/pfcache_tb.o $(OBJDIR)/memsim.o $(OBJDIR)/byteswap.o $(VLIB) $(RTLOBJD)/Vpfcache__ALL.a -o $@

pdump: pdump.cpp $(ZOBJS) $(OBJDIR)/zopcodes.o $(OBJDIR)/pdump.o
pdump: $(ZASM)/zopcodes.h testb.h byteswap.h zipelf.h
	$(CXX) $(CFLAGS) $(INCS) $(OBJDIR)/pdump.o $(ZOBJS) -lelf -o $@

.PHONY: stest
stest: zipsys_tb
	./zipsys_tb -s $(TESTF)

.PHONY: itest
itest: zipsys_tb
	./zipsys_tb $(TESTF)

.PHONY: test
test: zipsys_tb stest
	./zipsys_tb -a $(TESTF)

.PHONY: dhrystone
dhrystone: zipsys_tb
	./zipsys_tb -a $(DHRYSTONEF)

define	build-depends
	@echo "Building dependencies"
	$(mk-objdir)
	@$(CXX) $(CPPFLAGS) $(INCS) -MM zipcpu_tb.cpp $(VLIB) $(SOURCES) > $(OBJDIR)/sysdepends.txt
	@$(CXX) -DZIPBONES $(CPPFLAGS) $(INCS) -MM zipcpu_tb.cpp $(VLIB) $(SOURCES) > $(OBJDIR)/bondepends.txt
	@sed -e 's/^zipcpu_tb.o: /zipsys_tb.o: /' < $(OBJDIR)/sysdepends.txt > $(OBJDIR)/xdepends.txt
	@sed -e 's/^zipcpu_tb.o: /zipbones_tb.o: /' < $(OBJDIR)/bondepends.txt >> $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
	@rm $(OBJDIR)/sysdepends.txt
	@rm $(OBJDIR)/bondepends.txt
endef

tags: $(VLIB) $(SOURCES)
	@ctags $(SOURCES) $(VLIB)

.PHONY: depends
depends: tags $(OBJDIR)/
	$(build-depends)

define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"
endef

$(OBJDIR)/depends.txt: $(OBJDIR)/ depends

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/
	rm -rf ./zipsys_tb ./zipbones_tb pdump div_tb mpy_tb
	rm -rf pfcache_tb

-include $(OBJDIR)/depends.txt
