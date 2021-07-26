################################################################################
##
## Filename:	Makefile
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	This is a grand makefile for the entire project.  It will
##		build the assembler, and a Verilog testbench, and then
##		even test the CPU via that test bench.
##
##	Targets include:
##
##		bench	Build the CPP test bench/debugger facility.
##
##		doc	Build the ZipCPU chip specification and the GPL
##			license.  These should be distributed pre-built, but
##			you are welcome to rebuild them if you would like.
##
##		rtl	Run Verilator on the RTL
##
##		sw	Build the obsolete assembler, binutils, and GCC.  By
##			default, this also 'install's the compiler into the
##			sw/install/ subdirectory as well.
##
##		test	Run the test bench on the assembler test file.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2015-2021, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
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
## }}}
.PHONY: all
all: rtl sw sim

MAKE := make	# Was `which make`
SUBMAKE := $(MAKE) --no-print-directory -C

.PHONY: doc
## {{{
doc:
	@echo "Building docs"; cd doc;
	+@$(SUBMAKE) doc/
## }}}

.PHONY: rtl
## {{{
rtl:
	@echo "Building rtl for Verilator";
	+@$(SUBMAKE) rtl/
## }}}

.PHONY: sw
## {{{
sw:
	@echo "Building toolchain";
	+@$(SUBMAKE) sw/
## }}}

.PHONY: sim cppsim vsim
## {{{
sim:	cppsim vsim

cppsim:
	@echo "Building in C++ simulator";
	+@$(SUBMAKE) sim/cpp

vsim: rtl
	@echo "Building Verilator simulator";
	+@$(SUBMAKE) sim/verilator
## }}}

.PHONY: clean
## {{{
clean:
	+@$(SUBMAKE) rtl clean
	+@$(SUBMAKE) sw clean
	+@$(SUBMAKE) sim/cpp clean
	+@$(SUBMAKE) sim/verilator clean
	+@$(SUBMAKE) bench/asm clean
	+@$(SUBMAKE) bench/cpp clean
## }}}

.PHONY: bench
## {{{
bench: rtl sw
	@echo "Building in bench/asm"; $(SUBMAKE) bench/asm
## }}}

.PHONY: test
## {{{
test: bench sim
	@echo "Running simulation tests"; $(SUBMAKE) sim/verilator test
## }}}

# .PHONY: dhrystone
# dhrystone: sw bench
	# @echo "Building Asm Dhrystone"; $(SUBMAKE) zipdhry.z --no-print-directory
	# @echo "Running Dhrystone"; $(SUBMAKE) sim/verilator dhrystone
