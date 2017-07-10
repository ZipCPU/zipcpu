################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	This makefile builds a verilator simulation of the rtl
#		testbenches necessary to test certain components of the
#	ZipSystem using Verilator.  It does not make the system within Icarus,
#	Vivado or Quartus.
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
.PHONY: all
all: zipmmu_tb

CORED:= ../../rtl/core
PRPHD:= ../../rtl/peripherals
AUXD := ../../rtl/aux
VOBJ := obj_dir
VERILATOR := verilator
VFLAGS    := -Wall -MMD -trace -y $(PRPHD) -cc
SUBMAKE   := $(MAKE) --no-print-directory -C

$(VOBJ)/Vzipmmu_tb.cpp: $(PRPHD)/zipmmu.v zipmmu_tb.v memdev.v
	$(VERILATOR) $(VFLAGS) zipmmu_tb.v
$(VOBJ)/Vzipmmu_tb.h: $(VOBJ)/Vzipmmu_tb.cpp

$(VOBJ)/Vzipmmu_tb__ALL.a: $(VOBJ)/Vzipmmu_tb.cpp $(VOBJ)/Vzipmmu_tb.h
	$(SUBMAKE) $(VOBJ) -f Vzipmmu_tb.mk

.PHONY: zipmmu_tb
zipmmu_tb: $(VOBJ)/Vzipmmu_tb__ALL.a

.PHONY: clean
clean:
	rm -rf $(VOBJ)


DEPS := $(wildcard $(VOBJ)/*.d)
ifneq ($(DEPS),)
include $(DEPS)
endif
