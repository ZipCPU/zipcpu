################################################################################
##
## Filename:	Makefile
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	This makefile builds a verilator simulation of the zipsystem.
##		It does not make the system within Vivado or Quartus.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2015-2024, Gisselquist Technology, LLC
## {{{
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
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
.PHONY: all
## }}}
all: zipbones zipsystem zipaxil zipaxi div zipmmu cpuops pfcache
.DELETE_ON_ERROR:

## Canned configurations
## {{{
ASMCFG := -GOPT_PIPELINED=1\\\'b0	\
	-GOPT_LGICACHE=0		\
	-GOPT_LGDCACHE=0		\
	-GOPT_MPY=0			\
	-GOPT_DIV=1\\\'b0		\
	-GOPT_SHIFTS=1\\\'b0		\
	-GOPT_LOCK=1\\\'b0		\
	-GOPT_EARLY_BRANCHING=1\\\'b0	\
	-GOPT_LOWPOWER=1\\\'b0		\
	-GOPT_DISTRIBUTED_REGS=1\\\'b0	\
	-GOPT_USERMODE=1\\\'b0		\
	-GOPT_CIS=1\\\'b0
TRAPCFG := -GOPT_PIPELINED=1\\\'b0	\
	-GOPT_LGICACHE=0		\
	-GOPT_LGDCACHE=0		\
	-GOPT_MPY=0			\
	-GOPT_DIV=1\\\'b0		\
	-GOPT_SHIFTS=1\\\'b1		\
	-GOPT_LOCK=1\\\'b1		\
	-GOPT_EARLY_BRANCHING=1\\\'b0	\
	-GOPT_LOWPOWER=1\\\'b0		\
	-GOPT_DISTRIBUTED_REGS=1\\\'b0	\
	-GOPT_USERMODE=1\\\'b1		\
	-GOPT_CIS=1\\\'b0
MINCFG := -GOPT_PIPELINED=1\\\'b0	\
	-GOPT_LGICACHE=0		\
	-GOPT_LGDCACHE=0		\
	-GOPT_MPY=6			\
	-GOPT_DIV=1\\\'b1		\
	-GOPT_SHIFTS=1\\\'b1		\
	-GOPT_LOCK=1\\\'b1		\
	-GOPT_EARLY_BRANCHING=1\\\'b0	\
	-GOPT_LOWPOWER=1\\\'b0		\
	-GOPT_DISTRIBUTED_REGS=1\\\'b0	\
	-GOPT_USERMODE=1\\\'b1		\
	-GOPT_CIS=1\\\'b1
PIPECFG := -GOPT_PIPELINED=1\\\'b1	\
	-GOPT_LGICACHE=2		\
	-GOPT_LGDCACHE=2		\
	-GOPT_MPY=6			\
	-GOPT_DIV=1\\\'b1		\
	-GOPT_SHIFTS=1\\\'b1		\
	-GOPT_LOCK=1\\\'b1		\
	-GOPT_EARLY_BRANCHING=1\\\'b1	\
	-GOPT_LOWPOWER=1\\\'b0		\
	-GOPT_DISTRIBUTED_REGS=1\\\'b0	\
	-GOPT_USERMODE=1\\\'b1		\
	-GOPT_CIS=1\\\'b1
CACHECFG := -GOPT_PIPELINED=1\\\'b1	\
	-GOPT_LGICACHE=12		\
	-GOPT_LGDCACHE=12		\
	-GOPT_MPY=6			\
	-GOPT_DIV=1\\\'b1		\
	-GOPT_SHIFTS=1\\\'b1		\
	-GOPT_LOCK=1\\\'b1		\
	-GOPT_EARLY_BRANCHING=1\\\'b1	\
	-GOPT_LOWPOWER=1\\\'b0		\
	-GOPT_DISTRIBUTED_REGS=1\\\'b0	\
	-GOPT_USERMODE=1\\\'b1		\
	-GOPT_CIS=1\\\'b1
LWPWR := -GOPT_PIPELINED=1\\\'b1	\
	-GOPT_LGICACHE=12		\
	-GOPT_LGDCACHE=12		\
	-GOPT_MPY=6			\
	-GOPT_DIV=1\\\'b1		\
	-GOPT_SHIFTS=1\\\'b1		\
	-GOPT_LOCK=1\\\'b1		\
	-GOPT_EARLY_BRANCHING=1\\\'b1	\
	-GOPT_LOWPOWER=1\\\'b1		\
	-GOPT_DISTRIBUTED_REGS=1\\\'b0	\
	-GOPT_USERMODE=1\\\'b1		\
	-GOPT_CIS=1\\\'b1
## }}}

CORED:= core
DMAD := zipdma
PRPHD:= peripherals
EXD  := ex
## Verilator setup
## {{{
VOBJ := obj_dir
SUBMAKE := $(MAKE) --no-print-directory --directory=$(VOBJ) -f
ifeq ($(VERILATOR_ROOT),)
VERILATOR := verilator
else
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif
##
# VCOVERAGE to get coverage analysis of our test cases
# VCOVERAGE := --coverage
VCOVERAGE :=
##
VFLAGS := -Wall -MMD --trace $(VCOVERAGE) -cc -y $(CORED) -y $(PRPHD) -y $(EXD) -y $(DMAD)

## }}}
## Dependency suggestions
## {{{
SYSSRC := zipsystem.v						\
		$(PRPHD)/wbdmac.v $(PRPHD)/icontrol.v		\
		$(PRPHD)/zipcounter.v $(PRPHD)/zipjiffies.v	\
		$(PRPHD)/ziptimer.v				\
	$(CORED)/zipwb.v $(CORED)/zipcore.v $(CORED)/cpuops.v	\
		$(CORED)/idecode.v $(CORED)/div.v		\
		$(CORED)/pipefetch.v $(CORED)/prefetch.v	\
		$(CORED)/pfcache.v				\
		$(CORED)/memops.v $(CORED)/pipemem.v		\
		$(CORED)/dcache.v				\
	$(EXD)/busdelay.v					\
		$(EXD)/wbdblpriarb.v $(EXD)/wbpriarbiter.v	\
	$(CORED)/idecode.v $(CORED)/cpuops.v
BONSRC := zipbones.v						\
	$(CORED)/zipwb.v $(CORED)/zipcore.v			\
		$(CORED)/cpuops.v $(CORED)/idecode.v		\
		$(CORED)/pipefetch.v $(CORED)/prefetch.v	\
		$(CORED)/pfcache.v				\
		$(CORED)/memops.v $(CORED)/pipemem.v		\
		$(CORED)/div.v					\
	$(EXD)/busdelay.v $(EXD)/wbdblpriarb.v			\
	$(CORED)/idecode.v $(CORED)/cpuops.v
AXLSRC := zipaxil.v $(CORED)/zipcore.v				\
		$(CORED)/cpuops.v $(CORED)/idecode.v		\
		$(CORED)/axilfetch.v $(CORED)/prefetch.v	\
		$(CORED)/axilops.v $(CORED)/axilpipe.v		\
		$(CORED)/axidcache.v				\
		$(CORED)/div.v					\
	$(CORED)/idecode.v $(CORED)/cpuops.v
AXISRC := zipaxi.v $(CORED)/zipcore.v				\
		$(CORED)/cpuops.v $(CORED)/idecode.v		\
		$(CORED)/axilfetch.v $(CORED)/axiicache.v	\
		$(CORED)/axiops.v $(CORED)/axilpipe.v		\
		$(CORED)/axidcache.v				\
		$(CORED)/div.v					\
	$(CORED)/idecode.v $(CORED)/cpuops.v
## }}}
#

VERILATE=$(VERILATOR) $(VFLAGS)

# $(VOBJ)/V%__ALL.a: $(VOBJ)/V%.cpp $(VOBJ)/V%.h
#	$(SUBMAKE) V%.mk

.PHONY: zipsystem sysasm systrap sysmin syspipe syscache syslp
## {{{
zipsystem: sysasm systrap sysmin syspipe syscache syslp zipsys

sysasm: $(VOBJ)/Vsysasm__ALL.a
$(VOBJ)/Vsysasm.h: $(VOBJ)/Vsysasm.cpp
$(VOBJ)/Vsysasm.cpp: $(SYSSRC)
	$(VERILATE) $(ASMCFG) --prefix Vsysasm -cc zipsystem.v
$(VOBJ)/Vsysasm__ALL.a: $(VOBJ)/Vsysasm.cpp $(VOBJ)/Vsysasm.h
	$(SUBMAKE) Vsysasm.mk

systrap: $(VOBJ)/Vsystrap__ALL.a
$(VOBJ)/Vsystrap.h: $(VOBJ)/Vsystrap.cpp
$(VOBJ)/Vsystrap.cpp: $(SYSSRC)
	$(VERILATE) $(TRAPCFG) --prefix Vsystrap -cc zipsystem.v
$(VOBJ)/Vsystrap__ALL.a: $(VOBJ)/Vsystrap.cpp $(VOBJ)/Vsystrap.h
	$(SUBMAKE) Vsystrap.mk

sysmin: $(VOBJ)/Vsysmin__ALL.a
$(VOBJ)/Vsysmin.h: $(VOBJ)/Vsysmin.cpp
$(VOBJ)/Vsysmin.cpp: $(SYSSRC)
	$(VERILATE) $(MINCFG) --prefix Vsysmin -cc zipsystem.v
$(VOBJ)/Vsysmin__ALL.a: $(VOBJ)/Vsysmin.cpp $(VOBJ)/Vsysmin.h
	$(SUBMAKE) Vsysmin.mk

syspipe: $(VOBJ)/Vsyspipe__ALL.a
$(VOBJ)/Vsyspipe.h: $(VOBJ)/Vsyspipe.cpp
$(VOBJ)/Vsyspipe.cpp: $(SYSSRC)
	$(VERILATE) $(PIPECFG) --prefix Vsyspipe -cc zipsystem.v
$(VOBJ)/Vsyspipe__ALL.a: $(VOBJ)/Vsyspipe.cpp $(VOBJ)/Vsyspipe.h
	$(SUBMAKE) Vsyspipe.mk

syscache: $(VOBJ)/Vsyscache__ALL.a
$(VOBJ)/Vsyscache.h: $(VOBJ)/Vsyscache.cpp
$(VOBJ)/Vsyscache.cpp: $(SYSSRC)
	$(VERILATE) $(CACHECFG) --prefix Vsyscache -cc zipsystem.v
$(VOBJ)/Vsyscache__ALL.a: $(VOBJ)/Vsyscache.cpp $(VOBJ)/Vsyscache.h
	$(SUBMAKE) Vsyscache.mk

syslp: $(VOBJ)/Vsyslp__ALL.a
$(VOBJ)/Vsyslp.h: $(VOBJ)/Vsyslp.cpp
$(VOBJ)/Vsyslp.cpp: $(SYSSRC)
	$(VERILATE) $(LWPWR) --prefix Vsyslp -cc zipsystem.v
$(VOBJ)/Vsyslp__ALL.a: $(VOBJ)/Vsyslp.cpp $(VOBJ)/Vsyslp.h
	$(SUBMAKE) Vsyslp.mk

zipsys: $(VOBJ)/Vzipsystem__ALL.a
$(VOBJ)/Vzipsystem.h: $(VOBJ)/Vzipsystem.cpp
$(VOBJ)/Vzipsystem.cpp: $(SYSSRC)
	$(VERILATE) -DVBENCH_TB $(LWPWR) --prefix Vzipsystem -cc zipsystem.v
$(VOBJ)/Vzipsystem__ALL.a: $(VOBJ)/Vzipsystem.cpp $(VOBJ)/Vzipsystem.h
	$(SUBMAKE) Vzipsystem.mk
## }}}

.PHONY: zipbones bonesasm bonestrap bonesmin bonespipe bonescache boneslp
## {{{
zipbones:  bonesasm bonestrap bonesmin bonespipe bonescache boneslp zipbone

bonesasm: $(VOBJ)/Vbonesasm__ALL.a
$(VOBJ)/Vbonesasm.h: $(VOBJ)/Vbonesasm.cpp
$(VOBJ)/Vbonesasm.cpp: $(BONSRC)
	$(VERILATE) $(ASMCFG) --prefix Vbonesasm -cc zipbones.v
$(VOBJ)/Vbonesasm__ALL.a: $(VOBJ)/Vbonesasm.cpp $(VOBJ)/Vbonesasm.h
	$(SUBMAKE) Vbonesasm.mk

bonestrap: $(VOBJ)/Vbonestrap__ALL.a
$(VOBJ)/Vbonestrap.h: $(VOBJ)/Vbonestrap.cpp
$(VOBJ)/Vbonestrap.cpp: $(BONSRC)
	$(VERILATE) $(TRAPCFG) --prefix Vbonestrap -cc zipbones.v
$(VOBJ)/Vbonestrap__ALL.a: $(VOBJ)/Vbonestrap.cpp $(VOBJ)/Vbonestrap.h
	$(SUBMAKE) Vbonestrap.mk

bonesmin: $(VOBJ)/Vbonesmin__ALL.a
$(VOBJ)/Vbonesmin.h: $(VOBJ)/Vbonesmin.cpp
$(VOBJ)/Vbonesmin.cpp: $(BONSRC)
	$(VERILATE) $(MINCFG) --prefix Vbonesmin -cc zipbones.v
$(VOBJ)/Vbonesmin__ALL.a: $(VOBJ)/Vbonesmin.cpp $(VOBJ)/Vbonesmin.h
	$(SUBMAKE) Vbonesmin.mk

bonespipe: $(VOBJ)/Vbonespipe__ALL.a
$(VOBJ)/Vbonespipe.h: $(VOBJ)/Vbonespipe.cpp
$(VOBJ)/Vbonespipe.cpp: $(BONSRC)
	$(VERILATE) $(PIPECFG) --prefix Vbonespipe -cc zipbones.v
$(VOBJ)/Vbonespipe__ALL.a: $(VOBJ)/Vbonespipe.cpp $(VOBJ)/Vbonespipe.h
	$(SUBMAKE) Vbonespipe.mk

bonescache: $(VOBJ)/Vbonescache__ALL.a
$(VOBJ)/Vbonescache.h: $(VOBJ)/Vbonescache.cpp
$(VOBJ)/Vbonescache.cpp: $(BONSRC)
	$(VERILATE) $(CACHECFG) --prefix Vbonescache -cc zipbones.v
$(VOBJ)/Vbonescache__ALL.a: $(VOBJ)/Vbonescache.cpp $(VOBJ)/Vbonescache.h
	$(SUBMAKE) Vbonescache.mk

boneslp: $(VOBJ)/Vboneslp__ALL.a
$(VOBJ)/Vboneslp.h: $(VOBJ)/Vboneslp.cpp
$(VOBJ)/Vboneslp.cpp: $(BONSRC)
	$(VERILATE) $(LWPWR) --prefix Vboneslp -cc zipbones.v
$(VOBJ)/Vboneslp__ALL.a: $(VOBJ)/Vboneslp.cpp $(VOBJ)/Vboneslp.h
	$(SUBMAKE) Vboneslp.mk

zipbone: $(VOBJ)/Vzipbones__ALL.a
$(VOBJ)/Vzipbones.h: $(VOBJ)/Vzipbones.cpp
$(VOBJ)/Vzipbones.cpp: $(BONSRC)
	$(VERILATE) -DVBENCH_TB $(LWPWR) --prefix Vzipbones -cc zipbones.v
$(VOBJ)/Vzipbones__ALL.a: $(VOBJ)/Vzipbones.cpp $(VOBJ)/Vzipbones.h
	$(SUBMAKE) Vzipbones.mk
## }}}

.PHONY: zipaxil axilasm axiltrap axilmin axilpipe axilbench
## {{{
zipaxil: axilasm axiltrap axilmin axilpipe axilbench

axilasm: $(VOBJ)/Vaxilasm__ALL.a
$(VOBJ)/Vaxilasm.h: $(VOBJ)/Vaxilasm.cpp
$(VOBJ)/Vaxilasm.cpp: $(AXLSRC)
	$(VERILATE) $(ASMCFG) --prefix Vaxilasm -cc zipaxil.v
$(VOBJ)/Vaxilasm__ALL.a: $(VOBJ)/Vaxilasm.cpp $(VOBJ)/Vaxilasm.h
	$(SUBMAKE) Vaxilasm.mk

axiltrap: $(VOBJ)/Vaxiltrap__ALL.a
$(VOBJ)/Vaxiltrap.h: $(VOBJ)/Vaxiltrap.cpp
$(VOBJ)/Vaxiltrap.cpp: $(AXLSRC)
	$(VERILATE) $(TRAPCFG) --prefix Vaxiltrap -cc zipaxil.v
$(VOBJ)/Vaxiltrap__ALL.a: $(VOBJ)/Vaxiltrap.cpp $(VOBJ)/Vaxiltrap.h
	$(SUBMAKE) Vaxiltrap.mk

axilmin: $(VOBJ)/Vaxilmin__ALL.a
$(VOBJ)/Vaxilmin.h: $(VOBJ)/Vaxilmin.cpp
$(VOBJ)/Vaxilmin.cpp: $(AXLSRC)
	$(VERILATE) $(MINCFG) --prefix Vaxilmin -cc zipaxil.v
$(VOBJ)/Vaxilmin__ALL.a: $(VOBJ)/Vaxilmin.cpp $(VOBJ)/Vaxilmin.h
	$(SUBMAKE) Vaxilmin.mk

axilpipe: $(VOBJ)/Vaxilpipe__ALL.a
$(VOBJ)/Vaxilpipe.h: $(VOBJ)/Vaxilpipe.cpp
$(VOBJ)/Vaxilpipe.cpp: $(AXLSRC)
	$(VERILATE) $(PIPECFG) --prefix Vaxilpipe -cc zipaxil.v
$(VOBJ)/Vaxilpipe__ALL.a: $(VOBJ)/Vaxilpipe.cpp $(VOBJ)/Vaxilpipe.h
	$(SUBMAKE) Vaxilpipe.mk

axilbench: $(VOBJ)/Vzipaxil__ALL.a
$(VOBJ)/Vzipaxil.h: $(VOBJ)/Vzipaxil.cpp
$(VOBJ)/Vzipaxil.cpp: $(AXLSRC)
	$(VERILATE) $(PIPECFG) -DVBENCH_TB --prefix Vzipaxil -cc zipaxil.v
$(VOBJ)/Vzipaxil__ALL.a: $(VOBJ)/Vzipaxil.cpp $(VOBJ)/Vzipaxil.h
	$(SUBMAKE) Vzipaxil.mk
## }}}

.PHONY: zipaxi axiasm axitrap aximin axipipe axicache axilp
## {{{
zipaxi: axiasm axitrap aximin axipipe axicache axilp

axiasm: $(VOBJ)/Vaxiasm__ALL.a
$(VOBJ)/Vaxiasm.h: $(VOBJ)/Vaxiasm.cpp
$(VOBJ)/Vaxiasm__ALL.a: $(VOBJ)/Vaxiasm.cpp $(VOBJ)/Vaxiasm.h
	$(SUBMAKE) Vaxiasm.mk
$(VOBJ)/Vaxiasm.cpp: $(AXISRC)
	$(VERILATE) $(ASMCFG) --prefix Vaxiasm -cc zipaxi.v

axitrap: $(VOBJ)/Vaxitrap__ALL.a
$(VOBJ)/Vaxitrap.h: $(VOBJ)/Vaxitrap.cpp
$(VOBJ)/Vaxitrap__ALL.a: $(VOBJ)/Vaxitrap.cpp $(VOBJ)/Vaxitrap.h
	$(SUBMAKE) Vaxitrap.mk
$(VOBJ)/Vaxitrap.cpp: $(AXISRC)
	$(VERILATE) $(TRAPCFG) --prefix Vaxitrap -cc zipaxi.v

aximin: $(VOBJ)/Vaximin__ALL.a
$(VOBJ)/Vaximin.h: $(VOBJ)/Vaximin.cpp
$(VOBJ)/Vaximin__ALL.a: $(VOBJ)/Vaximin.cpp $(VOBJ)/Vaximin.h
	$(SUBMAKE) Vaximin.mk
$(VOBJ)/Vaximin.cpp: $(AXISRC)
	$(VERILATE) $(MINCFG) --prefix Vaximin -cc zipaxi.v

axipipe: $(VOBJ)/Vaxipipe__ALL.a
$(VOBJ)/Vaxipipe.h: $(VOBJ)/Vaxipipe.cpp
$(VOBJ)/Vaxipipe__ALL.a: $(VOBJ)/Vaxipipe.cpp $(VOBJ)/Vaxipipe.h
	$(SUBMAKE) Vaxipipe.mk
$(VOBJ)/Vaxipipe.cpp: $(AXISRC)
	$(VERILATE) $(PIPECFG) --prefix Vaxipipe -cc zipaxi.v

axicache: $(VOBJ)/Vaxicache__ALL.a
$(VOBJ)/Vaxicache.h: $(VOBJ)/Vaxicache.cpp
$(VOBJ)/Vaxicache__ALL.a: $(VOBJ)/Vaxicache.cpp $(VOBJ)/Vaxicache.h
	$(SUBMAKE) Vaxicache.mk
$(VOBJ)/Vaxicache.cpp: $(AXISRC)
	$(VERILATE) $(CACHECFG) --prefix Vaxicache -cc zipaxi.v

axilp: $(VOBJ)/Vaxilp__ALL.a
$(VOBJ)/Vaxilp.h: $(VOBJ)/Vaxilp.cpp
$(VOBJ)/Vaxilp__ALL.a: $(VOBJ)/Vaxilp.cpp $(VOBJ)/Vaxilp.h
	$(SUBMAKE) Vaxilp.mk
$(VOBJ)/Vaxilp.cpp: $(AXISRC)
	$(VERILATE) $(LWPWR) --prefix Vaxilp -cc zipaxi.v

## }}}

.PHONY: div
## {{{
div: $(VOBJ)/Vdiv__ALL.a
$(VOBJ)/Vdiv.h: $(VOBJ)/Vdiv.cpp
$(VOBJ)/Vdiv.cpp: $(CORED)/div.v
	$(VERILATE) $(CORED)/div.v
$(VOBJ)/Vdiv__ALL.a: $(VOBJ)/Vdiv.cpp $(VOBJ)/Vdiv.h
	$(SUBMAKE) Vdiv.mk
## }}}

.PHONY: cpuops
## {{{
cpuops: $(VOBJ)/Vcpuops__ALL.a
$(VOBJ)/Vcpuops.h: $(VOBJ)/Vcpuops.cpp
$(VOBJ)/Vcpuops.cpp: $(CORED)/cpuops.v
	$(VERILATE) -DVMPY_TB $(CORED)/cpuops.v
$(VOBJ)/Vcpuops__ALL.a: $(VOBJ)/Vcpuops.cpp $(VOBJ)/Vcpuops.h
	$(SUBMAKE) Vcpuops.mk
## }}}

.PHONY: zipmmu
## {{{
zipmmu: $(VOBJ)/Vzipmmu__ALL.a
$(VOBJ)/Vzipmmu.h: $(VOBJ)/Vzipmmu.cpp
$(VOBJ)/Vzipmmu.cpp: $(PRPHD)/zipmmu.v
	$(VERILATE) $(PRPHD)/zipmmu.v
$(VOBJ)/Vzipmmu__ALL.a: $(VOBJ)/Vzipmmu.cpp $(VOBJ)/Vzipmmu.h
	$(SUBMAKE) Vzipmmu.mk
## }}}

.PHONY: pfcache
## {{{
pfcache: $(VOBJ)/Vpfcache__ALL.a
$(VOBJ)/Vpfcache.h: $(VOBJ)/Vpfcache.cpp
$(VOBJ)/Vpfcache.cpp: $(CORED)/pfcache.v
	$(VERILATE) $(CORED)/pfcache.v
$(VOBJ)/Vpfcache__ALL.a: $(VOBJ)/Vpfcache.cpp $(VOBJ)/Vpfcache.h
	$(SUBMAKE) Vpfcache.mk
## }}}

.PHONY: clean
## {{{
clean:
	rm -rf $(VOBJ)
## }}}

## Verilator generated dependencies
## {{{
# Note Verilator's dependency created information, and include it here if we can
DEPS := $(wildcard $(VOBJ)/*.d)

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(DEPS),)
include $(DEPS)
endif
endif
## }}}
