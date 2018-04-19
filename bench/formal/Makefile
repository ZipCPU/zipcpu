################################################################################
##
## Filename:	Makefile
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To direct the formal verification of particular components of
##		the ZipCPU.
##
## Targets:	The default target, all, tests all of the components within
##		this module.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2018, Gisselquist Technology, LLC
##
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
##
TESTS := prefetch dblfetch pfcache memops pipemem idecode div
TESTS += zipmmu ziptimer zipcounter zipjiffies wbwatchdog zipmmu icontrol wbdmac
TESTS += busdelay wbpriarbiter wbdblpriarb cpuops cpu
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
# SOLVER  := -s yices
SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER)
INDARGS := $(SOLVER) -i

PFONE  := prefetch
PFTWO  := dblfetch
PFCACHE:= pfcache
WBDLY  := busdelay
PRIARB := wbpriarbiter
DBL    := wbdblpriarb
MEM    := memops
PIPE   := pipemem
MMU    := zipmmu
TMR    := ziptimer
CNT    := zipcounter
JIF    := zipjiffies
WDG    := wbwatchdog
INT    := icontrol
DCD    := idecode
DMA    := wbdmac
ALU    := cpuops
DIV    := div
CPU    := zipcpu
.PHONY: cpu
cpu: zipcpu

MASTER := $(RTL)/ex/fwb_master.v
SLAVE  := $(RTL)/ex/fwb_slave.v

$(PFONE).smt2: $(RTL)/core/$(PFONE).v $(MASTER) $(PFONE).ys
	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFTWO).smt2: $(RTL)/core/$(PFTWO).v $(MASTER) $(PFTWO).ys
	yosys -ql $(PFTWO).yslog -s $(PFTWO).ys

$(PFCACHE).smt2: $(RTL)/core/$(PFCACHE).v $(MASTER) $(PFCACHE).ys
	yosys -ql $(PFCACHE).yslog -s $(PFCACHE).ys

$(WBDLY).smt2: $(RTL)/ex/$(WBDLY).v $(MASTER) $(SLAVE) $(WBDLY).ys
	yosys -ql $(WBDLY).yslog -s $(WBDLY).ys

$(PRIARB).smt2: $(RTL)/ex/$(PRIARB).v $(MASTER) $(SLAVE) $(PRIARB).ys
	yosys -ql $(PRIARB).yslog -s $(PRIARB).ys

$(DBL).smt2: $(RTL)/ex/$(DBL).v $(MASTER) $(SLAVE) $(DBL).ys
	yosys -ql $(DBL).yslog -s $(DBL).ys

$(MEM).smt2: $(RTL)/core/$(MEM).v $(MASTER) $(MEM).ys
	yosys -ql $(MEM).yslog -s $(MEM).ys

$(PIPE).smt2: $(RTL)/core/$(PIPE).v $(MASTER) $(PIPE).ys
	yosys -ql $(PIPE).yslog -s $(PIPE).ys

$(MMU).smt2: $(RTL)/peripherals/$(MMU).v $(MASTER) $(SLAVE) $(MMU).ys
	yosys -ql $(MMU).yslog -s $(MMU).ys

$(CNT).smt2: $(RTL)/peripherals/$(CNT).v $(SLAVE) $(CNT).ys
	yosys -ql $(CNT).yslog -s $(CNT).ys

$(TMR).smt2: $(RTL)/peripherals/$(TMR).v $(SLAVE) $(TMR).ys
	yosys -ql $(TMR).yslog -s $(TMR).ys

$(JIF).smt2: $(RTL)/peripherals/$(JIF).v $(SLAVE) $(JIF).ys
	yosys -ql $(JIF).yslog -s $(JIF).ys

$(WDG).smt2: $(RTL)/peripherals/$(WDG).v $(SLAVE) $(WDG).ys
	yosys -ql $(WDG).yslog -s $(WDG).ys

$(INT).smt2: $(RTL)/peripherals/$(INT).v $(SLAVE) $(INT).ys
	yosys -ql $(INT).yslog -s $(INT).ys

$(DCD).smt2: $(RTL)/core/$(DCD).v $(DCD).ys f_idecode.v
	yosys -ql $(DCD).yslog -s $(DCD).ys

$(DMA).smt2: $(RTL)/peripherals/$(DMA).v $(MASTER) $(SLAVE) $(DMA).ys
	yosys -ql $(DMA).yslog -s $(DMA).ys

$(ALU).smt2: $(RTL)/core/$(ALU).v abs_mpy.v $(ALU).ys
	yosys -ql $(ALU).yslog -s $(ALU).ys

$(DIV).smt2: $(RTL)/core/$(DIV).v $(DIV).ys
	yosys -ql $(DIV).yslog -s $(DIV).ys


#$(PFONE).smt2: $(RTL)/$(PFONE).v
#	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFONE) : $(PFONE).check
$(PFONE).check: $(PFONE).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 60 --dump-vcd $(PFONE).vcd $(PFONE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 60 --dump-vcd $(PFONE).vcd $(PFONE).smt2
	$(SMTBMC)    $(INDARGS) -t 58 --dump-vcd $(PFONE).vcd $(PFONE).smt2
	touch $@


$(PFTWO) : $(PFTWO).check
$(PFTWO).check: $(PFTWO).smt2
	@rm -f $@
	$(SMTBMC) $(BMCARGS) -t 40 --dump-vcd $(PFTWO).vcd $(PFTWO).smt2
	$(SMTBMC) $(INDARGS) -t 38 --dump-vcd $(PFTWO).vcd $(PFTWO).smt2
	$(SMTBMC) -c $(BMCARGS) -t 40 --dump-vcd $(PFTWO)%.vcd $(PFTWO).smt2
	touch $@

$(PFCACHE) : $(PFCACHE).check
$(PFCACHE).check: $(PFCACHE).smt2
	@rm -f $@
	$(SMTBMC) $(BMCARGS) -t 80 --dump-vcd $(PFCACHE).vcd $(PFCACHE).smt2
	$(SMTBMC) $(INDARGS) -t 76 --dump-vcd $(PFCACHE).vcd $(PFCACHE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 80 --dump-vcd $(PFCACHE).vcd $(PFCACHE).smt2
	touch $@


$(WBDLY) : $(WBDLY).check
$(WBDLY).check: $(WBDLY).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 48 --dump-vcd $(WBDLY).vcd $(WBDLY).smt2
	$(SMTBMC)    $(INDARGS) -t 48 --dump-vcd $(WBDLY).vcd $(WBDLY).smt2
	$(SMTBMC) -g $(BMCARGS) -t 46 --dump-vcd $(WBDLY).vcd $(WBDLY).smt2
	touch $@

$(PRIARB) : $(PRIARB).check
$(PRIARB).check: $(PRIARB).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(PRIARB).vcd $(PRIARB).smt2
	$(SMTBMC)    $(INDARGS) -t 16 --dump-vcd $(PRIARB).vcd $(PRIARB).smt2
	$(SMTBMC) -g $(BMCARGS) -t 20 --dump-vcd $(PRIARB).vcd $(PRIARB).smt2
	touch $@

$(DBL) : $(DBL).check
$(DBL).check: $(DBL).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(DBL).vcd $(DBL).smt2
	$(SMTBMC)    $(INDARGS) -t 16 --dump-vcd $(DBL).vcd $(DBL).smt2
	$(SMTBMC) -g $(BMCARGS) -t 20 --dump-vcd $(DBL).vcd $(DBL).smt2
	touch $@

$(MEM) : $(MEM).check
$(MEM).check: $(MEM).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(MEM).vcd $(MEM).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(MEM).vcd $(MEM).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(MEM).vcd $(MEM).smt2
	touch $@

$(PIPE) : $(PIPE).check
$(PIPE).check: $(PIPE).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(PIPE).vcd $(PIPE).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(PIPE).vcd $(PIPE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(PIPE).vcd $(PIPE).smt2
	touch $@

$(MMU) : $(MMU).check
$(MMU).check: $(MMU).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 16 --dump-vcd $(MMU).vcd $(MMU).smt2
	$(SMTBMC)    $(INDARGS) -t 15 --dump-vcd $(MMU).vcd $(MMU).smt2
	$(SMTBMC) -g $(BMCARGS) -t 16 --dump-vcd $(MMU).vcd $(MMU).smt2
	touch $@

$(TMR) : $(TMR).check
$(TMR).check: $(TMR).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 15 --dump-vcd $(TMR).vcd $(TMR).smt2
	$(SMTBMC)    $(INDARGS) -t 10 --dump-vcd $(TMR).vcd $(TMR).smt2
	$(SMTBMC) -g $(BMCARGS) -t 15 --dump-vcd $(TMR).vcd $(TMR).smt2
	touch $@

$(CNT) : $(CNT).check
$(CNT).check: $(CNT).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 15 --dump-vcd $(CNT).vcd $(CNT).smt2
	$(SMTBMC)    $(INDARGS) -t 10 --dump-vcd $(CNT).vcd $(CNT).smt2
	$(SMTBMC) -g $(BMCARGS) -t 15 --dump-vcd $(CNT).vcd $(CNT).smt2
	touch $@

$(JIF) : $(JIF).check
$(JIF).check: $(JIF).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 15 --dump-vcd $(JIF).vcd $(JIF).smt2
	$(SMTBMC)    $(INDARGS) -t 10 --dump-vcd $(JIF).vcd $(JIF).smt2
	$(SMTBMC) -g $(BMCARGS) -t 15 --dump-vcd $(JIF).vcd $(JIF).smt2
	touch $@

$(WDG) : $(WDG).check
$(WDG).check: $(WDG).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 15 --dump-vcd $(WDG).vcd $(WDG).smt2
	$(SMTBMC)    $(INDARGS) -t 10 --dump-vcd $(WDG).vcd $(WDG).smt2
	$(SMTBMC) -g $(BMCARGS) -t 15 --dump-vcd $(WDG).vcd $(WDG).smt2
	touch $@

$(INT) : $(INT).check
$(INT).check: $(INT).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 15 --dump-vcd $(INT).vcd $(INT).smt2
	$(SMTBMC)    $(INDARGS) -t 10 --dump-vcd $(INT).vcd $(INT).smt2
	$(SMTBMC) -g $(BMCARGS) -t 15 --dump-vcd $(INT).vcd $(INT).smt2
	touch $@

$(DCD) : $(DCD).check
$(DCD).check: $(DCD).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 10 --dump-vcd $(DCD).vcd $(DCD).smt2
	$(SMTBMC)    $(INDARGS) -t  8 --dump-vcd $(DCD).vcd $(DCD).smt2
	$(SMTBMC) -g $(BMCARGS) -t 10 --dump-vcd $(DCD).vcd $(DCD).smt2
	touch $@

$(DMA) : $(DMA).check
$(DMA).check: $(DMA).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(DMA).vcd $(DMA).smt2
	$(SMTBMC)    $(INDARGS) -t 20 --dump-vcd $(DMA).vcd $(DMA).smt2
	touch $@

$(ALU) : $(ALU).check
$(ALU).check: $(ALU).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 10 --dump-vcd $(ALU).vcd $(ALU).smt2
	$(SMTBMC)    $(INDARGS) -t  8 --dump-vcd $(ALU).vcd $(ALU).smt2
	touch $@

$(DIV) : $(DIV).check
$(DIV).check: $(DIV).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(DIV).vcd $(DIV).smt2
	$(SMTBMC)    $(INDARGS) -t 38 --dump-vcd $(DIV).vcd $(DIV).smt2
	touch $@

$(CPU) : $(CPU).check
$(CPU).check: $(RTL)/core/$(CPU).v
$(CPU).check: $(RTL)/core/cpuops.v
$(CPU).check: $(RTL)/core/idecode.v
$(CPU).check: $(RTL)/core/pipemem.v
$(CPU).check: $(RTL)/core/memops.v
$(CPU).check: $(RTL)/ex/wbdblpriarb.v
$(CPU).check: $(RTL)/ex/fwb_counter.v
$(CPU).check: $(RTL)/cpudefs.v
$(CPU).check: f_idecode.v
$(CPU).check: $(MASTER) $(SLAVE) abs_div.v abs_prefetch.v abs_mpy.v $(CPU).sby
	@rm -f $@
	sby -f $(CPU).sby prove_first prove_second
	touch $@

.PHONY: clean
clean:
	rm -f $(PFONE).smt2   $(PFONE)*.vcd   $(PFONE).yslog
	rm -f $(PFTWO).smt2   $(PFTWO)*.vcd   $(PFTWO).yslog
	rm -f $(PFCACHE).smt2 $(PFCACHE)*.vcd $(PFCACHE).yslog
	rm -f $(WBDLY).smt2   $(WBDLY)*.vcd   $(WBDLY).yslog
	rm -f $(PRIARB).smt2  $(PRIARB)*.vcd  $(PRIARB).yslog
	rm -f $(DBL).smt2     $(DBL)*.vcd     $(DBL).yslog
	rm -f $(MEM).smt2     $(MEM)*.vcd     $(MEM).yslog
	rm -f $(PIPE).smt2    $(PIPE)*.vcd    $(PIPE).yslog
	rm -f $(MMU).smt2     $(MMU)*.vcd     $(MMU).yslog
	rm -f $(TMR).smt2     $(TMR)*.vcd     $(TMR).yslog
	rm -f $(CNT).smt2     $(CNT)*.vcd     $(CNT).yslog
	rm -f $(JIF).smt2     $(JIF)*.vcd     $(JIF).yslog
	rm -f $(WDG).smt2     $(WDG)*.vcd     $(WDG).yslog
	rm -f $(INT).smt2     $(INT)*.vcd     $(INT).yslog
	rm -f $(DCD).smt2     $(DCD)*.vcd     $(DCD).yslog
	rm -f $(DMA).smt2     $(DMA)*.vcd     $(DMA).yslog
	rm -f $(ALU).smt2     $(ALU)*.vcd     $(ALU).yslog
	rm -f $(DIV).smt2     $(DIV)*.vcd     $(DIV).yslog
	rm -f $(CPU).smt2     $(CPU)*.vcd     $(CPU).yslog $(CPU)/
	rm -f *.check
