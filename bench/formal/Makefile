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
## Copyright (C) 2017, Gisselquist Technology, LLC
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
TESTS := prefetch dblfetch pfcache busdelay wbpriarbiter memops
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
# SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER) --unroll
# BMCARGS := $(SOLVER) --unroll
# BMCARGS := $(SOLVER)
INDARGS := $(SOLVER) -i

PFONE  :=prefetch
PFTWO  := dblfetch
PFCACHE:= pfcache
WBDLY  := busdelay
PRIARB := wbpriarbiter
MEM    := memops
PIPE   := pipemem

MASTER := $(RTL)/aux/formal_master.v
SLAVE  := $(RTL)/aux/formal_slave.v

$(PFONE).smt2: $(RTL)/core/$(PFONE).v $(MASTER) $(PFONE).ys
	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFTWO).smt2: $(RTL)/core/$(PFTWO).v $(MASTER) $(PFTWO).ys
	yosys -ql $(PFTWO).yslog -s $(PFTWO).ys

$(PFCACHE).smt2: $(RTL)/core/$(PFCACHE).v $(MASTER) $(PFCACHE).ys
	yosys -ql $(PFCACHE).yslog -s $(PFCACHE).ys

$(WBDLY).smt2: $(RTL)/aux/$(WBDLY).v $(MASTER) $(SLAVE) $(WBDLY).ys
	yosys -ql $(WBDLY).yslog -s $(WBDLY).ys

$(PRIARB).smt2: $(RTL)/aux/$(PRIARB).v $(MASTER) $(SLAVE) $(PRIARB).ys
	yosys -ql $(PRIARB).yslog -s $(PRIARB).ys

$(MEM).smt2: $(RTL)/core/$(MEM).v $(MASTER) $(MEM).ys
	yosys -ql $(MEM).yslog -s $(MEM).ys

$(PIPE).smt2: $(RTL)/core/$(PIPE).v $(MASTER) $(PIPE).ys
	yosys -ql $(PIPE).yslog -s $(PIPE).ys

#$(PFONE).smt2: $(RTL)/$(PFONE).v
#	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFONE) : $(PFONE).check
$(PFONE).check: $(PFONE).smt2
	@rm -f $(PFONE).check
	$(SMTBMC)    $(BMCARGS) -t 60 --dump-vcd $(PFONE).vcd $(PFONE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 60 --dump-vcd $(PFONE).vcd $(PFONE).smt2
	$(SMTBMC)    $(INDARGS) -t 58 --dump-vcd $(PFONE).vcd $(PFONE).smt2
	touch $@


$(PFTWO) : $(PFTWO).check
$(PFTWO).check: $(PFTWO).smt2
	@rm -f $(PFTWO).check
	$(SMTBMC) $(BMCARGS) -t 40 --dump-vcd $(PFTWO).vcd $(PFTWO).smt2
	$(SMTBMC) $(INDARGS) -t 38 --dump-vcd $(PFTWO).vcd $(PFTWO).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(PFTWO).vcd $(PFTWO).smt2
	touch $@

$(PFCACHE) : $(PFCACHE).check
$(PFCACHE).check: $(PFCACHE).smt2
	@rm -f $(PFCACHE).check
	$(SMTBMC) $(BMCARGS) -t 80 --dump-vcd $(PFCACHE).vcd $(PFCACHE).smt2
	$(SMTBMC) $(INDARGS) -t 76 --dump-vcd $(PFCACHE).vcd $(PFCACHE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 80 --dump-vcd $(PFCACHE).vcd $(PFCACHE).smt2
	touch $@


$(WBDLY) : $(WBDLY).check
$(WBDLY).check: $(WBDLY).smt2
	@rm -f $(WBDLY).check
	$(SMTBMC)    $(BMCARGS) -t 48 --dump-vcd $(WBDLY).vcd $(WBDLY).smt2
	$(SMTBMC)    $(INDARGS) -t 48 --dump-vcd $(WBDLY).vcd $(WBDLY).smt2
	$(SMTBMC) -g $(BMCARGS) -t 46 --dump-vcd $(WBDLY).vcd $(WBDLY).smt2
	touch $@

$(PRIARB) : $(PRIARB).check
$(PRIARB).check: $(PRIARB).smt2
	@rm -f $(PRIARB).check
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(PRIARB).vcd $(PRIARB).smt2
	$(SMTBMC)    $(INDARGS) -t 16 --dump-vcd $(PRIARB).vcd $(PRIARB).smt2
	$(SMTBMC) -g $(BMCARGS) -t 20 --dump-vcd $(PRIARB).vcd $(PRIARB).smt2
	touch $@

$(MEM) : $(MEM).check
$(MEM).check: $(MEM).smt2
	@rm -f $(MEM).check
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(MEM).vcd $(MEM).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(MEM).vcd $(MEM).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(MEM).vcd $(MEM).smt2
	touch $@

$(PIPE) : $(PIPE).check
$(PIPE).check: $(PIPE).smt2
	@rm -f $(PIPE).check
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(PIPE).vcd $(PIPE).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(PIPE).vcd $(PIPE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(PIPE).vcd $(PIPE).smt2
	touch $@

.PHONY: clean
clean:
	rm -f $(PFONE).smt2   $(PFONE)*.vcd   $(PFONE).yslog
	rm -f $(PFTWO).smt2   $(PFTWO)*.vcd   $(PFTWO).yslog
	rm -f $(PFCACHE).smt2 $(PFCACHE)*.vcd $(PFCACHE).yslog
	rm -f $(WBDLY).smt2   $(WBDLY)*.vcd   $(WBDLY).yslog
	rm -f $(PRIARB).smt2  $(PRIARB)*.vcd  $(PRIARB).yslog
	rm -f $(MEM).smt2     $(MEM)*.vcd     $(MEM).yslog
	rm -f $(PIPE).smt2    $(PIPE)*.vcd    $(PIPE).yslog
	rm -f *.check
