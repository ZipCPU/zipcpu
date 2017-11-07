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

PFONE=prefetch
PFONEBMC=$(PFONE)_bmc
PFONEIND=$(PFONE)_ind

PFTWO    := dblfetch
PFTWOBMC := $(PFTWO)_bmc
PFTWOIND := $(PFTWO)_ind

PFCACHE    := pfcache
PFCACHEBMC := $(PFCACHE)_bmc
PFCACHEIND := $(PFCACHE)_ind

WBDLY    := busdelay
WBDLYBMC := $(WBDLY)_bmc
WBDLYIND := $(WBDLY)_ind

PRIARB    := wbpriarbiter
PRIARBBMC := $(PRIARB)_bmc
PRIARBIND := $(PRIARB)_ind

MEM    := memops
MEMBMC := $(MEM)_bmc
MEMIND := $(MEM)_ind

MASTER := $(RTL)/aux/formal_master.v
SLAVE  := $(RTL)/aux/formal_slave.v

$(PFONE).smt2: $(RTL)/core/$(PFONE).v $(MASTER)
	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFTWO).smt2: $(RTL)/core/$(PFTWO).v $(MASTER)
	yosys -ql $(PFTWO).yslog -s $(PFTWO).ys

$(PFCACHE).smt2: $(RTL)/core/$(PFCACHE).v $(MASTER)
	yosys -ql $(PFCACHE).yslog -s $(PFCACHE).ys

$(WBDLY).smt2: $(RTL)/aux/$(WBDLY).v $(MASTER) $(SLAVE)
	yosys -ql $(WBDLY).yslog -s $(WBDLY).ys

$(PRIARB).smt2: $(RTL)/aux/$(PRIARB).v $(MASTER) $(SLAVE)
	yosys -ql $(PRIARB).yslog -s $(PRIARB).ys

$(MEM).smt2: $(RTL)/core/$(MEM).v $(MASTER)
	yosys -ql $(MEM).yslog -s $(MEM).ys

#$(PFONE).smt2: $(RTL)/$(PFONE).v
#	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFONE) : $(PFONE).check
$(PFONE).check: $(PFONE).smt2
	@rm -f $(PFONE).check
	$(SMTBMC)    $(BMCARGS) -t 60 --dump-vcd $(PFONEBMC).vcd $(PFONE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 60 --dump-vcd $(PFONEBMC).vcd $(PFONE).smt2
	$(SMTBMC)    $(INDARGS) -t 58 --dump-vcd $(PFONEIND).vcd $(PFONE).smt2
	touch $@


$(PFTWO) : $(PFTWO).check
$(PFTWO).check: $(PFTWO).smt2
	@rm -f $(PFTWO).check
	$(SMTBMC) $(BMCARGS) -t 40 --dump-vcd $(PFTWOBMC).vcd $(PFTWO).smt2
	$(SMTBMC) $(INDARGS) -t 38 --dump-vcd $(PFTWOIND).vcd $(PFTWO).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(PFTWOBMC).vcd $(PFTWO).smt2
	touch $@

$(PFCACHE) : $(PFCACHE).check
$(PFCACHE).check: $(PFCACHE).smt2
	@rm -f $(PFCACHE).check
	$(SMTBMC) $(BMCARGS) -t 80 --dump-vcd $(PFCACHEBMC).vcd $(PFCACHE).smt2
	$(SMTBMC) $(INDARGS) -t 76 --dump-vcd $(PFCACHEIND).vcd $(PFCACHE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 80 --dump-vcd $(PFCACHEBMC).vcd $(PFCACHE).smt2
	touch $@


$(WBDLY) : $(WBDLY).check
$(WBDLY).check: $(WBDLY).smt2
	@rm -f $(PFCACHE).check
	$(SMTBMC)    $(BMCARGS) -t 48 --dump-vcd $(WBDLYBMC).vcd $(WBDLY).smt2
	$(SMTBMC)    $(INDARGS) -t 48 --dump-vcd $(WBDLYIND).vcd $(WBDLY).smt2
	$(SMTBMC) -g $(BMCARGS) -t 46 --dump-vcd $(WBDLYBMC).vcd $(WBDLY).smt2
	touch $@

$(PRIARB) : $(PRIARB).check
$(PRIARB).check: $(PRIARB).smt2
	@rm -f $(PFCACHE).check
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(PRIARBBMC).vcd $(PRIARB).smt2
	$(SMTBMC)    $(INDARGS) -t 16 --dump-vcd $(PRIARBIND).vcd $(PRIARB).smt2
	$(SMTBMC) -g $(BMCARGS) -t 20 --dump-vcd $(PRIARBBMC).vcd $(PRIARB).smt2
	touch $@

$(MEM) : $(MEM).check
$(MEM).check: $(MEM).smt2
	@rm -f $(PFCACHE).check
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(MEMBMC).vcd $(MEM).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(MEMIND).vcd $(MEM).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(MEMBMC).vcd $(MEM).smt2
	touch $@

.PHONY: clean
clean:
	rm -f $(PFONE).smt2   $(PFONE)*.vcd   $(PFONE).yslog
	rm -f $(PFTWO).smt2   $(PFTWO)*.vcd   $(PFTWO).yslog
	rm -f $(PFCACHE).smt2 $(PFCACHE)*.vcd $(PFCACHE).yslog
	rm -f $(WBDLY).smt2   $(WBDLY)*.vcd   $(WBDLY).yslog
	rm -f $(PRIARB).smt2  $(PRIARB)*.vcd  $(PRIARB).yslog
	rm -f $(MEM).smt2     $(MEM)*.vcd     $(MEM).yslog
	rm -f *.check
