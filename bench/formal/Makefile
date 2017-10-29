################################################################################
##
## Filename:	Makefile
##
## Project:	WBPMIC, wishbone control of a MEMs PMod MIC
##
## Purpose:	To direct the formal verification of the SPI A/DC (and FIFO)
##		sources.
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
################################################################################
##
##
TESTS := prefetch dblfetch pfcache busdelay
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
BMCARGS := --presat $(SOLVER) --unroll
# BMCARGS := $(SOLVER)    --unroll
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

$(PFONE).smt2: $(RTL)/core/$(PFONE).v
	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFTWO).smt2: $(RTL)/core/$(PFTWO).v
	yosys -ql $(PFTWO).yslog -s $(PFTWO).ys

$(PFCACHE).smt2: $(RTL)/core/$(PFCACHE).v
	yosys -ql $(PFCACHE).yslog -s $(PFCACHE).ys

$(WBDLY).smt2: $(RTL)/aux/$(WBDLY).v
	yosys -ql $(WBDLY).yslog -s $(WBDLY).ys

#$(PFONE).smt2: $(RTL)/$(PFONE).v
#	yosys -ql $(PFONE).yslog -s $(PFONE).ys

$(PFONE) : $(PFONE).check
$(PFONE).check: $(PFONE).smt2
	@rm -f $(PFONE).check
	$(SMTBMC) $(BMCARGS) -t 40 --dump-vcd $(PFONEBMC).vcd $(PFONE).smt2
	$(SMTBMC) $(INDARGS) -t 38 --dump-vcd $(PFONEIND).vcd $(PFONE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(PFONEBMC).vcd $(PFONE).smt2
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
	$(SMTBMC)   $(BMCARGS) -t 80 --dump-vcd $(WBDLYBMC).vcd $(WBDLY).smt2
	$(SMTBMC)   $(INDARGS) -t 76 --dump-vcd $(WBDLYIND).vcd $(WBDLY).smt2
	$(SMTBMC) -g $(BMCARGS) -t 80 --dump-vcd $(WBDLYBMC).vcd $(WBDLY).smt2
	touch $@



.PHONY: clean
clean:
	rm -f $(PFONE).smt2 $(PFONEBMC).smt2 $(PFONEIND).smt2 $(PFONE)*.vcd
	rm -f $(PFTWO).smt2 $(PFTWOBMC).smt2 $(PFTWOIND).smt2 $(PFTWO)*.vcd
	rm -f $(PFCACHE).smt2 $(PFCACHEBMC).smt2 $(PFCACHEIND).smt2 $(PFCACHE)*.vcd
	rm -f $(WBDLY).smt2 $(WBDLYBMC).smt2 $(WBDLYIND).smt2 $(WBDLY)*.vcd
	rm -f $(PFONE).yslog $(PFTWO).yslog $(PFCACHE).yslog $(WBDLY).yslog
	rm -f *.check
