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
## Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
TESTS += busdelay wbpriarbiter wbdblpriarb cpuops cpu dcache zipcpu
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
# SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER)
INDARGS := $(SOLVER) -i

PFONE  := prefetch
PFTWO  := dblfetch
PFCACHE:= pfcache
WBDLY  := busdelay
PRIARB := wbpriarbiter
DBL    := wbdblpriarb
PIPE   := pipemem
MEM    := memops
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
DCACHE := dcache
.PHONY: cpu
cpu: zipcpu

MASTER := $(RTL)/ex/fwb_master.v
SLAVE  := $(RTL)/ex/fwb_slave.v

.PHONY: $(PFONE)
$(PFONE) : $(PFONE)/PASS
$(PFONE)/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER)
	sby -f $(PFONE).sby

.PHONY: $(PFTWO)
$(PFTWO) : $(PFTWO)_prf/PASS $(PFTWO)_cvr/PASS
$(PFTWO)_prf/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER)
	sby -f $(PFTWO).sby prf
$(PFTWO)_cvr/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER)
	sby -f $(PFTWO).sby cvr


.PHONY: $(PFCACHE)
$(PFCACHE): $(PFCACHE)_prf/PASS $(PFCACHE)_cvr/PASS
$(PFCACHE)_prf/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER)
	sby -f $(PFCACHE).sby prf
$(PFCACHE)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER)
	sby -f $(PFCACHE).sby cvr

.PHONY: $(WBDLY)
$(WBDLY): $(WBDLY)/PASS
$(WBDLY)/PASS: $(WBDLY).sby $(RTL)/ex/$(WBDLY).v $(MASTER) $(SLAVE)
	sby -f $(WBDLY).sby

.PHONY: $(PRIARB)
$(PRIARB): $(PRIARB)/PASS
$(PRIARB)/PASS: $(PRIARB).sby $(RTL)/ex/$(PRIARB).v $(MASTER) $(SLAVE)
	sby -f $(PRIARB).sby

.PHONY: $(DBL)
$(DBL): $(DBL)/PASS
$(DBL)/PASS: $(DBL).sby $(RTL)/ex/$(DBL).v $(MASTER) $(SLAVE) $(DBL).ys
	sby -f $(DBL).sby

.PHONY: $(MEM)
$(MEM): $(MEM)_cover/PASS $(MEM)_proof/PASS
$(MEM)_proof/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER)
	sby -f $(MEM).sby proof
$(MEM)_cover/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER)
	sby -f $(MEM).sby cover

.PHONY: $(PIPE)
$(PIPE): $(PIPE)_lcl_aligned_lock/PASS
$(PIPE): $(PIPE)_lcl_aligned_nolock/PASS
$(PIPE): $(PIPE)_lcl_noaligned_lock/PASS
$(PIPE): $(PIPE)_lcl_noaligned_nolock/PASS
$(PIPE): $(PIPE)_nolcl_aligned_lock/PASS
$(PIPE): $(PIPE)_nolcl_aligned_nolock/PASS
$(PIPE): $(PIPE)_nolcl_noaligned_lock/PASS
$(PIPE): $(PIPE)_nolcl_noaligned_nolock/PASS
$(PIPE)_lcl_aligned_lock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby lcl_aligned_lock
$(PIPE)_lcl_aligned_nolock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby lcl_aligned_nolock
$(PIPE)_lcl_noaligned_lock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby lcl_noaligned_lock
$(PIPE)_lcl_noaligned_nolock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby lcl_noaligned_nolock
$(PIPE)_nolcl_aligned_lock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby nolcl_aligned_lock
$(PIPE)_nolcl_aligned_nolock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby nolcl_aligned_nolock
$(PIPE)_nolcl_noaligned_lock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby nolcl_noaligned_lock
$(PIPE)_nolcl_noaligned_nolock/PASS: $(PIPE).sby $(RTL)/core/$(PIPE).v $(MASTER)
	sby -f $(PIPE).sby nolcl_noaligned_nolock

.PHONY: $(MMU)
$(MMU): $(MMU)/PASS
$(MMU)/PASS: $(MMU).sby $(RTL)/peripherals/$(MMU).v $(MASTER) $(SLAVE)
	sby -f $(MMU).sby

.PHONY: $(TMR)
$(TMR): $(TMR)/PASS
$(TMR)/PASS: $(TMR).sby $(RTL)/peripherals/$(TMR).v $(SLAVE) $(TMR).ys
	sby -f $(TMR).sby

.PHONY: $(CNT)
$(CNT): $(CNT)/PASS
$(CNT)/PASS: $(CNT).sby $(RTL)/peripherals/$(CNT).v $(SLAVE)
	sby -f $(CNT).sby

.PHONY: $(JIF)
$(JIF): $(JIF)/PASS
$(JIF)/PASS: $(JIF).sby $(RTL)/peripherals/$(JIF).v $(SLAVE)
	sby -f $(JIF).sby

.PHONY: $(WDG)
$(WDG): $(WDG)/PASS
$(WDG)/PASS: $(WDG).sby $(RTL)/peripherals/$(WDG).v $(SLAVE)
	sby -f $(WDG).sby

.PHONY: $(INT)
$(INT): $(INT)_cvr/PASS $(INT)_prf/PASS
$(INT)_prf/PASS: $(INT).sby $(RTL)/peripherals/$(INT).v $(SLAVE)
	sby -f $(INT).sby prf
$(INT)_cvr/PASS: $(INT).sby $(RTL)/peripherals/$(INT).v $(SLAVE)
	sby -f $(INT).sby cvr

.PHONY: $(DCD)
$(DCD): $(DCD)_pipe_div_mpy_cis_opipe/PASS
$(DCD): $(DCD)_pipe_div_mpy_cis_nopipe/PASS
$(DCD): $(DCD)_pipe_div_mpy_nocis_pipe/PASS
$(DCD): $(DCD)_pipe_div_mpy_nocis_nopipe/PASS
$(DCD): $(DCD)_pipe_div_nompy_nocis_nopipe/PASS
$(DCD): $(DCD)_pipe_nodiv_nompy_nocis_nopipe/PASS
$(DCD): $(DCD)_nopipe_nodiv_nompy_nocis_nopipe/PASS

$(DCD)_pipe_div_mpy_cis_opipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby pipe_div_mpy_cis_opipe
$(DCD)_pipe_div_mpy_cis_nopipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby pipe_div_mpy_cis_nopipe
$(DCD)_pipe_div_mpy_nocis_pipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby pipe_div_mpy_nocis_pipe
$(DCD)_pipe_div_mpy_nocis_nopipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby pipe_div_mpy_nocis_nopipe
$(DCD)_pipe_div_nompy_nocis_nopipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby pipe_div_nompy_nocis_nopipe
$(DCD)_pipe_nodiv_nompy_nocis_nopipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby pipe_nodiv_nompy_nocis_nopipe
$(DCD)_nopipe_nodiv_nompy_nocis_nopipe/PASS: $(RTL)/core/$(DCD).v $(DCD).sby f_idecode.v
	sby -f $(DCD).sby nopipe_nodiv_nompy_nocis_nopipe


.PHONY: $(DMA)
$(DMA): $(DMA)/PASS
$(DMA)/PASS: $(RTL)/peripherals/$(DMA).v $(MASTER) $(SLAVE) $(DMA).sby
	sby -f $(DMA).sby

.PHONY: $(ALU)
$(ALU): $(ALU)/PASS
$(ALU)/PASS: $(ALU).sby $(RTL)/core/$(ALU).v abs_mpy.v
	sby -f $(ALU).sby

DCACHE_FILES := $(DCACHE).sby $(RTL)/core/dcache.v $(MASTER) $(RTL)/core/iscachable.v

.PHONY: $(DCACHE)
$(DCACHE) : $(DCACHE)_full/PASS $(DCACHE)_full_single/PASS $(DCACHE)_bare/PASS
$(DCACHE) : $(DCACHE)_nolock_nolocal/PASS $(DCACHE)_nolock_system/PASS
$(DCACHE) : $(DCACHE)_piped/PASS $(DCACHE)_cover/PASS $(DCACHE)_cover_pipe/PASS
$(DCACHE)_full/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby full
$(DCACHE)_full_single/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby full_single

$(DCACHE)_bare/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby bare

$(DCACHE)_nolock_nolocal/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby nolock_nolocal

$(DCACHE)_nolock_system/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby nolock_system

$(DCACHE)_piped/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby piped

$(DCACHE)_cover/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby cover

$(DCACHE)_cover_pipe/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby cover_pipe

.PHONY: $(DIV)
$(DIV) : $(DIV)/PASS
$(DIV)/PASS: $(DIV).sby $(RTL)/core/div.v
	sby -f $(DIV).sby

.PHONY: $(CPU)
$(CPU): $(CPU)_dcache/PASS $(CPU)_piped/PASS
$(CPU): $(CPU)_nopipe/PASS $(CPU)_lowlogic/PASS $(CPU)_ice40/PASS
# $(CPU): $(CPU)_unpipedearly/PASS
CPUDEPS:= $(RTL)/core/$(CPU).v $(RTL)/core/cpuops.v $(RTL)/core/idecode.v \
	$(RTL)/core/pipemem.v $(RTL)/core/memops.v	  \
	$(RTL)/ex/wbdblpriarb.v $(RTL)/ex/fwb_counter.v $(RTL)/cpudefs.v  \
	f_idecode.v abs_div.v abs_prefetch.v abs_mpy.v $(MASTER) $(SLAVE)  \
	$(CPU).sby
$(CPU)_dcache/PASS: $(CPUDEPS) $(RTL)/core/dcache.v $(RTL)/core/iscachable.v
	sby -f $(CPU).sby dcache

$(CPU)_piped/PASS: $(CPUDEPS)
	sby -f $(CPU).sby piped

$(CPU)_unpipedearly/PASS: $(CPUDEPS)
	sby -f $(CPU).sby unpipedearly

$(CPU)_nopipe/PASS: $(CPUDEPS)
	sby -f $(CPU).sby nopipe

$(CPU)_lowlogic/PASS: $(CPUDEPS)
	sby -f $(CPU).sby lowlogic

$(CPU)_ice40/PASS: $(CPUDEPS)
	sby -f $(CPU).sby ice40

.PHONY: clean
clean:
	rm -rf $(PFONE)*/     $(PFTWO)*/      $(PFCACHE)*/
	rm -rf $(WBDLY)*/     $(PRIARB)*/     $(DBL)*/
	rm -rf $(MEM)*/       $(PIPE)*/       $(MMU)*/
	rm -rf $(TMR)*/       $(CNT)*/        $(JIF)*/
	rm -rf $(WDG)*/       $(INT)_*/       $(DCD)_*/
	rm -rf $(DMA)*/       $(ALU)*/        $(DIV)*/
	rm -rf $(DCACHE)_*/
	rm -rf $(CPU)_*/
	rm -f *.check
