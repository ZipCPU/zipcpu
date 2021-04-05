################################################################################
##
## Filename:	Makefile
## {{{
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
## }}}
## Copyright (C) 2017-2020, Gisselquist Technology, LLC
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
TESTS := prefetch dblfetch pfcache memops pipemem idecode div axiicache
TESTS += axilfetch axilops axilpipe axilperiphs axiops axidcache
TESTS += zipmmu ziptimer zipcounter zipjiffies wbwatchdog icontrol wbdmac
TESTS += busdelay wbpriarbiter wbdblpriarb cpuops cpu dcache zipcore
TESTS += zipbones zipaxil
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

## Proofs
## {{{
PFONE  := prefetch
PFTWO  := dblfetch
PFCACHE:= pfcache
WBDLY  := busdelay
PRIARB := wbpriarbiter
DBL    := wbdblpriarb
WBPIPE := pipemem
MEM    := memops
TMR    := ziptimer
CNT    := zipcounter
JIF    := zipjiffies
WDG    := wbwatchdog
INT    := icontrol
DCD    := idecode
WBDMA  := wbdmac
ALU    := cpuops
DIV    := div
CPU    := zipcore
DCACHE := dcache

AXILPF := axilfetch
AXIICC := axiicache
AXILMEM:= axilops
AXIMEM := axiops
AXLPIPE:= axilpipe
AXLPH  := axilperiphs
AXIDCC := axidcache

## CPU Wrappers
BONES  := zipbones
ZAXIL  := zipaxil

MMU    := zipmmu
## }}}

.PHONY: cpu
cpu: zipcore

## Interfaces
## {{{
MASTER := $(RTL)/ex/fwb_master.v
SLAVE  := $(RTL)/ex/fwb_slave.v
FMEM   := fmem.v
IFETCH := ffetch.v
FDBG   := fdebug.v
AXIL   := faxil_master.v faxil_slave.v
AXI    := faxi_master.v faxi_slave.v faxi_valaddr.v faxi_wstrb.v faxi_addr.v
## }}}

## Macro names
## {{{
.PHONY: fmem ffetch
ffetch: prefetch dblfetch pfcache axilfetch axiicache
fmem:   memops pipemem dcache axilops axiops axidcache
## }}}

## Instruction fetch routines
## {{{
.PHONY: $(PFONE)
## {{{
$(PFONE) : $(PFONE)_prf/PASS
$(PFONE)_prf/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER) $(IFETCH)
	sby -f $(PFONE).sby prf
## }}}

.PHONY: $(AXILPF)
## {{{
$(AXILPF) : $(AXILPF)_prf/PASS      $(AXILPF)_cvr/PASS
$(AXILPF) : $(AXILPF)_prfdbl/PASS   $(AXILPF)_cvrdbl/PASS
$(AXILPF) : $(AXILPF)_prff/PASS     $(AXILPF)_cvrf/PASS
$(AXILPF) : $(AXILPF)_prf64/PASS    $(AXILPF)_cvr64/PASS
$(AXILPF) : $(AXILPF)_prfdbl64/PASS $(AXILPF)_cvrdbl64/PASS
$(AXILPF) : $(AXILPF)_prff64/PASS   $(AXILPF)_cvrf64/PASS
AXILPFDEPS := $(AXILPF).sby $(RTL)/core/$(AXILPF).v $(AXIL) $(IFETCH) $(RTL)/ex/sfifo.v
$(AXILPF)_prf/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby prf
$(AXILPF)_cvr/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby cvr
$(AXILPF)_prfdbl/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby prfdbl
$(AXILPF)_cvrdbl/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby cvrdbl
$(AXILPF)_prff/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby prff
$(AXILPF)_cvrf/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby cvrf
$(AXILPF)_prf64/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby prf64
$(AXILPF)_cvr64/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby cvr64
$(AXILPF)_prfdbl64/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby prfdbl64
$(AXILPF)_cvrdbl64/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby cvrdbl64
$(AXILPF)_prff64/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby prff64
$(AXILPF)_cvrf64/PASS: $(AXILPFDEPS)
	sby -f $(AXILPF).sby cvrf64
## }}}

.PHONY: $(PFTWO)
## {{{
$(PFTWO) : $(PFTWO)_prf/PASS $(PFTWO)_cvr/PASS
$(PFTWO)_prf/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby prf
$(PFTWO)_cvr/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby cvr
## }}}

.PHONY: $(PFCACHE)
## {{{
$(PFCACHE): $(PFCACHE)_prf/PASS $(PFCACHE)_cvr/PASS
$(PFCACHE)_prf/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER) $(IFETCH)
	sby -f $(PFCACHE).sby prf
$(PFCACHE)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER) $(IFETCH)
	sby -f $(PFCACHE).sby cvr
## }}}

.PHONY: $(AXIICC)
## {{{
$(AXIICC): $(AXIICC)_prf/PASS $(AXIICC)_prf64/PASS $(AXIICC)_cvr/PASS
$(AXIICC)_prf/PASS: $(AXIICC).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby prf
$(AXIICC)_prf64/PASS: $(AXIICC).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby prf64
$(AXIICC)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby cvr
## }}}
## }}}

## Data units
## {{{
.PHONY: $(DBL)
## {{{
$(DBL): $(DBL)_prf/PASS
$(DBL)_prf/PASS: $(DBL).sby $(RTL)/ex/$(DBL).v $(MASTER) $(SLAVE) $(DBL).ys
	sby -f $(DBL).sby prf
## }}}

.PHONY: $(MEM)
## {{{
$(MEM): $(MEM)_cvr/PASS $(MEM)_prf/PASS
$(MEM)_prf/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf
$(MEM)_cvr/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby cvr
## }}}

.PHONY: $(AXILMEM)
## {{{
$(AXILMEM): $(AXILMEM)_cvr/PASS     $(AXILMEM)_prf/PASS   $(AXILMEM)_prfu/PASS
$(AXILMEM): $(AXILMEM)_cvr64/PASS   $(AXILMEM)_prf64/PASS $(AXILMEM)_prfu64/PASS
$(AXILMEM): $(AXILMEM)_prflp/PASS   $(AXILMEM)_prfulp/PASS
$(AXILMEM): $(AXILMEM)_prf64lp/PASS $(AXILMEM)_prfu64lp/PASS
AXILMEMDEPS:= $(AXILMEM).sby $(RTL)/core/$(AXILMEM).v $(AXIL) $(FMEM)
$(AXILMEM)_prf/PASS:      $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prf
$(AXILMEM)_prfu/PASS:     $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prfu
$(AXILMEM)_prf64/PASS:    $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prf64
$(AXILMEM)_prfu64/PASS:   $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prfu64
$(AXILMEM)_prflp/PASS:    $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prflp
$(AXILMEM)_prfulp/PASS:   $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prfulp
$(AXILMEM)_prf64lp/PASS:  $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prf64lp
$(AXILMEM)_prfu64lp/PASS: $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby prfu64lp

$(AXILMEM)_cvr/PASS: $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby cvr
$(AXILMEM)_cvr64/PASS: $(AXILMEMDEPS)
	sby -f $(AXILMEM).sby cvr64
## }}}

.PHONY: $(AXIMEM)
## {{{
$(AXIMEM): $(AXIMEM)_cvr/PASS   $(AXIMEM)_prf/PASS   $(AXIMEM)_prfu/PASS
$(AXIMEM): $(AXIMEM)_cvr64/PASS $(AXIMEM)_prf64/PASS $(AXIMEM)_prfu64/PASS
$(AXIMEM): $(AXIMEM)_prflp/PASS   $(AXIMEM)_prfulp/PASS
$(AXIMEM): $(AXIMEM)_prf64lp/PASS $(AXIMEM)_prfu64lp/PASS
AXIMEMDEPS:= $(AXIMEM).sby $(RTL)/core/$(AXIMEM).v $(AXI) $(FMEM)
$(AXIMEM)_prf/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prf
$(AXIMEM)_prfu/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfu
$(AXIMEM)_prf64/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prf64
$(AXIMEM)_prfu64/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfu64
$(AXIMEM)_prflp/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prflp
$(AXIMEM)_prfulp/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfulp
$(AXIMEM)_prf64lp/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prf64lp
$(AXIMEM)_prfu64lp/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfu64lp

$(AXIMEM)_cvr/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby cvr
$(AXIMEM)_cvr64/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby cvr64

## }}}

.PHONY: $(AXLPIPE)
## {{{
$(AXLPIPE): $(AXLPIPE)_cvr/PASS   $(AXLPIPE)_prf/PASS   $(AXLPIPE)_prfu/PASS
$(AXLPIPE): $(AXLPIPE)_cvr64/PASS $(AXLPIPE)_prf64/PASS $(AXLPIPE)_prfu64/PASS
$(AXLPIPE): $(AXLPIPE)_cvru/PASS
$(AXLPIPE)_prf/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby prf
$(AXLPIPE)_prf64/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby prf64
$(AXLPIPE)_prfu/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby prfu
$(AXLPIPE)_prfu64/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby prfu64
$(AXLPIPE)_cvr/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby cvr
$(AXLPIPE)_cvru/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby cvru
$(AXLPIPE)_cvr64/PASS: $(AXLPIPE).sby $(RTL)/core/$(AXLPIPE).v $(AXIL) $(FMEM)
	sby -f $(AXLPIPE).sby cvr64
## }}}

.PHONY: $(WBPIPE)
## {{{
$(WBPIPE): $(WBPIPE)_lcl_aligned_lock/PASS
$(WBPIPE): $(WBPIPE)_lcl_aligned_nolock/PASS
$(WBPIPE): $(WBPIPE)_lcl_noaligned_lock/PASS
$(WBPIPE): $(WBPIPE)_lcl_noaligned_nolock/PASS
$(WBPIPE): $(WBPIPE)_nolcl_aligned_lock/PASS
$(WBPIPE): $(WBPIPE)_nolcl_aligned_nolock/PASS
$(WBPIPE): $(WBPIPE)_nolcl_noaligned_lock/PASS
$(WBPIPE): $(WBPIPE)_nolcl_noaligned_nolock/PASS
PIPEDEPS := $(WBPIPE).sby $(RTL)/core/$(WBPIPE).v $(MASTER) $(FMEM)
$(WBPIPE)_lcl_aligned_lock/PASS:       $(PIPEDEPS)
	sby -f $(WBPIPE).sby lcl_aligned_lock
$(WBPIPE)_lcl_aligned_nolock/PASS:     $(PIPEDEPS)
	sby -f $(WBPIPE).sby lcl_aligned_nolock
$(WBPIPE)_lcl_noaligned_lock/PASS:     $(PIPEDEPS)
	sby -f $(WBPIPE).sby lcl_noaligned_lock
$(WBPIPE)_lcl_noaligned_nolock/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby lcl_noaligned_nolock
$(WBPIPE)_nolcl_aligned_lock/PASS:     $(PIPEDEPS)
	sby -f $(WBPIPE).sby nolcl_aligned_lock
$(WBPIPE)_nolcl_aligned_nolock/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby nolcl_aligned_nolock
$(WBPIPE)_nolcl_noaligned_lock/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby nolcl_noaligned_lock
$(WBPIPE)_nolcl_noaligned_nolock/PASS: $(PIPEDEPS)
	sby -f $(WBPIPE).sby nolcl_noaligned_nolock
## }}}

.PHONY: $(AXIDCC)
## {{{
$(AXIDCC): $(AXIDCC)_prf/PASS $(AXIDCC)_prf64/PASS $(AXIDCC)_cvr/PASS
$(AXIDCC)_prf/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prf
$(AXIDCC)_prf64/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prf64
$(AXIDCC)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby cvr
## }}}
## }}}

## Peripherals
## {{{
.PHONY: $(TMR)
## {{{
$(TMR): $(TMR)_prf/PASS $(TMR)_prfr/PASS
$(TMR)_prf/PASS: $(TMR).sby $(RTL)/peripherals/$(TMR).v $(SLAVE) $(TMR).ys
	sby -f $(TMR).sby prf
$(TMR)_prfr/PASS: $(TMR).sby $(RTL)/peripherals/$(TMR).v $(SLAVE) $(TMR).ys
	sby -f $(TMR).sby prfr
## }}}

.PHONY: $(CNT)
## {{{
$(CNT): $(CNT)_prf/PASS
$(CNT)_prf/PASS: $(CNT).sby $(RTL)/peripherals/$(CNT).v $(SLAVE)
	sby -f $(CNT).sby prf
## }}}

.PHONY: $(JIF)
## {{{
$(JIF): $(JIF)_prf/PASS
$(JIF)_prf/PASS: $(JIF).sby $(RTL)/peripherals/$(JIF).v $(SLAVE)
	sby -f $(JIF).sby prf
## }}}

.PHONY: $(WDG)
## {{{
$(WDG): $(WDG)_prf/PASS
$(WDG)_prf/PASS: $(WDG).sby $(RTL)/peripherals/$(WDG).v $(SLAVE)
	sby -f $(WDG).sby prf
## }}}

.PHONY: $(INT)
## {{{
$(INT): $(INT)_cvr/PASS $(INT)_prf/PASS
$(INT)_prf/PASS: $(INT).sby $(RTL)/peripherals/$(INT).v $(SLAVE)
	sby -f $(INT).sby prf
$(INT)_cvr/PASS: $(INT).sby $(RTL)/peripherals/$(INT).v $(SLAVE)
	sby -f $(INT).sby cvr
## }}}

.PHONY: $(DCD)
## {{{
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
## }}}

.PHONY: $(WBDMA)
## {{{
$(WBDMA): $(WBDMA)_prf/PASS
$(WBDMA)_prf/PASS: $(WBDMA).sby $(RTL)/peripherals/$(WBDMA).v $(MASTER) $(SLAVE)
	sby -f $(WBDMA).sby prf
## }}}

.PHONY: $(AXLPH)
## {{{
$(AXLPH): $(AXLPH)_prf/PASS
$(AXLPH)_prf/PASS: $(AXLPH).sby $(RTL)/peripherals/$(AXLPH).v $(SLAVE) $(RTL)/ex/sfifo.v $(RTL)/ex/skidbuffer.v
	sby -f $(AXLPH).sby prf
## }}}
## }}}

## ZipCPU core components
## {{{
.PHONY: $(ALU)
## {{{
$(ALU): $(ALU)_prf/PASS
$(ALU)_prf/PASS: $(ALU).sby $(RTL)/core/$(ALU).v abs_mpy.v
	sby -f $(ALU).sby prf
## }}}

.PHONY: $(DCACHE)
## {{{
DCACHE_FILES := $(DCACHE).sby $(RTL)/core/dcache.v $(MASTER) $(FMEM) $(RTL)/core/iscachable.v

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
## }}}

.PHONY: $(DIV)
## {{{
$(DIV) : $(DIV)_prf/PASS
$(DIV)_prf/PASS: $(DIV).sby $(RTL)/core/div.v
	sby -f $(DIV).sby prf
## }}}

.PHONY: $(CPU)
## {{{
$(CPU): $(CPU)_piped/PASS     $(CPU)_nopipe/PASS
$(CPU): $(CPU)_lowlogic/PASS  $(CPU)_ice40/PASS
$(CPU): $(CPU)_pipedlp/PASS   $(CPU)_lowlogiclp/PASS   $(CPU)_nopipelp/PASS
$(CPU): $(CPU)_pipedlpck/PASS $(CPU)_lowlogiclpck/PASS
CPUDEPS:= $(CPU).sby $(RTL)/core/$(CPU).v $(RTL)/core/cpuops.v		\
	$(RTL)/core/idecode.v $(RTL)/ex/wbdblpriarb.v			\
	$(RTL)/ex/fwb_counter.v $(RTL)/cpudefs.v			\
	f_idecode.v abs_div.v abs_mpy.v $(MASTER) $(SLAVE)		\
	$(FMEM) $(IFETCH) $(FDBG)

$(CPU)_piped/PASS: $(CPUDEPS)
	sby -f $(CPU).sby piped
$(CPU)_nopipe/PASS: $(CPUDEPS)
	sby -f $(CPU).sby nopipe
$(CPU)_lowlogic/PASS: $(CPUDEPS)
	sby -f $(CPU).sby lowlogic
$(CPU)_ice40/PASS: $(CPUDEPS)
	sby -f $(CPU).sby ice40
$(CPU)_pipedlp/PASS: $(CPUDEPS)
	sby -f $(CPU).sby pipedlp
$(CPU)_nopipelp/PASS: $(CPUDEPS)
	sby -f $(CPU).sby nopipelp
$(CPU)_lowlogiclp/PASS: $(CPUDEPS)
	sby -f $(CPU).sby lowlogiclp
$(CPU)_pipedlpck/PASS: $(CPUDEPS)
	sby -f $(CPU).sby pipedlpck
$(CPU)_lowlogiclpck/PASS: $(CPUDEPS)
	sby -f $(CPU).sby lowlogiclpck
## }}}
## }}}

## ZipCPU wrappers
## {{{
.PHONY: $(BONES)
## {{{
$(BONES): $(BONES)_prf/PASS
$(BONES)_prf/PASS: $(BONES).sby $(RTL)/$(BONES).v $(FDBG) $(SLAVE)
	sby -f $(BONES).sby prf
## }}}

.PHONY: $(ZAXIL)
## {{{
$(ZAXIL): $(ZAXIL)_prf/PASS
$(ZAXIL)_prf/PASS: $(ZAXIL).sby $(RTL)/$(ZAXIL).v $(FDBG) $(AXIL) $(RTL)/ex/skidbuffer.v
	sby -f $(ZAXIL).sby prf
## }}}
## }}}

## Other
## {{{
.PHONY: $(MMU)
## {{{
$(MMU): $(MMU)_prf/PASS
$(MMU)_prf/PASS: $(MMU).sby $(RTL)/peripherals/$(MMU).v $(MASTER) $(SLAVE)
	sby -f $(MMU).sby prf
## }}}

.PHONY: $(WBDLY)
## {{{
$(WBDLY): $(WBDLY)_prf/PASS   $(WBDLY)_prfd/PASS
$(WBDLY): $(WBDLY)_prflp/PASS $(WBDLY)_prfdlp/PASS
$(WBDLY)_prf/PASS: $(WBDLY).sby $(RTL)/ex/$(WBDLY).v $(MASTER) $(SLAVE)
	sby -f $(WBDLY).sby prf
$(WBDLY)_prfd/PASS: $(WBDLY).sby $(RTL)/ex/$(WBDLY).v $(MASTER) $(SLAVE)
	sby -f $(WBDLY).sby prfd
$(WBDLY)_prflp/PASS: $(WBDLY).sby $(RTL)/ex/$(WBDLY).v $(MASTER) $(SLAVE)
	sby -f $(WBDLY).sby prflp
$(WBDLY)_prfdlp/PASS: $(WBDLY).sby $(RTL)/ex/$(WBDLY).v $(MASTER) $(SLAVE)
	sby -f $(WBDLY).sby prfdlp
## }}}

.PHONY: $(PRIARB)
## {{{
$(PRIARB): $(PRIARB)_prf/PASS
$(PRIARB)_prf/PASS: $(PRIARB).sby $(RTL)/ex/$(PRIARB).v $(MASTER) $(SLAVE)
	sby -f $(PRIARB).sby prf
## }}}

## }}}

.PHONY: clean
## {{{
clean:
	rm -rf $(PFONE)_*/    $(PFTWO)_*/     $(PFCACHE)_*/
	rm -rf $(WBDLY)*/     $(PRIARB)*/     $(DBL)*/
	rm -rf $(MEM)_*/      $(PIPE)*/       $(MMU)*/
	rm -rf $(TMR)*/       $(CNT)*/        $(JIF)*/
	rm -rf $(WDG)*/       $(INT)_*/       $(DCD)_*/
	rm -rf $(DMA)_*/      $(ALU)*/        $(DIV)*/
	rm -rf $(DCACHE)_*/
	rm -rf $(CPU)_*/
	rm -rf $(AXILPF)_*/   $(AXILMEM)_*/   $(AXIICC)_*/
	rm -f *.check
## }}}
