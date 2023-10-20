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
## Copyright (C) 2017-2023, Gisselquist Technology, LLC
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
TESTS := prefetch dblfetch pffifo pfcache memops pipemem idecode div # axiicache
TESTS += axilfetch axilops axilpipe axilperiphs # axiops axipipe # axidcache
TESTS += zipmmu ziptimer zipcounter zipjiffies wbwatchdog icontrol wbdmac
TESTS += busdelay wbpriarbiter wbdblpriarb cpuops cpu dcache zipcore
TESTS += zipbones zipaxil zipaxi
TESTS += txgears rxgears s2mm
.PHONY: $(TESTS)
all: $(TESTS)
RTL := ../../rtl

## Proofs
## {{{
PFONE  := prefetch
PFTWO  := dblfetch
PFFIFO := pffifo
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
AXIPIPE:= axipipe
AXLPH  := axilperiphs
AXIDCC := axidcache

## ZipDMA
MM2S    := zipdma_mm2s
RXGEARS := zipdma_rxgears
TXGEARS := zipdma_txgears
S2MM    := zipdma_s2mm

## CPU Wrappers
BONES  := zipbones
ZAXIL  := zipaxil
ZAXI   := zipaxi

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
$(PFONE) : $(PFONE)_prf/PASS $(PFONE)_prf64b/PASS $(PFONE)_prf128b/PASS
$(PFONE) : $(PFONE)_prf8b/PASS $(PFONE)_prf8ble/PASS
$(PFONE)_prf/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER) $(IFETCH)
	sby -f $(PFONE).sby prf
$(PFONE)_prf8b/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER) $(IFETCH)
	sby -f $(PFONE).sby prf8b
$(PFONE)_prf8ble/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER) $(IFETCH)
	sby -f $(PFONE).sby prf8ble
$(PFONE)_prf64b/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER) $(IFETCH)
	sby -f $(PFONE).sby prf64b
$(PFONE)_prf128b/PASS: $(PFONE).sby $(RTL)/core/$(PFONE).v $(MASTER) $(IFETCH)
	sby -f $(PFONE).sby prf128b
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
$(PFTWO) : $(PFTWO)_prf8b/PASS $(PFTWO)_prf64b/PASS $(PFTWO)_prf128b/PASS
$(PFTWO) : $(PFTWO)_prf8ble/PASS
$(PFTWO)_prf/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby prf
$(PFTWO)_cvr/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby cvr
$(PFTWO)_prf8b/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby prf8b
$(PFTWO)_prf8ble/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby prf8ble
$(PFTWO)_prf64b/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby prf64b
$(PFTWO)_prf128b/PASS: $(PFTWO).sby $(RTL)/core/$(PFTWO).v $(MASTER) $(IFETCH)
	sby -f $(PFTWO).sby prf128b
## }}}

.PHONY: $(PFFIFO)
## {{{
$(PFFIFO) : $(PFFIFO)_prf/PASS $(PFFIFO)_cvr/PASS
$(PFFIFO) : $(PFFIFO)_prf8b/PASS $(PFFIFO)_prf64b/PASS $(PFFIFO)_prf128b/PASS
$(PFFIFO) : $(PFFIFO)_prf8ble/PASS
$(PFFIFO)_prf/PASS: $(PFFIFO).sby $(RTL)/core/$(PFFIFO).v $(MASTER) $(IFETCH)
	sby -f $(PFFIFO).sby prf
$(PFFIFO)_cvr/PASS: $(PFFIFO).sby $(RTL)/core/$(PFFIFO).v $(MASTER) $(IFETCH)
	sby -f $(PFFIFO).sby cvr
$(PFFIFO)_prf8b/PASS: $(PFFIFO).sby $(RTL)/core/$(PFFIFO).v $(MASTER) $(IFETCH)
	sby -f $(PFFIFO).sby prf8b
$(PFFIFO)_prf8ble/PASS:$(PFFIFO).sby $(RTL)/core/$(PFFIFO).v $(MASTER) $(IFETCH)
	sby -f $(PFFIFO).sby prf8ble
$(PFFIFO)_prf64b/PASS: $(PFFIFO).sby $(RTL)/core/$(PFFIFO).v $(MASTER) $(IFETCH)
	sby -f $(PFFIFO).sby prf64b
$(PFFIFO)_prf128b/PASS:$(PFFIFO).sby $(RTL)/core/$(PFFIFO).v $(MASTER) $(IFETCH)
	sby -f $(PFFIFO).sby prf128b
## }}}

.PHONY: $(PFCACHE)
## {{{
$(PFCACHE): $(PFCACHE)_prf/PASS   $(PFCACHE)_cvr/PASS
$(PFCACHE): $(PFCACHE)_prf64/PASS $(PFCACHE)_prf128/PASS
$(PFCACHE)_prf/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER) $(IFETCH)
	sby -f $(PFCACHE).sby prf
$(PFCACHE)_prf64/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER) $(IFETCH)
	sby -f $(PFCACHE).sby prf64
$(PFCACHE)_prf128/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER) $(IFETCH)
	sby -f $(PFCACHE).sby prf128
$(PFCACHE)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(PFCACHE).v $(MASTER) $(IFETCH)
	sby -f $(PFCACHE).sby cvr
## }}}

.PHONY: $(AXIICC)
## {{{
$(AXIICC): $(AXIICC)_prf/PASS  $(AXIICC)_prf64/PASS  $(AXIICC)_cvr/PASS
$(AXIICC): $(AXIICC)_prfw/PASS $(AXIICC)_prfw64/PASS $(AXIICC)_cvrw/PASS
$(AXIICC)_prf/PASS: $(AXIICC).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby prf
$(AXIICC)_prf64/PASS: $(AXIICC).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby prf64
$(AXIICC)_prfw/PASS: $(AXIICC).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby prfw
$(AXIICC)_prfw64/PASS: $(AXIICC).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby prfw64
$(AXIICC)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby cvr
$(AXIICC)_cvrw/PASS: $(PFCACHE).sby $(RTL)/core/$(AXIICC).v $(AXI) $(IFETCH)
	sby -f $(AXIICC).sby cvrw
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
$(MEM): $(MEM)_prf/PASS       $(MEM)_prflp/PASS
$(MEM): $(MEM)_prflck/PASS    $(MEM)_prflcklp/PASS
$(MEM): $(MEM)_prflcklcl/PASS $(MEM)_prflcklplcl/PASS
$(MEM): $(MEM)_prflcl/PASS    $(MEM)_prflplcl/PASS
$(MEM): $(MEM)_prf64/PASS     $(MEM)_prf64lp/PASS
$(MEM): $(MEM)_prf64lcl/PASS  $(MEM)_prf64lplcl/PASS
$(MEM): $(MEM)_prf128/PASS    $(MEM)_prf128lp/PASS
$(MEM): $(MEM)_prf128lcl/PASS $(MEM)_prf128lplcl/PASS
$(MEM): $(MEM)_prf128lck/PASS
$(MEM): $(MEM)_cvr/PASS
$(MEM)_prf/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf
$(MEM)_prflp/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflp
$(MEM)_prf64/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf64
$(MEM)_prf64lp/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf64lp
$(MEM)_prf128/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf128
$(MEM)_prf128lp/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf128lp
$(MEM)_prflck/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflck
$(MEM)_prflcklp/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflcklp
$(MEM)_prf128lck/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf128lck
$(MEM)_prflcklcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflcklcl
$(MEM)_prflcklplcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflcklplcl
$(MEM)_prflcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflcl
$(MEM)_prflplcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prflplcl
$(MEM)_prf64lcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf64lcl
$(MEM)_prf64lplcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf64lplcl
$(MEM)_prf128lcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf128lcl
$(MEM)_prf128lplcl/PASS: $(MEM).sby $(RTL)/core/$(MEM).v $(MASTER) $(FMEM)
	sby -f $(MEM).sby prf128lplcl
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
$(AXIMEM): $(AXIMEM)_prfs/PASS  $(AXIMEM)_prfs64/PASS
$(AXIMEM): $(AXIMEM)_prfsu/PASS $(AXIMEM)_prfsu64/PASS
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
$(AXIMEM)_prfs/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfs
$(AXIMEM)_prfsu/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfsu
$(AXIMEM)_prfs64/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfs64
$(AXIMEM)_prfsu64/PASS: $(AXIMEMDEPS)
	sby -f $(AXIMEM).sby prfsu64
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

.PHONY: $(AXIPIPE)
## {{{
$(AXIPIPE): $(AXIPIPE)_cvr/PASS    $(AXIPIPE)_prf/PASS   $(AXIPIPE)_prfu/PASS
$(AXIPIPE): $(AXIPIPE)_cvr64/PASS  $(AXIPIPE)_prf64/PASS $(AXIPIPE)_prfu64/PASS
$(AXIPIPE): $(AXIPIPE)_prfs/PASS   $(AXIPIPE)_prfsu/PASS
$(AXIPIPE): $(AXIPIPE)_prfs64/PASS $(AXIPIPE)_prfsu64/PASS
$(AXIPIPE): $(AXIPIPE)_cvru/PASS
$(AXIPIPE)_prf/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prf
$(AXIPIPE)_prf64/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prf64
$(AXIPIPE)_prfu/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prfu
$(AXIPIPE)_prfu64/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prfu64
$(AXIPIPE)_prfs/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prfs
$(AXIPIPE)_prfs64/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prfs64
$(AXIPIPE)_prfsu/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prfsu
$(AXIPIPE)_prfsu64/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby prfsu64
$(AXIPIPE)_cvr/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby cvr
$(AXIPIPE)_cvru/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby cvru
$(AXIPIPE)_cvr64/PASS: $(AXIPIPE).sby $(RTL)/core/$(AXIPIPE).v $(AXI) $(FMEM)
	sby -f $(AXIPIPE).sby cvr64
## }}}

.PHONY: $(WBPIPE)
## {{{
$(WBPIPE): $(WBPIPE)_prf/PASS
$(WBPIPE): $(WBPIPE)_prflck/PASS
$(WBPIPE): $(WBPIPE)_prflcl/PASS
$(WBPIPE): $(WBPIPE)_prflcllck/PASS
$(WBPIPE): $(WBPIPE)_lcl_noaligned_lock/PASS
$(WBPIPE): $(WBPIPE)_lcl_noaligned_nolock/PASS
$(WBPIPE): $(WBPIPE)_nolcl_noaligned_lock/PASS
$(WBPIPE): $(WBPIPE)_nolcl_noaligned_nolock/PASS
$(WBPIPE): $(WBPIPE)_prf64/PASS $(WBPIPE)_prf128/PASS
PIPEDEPS := $(WBPIPE).sby $(RTL)/core/$(WBPIPE).v $(MASTER) $(FMEM)
$(WBPIPE)_prf/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby prf
$(WBPIPE)_prflck/PASS:     $(PIPEDEPS)
	sby -f $(WBPIPE).sby prflck
$(WBPIPE)_prflcl/PASS:     $(PIPEDEPS)
	sby -f $(WBPIPE).sby prflcl
$(WBPIPE)_prflcllck/PASS:       $(PIPEDEPS)
	sby -f $(WBPIPE).sby prflcllck
$(WBPIPE)_lcl_noaligned_lock/PASS:     $(PIPEDEPS)
	sby -f $(WBPIPE).sby lcl_noaligned_lock
$(WBPIPE)_lcl_noaligned_nolock/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby lcl_noaligned_nolock
$(WBPIPE)_nolcl_noaligned_lock/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby nolcl_noaligned_lock
$(WBPIPE)_nolcl_noaligned_nolock/PASS: $(PIPEDEPS)
	sby -f $(WBPIPE).sby nolcl_noaligned_nolock
$(WBPIPE)_prf64/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby prf64
$(WBPIPE)_prf128/PASS:   $(PIPEDEPS)
	sby -f $(WBPIPE).sby prf128
## }}}

.PHONY: $(AXIDCC)
## {{{
$(AXIDCC): $(AXIDCC)_prf/PASS      $(AXIDCC)_prf64/PASS   $(AXIDCC)_cvr/PASS
$(AXIDCC): $(AXIDCC)_prflp/PASS    $(AXIDCC)_prflk/PASS   $(AXIDCC)_prflplk/PASS
$(AXIDCC): $(AXIDCC)_prf64lk/PASS
## Swap
$(AXIDCC): $(AXIDCC)_prfs/PASS     $(AXIDCC)_prfs64/PASS
$(AXIDCC): $(AXIDCC)_prfsw/PASS    $(AXIDCC)_prfs64w/PASS
## Pipelined
$(AXIDCC): $(AXIDCC)_prfp/PASS     $(AXIDCC)_prf64p/PASS  $(AXIDCC)_cvrp/PASS
$(AXIDCC): $(AXIDCC)_prfplk/PASS   $(AXIDCC)_prfplp/PASS
$(AXIDCC): $(AXIDCC)_prfsp/PASS    $(AXIDCC)_prfs64p/PASS
$(AXIDCC): $(AXIDCC)_prfspw/PASS   $(AXIDCC)_prfs64pw/PASS
$(AXIDCC): $(AXIDCC)_prfspwlk/PASS $(AXIDCC)_prfs64pwlk/PASS
$(AXIDCC)_prf/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prf
$(AXIDCC)_prf64/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prf64
$(AXIDCC)_prflp/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prflp
$(AXIDCC)_prflk/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prflk
$(AXIDCC)_prflplk/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prflplk
$(AXIDCC)_prf64lk/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prf64lk
$(AXIDCC)_prfs/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfs
$(AXIDCC)_prfs64/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfs64
$(AXIDCC)_prfsw/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfsw
$(AXIDCC)_prfs64w/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfs64w
$(AXIDCC)_cvr/PASS: $(PFCACHE).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby cvr
## Pipelined
$(AXIDCC)_prfp/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfp
$(AXIDCC)_prf64p/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prf64p
$(AXIDCC)_prfplk/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfplk
$(AXIDCC)_prfplp/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfplp
$(AXIDCC)_prfsp/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfsp
$(AXIDCC)_prfs64p/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfs64p
$(AXIDCC)_prfspw/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfspw
$(AXIDCC)_prfs64pw/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfs64pw
$(AXIDCC)_prfspwlk/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfspwlk
$(AXIDCC)_prfs64pwlk/PASS: $(AXIDCC).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby prfs64pwlk
$(AXIDCC)_cvrp/PASS: $(PFCACHE).sby $(RTL)/core/$(AXIDCC).v $(AXI) $(FMEM)
	sby -f $(AXIDCC).sby cvrp
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
$(WBDMA): $(WBDMA)_prf/PASS $(WBDMA)_prf64/PASS $(WBDMA)_prf128/PASS
$(WBDMA)_prf/PASS: $(WBDMA).sby $(RTL)/peripherals/$(WBDMA).v $(MASTER) $(SLAVE)
	sby -f $(WBDMA).sby prf
$(WBDMA)_prf64/PASS: $(WBDMA).sby $(RTL)/peripherals/$(WBDMA).v $(MASTER) $(SLAVE)
	sby -f $(WBDMA).sby prf64
$(WBDMA)_prf128/PASS: $(WBDMA).sby $(RTL)/peripherals/$(WBDMA).v $(MASTER) $(SLAVE)
	sby -f $(WBDMA).sby prf128
## }}}

.PHONY: $(AXLPH)
## {{{
$(AXLPH): $(AXLPH)_prf/PASS
$(AXLPH)_prf/PASS: $(AXLPH).sby $(RTL)/peripherals/$(AXLPH).v $(SLAVE) $(RTL)/ex/sfifo.v $(RTL)/ex/skidbuffer.v
	sby -f $(AXLPH).sby prf
## }}}
## }}}

## ZipDMA
## {{{

.PHONY: mm2s $(MM2S)
## {{{
mm2s: $(MM2S)
$(MM2S): $(MM2S)_prf/PASS
$(MM2S)_prf/PASS: $(MM2S).sby $(RTL)/zipdma/$(MM2S).v $(MASTER)
	sby $(MM2S).sby prf
$(MM2S)_cvr/PASS: $(MM2S).sby $(RTL)/zipdma/$(MM2S).v $(MASTER)
	sby $(MM2S).sby cvr
## }}}

.PHONY: rxgears $(RXGEARS)
## {{{
rxgears: $(RXGEARS)
$(RXGEARS): $(RXGEARS)_prf/PASS $(RXGEARS)_prfw/PASS
$(RXGEARS): $(RXGEARS)_cvr/PASS
$(RXGEARS)_prf/PASS: $(RXGEARS).sby $(RTL)/zipdma/$(RXGEARS).v
	sby -f $(RXGEARS).sby prf
$(RXGEARS)_prfw/PASS: $(RXGEARS).sby $(RTL)/zipdma/$(RXGEARS).v
	sby -f $(RXGEARS).sby prfw
$(RXGEARS)_cvr/PASS: $(RXGEARS).sby $(RTL)/zipdma/$(RXGEARS).v
	sby -f $(RXGEARS).sby cvr
## }}}

.PHONY: txgears $(TXGEARS)
## {{{
txgears: $(TXGEARS)
$(TXGEARS): $(TXGEARS)_prf/PASS $(TXGEARS)_prfw/PASS
$(TXGEARS): $(TXGEARS)_cvr/PASS $(TXGEARS)_cvrw/PASS
$(TXGEARS)_prf/PASS: $(TXGEARS).sby $(RTL)/zipdma/$(TXGEARS).v
	sby -f $(TXGEARS).sby prf
$(TXGEARS)_prfw/PASS: $(TXGEARS).sby $(RTL)/zipdma/$(TXGEARS).v
	sby -f $(TXGEARS).sby prfw
$(TXGEARS)_cvr/PASS: $(TXGEARS).sby $(RTL)/zipdma/$(TXGEARS).v
	sby -f $(TXGEARS).sby cvr
$(TXGEARS)_cvrw/PASS: $(TXGEARS).sby $(RTL)/zipdma/$(TXGEARS).v
	sby -f $(TXGEARS).sby cvrw
## }}}

.PHONY: s2mm $(S2MM)
## {{{
s2mm: $(S2MM)
$(S2MM): $(S2MM)_prf/PASS $(S2MM)_cvr/PASS
$(S2MM)_prf/PASS: $(S2MM).sby $(RTL)/zipdma/$(S2MM).v $(MASTER)
	sby -f $(S2MM).sby prf
$(S2MM)_cvr/PASS: $(S2MM).sby $(RTL)/zipdma/$(S2MM).v $(MASTER)
	sby -f $(S2MM).sby cvr
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
$(DCACHE) : $(DCACHE)_piped/PASS  $(DCACHE)_cover/PASS $(DCACHE)_cover_pipe/PASS
$(DCACHE) : $(DCACHE)_prf64/PASS  $(DCACHE)_prf64lp/PASS
$(DCACHE) : $(DCACHE)_prf128/PASS $(DCACHE)_prf128lp/PASS
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

$(DCACHE)_prf64/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby prf64
$(DCACHE)_prf64lp/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby prf64lp

$(DCACHE)_prf128/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby prf128
$(DCACHE)_prf128lp/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby prf128lp

$(DCACHE)_cover/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby cover

$(DCACHE)_cover_pipe/PASS: $(DCACHE_FILES)
	sby -f $(DCACHE).sby cover_pipe
## }}}

.PHONY: $(DIV)
## {{{
$(DIV) : $(DIV)_prf/PASS
$(DIV) : $(DIV)_prflp/PASS
$(DIV)_prf/PASS: $(DIV).sby $(RTL)/core/div.v
	sby -f $(DIV).sby prf
$(DIV)_prflp/PASS: $(DIV).sby $(RTL)/core/div.v
	sby -f $(DIV).sby prflp
## }}}

.PHONY: $(CPU)
## {{{
$(CPU): $(CPU)_piped/PASS     $(CPU)_nopipe/PASS
$(CPU): $(CPU)_lowlogic/PASS  $(CPU)_ice40/PASS $(CPU)_pipedbk/PASS
$(CPU): $(CPU)_pipedlp/PASS   $(CPU)_lowlogiclp/PASS   $(CPU)_nopipelp/PASS
$(CPU): $(CPU)_pipedlpck/PASS $(CPU)_lowlogiclpck/PASS
$(CPU): $(CPU)_pipedckh/PASS  $(CPU)_lowlogiclpckh/PASS
$(CPU): $(CPU)_pipedlpckh/PASS
$(CPU): $(CPU)_cvr/PASS
CPUDEPS:= $(CPU).sby $(RTL)/core/$(CPU).v $(RTL)/core/cpuops.v		\
	$(RTL)/core/idecode.v $(RTL)/ex/wbdblpriarb.v			\
	$(RTL)/ex/fwb_counter.v						\
	f_idecode.v abs_div.v abs_mpy.v $(MASTER) $(SLAVE)		\
	$(FMEM) $(IFETCH) $(FDBG)

$(CPU)_piped/PASS: $(CPUDEPS)
	sby -f $(CPU).sby piped
$(CPU)_nopipe/PASS: $(CPUDEPS)
	sby -f $(CPU).sby nopipe
$(CPU)_pipedbk/PASS: $(CPUDEPS)
	sby -f $(CPU).sby pipedbk
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
$(CPU)_pipedckh/PASS: $(CPUDEPS)
	sby -f $(CPU).sby pipedckh
$(CPU)_pipedlpck/PASS: $(CPUDEPS)
	sby -f $(CPU).sby pipedlpck
$(CPU)_pipedlpckh/PASS: $(CPUDEPS)
	sby -f $(CPU).sby pipedlpckh
$(CPU)_lowlogiclpck/PASS: $(CPUDEPS)
	sby -f $(CPU).sby lowlogiclpck
$(CPU)_lowlogiclpckh/PASS: $(CPUDEPS)
	sby -f $(CPU).sby lowlogiclpckh
$(CPU)_cvr/PASS: $(CPUDEPS)
	sby -f $(CPU).sby cvr
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

.PHONY: $(ZAXI)
## {{{
$(ZAXI): $(ZAXI)_prf/PASS
$(ZAXI)_prf/PASS: $(ZAXI).sby $(RTL)/$(ZAXI).v $(FDBG) $(AXIL) $(RTL)/ex/skidbuffer.v
	sby -f $(ZAXI).sby prf
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

.PHONY: report
report:
	+perl genreport.pl > report.html

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
