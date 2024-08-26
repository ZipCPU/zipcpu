################################################################################
##
## Filename:	sim/zipsw/Makefile
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2016-2024, Gisselquist Technology, LLC
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
################################################################################
##
## }}}
.PHONY: all
PROGRAMS := hello cputest hellostep lockcheck hellosim dmatest stepchk
all:	$(PROGRAMS) hex
#
#
CC	:=zip-gcc
AS	:=zip-as
LD	:=zip-ld
NM	:=zip-nm
OBJDIR	:= obj-zip
RDELF	:= zip-readelf
OBJDUMP := zip-objdump
SUBMAKE:= $(MAKE) --no-print-directory -C
MKHEX := ../verilator/mkhex
#
#
TTTT    := tttt
SOURCES := hello.c sdtest.c cputest.c gpiotoggle.c contest.c # rintftst.c
HEADERS :=
DUMPRTL := -fdump-rtl-all
DUMPTREE:= -fdump-tree-all
LDSCRIPT:= board.ld
LFLAGS  := -T $(LDSCRIPT) -Lzlib
CFLAGS  := -O3 -I. -Izlib
LIBS    := -lc -lziptb -lgcc
INSTALLD=$(shell bash -c "which zip-gcc | sed -e 's/.cross-tools.*$\//'")
NLIBD=$(INSTALLD)/cross-tools/zip/lib
ZLIBD=zlib
LIB=$(ZLIBD)/libziptb.a $(NLIBD)/libg.a $(NLIBD)/libc.a
#
# For source analysis, the following macros are defined:
#

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) $(DUMPRTL) -S $< -o $@
$(OBJDIR)/%.txt: $(OBJDIR)/%.o
	bash -c "$(RDELF) -a $^ ; $(OBJDUMP) -S -D $^ " | tee $@
%.txt: %
	$(OBJDUMP) -S -D $^ > $@


#
# The CPUTest program here is special--it doesn't use the C library.  Hence,
# it must have the -fno-builtin flag in order to build, and the -Tartyram.ld
# linker script to build something that doesn't go into flash but directly into
# RAM instead.
#
$(OBJDIR)/cputest.o: cputest.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-nocis -fno-builtin $< -o $@
$(OBJDIR)/cputestcis.o: cputest.c
	$(CC) $(CFLAGS) -c -Wa,-cis -fno-builtin $< -o $@
$(OBJDIR)/cputest.s: cputest.c
	$(CC) $(CFLAGS) -S -Wa,-cis -fno-builtin $< -o $@

cputest: $(OBJDIR)/cputestcis.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

clkgatechk: $(OBJDIR)/clkgatechk.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

stepchk: $(OBJDIR)/stepchk.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

$(OBJDIR)/contest.o: contest.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -fno-builtin $< -o $@

contest: $(OBJDIR)/contest.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

$(OBJDIR)/hello.o: hello.c
	$(CC) -O3 -c $< -o $@
$(OBJDIR)/rintftst.o: rintftst.c
	$(CC) $(CFLAGS) -O3 -c $< -o $@
$(OBJDIR)/gettysburg.o: gettysburg.c
	$(CC) -O3 -c $< -o $@
$(OBJDIR)/gpiotoggle.o: gpiotoggle.c
#	$(CC) -O3 -c $< -o $@

hello: $(OBJDIR)/hello.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

hellostep: $(OBJDIR)/hellostep.o board.ld $(OBJDIR)/txfns.o $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

lockcheck: $(OBJDIR)/lockcheck.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

dmatest: $(OBJDIR)/dmatest.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

################################################################################
##
## Convert executables to hex
##
.PHONY: hex
hex: cputest.hex cputest64.hex lockcheck.hex lockcheck64.hex
hex: hello.hex hello64.hex hellosim.hex hellosim64.hex
hex: hellostep.hex hellostep64.hex clkgatechk.hex dmatest.hex dmatest64.hex
hex: stepchk.hex stepchk64.hex

cputest.hex: cputest
	$(MKHEX) cputest -o $@

clkgatechk.hex: clkgatechk
	$(MKHEX) clkgatechk -o $@

cputest64.hex: cputest
	$(MKHEX) cputest -w 64 -o $@

lockcheck.hex: lockcheck
	$(MKHEX) lockcheck -o $@

lockcheck64.hex: lockcheck
	$(MKHEX) lockcheck -w 64 -o $@

hello.hex: hello
	$(MKHEX) hello -o $@

hello64.hex: hello
	$(MKHEX) hello -w 64 -o $@

hellosim.hex: hellosim
	$(MKHEX) hellosim -o $@

hellosim64.hex: hellosim
	$(MKHEX) hellosim -w 64 -o $@

hellostep.hex: hellostep
	$(MKHEX) hellostep -o $@

hellostep64.hex: hellostep
	$(MKHEX) hellostep -w 64 -o $@

dmatest.hex: dmatest
	$(MKHEX) dmatest -o $@

dmatest64.hex: dmatest
	$(MKHEX) dmatest -w 64 -o $@

stepchk.hex: stepchk
	$(MKHEX) stepchk -o $@

stepchk64.hex: stepchk
	$(MKHEX) stepchk -w 64 -o $@


.PHONY: iftttt
ifeq (,$(wildcard tttt/))
iftttt:
else
iftttt: 
	$(SUBMAKE) tttt/src ARCH=zip CROSS=zip- zip-tttt
endif

.PHONY: tttt
tttt:
	@bash -c "if [ ! -e $(TTTT)/src/Makefile ]; then git submodule add https://github.com/ZipCPU/tttt; git submodule init; git submodule update; fi"
	CROSS=zip- ARCH=zip $(SUBMAKE) tttt/src ARCH=zip CROSS=zip- zip-tttt


hellosim: hellosim.s
	$(AS) $< -o $(OBJDIR)/hellosim.o
	$(LD) -T board.ld $(OBJDIR)/hellosim.o -o $@


define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"
endef

define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

.PHONY: clean
clean:
	make -C zlib clean
	rm -f $(PROGRAMS) hellosim
	rm -rf $(addsuffix .map,$(PROGRAMS))
	rm -rf $(addsuffix .txt,$(PROGRAMS))
	rm -rf $(wildcard *.hex)
	rm -rf $(OBJDIR)/
ifneq (,$(wildcard tttt/))
	$(SUBMAKE) tttt/src ARCH=zip CROSS=zip- clean
endif

ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
