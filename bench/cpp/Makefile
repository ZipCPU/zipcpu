################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	To direct and simplify the build of a variety of simple test
#		programs which will use one (or both) of the ZipCPU simulators.
#
# Targets include:
#
#		helloworld
#
#
#
# Creator:	Dan Gisselquist, Ph.D.
#		Gisselquist Technology, LLC
#
################################################################################
#
# Copyright (C) 2017, Gisselquist Technology, LLC
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
# You should have received a copy of the GNU General Public License along
# with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
# target there if the PDF file isn't present.)  If not, see
# <http://www.gnu.org/licenses/> for a copy.
#
# License:	GPL, v3, as defined and found on www.gnu.org,
#		http://www.gnu.org/licenses/gpl.html
#
#
################################################################################
#
.PHONY: all
all: helloworld

CC      := zip-gcc
OBJDUMP := zip-objdump
OBJDIR := obj-zip
CFLAGS := -O3
LIBD   := ../../sw/install/cross-tools/zip/lib
LIBS   := -L$(LIBD) -lzipbasic
SOURCES:= helloworld.c
LDSCRIPT:= ../zipsim.ld

$(OBJDIR)/%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

helloworld: $(OBJDIR)/helloworld.o
	$(CC) -T $(LDSCRIPT) $(CFLAGS) $(LIBD)/crt0.o $(LIBS) $< -o $@

helloworld.txt: helloworld
	$(OBJDUMP) -dr $< > $@

define	build-depends
	$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm -f $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES)
	@ctags $(SOURCES)

.PHONY: depends
depends: tags $(OBJDIR)/
	$(build-depends)

$(OBJDIR)/:
	@bash -c "if [[ ! -e $(OBJDIR) ]]; then mkdir -p $(OBJDIR)/; fi"

.PHONY: clean
clean:
	rm -rf helloworld
