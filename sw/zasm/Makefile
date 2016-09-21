################################################################################
#
# Filename:	Makefile
#
# Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
#
# Purpose:	This makefile builds an assembler preprocessor (zpp), an
#		assembler (zasm) and a disassembler (zdump).  Make with no
#		arguments will produce these files.  Other targets include:
#
#	make clean
#	make test
#		Assembles a test file and then produces a disassembly of it.
#	make depends
#		Doesn't work.  Dependencies are currently all hand coded.
#	make tags
#	make install
#		Attempts to copy zasm, zpp and zdump to the install directory, 
#		defined herein
#
#
# Creator:	Dan Gisselquist, Ph.D.
#		Gisselquist Technology, LLC
#
################################################################################
#
# Copyright (C) 2015, Gisselquist Technology, LLC
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
# License:	GPL, v3, as defined and found on www.gnu.org,
#		http://www.gnu.org/licenses/gpl.html
#
#
################################################################################
#
OBJDIR=	obj-pc
CXX=	g++
CC=	gcc
YACC=	bison
LEX=	flex
YYMMDD=`date +%Y%m%d`
DBGFLAGS= -g -O0
OPTFLAGS= -O3
CCFLAGS= $(DBGFLAGS)
PROGRAMS= zasm zdump zpp
INSTALLD= ../install/cross-tools/bin
CFILES= asmdata.cpp twoc.cpp zdump.cpp zopcodes.cpp zparser.cpp
HFILES= asmdata.h twoc.h zopcodes.h zparser.h

.PHONY: programs
all:	$(OBJDIR)/ programs

install: zasm zdump zpp
	cp $^ $(INSTALLD)/

programs:	$(PROGRAMS)

$(OBJDIR)/zpp.cpp: zpp.l
	$(LEX) -o $@ $^
$(OBJDIR)/zpp.o: $(OBJDIR)/zpp.cpp
	$(CXX) -c $(CCFLAGS) $(OBJDIR)/zpp.cpp -o $@
zpp: $(OBJDIR)/zpp.o
	$(CXX) -o $@ $(CCFLAGS) $^

$(OBJDIR)/zasm.tab.h: zasm.y asmdata.h zparser.h
	$(YACC) -b $(OBJDIR)/zasm -d zasm.y
zasm.output: zasm.y asmdata.h
	$(YACC) -v -b $(OBJDIR)/zasm -d zasm.y
$(OBJDIR)/zasm.lex.cpp: zasm.l $(OBJDIR)/zasm.tab.h
	$(LEX) -o $@ zasm.l
$(OBJDIR)/zasm.lex.o: $(OBJDIR)/zasm.lex.cpp
	$(CXX) -c -I. -I$(OBJDIR)/ $(CCFLAGS) $(OBJDIR)/zasm.lex.cpp -o $@
$(OBJDIR)/zasm.tab.o: $(OBJDIR)/zasm.tab.c $(OBJDIR)/zasm.tab.h
	$(CXX) -c -I. -I$(OBJDIR)/ $(CCFLAGS) $(OBJDIR)/zasm.tab.c -o $@
$(OBJDIR)/asmdata.o: asmdata.cpp zopcodes.h zparser.h
	$(CXX) -c -I. $(CCFLAGS) asmdata.cpp -o $@
zasm: $(OBJDIR)/zasm.lex.o $(OBJDIR)/zasm.tab.o $(OBJDIR)/asmdata.o
zasm: $(OBJDIR)/zparser.o $(OBJDIR)/zopcodes.o $(OBJDIR)/twoc.o
	$(CXX) -o $@ $(CCFLAGS) $^

ZDMPSRC= zdump.cpp zopcodes.cpp twoc.cpp
ZDMPOBJ= $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(ZDMPSRC)))
zdump:	$(ZDMPOBJ)
	$(CXX) $(CCFLAGS) $(ZDMPOBJ) -o $@

$(OBJDIR)/%.o: %.cpp
	$(CXX) -c $(CCFLAGS) $< -o $@

$(OBJDIR)/:
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"

.PHONY: test
test:	dumpd.txt
z.out:	test.S sys.i zasm zdump zpp 
	./zasm test.S -o z.out
dumpd.txt:	z.out zdump
	./zdump z.out > dumpd.txt

define	build-depends
	@echo "Building dependency file(s)"
	@$(CXX) -I $(OBJDIR)/ $(CCFLAGS) -MM $(CFILES) > xd.txt
	@$(CXX) -I $(OBJDIR)/ -I. $(CCFLAGS) -MM $(OBJDIR)/zasm.tab.c >> xd.txt
	@$(CXX) -I $(OBJDIR)/ -I. $(CCFLAGS) -MM $(OBJDIR)/zpp.cpp >> xd.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < xd.txt > $(OBJDIR)/depends.txt
	@rm xd.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(CFILES) $(HFILES) # $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

.PHONY: clean
clean:
	rm -rf $(OBJDIR) $(PROGRAMS) z.out dumpd.txt

-include $(OBJDIR)/depends.txt


