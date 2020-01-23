################################################################################
##
## Filename:	Makefile
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	
##
## Targets:
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2020, Gisselquist Technology, LLC
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
all: zsim

CXX	:= g++
FLAGS	:= -Wall -g
INCS	:= 
SOURCES := zsim.cpp twoc.cpp zipelf.cpp
LIBS	:= -lelf
TESTF	:= $(ZASM)/z.out
DHRYSTONEF := ../asm/zipdhry.z

zsim: $(SOURCES) zipelf.h twoc.h
	$(CXX) $(FLAGS) $(INCS) $(SOURCES) $(LIBS) -o $@

.PHONY: clean
clean:
	rm -f zsim
