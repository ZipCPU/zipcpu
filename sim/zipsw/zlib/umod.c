////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/zipsw/zlib/umod.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a temporary file--a crutch if you will--until a similar
//		capability is merged into GCC.  Right now, GCC has no way of
//	taking the module of two 64-bit numbers, and this routine provides that
//	capability.
//
//	This routine is required by and used by newlib's printf in order to
//	print decimal numbers (%d) to an IO stream.
//
//	Once gcc is properly patched, this will be removed from the 
//	repository.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2023, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include <stdint.h>


unsigned long __udivdi3(unsigned long, unsigned long);

__attribute((noinline))
unsigned long __umoddi3(unsigned long a, unsigned long b) {
	unsigned long	r;

	// Return a modulo b, or a%b in C syntax
	r = __udivdi3(a, b);
	r = r * b;
	r = a - r;
	return r;
}

