////////////////////////////////////////////////////////////////////////////////
//
// Filename:	mpyraw.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To test GCC's multiply "instructions", and see if they work
//		properly.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2022, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
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

asm("\t.section\t.start,\"ax\",@progbits\n"
	"\t.global\t_start\n"
"_start:\n"
	"\tLDI\t_top_of_stack,SP\n"
	"\tJSR\tentry\n"
"_halt_cpu:\n"
	"\tNOOP\n"
	"\tNEXIT 0\n"
	"\tHALT\n");

long	mpysquare(long a) {
	return a * a;
}

long	mpypair(long a, long b) {
	return a * b;
}

void	entry(void) {
	uint32_t	fill, taps;

	fill = 1;
	taps = 0x4597f;

	for(int i=0; i<50; i++) {
		long	r; uint32_t	hi, lo;
		r = mpypair(0x271828314159l + (unsigned)fill, 0x3415928l);
		lo = (uint32_t)r;
		hi = (uint32_t)(r>>32);
		asm("NDUMP %0" : : "r"(lo));
		asm("NDUMP %0" : : "r"(hi));

		r = mpysquare(0x271828314159l + (unsigned)fill);
		lo = (uint32_t)r;
		hi = (uint32_t)(r>>32);
		asm("NDUMP %0" : : "r"(lo));
		asm("NDUMP %0" : : "r"(hi));

		if (fill&1) {
			fill = (fill >> 1)^taps;
		} else	fill = fill >> 1;
	}
}
