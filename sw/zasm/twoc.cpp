////////////////////////////////////////////////////////////////////////////
//
// Filename: 	twoc.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Some various two's complement related C++ helper routines.
//		Specifically, these help extract signed numbers from
//		packed bitfields, while guaranteeing that the upper bits
//		are properly sign extended (or not) as desired.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
//
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
///////////////////////////////////////////////////////////////////////////
#include <stdio.h>
#include <assert.h>
#include "twoc.h"

long	sbits(const long val, const int bits) {
	long	r;

	r = val & ((1l<<bits)-1);
	if (r & (1l << (bits-1)))
		r |= (-1l << bits);
	return r;
}

bool	sfits(const long val, const int bits) {
	return (sbits(val, bits) == bits);
}

unsigned long	ubits(const long val, const int bits) {
	unsigned long r = val & ((1l<<bits)-1);
	return r;
}

unsigned long	rndbits(const long val, const int bits_in, const int bits_out) {
	long	s = sbits(val, bits_in); // Signed input value
	long	t = s;	// Truncated input value
	long	r;	// Result

	// printf("RNDBITS(%08lx, %d, %d)\n", val, bits_in, bits_out);
	// printf("S = %lx\n", s);
	// printf("T = %lx\n", t);
	// assert(bits_in > bits_out);
	if (bits_in == bits_out)
		r = s;
	else if (bits_in-1 == bits_out) {
		t = sbits(val>>1, bits_out);
		// printf("TEST! S = %ld, T = %ld\n", s, t);
		if (3 == (s&3))
			t = t+1;
		r = t;
	} else {
		// A. 0XXXX.0xxxxx -> 0XXXX
		// B. 0XXX0.100000 -> 0XXX0;
		// C. 0XXX1.100000 -> 0XXX1+1;
		// D. 0XXXX.1zzzzz -> 0XXXX+1;
		// E. 1XXXX.0xxxxx -> 1XXXX
		// F. 1XXX0.100000 ->  ??? XXX0;
		// G. 1XXX1.100000 ->  ??? XXX1+1;
		// H. 1XXXX.1zzzzz -> 1XXXX+1;
		t = sbits(val>>(bits_in-bits_out), bits_out); // Truncated value
		if (0 == ((s >> (bits_in-bits_out-1))&1)) {
			// printf("A\n");
			r = t;
		} else if (0 != (s & ((1<<(bits_in-bits_out-1))-1))) {
			// printf("D\n");
			r = t+1;
		} else if (t&1) {
			// printf("C\n");
			r = t+1;
		} else { // 3 ..?11
			// printf("B\n");
			r = t;
		}
	} return r;
}


