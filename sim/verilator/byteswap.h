////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/verilator/byteswap.h
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To convert between little endian and big endian byte orders,
//		and to handle conversions between character strings and
//	bit-endian words made from those characters.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2025, Gisselquist Technology, LLC
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
#ifndef	BYTESWAP_H
#define	BYTESWAP_H

#include <stdint.h>

/*
 * The byte swapping routines below are designed to support conversions from a
 * little endian machine/host (such as my PC) to the big endian byte order used
 * on the ZipCPU.  If the current machine is already little endian, no byte
 * swapping is required.
 */
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
/*
 * byteswap
 *
 * Given a big (or little) endian word, return a little (or big) endian word.
 */
extern	uint32_t
byteswap(uint32_t v);

/*
 * byteswapbuf
 *
 * To swap from the byte order of every 32-bit word in the given buffer.
 */
extern	void	byteswapbuf(int ln, uint32_t *buf);

#else
#define	byteswap(A)		 (A)
#define	byteswapbuf(A, B)
#endif

/*
 * buildword
 *
 * Given a pointer within an array of characters, build a 32-bit big-endian
 * word from those characters.  Does not require the character pointer to be
 * aligned.
 */ 
extern	uint32_t buildword(const unsigned char *p);

/*
 * buildswap
 *
 * Same as buildword, except that we build a little endian word from the
 * characters given to us.  Hence the first character is the low order octet
 * of the word.
 */
extern	uint32_t buildswap(const unsigned char *p);

#endif
