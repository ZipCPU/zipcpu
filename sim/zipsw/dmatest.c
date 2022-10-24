////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dmatest.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Test the new ZipDMA IP.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022, Gisselquist Technology, LLC
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
#include <zipcpu.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// }}}

const unsigned	ZIPDMA_BUSY = 0x80000000,
		ZIPDMA_ERR  = 0x40000000,
		ZIPDMA_DINC = 0x00400000,
		ZIPDMA_SINC = 0x00040000,
		ZIPDMA_TLEN = 0x0000ffff,
		DMACMD_MEMCPY= 0;

typedef	struct	ZIPDMA_S {
	unsigned	d_ctrl;
	void		*d_src;
	void		*d_dst;
	unsigned	d_len;
} ZIPDMA;

static	volatile	ZIPDMA *const _zipdma = ((ZIPDMA *)0xff000040);
const int	TESTLEN = 4096;

void	dma_memcpy(void *d, void *s, unsigned len) {
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = s;
		_zipdma->d_dst = d;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;
}

int	main(int argc, char **argv) {
	char	*src, *dst;
	int	fail = 0;

	src = malloc(TESTLEN+8);
	dst = malloc(TESTLEN+8);

	// printf("Initial ptrs: SRC = 0x%08x, DST = 0x%08x\n", src, dst);

	*src++ = 0x01;
	*src++ = 0x02;
	*src++ = 0x03;
	*src++ = 0x04;

	*dst++ = 0x05;
	*dst++ = 0x06;
	*dst++ = 0x07;
	*dst++ = 0x08;

	src[TESTLEN+0] = 0x09; src[TESTLEN+1] = 0x0a;
	src[TESTLEN+2] = 0x0b; src[TESTLEN+3] = 0x0c;

	dst[TESTLEN+0] = 0x0d; dst[TESTLEN+1] = 0x0e;
	dst[TESTLEN+2] = 0x0f; dst[TESTLEN+3] = 0x00;

	for(int i=0; i<TESTLEN; i++)
		src[i] = rand();

	printf("Basic MEMCPY: ");
	dma_memcpy(dst, src, TESTLEN);
	if (memcmp(dst, src, TESTLEN) != 0) {
		printf("FAIL!\n"); fail = 1;
	} else
		printf("PASS\n");

	// Sublen test : Can we do lengths other than the bus width?
	// {{{
	{
		unsigned s = 0;
		for(unsigned ln=1; ln<32 && !fail; ln++) {

			printf("SubLen #%d MEMCPY: ", ln);
			if (ln + s >= TESTLEN)
				s = 0;
			dma_memcpy(dst, src+s, ln);
			if (memcmp(dst, src+s, ln) != 0) {
				printf("FAIL!\n"); fail = 1;
			} else
				printf("PASS\n");

			s += ln;
		}
	}
	// }}}

	// All offsets test
	// {{{
	for(int s=0; s<8 && !fail; s++) {
		for(int d=0; d<8 && !fail; d++) {
			unsigned	ln, ln1;

			for(unsigned ln1=1; ln1<8; ln1++) {
				printf("Offset #%d/#%3d MEMCPY #%d: ", s,TESTLEN-d-ln1,ln1);
				dma_memcpy(dst+TESTLEN-d-ln1, src+s, ln1);
				if (memcmp(dst+TESTLEN-d-ln1, src+s, ln1) != 0) {
					printf("FAIL!\n"); fail = 1;
				} else
					printf("PASS\n");
			}

			printf("Offset #%d/#%3d MEMCPY: ", s, d);
			ln = (d > s) ? (TESTLEN-d):(TESTLEN-s);
			dma_memcpy(dst+d, src+s, ln);
			if (memcmp(dst+d, src+s, ln) != 0) {
				printf("FAIL!\n"); fail = 1;
			} else
				printf("PASS\n");
		}
	}
	// }}}

	if (0x09 != src[TESTLEN+0]) {
		printf("src[TESTLEN+0] = %02x (FAIL)\n", src[TESTLEN+0]);fail=1;
	} if (0x0a != src[TESTLEN+1]) {
		printf("src[TESTLEN+1] = %02x (FAIL)\n", src[TESTLEN+1]);fail=1;
	} if (0x0b != src[TESTLEN+2]) {
		printf("src[TESTLEN+2] = %02x (FAIL)\n", src[TESTLEN+2]);fail=1;
	} if (0x0c != src[TESTLEN+3]) {
		printf("src[TESTLEN+3] = %02x (FAIL)\n", src[TESTLEN+3]);fail=1;
	} if (0x0d != dst[TESTLEN+0]) {
		printf("dst[TESTLEN+1] = %02x (FAIL)\n", dst[TESTLEN+0]);fail=1;
	} if (0x0e != dst[TESTLEN+1]) {
		printf("dst[TESTLEN+2] = %02x (FAIL)\n", dst[TESTLEN+1]);fail=1;
	} if (0x0f != dst[TESTLEN+2]) {
		printf("dst[TESTLEN+3] = %02x (FAIL)\n", dst[TESTLEN+2]);fail=1;
	} if (0x00 != dst[TESTLEN+3]) {
		printf("dst[TESTLEN+0] = %02x (FAIL)\n", dst[TESTLEN+3]);fail=1;
	}
	src -= 4; dst -= 4;
	if (0x01 != src[0]) {
		printf("src[0] = %02x (FAIL)\n", src[0]);fail=1;
	} if (0x02 != src[1]) {
		printf("src[1] = %02x (FAIL)\n", src[1]);fail=1;
	} if (0x03 != src[2]) {
		printf("src[2] = %02x (FAIL)\n", src[2]);fail=1;
	} if (0x04 != src[3]) {
		printf("src[3] = %02x (FAIL)\n", src[3]);fail=1;
	} if (0x05 != dst[0]) {
		printf("dst[0] = %02x (FAIL)\n", dst[0]);fail=1;
	} if (0x06 != dst[1]) {
		printf("dst[1] = %02x (FAIL)\n", dst[1]);fail=1;
	} if (0x07 != dst[2]) {
		printf("dst[2] = %02x (FAIL)\n", dst[2]);fail=1;
	} if (0x08 != dst[3]) {
		printf("dst[3] = %02x (FAIL)\n", dst[3]);fail=1;
	}

	// printf("Final   ptrs: SRC = 0x%08x, DST = 0x%08x\n", src, dst);

	if (fail)
		printf("TEST FAILURE!\n");
	else
		printf("SUCCESS!!  All tests pass\n");
}
