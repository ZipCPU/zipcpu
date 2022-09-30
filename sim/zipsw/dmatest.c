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

static	volatile	ZIPDMA *const _zipdma = ((ZIPDMA *)0xff000000);
const int	TESTLEN = 512;

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
	char	*src, *dst, *buf;

	src = malloc(TESTLEN);
	dst = malloc(TESTLEN);
	buf = malloc(TESTLEN);

	for(int i=0; i<TESTLEN; i++)
		src[i] = rand();

	printf("Basic MEMCPY: ");
	dma_memcpy(dst, src, TESTLEN);
	if (memcmp(dst, src, TESTLEN) != 0) {
		printf("FAIL!\n");
	} else
		printf("PASS\n");

	// Sublen test : Can we do lengths other than the bus width?
	// {{{
	{
		unsigned s = 0;
		for(unsigned ln=1; ln<32; ln++) {

			printf("SubLen #%d MEMCPY: ", ln);
			if (ln + s >= TESTLEN)
				s = 0;
			dma_memcpy(dst, src+s, ln);
			if (memcmp(dst, src+s, ln) != 0) {
				printf("FAIL!\n");
			} else
				printf("PASS\n");

			s += ln;
		}
	}
	// }}}

	// All offsets test
	// {{{
	for(int s=0; s<8; s++) {
		for(int d=0; d<8; d++) {
			unsigned	ln, ln1;

			for(unsigned ln1=1; ln1<8; ln1++) {
				printf("Offset #%d/#%3d MEMCPY #%d: ", s,TESTLEN-d-ln1,ln1);
				dma_memcpy(dst+TESTLEN-d-ln1, src+s, ln1);
				if (memcmp(dst+TESTLEN-d-ln1, src+s, ln1) != 0) {
					printf("FAIL!\n");
				} else
					printf("PASS\n");
			}

			printf("Offset #%d/#%3d MEMCPY: ", s, d);
			ln = (d > s) ? (TESTLEN-d):(TESTLEN-s);
			dma_memcpy(dst+d, src+s, ln);
			if (memcmp(dst+d, src+s, ln) != 0) {
				printf("FAIL!\n");
			} else
				printf("PASS\n");
		}
	}
	// }}}
}
