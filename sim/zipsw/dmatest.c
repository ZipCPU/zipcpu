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
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
#include <board.h>
#include <zipcpu.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// }}}
const unsigned	ZIPDMA_BUSY = 0x80000000,
		ZIPDMA_ERR  = 0x40000000,
		ZIPDMA_DFIX = 0x00400000,
		ZIPDMA_SFIX = 0x00040000,
		ZIPDMA_TLEN = 0x0000ffff,
		//
		DMACMD_FIXDST   = 0x0400000,
		DMACMD_DSTBYTE  = 0x0300000,
		DMACMD_DST16B   = 0x0200000,
		DMACMD_DST32B   = 0x0100000,
		//
		DMACMD_FIXSRC   = 0x0040000,
		DMACMD_SRCBYTE  = 0x0030000,
		DMACMD_SRC16B   = 0x0020000,
		DMACMD_SRC32B   = 0x0010000,
		DMACMD_BUSSRC   = 0,
		//
		DMACMD_BUSDST   = 0,
		DMACMD_MEMCPY	= 0;

typedef	struct	ZIPDMA_S {
	unsigned	d_ctrl;
	void		*d_src;
	void		*d_dst;
	unsigned	d_len;
} ZIPDMA;

#define ZIPDMA_BASE_ADDRESS 0xff000040
static volatile ZIPDMA *const _zipdma = ((ZIPDMA *)ZIPDMA_BASE_ADDRESS);
const int	TESTLEN = 1024*16;

#define DW	64

#define err_detect() 		(_zdmastcheck->zck_check & 0x1)
#define read_lfsr_char() 	(_zdmacheck->z_char[0])
#define read_lfsr_short() 	(_zdmacheck->z_short[0])
#define read_lfsr_int() 	(_zdmacheck->z_word[0])

#define to_char(val, out) 	(out = (char)((val & 0xFF00000000000000) >> 56))
#define to_short(val, out) 	(out = (short)((val & 0xFFFF000000000000) >> 48))
#define to_int(val, out) 	(out = (unsigned int)((val & 0xFFFFFFFF00000000) >> 32))

enum sizes {
	S_BYTE,
	S_SHORT,
	S_INT,
	S_BUS
};

//typedef union {
//    volatile char * __attribute__((aligned(8))) charValue;
//    volatile short * __attribute__((aligned(4))) shortValue;
//    volatile unsigned int * __attribute__((aligned(2))) intValue;
//} LfsrValue;

int	dma_memcpy(void *dst, void *src, unsigned len) {
	// {{{
	printf("  DMA_MEMCPY(0x%08x, 0x%08x, %6d);\n", (unsigned)dst,
		(unsigned)src, len);
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = src;
		_zipdma->d_dst = dst;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;

	if (_zipdma->d_ctrl & ZIPDMA_ERR) {
		if (dst && src) {
			printf("ERR: DMA transfer failed\n");
			return 1;
		}
	} else if (len > 0 && (NULL == dst || NULL == src)) {
		printf("ERR: DMA transfer failed to produce a bus error\n");
		return 1;
	}

	return 0;
}
// }}}

int	dma_memcpy_flags(void *d, void *s, unsigned ln, unsigned flags) {
	// {{{
	printf("    DMA-MEMCPY(D=0x%08x, S=0x%08x, %5d, F=0x%08x);\n",
				(unsigned)d, (unsigned)s, ln, flags);

	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = s;
		_zipdma->d_dst = d;
		_zipdma->d_len = ln;

		_zipdma->d_ctrl = DMACMD_MEMCPY | flags;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;

	if (_zipdma->d_ctrl & ZIPDMA_ERR) {
		printf("ERR: DMA/Z transfer failed\n");
		return 1;
	}

	return 0;
}
// }}}

void init_lfsr(uint32_t init_value) {
	// {{{
	_zdmastcheck->zck_state = init_value;
}
// }}}

int	dma_test(unsigned seed, unsigned soff, unsigned doff, unsigned len,
		unsigned flags) {
	// {{{
	printf("  DMA TEST(0x%08x, S[%2d], D[%02d], %5d, 0x%08x);\n",
		seed, soff, doff, len, flags);

	char	*buf = malloc(len);
	int	err = 0;

	init_lfsr(seed);
	err = dma_memcpy_flags(buf, (void *)&_zdmacheck->z_char[soff], len,
				flags & (~(DMACMD_FIXDST | DMACMD_DSTBYTE)));
	if (err)
		printf("    BUS-ERROR! ->MEM\n");
	if (0 == err) {
		init_lfsr(seed);
		err |= dma_memcpy_flags((void *)&_zdmacheck->z_char[doff], buf, len,
				flags & (~(DMACMD_FIXSRC | DMACMD_SRCBYTE)));
		if (err)
			printf("    BUS-ERROR! MEM->\n");
	}

	free(buf);

	if (0 != err)
		return err;
	if (err_detect()) {
		printf("    ERR: Returns do not match!\n");
		return 2;
	}
	return 0;
}
// }}}

int	main(int argc, char **argv) {
	const unsigned	SZBYTE = DMACMD_DSTBYTE | DMACMD_SRCBYTE,
			SZHALF = DMACMD_DST16B  | DMACMD_SRC16B,
			SZ32   = DMACMD_DST32B  | DMACMD_SRC32B,
			SZBUS  = DMACMD_BUSDST  | DMACMD_BUSSRC;
	int	fail = 0, err = 0;
	uint32_t	lfsr_state;

	// enum sizes s_size;
	////////////////////////////////////////////////////////////////////////
	//
	// 8b test
	// {{{
	if (0) {
		printf("Basic MEMCPY( 8b): \n");

		// compare hw-sw lfsr values for 8 bit
		lfsr_state = 0xf1000000;	// big endian for cpu

		err |= dma_test(lfsr_state, 0, 0, TESTLEN, SZBYTE);
		for(int fx=0; fx<4; fx++) {
			unsigned flags = SZBYTE;
			if (1 & fx)
				flags |= DMACMD_FIXSRC;
			if (2 & fx)
				flags |= DMACMD_FIXDST;

			for(unsigned off=1; off<15 && (0 == err); off++) {
				err |= dma_test(lfsr_state + off, 0, off,TESTLEN,flags);
				if (0 == err)
					err |= dma_test(lfsr_state + 17 + off, off, 0,
							TESTLEN, flags);

				for(unsigned tln=1; tln<15 && (0 == err); tln++) {
					err |= dma_test(lfsr_state + 19 + off + tln, off, 0,
								tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19 + off + tln,
								0, off, tln, flags);
				}

				for(unsigned tln=254; tln<258 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=510; tln<514 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}
			}
		}

		if (0 == err)
			printf("Basic MEMCPY( 8b) -- Pass\n");
		else {
			printf("Basic MEMCPY( 8b) -- Errors\n");
			fail = 1;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 16b test
	// {{{
	if (0 && !fail) {
		printf("Basic MEMCPY( 16b): \n");

		// compare hw-sw lfsr values for 8 bit
		lfsr_state = 0xf2000000;	// big endian for cpu

		err |= dma_test(lfsr_state, 0, 0, TESTLEN, SZHALF);
		for(int fx=0; fx<4; fx++) {
			unsigned flags = SZHALF;
			if (1 & fx)
				flags |= DMACMD_FIXSRC;
			if (2 & fx)
				flags |= DMACMD_FIXDST;

			for(unsigned off=1; off<15 && (0 == err); off++) {
				err |= dma_test(lfsr_state + off, 0, off, TESTLEN, flags);
				if (0 == err)
					err |= dma_test(lfsr_state + 17 + off,
							off,0, TESTLEN, flags);

				for(unsigned tln=1; tln<15 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=510; tln<514 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=1022; tln<1026 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}
			}
		}

		if (0 == err)
			printf("Basic MEMCPY(16b) -- Pass\n");
		else {
			printf("Basic MEMCPY(16b) -- Errors\n");
			fail = 1;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 32b test
	// {{{
	if (1 && !fail) {
		printf("Basic MEMCPY( 32b): \n");

		// compare hw-sw lfsr values for 8 bit
		lfsr_state = 0xf4000000;	// big endian for cpu

		err |= dma_test(lfsr_state, 0, 0, TESTLEN, SZ32);
		for(int fx=2; fx<4; fx++) {
			unsigned flags = SZ32;
			if (1 & fx)
				flags |= DMACMD_FIXSRC;
			if (2 & fx)
				flags |= DMACMD_FIXDST;

			for(unsigned off=1; off<15 && (0 == err); off++) {
				err |= dma_test(lfsr_state + off, 0, off, TESTLEN, flags);
				if (0 == err)
					err |= dma_test(lfsr_state + 17 + off,
							off,0, TESTLEN, flags);

				for(unsigned tln=1; tln<15 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=1022; tln<1026 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=2046; tln<2050 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}
			}
		}

		if (0 == err)
			printf("Basic MEMCPY(32b) -- Pass\n");
		else {
			printf("Basic MEMCPY(32b) -- Errors\n");
			fail = 1;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus width test
	// {{{
	if (1 && !fail) {
		printf("Basic MEMCPY( BUS): \n");

		// compare hw-sw lfsr values for 8 bit
		lfsr_state = 0xf6400000;	// big endian for cpu

		err |= dma_test(lfsr_state, 0, 0, TESTLEN, SZBUS);
		for(int fx=0; fx<4; fx++) {
			unsigned flags = SZBUS;
			if (1 & fx)
				flags |= DMACMD_FIXSRC;
			if (2 & fx)
				flags |= DMACMD_FIXDST;

			for(unsigned off=1; off<15 && (0 == err); off++) {
				err |= dma_test(lfsr_state + off, 0, off, TESTLEN, flags);
				if (0 == err)
					err |= dma_test(lfsr_state + 17 + off,
							off,0, TESTLEN, flags);

				for(unsigned tln=1; tln<15 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=2046; tln<2050 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}

				for(unsigned tln=4094; tln<4098 && (0 == err); tln++) {
					err |= dma_test(lfsr_state+19+off+tln,
							off, 0, tln, flags);
					if (0 == err)
						err |= dma_test(lfsr_state + 19
								+ off + tln,
							0, off, tln, flags);
				}
			}
		}

		if (0 == err)
			printf("Basic MEMCPY(BUS) -- Pass\n");
		else {
			printf("Basic MEMCPY(BUS) -- Errors\n");
			fail = 1;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// obtain valid error signal
	// {{{
	if (!fail) {
		char	*c_src = NULL, *c_dst = NULL;

		err = dma_memcpy(c_dst, c_src, TESTLEN);
		if (err) {
			printf("FAIL!\n");
			fail = 1;
		} else
			printf("PASS\n");
	}
	// }}}

	if (fail)
		printf("TEST FAILURE!\n");
	else
		printf("SUCCESS! All tests pass\n");
#if 0
#endif
}
