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
// Copyright (C) 2022-2023, Gisselquist Technology, LLC
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
#include <stdint.h>

const unsigned	ZIPDMA_BUSY = 0x80000000,
		ZIPDMA_ERR  = 0x40000000,
		ZIPDMA_DINC = 0x00400000,
		ZIPDMA_SINC = 0x00040000,
		ZIPDMA_TLEN = 0x0000ffff,
		//
		DMACMD_FIXSRC   = 0x0400000,
		DMACMD_SRCBYTE  = 0x0300000,
		DMACMD_SRC16B   = 0x0200000,
		DMACMD_SRC32B   = 0x0100000,
		DMACMD_BUSSRC   = 0,
		//
		DMACMD_FIXDST   = 0x0040000,
		DMACMD_DSTBYTE  = 0x0030000,
		DMACMD_DST16B   = 0x0020000,
		DMACMD_DST32B   = 0x0010000,
		DMACMD_BUSDST   = 0,
		DMACMD_MEMCPY	= 0;

typedef	struct	ZIPDMA_S {
	unsigned	d_ctrl;
	void		*d_src;
	void		*d_dst;
	unsigned	d_len;
} ZIPDMA;

static	volatile	ZIPDMA *const _zipdma = ((ZIPDMA *)0xff000040);
const int	TESTLEN = 4096;

int	dma_memcpy(void *des, void *src, unsigned len) {
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = src;
		_zipdma->d_dst = des;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;

	return (_zipdma->d_ctrl & ZIPDMA_ERR) ? 1:0;
}

int	dma_memcpy_size(void *des, void *src, unsigned len, unsigned size) {
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = src;
		_zipdma->d_dst = des;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY | size;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;

	return (_zipdma->d_ctrl & ZIPDMA_ERR) ? 1:0;
}

int	dma_memcpy_noninc(void *des, void *src, unsigned len, unsigned size) {
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = src;
		_zipdma->d_dst = des;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY | ZIPDMA_DINC | ZIPDMA_SINC | size;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;

	return (_zipdma->d_ctrl & ZIPDMA_ERR) ? 1:0;
}

uint64_t lfsr_shift(uint64_t state) {
    uint64_t feedback = (state >> 63) ^ (state >> 62);
    uint64_t new_bit = feedback & 1;
    return (state << 1) | new_bit;
}

// make bus peripheral for comparison (for both dst and src)
// LFSR 
int	main(int argc, char **argv) {
	const unsigned	SZBYTE = DMACMD_DSTBYTE | DMACMD_SRCBYTE;
	const unsigned	SZHALF = DMACMD_DST16B  | DMACMD_SRC16B;
	const unsigned	SZ32   = DMACMD_DST32B  | DMACMD_SRC32B;
	const unsigned	SZBUS  = DMACMD_BUSDST  | DMACMD_BUSSRC;
	int	fail = 0, err;
	char *src, *dst;
	unsigned offset_addr = 0;
	unsigned transfer_len, transfer_len1;

	uint64_t lfsr_state = 0xdeadbeafdeadbeaf;

	src = malloc(TESTLEN+8);
	dst = malloc(TESTLEN+8);

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

	//for(int i=0; i<TESTLEN; i++) {
	//	//src[i] = rand();
	//	printf("LFSR State: 0x%llx\n", lfsr_state);
	//	lfsr_state = lfsr_shift(lfsr_state);
	//}

	// -----------
	// 8b test
	// -----------
	printf("Basic MEMCPY( 8b): ");
	err = dma_memcpy_size(dst, src, TESTLEN, SZBYTE);
	if (err || memcmp(dst, src, TESTLEN) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	err = dma_memcpy_noninc(dst, src, 1, SZBYTE);
	if (err || memcmp(dst, src, TESTLEN) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	// -----------
	// 16b test
	// -----------
	printf("Basic MEMCPY( 16b): ");
	err = dma_memcpy_size(dst, src + offset_addr, TESTLEN, SZHALF);
	if (err || memcmp(dst + offset_addr, src + offset_addr, TESTLEN) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	err = dma_memcpy_noninc(dst, src, 2, SZHALF);
	if (err || memcmp(dst, src, 2) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	// 16b edge casez: transfer_len = 1, 2, 3
	for(transfer_len = 1; transfer_len < 4 && !fail; transfer_len++) {
		err = dma_memcpy_size(dst, src + offset_addr, transfer_len, SZHALF);
		if (err || memcmp(dst, src + offset_addr, transfer_len) != 0) {
			printf("FAIL!\n"); 
			fail = 1;
		} else
			printf("PASS\n");

		offset_addr += transfer_len;
	}

	// -----------
	// 32b test
	// -----------
	printf("Basic MEMCPY( 32b): ");
	err = dma_memcpy_size(dst, src + offset_addr, TESTLEN, SZ32);
	if (err || memcmp(dst, src + offset_addr, TESTLEN) != 0) {
		printf("FAIL!\n");
		fail = 1;
	} else
		printf("PASS\n");

	err = dma_memcpy_noninc(dst, src, 4, SZ32);
	if (err || memcmp(dst, src, 4) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	// 32b edge casez: transfer_len = 1, 2, .., 15
	for(transfer_len = 1; transfer_len < 16 && !fail; transfer_len++) {		
		err = dma_memcpy_size(dst, src + offset_addr, transfer_len, SZ32);
		if (err || memcmp(dst, src + offset_addr, transfer_len) != 0) {
			printf("FAIL!\n"); 
			fail = 1;
		} else
			printf("PASS\n");

		offset_addr += transfer_len;
	}

	// -----------
	// Bus width test
	// -----------
	printf("Basic MEMCPY( BUS): ");
	err = dma_memcpy(dst, src + offset_addr, TESTLEN);
	if (err || memcmp(dst, src + offset_addr, TESTLEN) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	err = dma_memcpy_noninc(dst, src, 8, SZBUS);
	if (err || memcmp(dst, src, 8) != 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

	// Bus width edge casez: transfer_len = 1, 2, .., 32
	for(transfer_len = 1; transfer_len < 32 && !fail; transfer_len++) {
		err = dma_memcpy(dst, src + offset_addr, transfer_len);
		if (err || memcmp(dst, src + offset_addr, transfer_len) != 0) {
			printf("FAIL!\n"); 
			fail = 1;
		} else
			printf("PASS\n");

		offset_addr += transfer_len;
	}

	//unsigned odd_even;
	//for (transfer_len = 1; transfer_len < 8 && !fail; transfer_len++) {
	//	odd_even = (offset_addr & 0x1) + 1;	// If src is even then make des odd or vice versa
	//	for (int src_cnt = 0; src_cnt < 8; src_cnt++) {
	//		for (int dst_cnt = 0; dst_cnt < 8; dst_cnt++) {
	//			err = dma_memcpy_size(dst + TESTLEN - transfer_len - dst_cnt, src + TESTLEN - transfer_len - src_cnt, transfer_len, SZHALF);
	//		if (err || memcmp(dst + TESTLEN - transfer_len - dst_cnt, src + TESTLEN - transfer_len - src_cnt, transfer_len) != 0) {
	//			printf("FAIL!\n"); 
	//			fail = 1;
	//		} else
	//			printf("PASS\n");
	//		}
	//	}
	//}

	// -----------
	// obtain valid error signal
	// -----------
	src = NULL;
	dst = NULL;

	err = dma_memcpy(dst, src, TESTLEN);
	if (err == 0) {
		printf("FAIL!\n"); 
		fail = 1;
	} else
		printf("PASS\n");

#if 0

#endif

	if (fail)
		printf("TEST FAILURE!\n");
	else
		printf("SUCCESS! All tests pass\n");
}
