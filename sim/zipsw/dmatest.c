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

#define ZIPDMA_BASE_ADDRESS 0xff000040
static volatile ZIPDMA *const _zipdma = ((ZIPDMA *)ZIPDMA_BASE_ADDRESS);
const int	TESTLEN = 32;

#define DW	64

#define err_detect() 		(_zdmastcheck->zck_check & 0x1)
#define read_lfsr_char() 	(_zdmacheck->z_data0[0])
#define read_lfsr_short() 	(_zdmacheck->z_data1[0])
#define read_lfsr_int() 	(_zdmacheck->z_data2[0])

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

int	dma_memcpy_size(void *dst, void *src, unsigned len, unsigned size) {
	// {{{
	printf("  DMA_MEMCPY_SIZE(0x%08x, 0x%08x, %6d, %1d);\n", (unsigned)dst,
		(unsigned)src, len, (size>>20)&3);
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
		while(_zipdma->d_ctrl & ZIPDMA_BUSY)
			;
	} else {
		_zipdma->d_src = src;
		_zipdma->d_dst = dst;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY | size;
	}

	while(_zipdma->d_ctrl & ZIPDMA_BUSY) {
		asm("NOOP");
	} CLEAR_DCACHE;

	if (_zipdma->d_ctrl & ZIPDMA_ERR) {
		printf("ERR: DMA/SZ transfer failed\n");
		return 1;
	}

	return 0;
}
// }}}

int	dma_memcpy_noninc(void *des, void *src, unsigned len, unsigned size, unsigned mode) {
	// {{{
	printf("  DMA_MEMCPY_FIXD(0x%08x, 0x%08x, %6d, %1d);\n", (unsigned)dst,
		(unsigned)src, len, (size>>20)&3);
	if (_zipdma->d_ctrl & ZIPDMA_BUSY) {
		printf("ERR: DMA is already busy\n");
	} else {
		_zipdma->d_src = src;
		_zipdma->d_dst = dst;
		_zipdma->d_len = len;

		_zipdma->d_ctrl = DMACMD_MEMCPY | size | mode;
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

//LfsrValue read_lfsr_value(unsigned size) {
//	// {{{
//    LfsrValue value;
//
//    switch(size) {
//        case S_BYTE:
//            value.charValue = _zdmacheck->z_data0;
//            break;
//        case S_SHORT:
//            value.shortValue = _zdmacheck->z_data1;
//            break;
//        case S_INT:
//            value.intValue = _zdmacheck->z_data2;
//            break;
//        default:
//            printf("ERR: Invalid size\n");
//            value.intValue = NULL; 	// return null value in case an error situation
//            break;
//    }
//
//    return value;
//}
// }}}

void init_lfsr(uint32_t init_value) {
	// {{{
	_zdmastcheck->zck_check = init_value;
}
// }}}

void cmp_lfsr(void *cmp_value, unsigned size) {
	// {{{
	switch(size) {
	case S_BYTE:
		_zdmacheck->z_data0[0] = (*(char *)cmp_value);
		break;
	case S_SHORT:
		_zdmacheck->z_data1[0] = (*(short *)cmp_value);
		break;
	case S_INT:
		_zdmacheck->z_data2[0] = (*(unsigned *)cmp_value);
		break;
	case S_BUS:
		_zdmacheck->z_data2[0] = (*(unsigned *)cmp_value);
		break;
	default:
		printf("ERR: Invalid size\n");
		break;
	}
}
// }}}

uint64_t lfsr_shift(uint32_t state) {
	// {{{
	uint32_t feedback, new_bit, result;

	feedback = (state >> (DW-1)) ^ (state >> (DW-2));
	new_bit  = feedback & 0x1;

	result = ((state << 1) | new_bit);
	return result;
}
// }}}

void	memdump(void *vd, void *vs, unsigned ln) {
	// {{{
	char	*d = (char *)vd, *s = (char *)vs;
	for(unsigned k=0; k<ln; k++) {
		printf("  ER %6d: %02x %02x\n", k, *d, *s);
		if (*d != *s)
			break;
		d++; s++;
	}
}
// }}}

int	main(int argc, char **argv) {
	const unsigned	SZBYTE = DMACMD_DSTBYTE | DMACMD_SRCBYTE;
	const unsigned	SZHALF = DMACMD_DST16B  | DMACMD_SRC16B;
	const unsigned	SZ32   = DMACMD_DST32B  | DMACMD_SRC32B;
	const unsigned	SZBUS  = DMACMD_BUSDST  | DMACMD_BUSSRC;
	int	fail = 0, err;
	unsigned cmp_err;
	char		*c_src,	*c_dst,	*lfsr_state_hw_0;
	short		*s_src, *s_dst,	*lfsr_state_hw_1;
	unsigned	*w_src,	*w_dst,	*lfsr_state_hw_2;
	uint32_t	lfsr_state;
	unsigned	offset_addr;
	unsigned	transfer_len, transfer_len1;

	enum sizes s_size;
	//LfsrValue lfsrVal;

	c_src = malloc(sizeof(char) * (TESTLEN+8));
	c_dst = malloc(sizeof(char) * (TESTLEN+8));
	lfsr_state_hw_0 = malloc(sizeof(char) * (TESTLEN+8));

	s_src = malloc(sizeof(short) * (TESTLEN+8));
	s_dst = malloc(sizeof(short) * (TESTLEN+8));
	lfsr_state_hw_1 = malloc(sizeof(short) * (TESTLEN+8));

	w_src = malloc(sizeof(int) * (TESTLEN+8));
	w_dst = malloc(sizeof(int) * (TESTLEN+8));
	lfsr_state_hw_2 = malloc(sizeof(int) * (TESTLEN+8));

	if (lfsr_state_hw_0 == NULL || lfsr_state_hw_1 == NULL
					|| lfsr_state_hw_2 == NULL) {
		printf("Memory allocation failed\n");
		return 1;
	}

	// initilaize pointers
	//lfsrVal.charValue = lfsr_state_hw_0;
	//lfsrVal.shortValue = lfsr_state_hw_1;
	//lfsrVal.intValue = lfsr_state_hw_2;

	*c_src++ = 0x01;
	*c_src++ = 0x02;
	*c_src++ = 0x03;
	*c_src++ = 0x04;

	*c_dst++ = 0x05;
	*c_dst++ = 0x06;
	*c_dst++ = 0x07;
	*c_dst++ = 0x08;

	c_src[TESTLEN+0] = 0x09; c_src[TESTLEN+1] = 0x0a;
	c_src[TESTLEN+2] = 0x0b; c_src[TESTLEN+3] = 0x0c;

	c_dst[TESTLEN+0] = 0x0d; c_dst[TESTLEN+1] = 0x0e;
	c_dst[TESTLEN+2] = 0x0f; c_dst[TESTLEN+3] = 0x00;

	////////////////////////////////////////////////////////////////////////
	//
	// 8b test
	// {{{
	printf("Basic MEMCPY( 8b): \n");

	// compare hw-sw lfsr values for 8 bit
	s_size = S_BYTE;
	lfsr_state = 0xf1000000;	// big endian for cpu
	init_lfsr(lfsr_state);
	for(int i = 0; i < 2; i++) {
		lfsr_state = lfsr_shift(lfsr_state);
		to_char(lfsr_state, c_src[i]);
		lfsr_state_hw_0[i] = read_lfsr_char();
		//lfsrVal = read_lfsr_value(s_size);
		//printf("----------\n");
		//printf("%d\n", i);
		//printf("(char) LFSR_SW State: 0x%lx\n", lfsr_state);
		//printf("(char) LFSR_HW State: 0x%x\n", lfsr_state_hw_0[i]);
	}

	cmp_lfsr(&c_src[TESTLEN-1], s_size);
	cmp_err = err_detect();
	if (cmp_err != 0)
		printf("(char) Error: 0x%x\n", cmp_err);
	// data copy from sw lfsr to destination for 8 bit
	err = dma_memcpy_size(c_dst, c_src, TESTLEN, SZBYTE);

	// compare hw-sw lfsr values for 8 bit
	if (err) {
		printf("  (char) DMA (bus) error\n");
		fail = 1;
	} else if ((0 && cmp_err) || 0 != memcmp(lfsr_state_hw_0, c_dst, TESTLEN)) {
		memdump(lfsr_state_hw_0, c_dst, TESTLEN);
		printf("  (char) No match between sw and hw lfsr values!\n");
		fail = 1;
	} // else printf("  (char) LFSR Matches\n");


	for(int ln=1; ln<15 && !fail; ln++) {
	if (!fail) {
		lfsr_state_hw = 0xf1000000;	// big endian for cpu
		// Test reading from a constant address
		err = dma_memcpy_noninc(dst, c_lfsr_state_hw, TESTLEN-ln, SZBYTE, ZIPDMA_SFIX);
		lfsr_state_hw = 0xf1000000;	// big endian for cpu
		// Test writing to a constant address
		err = err || dma_memcpy_noninc(c_lfsr_state_hw, dst, TESTLEN-ln, SZBYTE, ZIPDMA_DFIX);
		if (err) {
			printf("  (char) DMA (bus) error\n");
			fail = 1;
		} else if (err_detect()) {
			printf("  FAIL: (char) Stream comparison failure!\n");
			fail = 1;
		} else
			printf("Pass\n");
	}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 16b test
	// {{{
	if (0 && !fail) {
		printf("Basic MEMCPY( 16b): \n");

		// compare hw-sw lfsr values for 16 bit
		s_size = S_SHORT;
		lfsr_state = 0xbeaf0000;
		init_lfsr(lfsr_state);
		for(int i = 0; i < TESTLEN; i++) {
			lfsr_state = lfsr_shift(lfsr_state);
			to_short(lfsr_state, s_src[i]);
			lfsr_state_hw_1[i] = read_lfsr_short();
			//printf("(short) LFSR_SW State: 0x%x\n", s_src[i]);
			//printf("(short) LFSR_HW State: 0x%x\n", lfsr_state_hw_1[i]);
		}
		cmp_lfsr(&s_src[TESTLEN-1], s_size);
		cmp_err = err_detect();
		if (cmp_err != 0)
			printf("(short) Error: 0x%x\n", cmp_err);

		// data copy from sw lfsr to destination for 16 bit
		err = dma_memcpy_size(s_dst, s_src, TESTLEN, SZHALF);

		// compare hw-sw lfsr values for 16 bit
		if (err) {
			printf("  (short) DMA (bus) error\n");
			fail = 1;
		} else if ((0 && cmp_err) || 0 != memcmp(lfsr_state_hw_1, s_dst, TESTLEN)) {
			printf("  (short) No match between SW and HW LFSR values!\n");
			fail = 1;
		} // else printf("  (short) LFSR Matches\n");

		if (!fail) {
			err = dma_memcpy_noninc(s_dst, s_src, 2, SZHALF);
			if (err) {
				printf("  (short) DMA (bus) error\n");
				fail = 1;
			} else if (0 != memcmp(s_dst, s_src, 2)) {
				printf("FAIL!\n");
				fail = 1;
			} else
				printf("PASS\n");
		}

		// 16b edge casez: transfer_len = 1, 2, 3
		offset_addr = 4;
		for(transfer_len = 1; transfer_len < 4 && !fail; transfer_len++) {
			err = dma_memcpy_size(s_dst, s_src + offset_addr, transfer_len, SZHALF);
			if (err) {
				printf("  (short) DMA (bus) error\n");
				fail = 1;
			} else if (0 != memcmp(s_dst, s_src + offset_addr, transfer_len)) {
				printf("FAIL!\n");
				fail = 1;
			} else
				printf("PASS\n");

			offset_addr++;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 32b test
	// {{{
	if (0 && !fail) {
		printf("Basic MEMCPY( 32b): \n");

		// compare hw-sw lfsr values for 32 bit
		s_size = S_INT;
		lfsr_state = 0xdeadbeaf;
		init_lfsr(lfsr_state);
		for(int i = 0; i < TESTLEN; i++) {
			lfsr_state = lfsr_shift(lfsr_state);
			to_int(lfsr_state, w_src[i]);
			lfsr_state_hw_2[i] = read_lfsr_int();
			//printf("(int) LFSR_SW State: 0x%x\n", w_src[i]);
			//printf("(int) LFSR_HW State: 0x%x\n", lfsr_state_hw_2[i]);
		}
		cmp_lfsr(&w_src[TESTLEN-1], s_size);
		cmp_err = err_detect();
		if (cmp_err != 0)
			printf("  (int) Error: 0x%x\n", cmp_err);

		// data copy from sw lfsr to destination for 32 bit
		err = dma_memcpy_size(w_dst, w_src, TESTLEN, SZ32);

		// compare hw-sw lfsr values for 32 bit
		if (err) {
			printf("  (int) DMA (bus) error\n");
			fail = 1;
		} else if ((0 && cmp_err) || memcmp(lfsr_state_hw_2, w_dst, TESTLEN) != 0) {
			printf("  (int) No match between SW and HW LFSR values!\n");
			fail = 1;
		} // else printf("  (int) LFSR Matches\n");

		if (!fail) {
			err = dma_memcpy_noninc(w_dst, w_src, 4, SZ32);
			if (err) {
				printf("  (int) DMA (bus) error\n");
				fail = 1;
			} else if (0 != memcmp(w_dst, w_src, 4)) {
				printf("FAIL!\n");
				fail = 1;
			} else
				printf("PASS\n");
		}

		// 32b edge casez: transfer_len = 1, 2, .., 15
		offset_addr = 8;
		for(transfer_len = 1; transfer_len < 16 && !fail; transfer_len++) {
			err = dma_memcpy_size(w_dst, w_src + offset_addr, transfer_len, SZ32);
			if (err) {
				printf("  (int) DMA (bus) error\n");
				fail = 1;
			} else if (0 != memcmp(w_dst, w_src + offset_addr, transfer_len)) {
				printf("FAIL!\n");
				fail = 1;
			} else
				printf("PASS\n");

			offset_addr++;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus width test
	// {{{
	if (!fail) {
		printf("Basic MEMCPY( BUS): \n");

		// compare hw-sw lfsr values for 64 bit
		s_size = S_BUS;
		lfsr_state = 0xdeadbeaf;
		init_lfsr(lfsr_state);
		for(int i = 0; i < TESTLEN; i++) {
			lfsr_state = lfsr_shift(lfsr_state);
			to_int(lfsr_state, w_src[i]);
			lfsr_state_hw_2[i] = read_lfsr_int();
			printf("(bus) LFSR    State: 0x%016lx\n", lfsr_state);
			printf("(bus) LFSR_SW State: 0x%08x\n", w_src[i]);
			printf("(bus) LFSR_HW State: 0x%08x\n", lfsr_state_hw_2[i]);
		}
		cmp_lfsr(&w_src[TESTLEN-1], s_size);
		cmp_err = err_detect();
		if (cmp_err != 0)
			printf("  (bus) Error: 0x%x\n", cmp_err);

		// data copy from sw lfsr to destination for 32 bit
		err = dma_memcpy_size(w_dst, w_src, TESTLEN, SZBUS);

		// compare hw-sw lfsr values for 32 bit
		if (err) {
			printf("  (bus) DMA (bus) error\n");
			fail = 1;
		} else if ((0 && cmp_err) || memcmp(lfsr_state_hw_2, w_dst, TESTLEN) != 0) {
			memdump(lfsr_state_hw_2, w_dst, TESTLEN);
			printf("  (bus) No match between SW and HW LFSR values!\n");
			fail = 1;
		} // else printf("  (bus) LFSR Matches\n");

		if (!fail) {
			err = dma_memcpy_noninc(w_dst, w_src, 8, SZBUS);
			if (err) {
				printf("  (bus) DMA (bus) error\n");
				fail = 1;
			} else if (0 != memcmp(w_dst, w_src, 8) != 0) {
				memdump(w_dst, w_src, 8);
				printf("FAIL!\n");
				fail = 1;
			} else
				printf("PASS\n");
		}

		// Bus width edge casez: transfer_len = 1, 2, .., 32
		offset_addr = 8;
		for(transfer_len = 1; transfer_len < 32 && !fail; transfer_len++) {
			err = dma_memcpy(w_dst, w_src + offset_addr, transfer_len);
			if (err) {
				printf("  (bus) DMA (bus) error\n");
				fail = 1;
			} else if (0 != memcmp(w_dst, w_src + offset_addr, transfer_len)) {
				memdump(w_dst, w_src + offset_addr, transfer_len);
				printf("FAIL!\n");
				fail = 1;
			} else
				printf("PASS\n");

			offset_addr++;
		}
	}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// obtain valid error signal
	// {{{
	if (!fail) {
		c_src = NULL;
		c_dst = NULL;

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
