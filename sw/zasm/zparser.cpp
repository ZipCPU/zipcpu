////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zparser.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This file is really mis-named.  At one time it was going to
//		be the parser for the Zip Assembler, zasm.  Since then, I
//		discovered Flex and Bison and have written a parser using
//		those tools.  The true parser may therefore be found in zasm.y.
//		This file, however, still contains some very valuable tools.
//		In particular, all of the routines used to build instructions
//		from the appropriate fields are kept in this file.  For example,
//		op_noop() returns the instruction code for a NOOP  instruction.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015, Gisselquist Technology, LLC
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
////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <strings.h>
#include <assert.h>

#include "zparser.h"
#include "zopcodes.h"

#define	IMMOP(OP,CND,IMM,A) (((OP&0x01f)<<22)|((A&0x0f)<<27)|((CND&0x07)<<19) \
			| (IMM & 0x03ffff))

#define	DBLREGOP(OP,CND,IMM,B,A) (((OP&0x01f)<<22)|((A&0x0f)<<27)	\
			|((CND&0x07)<<19)|(1<<18)|((B&0x0f)<<14)	 \
			| (IMM & 0x03fff))

#define	LONG_MPY

ZPARSER::ZIPIMM	ZPARSER::brev(ZIPIMM v) const {
	unsigned r=0, b;

	for(b=0; b<32; b++, v>>=1)
		r = (r<<1)|(v&1);

	return r;
}

ZIPI	ZPARSER::op_cmp(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_CMP, cnd, imm, b, a);
}

ZIPI	ZPARSER::op_cmp(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_CMP, cnd, imm, a);
}


ZIPI	ZPARSER::op_tst(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_TST, cnd, imm, b, a);
} ZIPI	ZPARSER::op_tst(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_TST, cnd, imm, a);
}

ZIPI	ZPARSER::op_mov(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	ZIPI	in;

	in = (ZIPO_MOV)<<22;
	in |= ((a  &0x0f)<<27);
	in |= ((cnd&0x07)<<19);
	in |= ((b  &0x0f)<<14);
	in |= ( imm&0x01fff);


	if (b & 0x10)
		in |= (1<<13);
	if (a & 0x10)
		in |= (1<<18);
	return in;
}


ZIPI	ZPARSER::op_ldi(ZIPIMM imm, ZIPREG a) const {
	ZIPI	in;
	in = ((a&0x0f)<<27) | (ZIPO_LDI << 22) | (imm & ((1<<23)-1));
	return in;
}

ZIPI	ZPARSER::op_trap(ZIPCOND cnd, ZIPIMM imm) const {
	ZIPI	in;
	if (cnd != ZIPC_ALWAYS)
		return op_ldilo(cnd, imm, ZIP_CC);
	else
		return op_ldi(imm, ZIP_CC);
	// in  = ((0x4f)<<24)|((cnd&0x07)<<21)|(1<<20)|((0x0e)<<16);
	// in |= (imm & 0x0ffff);
	return in;
}

ZIPI	ZPARSER::op_noop(void) const {
	return 0x76000000;
} ZIPI	ZPARSER::op_break(void) const {
	return 0x76400000;
} ZIPI	ZPARSER::op_lock(void) const {
	return 0x76800000;
}

#ifdef	LONG_MPY
ZIPI	ZPARSER::op_mpy(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_MPY, cnd, imm, b, a);
} ZIPI	ZPARSER::op_mpy(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_MPY, cnd, imm, a);
}
#else
ZIPI	ZPARSER::op_ldihi(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	ZIPI	in = IMMOP(ZIPO_LDIHI, cnd, (imm & 0x0ffff), a);
	return in;
}
#endif
ZIPI	ZPARSER::op_ldilo(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	ZIPI	in = IMMOP(ZIPO_LDILO, cnd, (imm & 0x0ffff), a);
	return in;
}

#ifdef	LONG_MPY
ZIPI	ZPARSER::op_mpyuhi(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_MPYUHI, cnd, imm, b, a);
} ZIPI	ZPARSER::op_mpyuhi(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_MPYUHI, cnd, imm & 0x0ffff, a);
}

ZIPI	ZPARSER::op_mpyshi(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_MPYSHI, cnd, imm, b, a);
} ZIPI	ZPARSER::op_mpyshi(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_MPYSHI, cnd, imm & 0x0ffff, a);
}
#else
ZIPI	ZPARSER::op_mpyu(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_MPYU, cnd, imm, b, a);
} ZIPI	ZPARSER::op_mpyu(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_MPYU, cnd, imm & 0x0ffff, a);
}

ZIPI	ZPARSER::op_mpys(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_MPYS, cnd, imm, b, a);
} ZIPI	ZPARSER::op_mpys(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_MPYS, cnd, imm & 0x0ffff, a);
}
#endif

ZIPI	ZPARSER::op_rol(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_ROL, cnd, imm, b, a);
} ZIPI	ZPARSER::op_rol(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_ROL, cnd, imm, a);
}

ZIPI	ZPARSER::op_popc(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_POPC, cnd, imm, b, a);
} ZIPI	ZPARSER::op_popc(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_POPC, cnd, imm, a);
}

ZIPI	ZPARSER::op_brev(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_BREV, cnd, imm, b, a);
} ZIPI	ZPARSER::op_brev(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_BREV, cnd, imm, a);
}

ZIPI	ZPARSER::op_lod(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_LOD, cnd, imm, b, a);
} ZIPI	ZPARSER::op_lod(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_LOD, cnd, imm, a);
}


ZIPI	ZPARSER::op_sto(ZIPCOND cnd, ZIPREG v, ZIPIMM imm, ZIPREG b) const {
	return DBLREGOP(ZIPO_STO, cnd, imm, b, v);
} ZIPI	ZPARSER::op_sto(ZIPCOND cnd, ZIPREG v, ZIPIMM imm) const {
	return IMMOP(ZIPO_STO, cnd, imm, v);
}


ZIPI	ZPARSER::op_sub(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_SUB, cnd, imm, b, a);
} ZIPI	ZPARSER::op_sub(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	// While it seems like we might do well replacing a subtract immediate
	// with an add of the negative same, the conditions aren't the same
	// when doing so.  Hence this is an invalid substitution.
	// return IMMOP(0xa, cnd, -imm, a); // Do an add of the negative of imm
	return IMMOP(ZIPO_SUB, cnd, imm, a);
}


ZIPI	ZPARSER::op_and(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_AND, cnd, imm, b, a);
} ZIPI	ZPARSER::op_and(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_AND, cnd, imm, a);
}


ZIPI	ZPARSER::op_add(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_ADD, cnd, imm, b, a);
} ZIPI	ZPARSER::op_add(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_ADD, cnd, imm, a);
}


ZIPI	ZPARSER::op_or(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_OR, cnd, imm, b, a);
} ZIPI	ZPARSER::op_or(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_OR, cnd, imm, a);
}

ZIPI	ZPARSER::op_xor(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_XOR, cnd, imm, b, a);
} ZIPI	ZPARSER::op_xor(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_XOR, cnd, imm, a);
}

ZIPI	ZPARSER::op_lsl(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_LSL, cnd, imm, b, a);
} ZIPI	ZPARSER::op_lsl(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_LSL, cnd, imm, a);
}

ZIPI	ZPARSER::op_asr(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_ASR, cnd, imm, b, a);
} ZIPI	ZPARSER::op_asr(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_ASR, cnd, imm, a);
}

ZIPI	ZPARSER::op_lsr(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_LSR, cnd, imm, b, a);
} ZIPI	ZPARSER::op_lsr(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_LSR, cnd, imm, a);
}

ZIPI	ZPARSER::op_divu(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_DIVU, cnd, imm, b, a);
} ZIPI	ZPARSER::op_divu(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_DIVU, cnd, imm, a);
}

ZIPI	ZPARSER::op_divs(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const {
	return DBLREGOP(ZIPO_DIVS, cnd, imm, b, a);
} ZIPI	ZPARSER::op_divs(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const {
	return IMMOP(ZIPO_DIVS, cnd, imm, a);
}

ZPARSER::ZIPIMM	ZPARSER::immediate(const ZIPI a) {
	ZIPOP	op((ZIPOP)((a>>22)&0x01f));
	ZIPIMM	imm;
	
	switch(op) {
		case ZIPO_MOV:
			imm = (a & 0x0fff); if (a&0x1fff) imm |= -0x1000; break;
		case ZIPO_LDI:
			imm = (a & 0x03fffff); break;
		case ZIPO_LDIn:
			imm = (a & 0x03fffff); imm |= -0x200000; break;
		case ZIPO_LDILO:
#ifndef	LONG_MPY
		case ZIPO_LDIHI:
#endif
			imm = (a & 0x0ffff);   break;
		default:
			if (a & 0x040000) {
				imm = (a&0x3fff);
				if (a&0x2000) imm |= -0x02000;
			} else {
				imm = (a&0x3ffff);
				if (a&0x20000)
					imm |= -0x20000;
			}
	}

	return imm;
}

bool	ZPARSER::can_merge(const ZIPI a, const ZIPI b) {
	// 1. Can't merge anything that's already merged
	if ((a|b) & 0x80000000)
		return false;

	ZIPOP	opa((ZIPOP)((a>>22)&0x01f)), opb((ZIPOP)((b>>22)&0x01f));
	// 2. Conditions
	{
		ZIPCOND	ca((ZIPCOND)((a>>19)&0x07)),cb((ZIPCOND)((b>>19)&0x07));

		if ((opa == ZIPO_LDI)||(opa == ZIPO_LDIn))
			ca = ZIPC_ALWAYS;
		if ((opb == ZIPO_LDI)||(opb == ZIPO_LDIn))
			cb = ZIPC_ALWAYS;

		if ((ca == ZIPC_ALWAYS)&&(cb != ZIPC_ALWAYS))
			return false;
		if ((ca|cb) &0x04)
			return false;
		if ((ca != ZIPC_ALWAYS)&&((cb != ca)&&(cb != ZIPC_ALWAYS)))
			return false;
		// if ((ca != ZIPC_ALWAYS)||(cb != ZIPC_ALWAYS))
			// return false;
	}

	// 3. Moves ... only move if the move doesn't address user registers

	if ((opa == ZIPO_MOV)&&(a & ((1<<18)|(1<<13))))
		return false;
	if ((opb == ZIPO_MOV)&&(b & ((1<<18)|(1<<13))))
		return false;

	// 4. Immediates.  If Register + Immediate, the answer is No.
	ZIPIMM imma, immb;
	switch(opa) {
		case ZIPO_MOV:
			imma = (a & 0x03fff); if (a) return false; break;
		case ZIPO_LDI: case ZIPO_LDIn:
		case ZIPO_LDILO:
#ifndef	LONG_MPY
		case ZIPO_LDIHI:
#endif
			imma = immediate(a);   break;
		default:
			if (a & 0x040000) {
				imma = (a&0x3ffff);
				// if (a&0x20000) a |= -0x20000;
				if (imma != 0)
					return false;
			} else {
				imma = (a&0x3fff);
				if (a&0x2000) // Sign extension?
					imma |= -0x02000;
			}
	} switch(opb) {
		case ZIPO_MOV:
			immb = (b & 0x0fff); if (b) return false; break;
		case ZIPO_LDI: case ZIPO_LDIn:
		case ZIPO_LDILO:
#ifndef	LONG_MPY
		case ZIPO_LDIHI:
#endif
			immb = immediate(b);   break;
		default:
			if (b & 0x040000) {
				immb = (b&0x3fff);
				// if (b&0x2000) b |= -0x02000;
				if (immb != 0)
					return false;
			} else {
				immb = (b&0x3ffff);
				if (b&0x20000)
					immb |= -0x20000;
			}
	}

	if ((opa == ZIPO_LDI)||(opa == ZIPO_LDIn)
#ifndef	LONG_MPY
		||(opa == ZIPO_LDIHI)
#endif
		||(opa == ZIPO_LDILO)) {
		if ((imma > 15)||(imma < -16))
			return false;
	} else if ((imma > 7)||(imma < -8))
			return false;
	if ((opb == ZIPO_LDI)||(opb == ZIPO_LDIn)
#ifndef	LONG_MPY
		||(opb == ZIPO_LDIHI)
#endif
		||(opb == ZIPO_LDILO)) {
		if ((immb > 15)||(immb < -16))
			return false;
	} else if ((immb > 7)||(immb < -8))
			return false;

	return true;
}

ZIPI	ZPARSER::merge(const ZIPI a, const ZIPI b) {
	assert(can_merge(a, b));
	ZIPI	ni;

	ZIPCOND	ca( (ZIPCOND)((a>>19)&0x007)), cb( (ZIPCOND)((b>>19)&0x007));
	ZIPOP	opa((ZIPOP)((a>>25)&0x012)), opb((ZIPOP)((b>>22)&0x01f));

	if ((opa == ZIPO_LDI)||(opa == ZIPO_LDIn))
		ca = ZIPC_ALWAYS;
	if ((opb == ZIPO_LDI)||(opb == ZIPO_LDIn))
		cb = ZIPC_ALWAYS;

	ZIPIMM imma, immb;
	imma = immediate(a);
	immb = immediate(b);

	ni = (opa << 26)|(opb<<9)|0x80000000;
	if (ca != ZIPC_ALWAYS) {
		ni |= (ca << 19);
		if (cb == ca)
			ni |= (1<<21);
	}

	// The result register(s)
	ni |= (a & 0x78000000);
	ni |= ((b>>27)&0x0f)<<5;

	// Are we using the register form of opB?
	switch(opa) {
		case ZIPO_MOV: ni |= (a&0x078000); break; // Always a register
		case ZIPO_LDI: case ZIPO_LDIn:
		case ZIPO_LDILO:
#ifndef	LONG_MPY
		case ZIPO_LDIHI:
#endif
			ni |= (imma & 0x01f)<<14;
			break;
		default:
			if (a & 0x040000) {
				ni |= (a&0x078000);
			} else
				ni |= (imma & 0x0f)<<14;
	}

	switch(opb) {
		case ZIPO_MOV:
			ni |= ((b>>14)&0x0f)|0x10; break;
		case ZIPO_LDI: case ZIPO_LDIn:
		case ZIPO_LDILO:
#ifndef	LONG_MPY
		case ZIPO_LDIHI:
#endif
			ni |= (immb & 0x01f);
			break;
		default:
			if (b & 0x040000) {
				ni |= ((b>>14)&0x0f)|0x10;
			} else
				ni |= (immb & 0x0f);
	}

	return ni;
}
