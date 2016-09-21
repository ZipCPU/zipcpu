////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zparser.h
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This file is really mis-named.  At one time it was going to
//		be header file for the parser for the Zip Assembler, zasm. 
//		Since then, I discovered Flex and Bison and have written a
//		parser using those tools.  The true parser may therefore be
//		found in zasm.y.  This file, however, still declares some
//		very valuable tools.  In particular, all of the routines used
//		to build instructions from the appropriate fields are declared
//		in this file. 
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

#ifndef	ZPARSER_H
#define	ZPARSER_H

/*
 * LONG_MPY controls whether or not the instruction set has:
 *   (if not defined)
 * 	LDIHI	- load the value into the upper 16 bits of a register
 *	MPYS	- Multiplies two 16-bit values into a    signed 32-bit result
 *	MPYU	- Multiplies two 16-bit values into an unsigned 32-bit result
 *   (if defined)
 *	MPY	- Multiplies two 32-bit values and returns the lower 32-bits of
 *			the result.  Works for signed and unsigned values.
 *	MPYSHI	- Multiplies two 32-bit values and returns the upper 32-bits of
 *			the   signed 64-bit result
 *	MPYUHI	- Multiplies two 32-bit values and returns the upper 32-bits of
 *			the unsigned 64-bit result
 *
 */
#define	LONG_MPY

#include "zopcodes.h"

class	ZPARSER {
public:
	typedef	unsigned int	ZIPA;
	typedef	int	ZIPIMM;
	typedef	enum {
		ZIP_R0, ZIP_R1, ZIP_R2, ZIP_R3, ZIP_R4, ZIP_R5, ZIP_R6, ZIP_R7,
		ZIP_R8, ZIP_R9, ZIP_R10, ZIP_R11, ZIP_R12,
			ZIP_SP, ZIP_CC, ZIP_PC,
		ZIP_uR0, ZIP_uR1, ZIP_uR2, ZIP_uR3, ZIP_uR4, ZIP_uR5, ZIP_uR6, ZIP_uR7,
		ZIP_uR8, ZIP_uR9, ZIP_uR10, ZIP_uR11, ZIP_uR12,
			ZIP_uSP, ZIP_uCC, ZIP_uPC,
		ZIP_Rnone
	} ZIPREG;

	typedef	enum {
		ZIPC_ALWAYS, ZIPC_LT, ZIPC_Z, ZIPC_NZ,
		ZIPC_GT, ZIPC_GE, ZIPC_C, ZIPC_V
	} ZIPCOND;

	typedef	enum {
		// 16 ALU instructions
		ZIPO_SUB=0, ZIPO_AND, ZIPO_ADD, ZIPO_OR,	// 5'h000xx
		ZIPO_XOR, ZIPO_LSR, ZIPO_LSL, ZIPO_ASR,		// 5'h001xx
#ifdef	LONG_MPY
		ZIPO_MPY, ZIPO_LDILO, ZIPO_MPYUHI, ZIPO_MPYSHI,	// 5'h010xx
#else
		ZIPO_LDIHI, ZIPO_LDILO, ZIPO_MPYU, ZIPO_MPYS,	// 5'h010xx
#endif
		ZIPO_BREV, ZIPO_POPC, ZIPO_ROL, ZIPO_MOV,	// 5'h011xx
		ZIPO_CMP, ZIPO_TST,				// 5'h1000x
		ZIPO_LOD, ZIPO_STO,				// 5'h1001w
		ZIPO_DIVU, ZIPO_DIVS,				// 5'h1010s
		ZIPO_LDI, ZIPO_LDIn,				// 5'h1011x
		// ZIPO_, ZIPO_DIVS,				// 5'h11000
		ZIPO_FPADD=0x18, ZIPO_FPSUB,			// 5'h1100x
		ZIPO_FPMUL, ZIPO_FPDIV,				// 5'h1101x
		ZIPO_FPCVT, ZIPO_FPINT,				// 5'h1110x
	} ZIPOP;

	ZIPIMM	brev(ZIPIMM) const;

	ZIPI	op_cmp(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_cmp(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_cmp(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_cmp(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_cmp(ZIPIMM imm, ZIPREG a) const
		{ return op_cmp(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_tst(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_tst(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_tst(ZIPIMM imm, ZIPREG a) const
		{ return op_tst(ZIPC_ALWAYS, imm, a); }
	ZIPI	op_tst(ZIPCOND cnd, ZIPREG a) const
		{ return op_tst(cnd, -1, a); }

	ZIPI	op_mov(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_mov(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_mov(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_mov(ZIPREG b, ZIPREG a) const
		{ return op_mov(ZIPC_ALWAYS, 0, b, a); }

	ZIPI	op_ldi(ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_trap(ZIPCOND cnd, ZIPIMM imm) const;
	ZIPI	op_trap(ZIPIMM imm) const
		{ return op_trap(ZIPC_ALWAYS, imm); }
	ZIPI	op_clr(ZIPREG a) const { return op_ldi(0, a); }

	ZIPI	op_noop(void) const;
	ZIPI	op_break(void) const;
	ZIPI	op_lock(void) const;

#ifdef	LONG_MPY
	ZIPI	op_mpy(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_mpy(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_mpy(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_mpy(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_mpy(ZIPIMM imm, ZIPREG a) const
		{ return op_mpy(ZIPC_ALWAYS, imm, a); }
#else
	ZIPI	op_ldihi(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_ldihi(ZIPIMM imm, ZIPREG a) const
		{ return op_ldihi(ZIPC_ALWAYS, imm, a); }
#endif
	ZIPI	op_ldilo(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_ldilo(ZIPIMM imm, ZIPREG a) const
		{ return op_ldilo(ZIPC_ALWAYS, imm, a); }

#ifdef LONG_MPY
	ZIPI	op_mpyuhi(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_mpyuhi(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_mpyuhi(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_mpyuhi(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_mpyuhi(ZIPIMM imm, ZIPREG a) const
		{ return op_mpyuhi(ZIPC_ALWAYS,imm,a); }
#else
	ZIPI	op_mpyu(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_mpyu(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_mpyu(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_mpyu(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_mpyu(ZIPIMM imm, ZIPREG a) const
		{ return op_mpyu(ZIPC_ALWAYS, imm, a); }
#endif
//

#ifdef	LONG_MPY
	ZIPI	op_mpyshi(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_mpyshi(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_mpyshi(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_mpyshi(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_mpyshi(ZIPIMM imm, ZIPREG a) const
		{ return op_mpyshi(ZIPC_ALWAYS, imm, a); }
#else
	ZIPI	op_mpys(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_mpys(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_mpys(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_mpys(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_mpys(ZIPIMM imm, ZIPREG a) const
		{ return op_mpys(ZIPC_ALWAYS, imm, a); }
#endif

	ZIPI	op_rol(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_rol(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_rol(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_rol(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_rol(ZIPIMM imm, ZIPREG a) const
		{ return op_rol(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_popc(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_popc(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_popc(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_popc(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_popc(ZIPIMM imm, ZIPREG a) const
		{ return op_popc(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_brev(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_brev(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_brev(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_brev(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_brev(ZIPIMM imm, ZIPREG a) const
		{ return op_brev(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_lod(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_lod(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_lod(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_lod(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_lod(ZIPIMM imm, ZIPREG a) const
		{ return op_lod(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_sto(ZIPCOND cnd, ZIPREG v, ZIPIMM imm, ZIPREG b) const;
	ZIPI	op_sto(ZIPCOND cnd, ZIPREG v, ZIPIMM imm) const;
	ZIPI	op_sto(ZIPREG v, ZIPIMM imm, ZIPREG b) const
		{ return op_sto(ZIPC_ALWAYS, v, imm, b); }
	ZIPI	op_sto(ZIPREG v, ZIPIMM imm) const
		{ return op_sto(ZIPC_ALWAYS, v, imm); }

	ZIPI	op_sub(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_sub(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_sub(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_sub(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_sub(ZIPIMM imm, ZIPREG a) const
		{ return op_sub(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_and(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_and(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_and(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_and(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_and(ZIPIMM imm, ZIPREG a) const
		{ return op_and(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_add(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_add(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_add(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_add(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_add(ZIPIMM imm, ZIPREG a) const	// GOOD
		{ return op_add(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_or(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_or(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_or(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_or(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_or(ZIPIMM imm, ZIPREG a) const
		{ return op_or(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_xor(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_xor(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_xor(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_xor(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_xor(ZIPIMM imm, ZIPREG a) const
		{ return op_xor(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_lsl(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_lsl(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_lsl(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_lsl(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_lsl(ZIPIMM imm, ZIPREG a) const
		{ return op_lsl(ZIPC_ALWAYS, imm, a); }
	ZIPI	op_asl(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_lsl(cnd, imm, b, a); }
	ZIPI	op_asl(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const
		{ return op_lsl(cnd, imm, a); }
	ZIPI	op_asl(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_lsl(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_asl(ZIPIMM imm, ZIPREG a) const
		{ return op_lsl(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_asr(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_asr(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_asr(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_asr(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_asr(ZIPIMM imm, ZIPREG a) const
		{ return op_asr(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_lsr(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_lsr(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_lsr(ZIPIMM imm, ZIPREG b, ZIPREG a) const
		{ return op_lsr(ZIPC_ALWAYS, imm, b, a); }
	ZIPI	op_lsr(ZIPIMM imm, ZIPREG a) const
		{ return op_lsr(ZIPC_ALWAYS, imm, a); }

	ZIPI	op_bra(ZIPCOND cnd, ZIPIMM imm) const
		{ return op_add(cnd, imm, ZIP_PC); }
	ZIPI	op_bra(ZIPIMM imm) const
		{ return op_add(ZIPC_ALWAYS, imm, ZIP_PC); }
	ZIPI	op_brz(ZIPIMM imm) const
		{ return op_add(ZIPC_Z, imm, ZIP_PC); }
	ZIPI	op_bnz(ZIPIMM imm) const
		{ return op_add(ZIPC_NZ, imm, ZIP_PC); }
	ZIPI	op_bge(ZIPIMM imm) const
		{ return op_add(ZIPC_GE, imm, ZIP_PC); }
	ZIPI	op_bgt(ZIPIMM imm) const
		{ return op_add(ZIPC_GT, imm, ZIP_PC); }
	ZIPI	op_blt(ZIPIMM imm) const
		{ return op_add(ZIPC_LT, imm, ZIP_PC); }
	ZIPI	op_brc(ZIPIMM imm) const
		{ return op_add(ZIPC_C, imm, ZIP_PC); }
	ZIPI	op_brv(ZIPIMM imm) const
		{ return op_add(ZIPC_V, imm, ZIP_PC); }
	ZIPI	op_bv(ZIPIMM imm) const
		{ return op_brv(imm); }

	ZIPI	op_clrf(ZIPCOND cnd, ZIPREG a) const
		{ return op_xor(cnd, 0, a, a); }
	ZIPI	op_clrf(ZIPREG a) const
		{ return op_xor(ZIPC_ALWAYS, 0, a, a); }
	// ZIPI	op_retn(ZIPCOND c) const
		// { return op_lod(c, 1, ZIP_SP, ZIP_PC); }
	ZIPI	op_halt(ZIPCOND c) const {
		return op_or(c, 0x10, ZIP_CC); }
	ZIPI	op_wait(ZIPCOND c) const {
		return op_or(c, 0x30, ZIP_CC); }
	ZIPI	op_halt(void) const {
		return op_or(ZIPC_ALWAYS, 0x10, ZIP_CC); }
	ZIPI	op_wait(void) const {
		return op_or(ZIPC_ALWAYS, 0x10, ZIP_CC); }
	ZIPI	op_busy(ZIPCOND c) const {
		return op_add(c, -1, ZIP_PC); }
	ZIPI	op_busy(void) const {
		return op_add(ZIPC_ALWAYS, -1, ZIP_PC); }

	ZIPI	op_rtu(void) const {
		return op_or(ZIPC_ALWAYS, 0x20, ZIP_CC); }
	ZIPI	op_rtu(ZIPCOND cnd) const {
		return op_or(cnd, 0x20, ZIP_CC); }

	ZIPI	op_jmp(ZIPCOND c, ZIPIMM imm, ZIPREG r) const
		{ return op_mov(ZIPC_ALWAYS, imm, r, ZIP_PC); }

	ZIPI	op_ljmp(void) const { return 0x7c87c000; }

	ZIPI	op_ljmp(ZIPCOND c, ZIPIMM imm) const {
		return op_add(ZIPC_ALWAYS, imm, ZIP_PC); }

	ZIPI	op_not(ZIPCOND c, ZIPREG r) const
		{ return op_xor(c, -1, r); }
	ZIPI	op_not(ZIPREG r) const
		{ return op_xor(ZIPC_ALWAYS, -1, r); }

	ZIPI	op_divu(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_divu(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;
	ZIPI	op_divs(ZIPCOND cnd, ZIPIMM imm, ZIPREG b, ZIPREG a) const;
	ZIPI	op_divs(ZIPCOND cnd, ZIPIMM imm, ZIPREG a) const;

	bool	can_merge(const ZIPI a, const ZIPI b);
	ZIPI	merge(const ZIPI a, const ZIPI b);
	ZIPIMM	immediate(const ZIPI a);

};

#endif
