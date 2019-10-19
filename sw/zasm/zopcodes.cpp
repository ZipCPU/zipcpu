////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zopcodes.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	A simple program to handle the disassembly and definition
//		of the various Zip Assembly opcodes.  The primary function
//	of this file is the zipi_to_double_string, or Zip Instruction to a
//	pair of strings (disassemble) conversion.  The pair of strings is
//	necessary since Zip instruction words may contain two separate
//	instructions.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
//
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <stdio.h>
#include <strings.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include "twoc.h"
#include "zopcodes.h"

const	char	*zip_regstr[] = {
	"R0", "R1", "R2", "R3",
	"R4", "R5", "R6", "R7",
	"R8", "R9", "R10","R11",
	"R12","SP", "CC", "PC",
	"uR0", "uR1", "uR2", "uR3",
	"uR4", "uR5", "uR6", "uR7",
	"uR8", "uR9", "uR10", "uR11",
	"uR12", "uSP", "uCC", "uPC",
	"sR0", "sR1", "sR2", "sR3",
	"sR4", "sR5", "sR6", "sR7",
	"sR8", "sR9", "sR10","sR11",
	"sR12","sSP", "sCC", "sPC", "rILL"
};

const	char	*zip_ccstr[8] = {
	"",  ".Z",  ".LT", ".C",
	".V",".NZ", ".GE", ".NC"
};

static const ZOPCODE	zip_oplist_raw[] = {
	// Special case instructions.  These are general instructions, but with
	// special opcodes
	// Conditional branches
	//	0.1111.0111.ccc.0.111.10iiiii--
	//	0111 1011 11cc c011 110i iiii iiii iiii
	{ "BUSY", 0xffc7ffff, 0x7883ffff, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	{ "BZ",  0xfffc0000, 0x78880000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BLT", 0xfffc0000, 0x78900000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BC",  0xfffc0000, 0x78980000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BV",  0xfffc0000, 0x78a00000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BNZ",  0xfffc0000, 0x78a80000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BGE",  0xfffc0000, 0x78b00000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BNC",  0xfffc0000, 0x78b80000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_OPUNUSED },
	{ "BRA",  0xffc40000, 0x78800000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	// Changes/updates to CC, based upon LDI
	{ "TRAP", 0xfffffff0, 0x76000000, ZIP_OPUNUSED,ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	{ "TRAP", 0xff800000, 0x76000000, ZIP_OPUNUSED,ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	// BREV based traps
	{ "TRAP", 0xffc7ffff, 0x72000000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	// LDILO based traps
	{ "TRAP",0xffc4ffff, 0x72400000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	{ "TRAP",0xffc40000, 0x72400000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	// CLR -- a LDI of zero
	//	0.rrrr.1100.iiiiiii--
	//	0rrr r110 0...
	{ "CLR",  0x87ffffff, 0x06000000, ZIP_REGFIELD(27),ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	// BREV based clears
	{ "CLR", 0x87c7ffff, 0x02000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	// HALT
	//	0.1110.00011.ccc.0.0000000000010
	//	0111.0000.11cc.c000.0000.0000.0000.0010
	{ "HALT", 0xffc7ffff, 0x70c00010, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	// The "wait" instruction is identical, with the only difference being
	// the interrrupt context of the processor.  Well, almost.  To
	// facilitate waits from supervisor mode, the wait instruction
	// explicitly forces the CPU into user mode.
	{ "WAIT", 0xffc7ffff, 0x70c00030, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	// 1.0011.11000.000.0000...... 5f ? A carefully chosen illegal insn ??
	// "INT", 0xff10007f, 0x9e00005f, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19),
	// Return to user space
	{ "RTU", 0xffc7ffff, 0x70c00020, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	// The return instruction: JMP R0 (possibly conditional) = MOV R0,PC
	{ "RTN", 0xffc7ffff, 0x7b400000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	// JMP (possibly a conditional jump, if not covered by branches above)
	// 0.1111.01101.ccc.a.rrrr.biiiiiiiiiiiiiiii
	// 0111.1011.01cc.c0rr.rrbi.iiii.iiii.iiii		MOV x,PC
	{ "JMP",  0xffc40000, 0x7b400000, ZIP_OPUNUSED,ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(13,0), ZIP_BITFIELD(3,19) },
	// 0.1111.1100.ii.iiii.iiii.iiii.iiii.iiii.iiii
	// 0111.1110.0iii.iiii.iiii.iiii.iiii.iiii		LDI x,PC
	{ "JMPI", 0xff800000, 0x7e000000, ZIP_REGFIELD(27),ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(23,0), ZIP_OPUNUSED },
	// 0.1111.10010.000.1.1111.000000000000000
	// 0111.1100.1000.0111.11ii.iiii.iiii.iiii		LOD (PC),PC
	{ "LJMP", 0xffffffff, 0x7c87c000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	// NOT : XOR w/ -1
	//	0.rrrr.00100.ccc.0111.11111111111
	//	0rrr.r001.00cc.c011.f.f.f.f
	// { "NOT", 0x87c7ffff, 0x0103ffff, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	// General instructions
	// 0rrr.rooo.oocc.cxrr.rrii.iiii.iiii.iiii
	{ "SUB", 0x87c40000, 0x00000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "SUB", 0x87c40000, 0x00040000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "AND", 0x87c40000, 0x00400000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "AND", 0x87c40000, 0x00440000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "ADD", 0x87c40000, 0x00800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "ADD", 0x87c40000, 0x00840000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "OR",	0x87c40000, 0x00c00000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "OR",	0x87c40000, 0x00c40000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "XOR", 0x87c40000, 0x01000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "XOR", 0x87c40000, 0x01040000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "LSR", 0x87c40000, 0x01400000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "LSR", 0x87c40000, 0x01440000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "LSL", 0x87c40000, 0x01800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "LSL", 0x87c40000, 0x01840000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "ASR", 0x87c40000, 0x01c00000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "ASR", 0x87c40000, 0x01c40000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "BREV",0x87c40000, 0x02000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "BREV",0x87c40000, 0x02040000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "LDILO",0x87c40000, 0x02400000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "LDILO",0x87c40000, 0x02440000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	//
	{ "MPYUHI", 0x87c40000, 0x02800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "MPYUHI", 0x87c40000, 0x02840000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "MPYSHI", 0x87c40000, 0x02c00000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "MPYSHI", 0x87c40000, 0x02c40000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "MPY", 0x87c40000, 0x03000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "MPY", 0x87c40000, 0x03040000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "MOV", 0x87c42000, 0x03400000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(13,0), ZIP_BITFIELD(3,19) },
	{ "MOV", 0x87c42000, 0x03440000, ZIP_URGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(13,0), ZIP_BITFIELD(3,19) },
	{ "MOV", 0x87c42000, 0x03402000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_URGFIELD(14), ZIP_IMMFIELD(13,0), ZIP_BITFIELD(3,19) },
	{ "MOV", 0x87c42000, 0x03442000, ZIP_URGFIELD(27), ZIP_OPUNUSED, ZIP_URGFIELD(14), ZIP_IMMFIELD(13,0), ZIP_BITFIELD(3,19) },
	//
	{ "DIVU", 0x87c40000, 0x03800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "DIVU", 0x87c40000, 0x03840000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "DIVS", 0x87c40000, 0x03c00000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "DIVS", 0x87c40000, 0x03c40000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "CMP", 0x87c40000, 0x04000000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "CMP", 0x87c40000, 0x04040000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	{ "TST", 0x87c40000, 0x04400000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "TST", 0x87c40000, 0x04440000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "LW", 0x87c40000, 0x04800000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "LW", 0x87c40000, 0x04840000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "SW", 0x87c40000, 0x04c00000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "SW", 0x87c40000, 0x04c40000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "LH", 0x87c40000, 0x05000000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "LH", 0x87c40000, 0x05040000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "SH", 0x87c40000, 0x05400000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "SH", 0x87c40000, 0x05440000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "LB", 0x87c40000, 0x05800000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "LB", 0x87c40000, 0x05840000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	{ "SB", 0x87c40000, 0x05c00000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "SB", 0x87c40000, 0x05c40000, ZIP_OPUNUSED, ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	// 0rrr.r101.1
	{ "LDI",  0x87800000, 0x06000000, ZIP_REGFIELD(27),ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(23,0), ZIP_OPUNUSED },
	// 0111.x111.00.xxxxxxxx
	{ "BRK",   0xf7ffffff, 0x77000000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	{ "BRK",   0xf7c00000, 0x77000000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(22,0), ZIP_OPUNUSED },
	{ "LOCK",  0xf7ffffff, 0x77400000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	{ "LOCK",  0xf7c00000, 0x77400000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(22,0), ZIP_OPUNUSED },
	// 0.111x.00000.xxx.xxx.xxxx.xxxx.xxxx.xxxx
	// 0111.x111.11.xxx.xxx.xxxx.xxxx.xxxx.xxxx
	// SNOOP = SIM w/ no argument(s)
	{ "SIM",  0xf7ffffff, 0x77800000, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SEXIT",0xf7ffffff, 0x77800100, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SEXIT",0xf7fffff0, 0x77800310, ZIP_OPUNUSED, ZIP_URGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SEXIT",0xf7ffffe0, 0x77800300, ZIP_OPUNUSED, ZIP_REGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SEXIT",0xf7ffff00, 0x77800100, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD( 8,0), ZIP_OPUNUSED },
	{ "SDUMP",0xf7ffffff, 0x778002ff, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SDUMP",0xf7fffff0, 0x77800200, ZIP_OPUNUSED, ZIP_REGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SDUMP",0xf7fffff0, 0x77800210, ZIP_OPUNUSED, ZIP_URGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SOUT", 0xf7fffff0, 0x77800230, ZIP_OPUNUSED, ZIP_URGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SOUT", 0xf7ffffe0, 0x77800220, ZIP_OPUNUSED, ZIP_REGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "SOUT", 0xf7ffff00, 0x77800400, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD( 8,0), ZIP_OPUNUSED },
	{ "SDUMP",0xf7ffff00, 0x77800200, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD( 8,0), ZIP_OPUNUSED },
	{ "SIM",  0xf7c00000, 0x77800000, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD(22,0), ZIP_OPUNUSED },
	{ "NOOP", 0xf7ffffff, 0x77c00000, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NEXIT",0xf7ffffff, 0x77c00100, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NEXIT",0xf7ffff00, 0x77c00100, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD( 8,0), ZIP_OPUNUSED },
	{ "NEXIT",0xf7fffff0, 0x77c00310, ZIP_OPUNUSED, ZIP_URGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NEXIT",0xf7ffffe0, 0x77c00300, ZIP_OPUNUSED, ZIP_REGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NDUMP",0xf7ffffff, 0x77c002ff, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NDUMP",0xf7fffff0, 0x77c00200, ZIP_OPUNUSED, ZIP_REGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NDUMP",0xf7fffff0, 0x77c00210, ZIP_OPUNUSED, ZIP_URGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },

	{ "NOUT", 0xf7fffff0, 0x77c00230, ZIP_OPUNUSED, ZIP_URGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NOUT", 0xf7ffffe0, 0x77c00220, ZIP_OPUNUSED, ZIP_REGFIELD(0), ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NOUT", 0xf7ffff00, 0x77c00400, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD( 8,0), ZIP_OPUNUSED },
	{ "NDUMP",0xf7ffff00, 0x77c00200, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_OPUNUSED,       ZIP_OPUNUSED },
	{ "NSIM", 0xf7c00000, 0x77c00000, ZIP_OPUNUSED, ZIP_OPUNUSED,    ZIP_OPUNUSED, ZIP_IMMFIELD(22,0), ZIP_OPUNUSED },
	//
	//
	// 0rrr.r11f.ffcc.cxrr.rrii.iiii.iiii.iiii
	{ "FPADD",0x87c43fff, 0x06840000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	{ "FPSUB",0x87c43fff, 0x06c40000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	{ "FPMPY",0x87c43fff, 0x07040000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	{ "FPDIV",0x87c43fff, 0x07440000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(14), ZIP_OPUNUSED, ZIP_BITFIELD(3,19) },
	{ "FPI2F",0x87c40000, 0x07800000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(18,0), ZIP_BITFIELD(3,19) },
	{ "FPI2F",0x87c40000, 0x07840000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	{ "FPF2I",0x87c40000, 0x07c40000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_REGFIELD(14), ZIP_IMMFIELD(14,0), ZIP_BITFIELD(3,19) },
	//
	//
	//
	//
	//
	//	16-bit instructions, high side
	//
	// 
	//	1.1111.00010.xcc.0iiii.xxxx.xxxxx.xxxxx
	//	1111.1000.10xc.c0ii.iixx.xxxx.xxxx.xxxx
	// Mask, val, result, Ra, Rb, I, condition (no conditions for OP_UNDER_TEST)
	// BRA: 1.1111.011.0.sssssss
	{ "BRA", 0xff800000, 0xf9000000, ZIP_OPUNUSED,     ZIP_OPUNUSED, ZIP_OPUNUSED,     ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	// CLR: 1.rrrr.110.00000000
	{ "CLR", 0x87ff0000, 0x86000000, ZIP_REGFIELD(27), ZIP_OPUNUSED, ZIP_OPUNUSED,     ZIP_OPUNUSED,       ZIP_OPUNUSED },
	// RTN: 1.1111.111.0.0000.000, MOV R0,Pc
	{ "RTN", 0xffff0000, 0xff800000, ZIP_OPUNUSED,     ZIP_OPUNUSED, ZIP_OPUNUSED,     ZIP_OPUNUSED,       ZIP_OPUNUSED },
	// JMP: 1.1111.111.0.rrrrsss
	{ "JMP", 0xff800000, 0xff000000, ZIP_REGFIELD(27),ZIP_OPUNUSED,  ZIP_REGFIELD(19), ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	// LJSR: 1.000_0.011_.0.111_1.001 ?.1111.110.1.1111.000
	// { "LJSR",0xffffffff, 0x83797ef8, ZIP_REGFIELD(27),ZIP_OPUNUSED, ZIP_REGFIELD(19), ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	//
	// 1.rrrr.000.0.sssssss
	// 1rrr.r000.0sss.ssss
	{ "SUB", 0x87800000, 0x80000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	// 1.rrrr.000.1.rrrrsss
	{ "SUB", 0x87800000, 0x80800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(19), ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	//
	// 1.rrrr.001.0.sssssss
	// 1.rrrr.001.1.rrrrsss
	{ "AND", 0x87800000, 0x81000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	{ "AND", 0x87800000, 0x81800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(19), ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	//
	// 1.rrrr.010.0.sssssss
	// 1.rrrr.010.1.rrrrsss
	{ "ADD", 0x87800000, 0x82000000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	{ "ADD", 0x87800000, 0x82800000, ZIP_REGFIELD(27), ZIP_REGFIELD(27), ZIP_REGFIELD(19), ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	//
	// 1.rrrr.011.a.rrrrsss
	{ "CMP", 0x87800000, 0x83000000, ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_OPUNUSED,     ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	{ "CMP", 0x87800000, 0x83800000, ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_REGFIELD(19), ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	//
	// 1.rrrr.100.0.sssssss
	// 1.rrrr.100.1.rrrrsss
	{ "LW", 0x87800000, 0x84000000,  ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_SP,            ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	{ "LW", 0x87800000, 0x84800000,  ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_REGFIELD(19),  ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	// 1.rrrr.101.ssssssss
	{ "SW", 0x87800000, 0x85000000,  ZIP_OPUNUSED,     ZIP_REGFIELD(27), ZIP_SP,            ZIP_IMMFIELD(7,16), ZIP_OPUNUSED },
	// 1.rrrr.110.0.sssssss
	{ "SW", 0x87800000, 0x85800000,  ZIP_OPUNUSED,     ZIP_REGFIELD(27), ZIP_REGFIELD(19),  ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	// 1.rrrr.110.iiiiiiii
	{ "LDI", 0x87000000, 0x86000000, ZIP_REGFIELD(27), ZIP_OPUNUSED,     ZIP_OPUNUSED,      ZIP_IMMFIELD(8,16), ZIP_OPUNUSED },
	// 1.rrrr.111.1.sssssss
	{ "MOV", 0x87800000, 0x87800000, ZIP_OPUNUSED,     ZIP_REGFIELD(27), ZIP_REGFIELD(19),  ZIP_IMMFIELD(3,16), ZIP_OPUNUSED },
	//
	// 1.rrrr.111.1.rrrrsss
	// Illegal instruction !!
	{ "ILLV", 0x80000000, 0x80000000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(32,16), ZIP_OPUNUSED },
	// Global illegal instruction
	{ "ILL", 0x00000000, 0x00000000,  ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(32,0),  ZIP_OPUNUSED }
};

static const ZOPCODE	zip_opbottomlist_raw[] = {
	//
	//
	//
	//	16-bit instructions, low side ... treat these as special
	//
	//
	// Mask, val, result, Ra, Rb, I, condition (no conditions for OP_UNDER_TEST)
	// BRA: 1.xxx_xxxx_xxxx_xxxx_?.111_1.011.0.sssssss
	{ "BRA", 0x80007f80, 0x80007900, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	// CLR: 1.xxx_xxxx_xxxx_xxxx_?.rrr_r.101.0000_0000
	{ "CLR", 0x800007ff, 0x80000600, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	// RTN: 1.1111.111.0.0000.000, MOV R0,Pc
	{ "RTN", 0x80007fff, 0x80007f80, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED },
	// JMP: 1.1111.111.0.rrrrsss
	{ "JMP", 0x80007f80, 0x80007f00, ZIP_REGFIELD(11),ZIP_OPUNUSED, ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	// LJMP: 1.xxx_xxxx_xxxx_xxxx_?.111_1.100._1.111_1.000
	{ "LJMP", 0x80007fff, 0x80007cf8, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	//
	// 1.rrrr.000.0.sssssss
	{ "SUB", 0x80000780, 0x80000000, ZIP_REGFIELD(11), ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	// 1.rrrr.000.1.rrrrsss
	{ "SUB", 0x80000780, 0x80000080, ZIP_REGFIELD(11), ZIP_REGFIELD(11), ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	//
	// 1.rrrr.001.0.sssssss
	// 1.rrrr.001.1.rrrrsss
	{ "AND", 0x80000780, 0x80000100, ZIP_REGFIELD(11), ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	{ "AND", 0x80000780, 0x80000180, ZIP_REGFIELD(11), ZIP_REGFIELD(11), ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	//
	// 1.rrrr.010.0.sssssss
	// 1.rrrr.010.1.rrrrsss
	{ "ADD", 0x80000780, 0x80000200, ZIP_REGFIELD(11), ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	{ "ADD", 0x80000780, 0x80000280, ZIP_REGFIELD(11), ZIP_REGFIELD(11), ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	//
	// 1.rrrr.011.a.rrrrsss
	{ "CMP", 0x80000780, 0x80000300, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	{ "CMP", 0x80000780, 0x80000380, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	//
	// 1.rrrr.100.0.sssssss
	// 1.rrrr.100.1.rrrrsss
	{ "LW", 0x80000780, 0x80000400, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_SP, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	{ "LW", 0x80000780, 0x80000480, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	// 1.rrrr.101.ssssssss
	{ "SW", 0x80000780, 0x80000500, ZIP_OPUNUSED, ZIP_REGFIELD(11), ZIP_SP, ZIP_IMMFIELD(7,0), ZIP_OPUNUSED },
	{ "SW", 0x80000780, 0x80000580, ZIP_OPUNUSED, ZIP_REGFIELD(11), ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	// 1.rrr_r.110.ssssssss
	{ "LDI", 0x80000700, 0x80000600, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(8,0), ZIP_OPUNUSED },
	// 1.rrr_r.111_.x.rrr_rsss
	{ "MOV", 0x80000780, 0x80000780, ZIP_REGFIELD(11), ZIP_OPUNUSED, ZIP_REGFIELD(3), ZIP_IMMFIELD(3,0), ZIP_OPUNUSED },
	//
	//
	// Illegal instruction !!
	{ "ILLV",	0x80000000, 0x80000000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(15,0), ZIP_OPUNUSED },
	{ "ILL",	0x00000000, 0x00000000, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_OPUNUSED, ZIP_IMMFIELD(15,0), ZIP_OPUNUSED }
};

const ZOPCODE	*zip_oplist = zip_oplist_raw,
		*zip_opbottomlist = zip_opbottomlist_raw;

const int	nzip_oplist = (sizeof(zip_oplist_raw)/sizeof(ZOPCODE));
const int	nzip_opbottom = (sizeof(zip_opbottomlist_raw)/sizeof(ZOPCODE));


static inline	int
TWOWORD_LOAD(uint32_t one, uint32_t two) {
	// BREV followed by LODILO
	if (((one&0x87c40000)==0x02000000)&&((two&0x87c40000)==0x02400000)
		// Must be to the same register too, and on the same condition
		&&(((one^two)&0xf8380000)==0))
		return 1;
	return 0;
}

static	inline	int
OFFSET_PC_MOV(uint32_t ins) {
	// 0.xxxx.01101.ccc.0.1111.0.iiiiiiiiiiiii
	// 0xxx.x011.01cc.c011.110i.iiii.iiii.iiii
	//
	return ((ins & 0x87c7e000)==0x0343c000);
}

static	inline	int
TWOWORD_LJMP(uint32_t iword) {
	// LJMP a long jump instruction, for which the address of the target
	// is found in the next word
	if (iword==0x7c87c000)
		return 1;
	// Now, the CIS form ... an
	// Unconditional LJMP in the second half word
	if ((iword&0x80007fff)==0x80007cf8)
		return 1;
	return 0;
}


static	inline	int
TWOWORD_JSR(uint32_t iword, uint32_t nxtword) {
	// First word moves the return address to R0
	if (iword != 0x0343c001)
		return 0;
	// Second word is a BRA statement to ... anywhere
	// 0.1111.00010.ccc.0.iiiiiiiiiiiiiiiiii
	// 0111.1000.10cc.c0ii.iiii.iiii.iiii.iiii
	if ((nxtword&0xffc40000) == 0x78800000)
		return 1;
	return 0;
}

static	inline	int
THREEWORD_LJSR(uint32_t iword, uint32_t nxtword) {
	// First word moves the return address to R0
	if (iword!=0x0343c002)
		return 0;
	// Second word is an LJMP statement
	if (nxtword==0x7c87c000)
		return 1;
	return 0;
}

static	inline	int
TWOWORD_CIS_JSR(uint32_t iword) {
	// MOV 2(PC) | LOD (PC),PC
	//
	// 1.0000.111.1.1111.010
	//			1.1111.100.1.1111.000
	if (iword == 0x87fafcf8)
		return 1;
	return 0;
}

static	inline	int
CIS_JSR(uint32_t iword __attribute__((unused)) ) {
	if (TWOWORD_CIS_JSR(iword))
		return 1;
	// MOV 1(PC) | MOV Rx,PC
	//
	// 1.0000.111.1.1111.001
	//			1.1111.111.1.xxxx.000
	if ((iword&0xffffff87) == 0x87f9ff80)
		return 1;
	// There is no code for this without CIS_OP_UNDER_TEST
	return 0;
}

static inline	int
POSSIBLE_TWOWORD_BEGINNING(uint32_t iword) {
	// Unconditional LJMP
	if (TWOWORD_LJMP(iword))
		return 1;
	// MOV 1(PC),PC
	if (iword == 0x0343c001)
		return 1;
	// MOV 2(PC),PC
	if (iword == 0x0343c002)
		return 1;
	if (CIS_JSR(iword))
		return 1;
	// The conditional LJMP is three words, which we don't handle ...
	// Any BREV command could be the beginning of a twoword instruction
	//
	// Of course, the point here is to determine whether we should (or need
	// to) read a second word from our read-memory function.  Reading a 
	// second word, given that the first is a BREV, isn't a problem since a
	// program can't end on/with a BREV instruction.
	//
	// BREV #,Rx
	if ((iword&0x87c40000)==0x02000000)
		return 1;
	return 0;
}


static uint32_t
zip_bitreverse(uint32_t v) {
	uint32_t r=0, b;
	for(b=0; b<32; b++, v>>=1)
		r = (r<<1)|(v&1);
	return r;
}

static inline	uint32_t
TWOWORD_VALUE(uint32_t one, uint32_t two) {
	return ((two&0x0ffff)|(zip_bitreverse(one&0x0ffff)));
}

static long
zip_sbits(const long val, const int bits) {
	long	r;

	r = val & ((1l<<bits)-1);
	if (r & (1l << (bits-1)))
		r |= (-1l << bits);
	return r;
}

static unsigned long
zip_ubits(const long val, const int bits) {
	unsigned long r = val & ((1l<<bits)-1);
	return r;
}

static	int
zip_getbits(const ZIPI ins, const int which)
{
	if (which & 0x40000000) {
		return zip_sbits(ins>>(which & 0x03f), (which>>8)&0x03f);
	} else { // if (which &0x03f)
		return zip_ubits(ins>>(which & 0x03f), (which>>8)&0x03f)
			+ ((which>>16)&0x0ff);
	}
}

static	void
zipi_to_halfstring(const uint32_t addr, const ZIPI ins, char *line, const ZOPCODE *listp) {

	if (OFFSET_PC_MOV(ins)) {
		int	cv = zip_getbits(ins, ZIP_BITFIELD(3,19));
		int	dv = zip_getbits(ins, ZIP_REGFIELD(27));
		int	iv = zip_sbits(ins, 13);
		uint32_t	ref;

		ref = (iv<<2) + addr + 4;

		sprintf(line, "%s%s", "MOV", zip_ccstr[cv]);
		sprintf(line, "%-11s", line);
		sprintf(line, "%s0x%08x", line, ref);
		sprintf(line, "%s,%s", line, zip_regstr[dv]);

		return;
	} else if (TWOWORD_CIS_JSR(ins)) {
		sprintf(line, "%-11s", "LJSR");
		return;
	} else if (CIS_JSR(ins)) {
		int ra = zip_getbits(ins, ZIP_REGFIELD(3));
		sprintf(line, "%-11s%s", "JSR", zip_regstr[ra]);
		return;
	}

	int	i;
	for(i=0; i<nzip_oplist; i++) {
		if (((~zip_oplist[i].s_mask)&zip_oplist[i].s_val)!=0) {
			printf("Instruction %d, %s, fails consistency check\n",
				i, zip_oplist[i].s_opstr);
			printf("%08x & %08x = %08x != %08x\n",
				zip_oplist[i].s_mask,
				zip_oplist[i].s_val,
				(~zip_oplist[i].s_mask)&zip_oplist[i].s_val,
				0);
			assert(((~zip_oplist[i].s_mask)&zip_oplist[i].s_val)==0);
		}
	} line[0] = '\0';
	for(i=0; (listp[i].s_mask != 0); i++) {
		// printf("%2d: %6s %08x & %08x == %08x\n",
			// i, zip_oplist[i].s_opstr, ins,
			// zip_oplist[i].s_mask, zip_oplist[i].s_val);
		if ((ins & listp[i].s_mask) == listp[i].s_val) {
			// Write the opcode onto our line
			sprintf(line, "%s", listp[i].s_opstr);
			if (listp[i].s_cf != ZIP_OPUNUSED) {
				int bv = zip_getbits(ins, listp[i].s_cf);
				strcat(line, zip_ccstr[bv]);
			} sprintf(line, "%-11s", line); // Pad it to 11 chars

			int	ra = -1, rb = -1, rr = -1, imv = 0;

			if (listp[i].s_result != ZIP_OPUNUSED)
				rr = zip_getbits(ins, listp[i].s_result);
			if (listp[i].s_ra != ZIP_OPUNUSED)
				ra = zip_getbits(ins, listp[i].s_ra);
			if (listp[i].s_rb != ZIP_OPUNUSED)
				rb = zip_getbits(ins, listp[i].s_rb);
			if (listp[i].s_i != ZIP_OPUNUSED)
				imv = zip_getbits(ins, listp[i].s_i);

			if ((listp[i].s_rb != ZIP_OPUNUSED)&&(rb == 15))
				imv <<= 2;

			// Treat stores special
			if ((strncasecmp("SW",listp[i].s_opstr, 2)==0)
				||(strncasecmp("SH",listp[i].s_opstr, 2)==0)
				||(strncasecmp("SB",listp[i].s_opstr, 2)==0)) {
				strcat(line, zip_regstr[ra]);
				strcat(line, ",");
					
				if (listp[i].s_i != ZIP_OPUNUSED) {
					if (listp[i].s_rb == ZIP_OPUNUSED)
						sprintf(&line[strlen(line)],
							"($%d)", imv);
					else if (imv != 0)
						sprintf(&line[strlen(line)],
							"$%d", imv);
				} if (listp[i].s_rb != ZIP_OPUNUSED) {
					sprintf(&line[strlen(line)],
						"(%s)", zip_regstr[rb]);
				}
			// Treat long jumps special
			} else if (strncasecmp("LJMP",listp[i].s_opstr, 3)==0) {
			// Treat relative jumps (branches) specially as well
			} else if ((toupper(listp[i].s_opstr[0]=='B'))
				&&(strcasecmp(listp[i].s_opstr,"BUSY")!=0)
				&&(strcasecmp(listp[i].s_opstr,"BREV")!=0)
				&&(strcasecmp(listp[i].s_opstr,"BRK")!=0)
				&&(addr != 0)) {
				// Branch instruction: starts with B and isn't
				// BREV (bit reverse), BRK (break), or 
				// BUSY
				uint32_t target = addr;

				target += zip_getbits(ins, listp[i].s_i)+4;
				sprintf(&line[strlen(line)], "@0x%08x", target);
			} else {
				int memop = 0;
				if (('L'==toupper(listp[i].s_opstr[0]))
					&&(('W'==toupper(listp[i].s_opstr[1]))
					 ||('H'==toupper(listp[i].s_opstr[1]))
					 ||('B'==toupper(listp[i].s_opstr[1])))
					&&(!listp[i].s_opstr[2]))
					memop = 1;

				if (listp[i].s_i != ZIP_OPUNUSED) {
					if((memop)&&(listp[i].s_rb == ZIP_OPUNUSED))
						sprintf(&line[strlen(line)],
							"($%d)", imv);
					else if((memop)&&(imv != 0))
						sprintf(&line[strlen(line)],
							"%d", imv);
					else if((!memop)&&((imv != 0)||(listp[i].s_rb == ZIP_OPUNUSED)))
						sprintf(&line[strlen(line)],
							"$%d%s", imv,
							(listp[i].s_rb!=ZIP_OPUNUSED)?"+":"");
				} if (listp[i].s_rb != ZIP_OPUNUSED) {
					if (memop)
						sprintf(&line[strlen(line)],
							"(%s)", zip_regstr[rb]);
					else
						strcat(line, zip_regstr[rb]);
				} if(((listp[i].s_i != ZIP_OPUNUSED)||(listp[i].s_rb != ZIP_OPUNUSED))
					&&((listp[i].s_ra != ZIP_OPUNUSED)||(listp[i].s_result != ZIP_OPUNUSED)))
					strcat(line, ",");

				if (listp[i].s_ra != ZIP_OPUNUSED) {
					strcat(line, zip_regstr[ra]);
				} else if (listp[i].s_result != ZIP_OPUNUSED) {
					strcat(line, zip_regstr[rr]);
				}
			}
			break;
		}
	} if (line[0] == '\0') {
		sprintf(line, "ILL %08x", ins);
	}
}

void
zipi_to_double_string(const uint32_t addr, const ZIPI ins, char *la, char *lb) {
	zipi_to_halfstring(addr, ins, la, zip_oplist);
	if (lb) {
		if ((ins & 0x80000000)&&(!CIS_JSR(ins))) {
			zipi_to_halfstring(addr, ins, lb, zip_opbottomlist);
		} else lb[0] = '\0';
	}
}

unsigned int	zop_early_branch(const unsigned int pc, const ZIPI insn) {
	if ((insn & 0xf8000000) != 0x78000000)
		return pc+4;
	if ((insn & 0xffc60000) == 0x78800000)	// BRA high bit clear
		return (pc + 4 + ((insn & 0x3ffff)<<2));
	if ((insn & 0xffc60000) == 0x78820000)	// BRA high bit set (negative)
		return (pc + 4 + ((0x40000 - (insn & 0x3ffff))<<2));
	return pc+4;
}


