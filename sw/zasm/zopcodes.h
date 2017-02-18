////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zopcodes.h
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	A structure defined to keep track of our various opcodes and
//		some of their shortcut synonyms.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
#ifndef	ZOPCODES_H
#define	ZOPCODES_H

#include <stdint.h>

// MACROS used in the instruction definition list.
#define	ZIP_OPUNUSED	-1
#define	ISUSEROP(A)	((a&(~0x0f))==0x000)
#define	ISSUPROP(A)	((a&(~0x0f))==0x010)
#define	ISLCLROP(A)	((a&(~0x0f))==0x020)
#define	ZIP_BITFIELD(LN,MN)	(((LN&0x0ff)<<8)+(MN&0x0ff)) // A generic bitfield
#define	ZIP_REGFIELD(MN)	(0x00000400 +(MN&0x0ff)) // Normal register field
#define	ZIP_URGFIELD(MN)	(0x0100400 +(MN&0x0ff))	// User register field
#define	ZIP_IMMFIELD(LN,MN)	(0x40000000 + (((LN&0x0ff)<<8)+(MN&0x0ff))) // Sgn extnd
#define	ZIP_SRGFIELD(MN)	(0x0200400 +(MN&0x0ff))
#define	ZIP_SP	0xd0000

typedef	uint32_t	ZIPI;	// A Zip CPU instruction

typedef	struct {
	char	s_opstr[8];	// OPCode name
	ZIPI	s_mask,		// Bits that must match 4 this pattern to match
		s_val;		// What those masked bits must be
	//
	// The following describe not the value, but the bits where there
	// respective vaules will be found within the instruction.  For example,
	// an instruction with no immediate will have an s_i value of -1
	// (ZIP_OPUNUSED), whereas an instruction with an immediate value of -1
	// might have an s_i value of ZIP_BITFIELD(14,0), or 0x0400.  The
	// opcode itself will tell you what the value is--not this structure
	// describing the opcode.
	//
	int	s_result,	// Register where the result will be placed
		s_ra,		// A register, often the result
		s_rb,		// B register, source operand (if used)
		s_i,		// Immediate value, added to B if B is used
		s_cf;		// Condition flags.
} ZOPCODE;

extern	const	char	*zip_regstr[49], *zip_ccstr[8];

extern	const ZOPCODE	*zip_oplist, *zip_opbottomlist;
extern	const int	nzip_oplist, nzip_opbottom;

// Disassemble an opcode
extern	void zipi_to_double_string(const uint32_t, const ZIPI, char *, char *);
extern	const	char	*zop_regstr[];
extern	const	char	*zop_ccstr[];
extern	unsigned int	zop_early_branch(const unsigned int pc, const ZIPI ins);

#endif
