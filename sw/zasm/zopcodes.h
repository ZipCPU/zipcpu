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
#ifndef	ZOPCODES_H
#define	ZOPCODES_H

#define	ZIP_OPUNUSED	-1
#define	ISUSEROP(A)	((a&(~0x0f))==0x000)
#define	ISSUPROP(A)	((a&(~0x0f))==0x010)
#define	ISLCLROP(A)	((a&(~0x0f))==0x020)
#define	ZIP_BITFIELD(LN,MN)	(((LN&0x0ff)<<8)+(MN&0x0ff))
#define	ZIP_REGFIELD(MN)	(0x00000400 +(MN&0x0ff))
#define	ZIP_URGFIELD(MN)	(0x0100400 +(MN&0x0ff))
#define	ZIP_SRGFIELD(MN)	(0x0200400 +(MN&0x0ff))
#define	ZIP_IMMFIELD(LN,MN)	(0x40000000 + (((LN&0x0ff)<<8)+(MN&0x0ff))) // Sgn extnd
// #define	REGVAL(V)	((V & 0x0f)+0x020)

typedef	unsigned int	ZIPI;	// A Zip CPU instruction

typedef	struct {
	char	s_opstr[8];
	ZIPI	s_mask, s_val;
	int	s_result, s_ra, s_rb, s_i, s_cf;
} ZOPCODE;

extern	const ZOPCODE	zoplist[];
extern	const int	nzoplist;

// Disassemble an opcode
extern	void	zipi_to_string(const ZIPI ins, char *la, char *lb);
extern	const	char	*zop_regstr[];
extern	const	char	*zop_ccstr[];
extern	unsigned int	zop_early_branch(const unsigned int pc, const ZIPI ins);

#endif
