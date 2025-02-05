////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/zipsw/zlib/zipcpu.h
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Declare the capabilities and memory structure of the ZipSystem
//		for programs that must interact with it.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2025, Gisselquist Technology, LLC
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
// }}}
#ifndef	ZIPCPU_H
#define	ZIPCPU_H

#define	CC_Z		0x0001
#define	CC_C		0x0002
#define	CC_N		0x0004
#define	CC_V		0x0008
#define	CC_SLEEP	0x0010
#define	CC_GIE		0x0020
#define	CC_STEP		0x0040
#define	CC_BREAK	0x0080
#define	CC_ILL		0x0100
#define	CC_TRAP		0x0200
#define	CC_BUSERR	0x0400
#define	CC_DIVERR	0x0800
#define	CC_FPUERR	0x1000
#define	CC_IPHASE	0x2000
#define	CC_MMUERR	0x8000
#define	CC_FAULT	(CC_ILL|CC_BUSERR|CC_DIVERR|CC_FPUERR)
#define	CC_EXCEPTION	(CC_BREAK|CC_FAULT|CC_MMUERR)

#define	CLEAR_ICACHE	asm("OR 16384,CC")
#define	CLEAR_DCACHE	asm("OR 32768,CC")
#define	CLEAR_CACHE	asm("OR 49152,CC")

// extern void	zip_break(void);
#define	zip_break()		asm("BREAK\n")
// #define	BREAK(ID)	asm("BREAK " ##ID "\n")
#define	GETUREG(A,ID)	asm volatile ("MOV " ID ",%0" : "=r"(A))
#define	SETUREG(A,ID)	asm("MOV %0," ID : : "r"(A))
#define	NSTR(A)		asm("NSTR \"" A "\\n\"")
#define	NVAL(V)		do { unsigned tmp = (unsigned)(V); asm volatile("NDUMP %0":"=r"(tmp):"0"(tmp)); } while(0)
#define	NEXIT(V)	do { unsigned tmp = (unsigned)(V); asm volatile("NEXIT %0":"=r"(tmp)); } while(0)
extern void	zip_rtu(void);
extern void	zip_halt(void);
extern void	zip_idle(void);
extern void	zip_syscall(void);
extern void	zip_restore_context(void *);
extern void	zip_save_context(void *);
extern int	zip_bitrev(int v);
extern unsigned	zip_cc(void);
extern unsigned	zip_ucc(void);

extern	void	save_context(int *);
extern	void	restore_context(int *);
extern	int	syscall(int,int,int,int);

#ifndef	NULL
#define	NULL	((void *)0)
#endif

#define	ASMFNSTR(A)	"\t.section\t.text\n\t.global\t" A "\n\t.type\t" A ",@function\n" A ":\n"

#endif
