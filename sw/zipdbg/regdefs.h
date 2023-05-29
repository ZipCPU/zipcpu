////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	regdefs.h
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a generic file that will need to be modified from one
//		board implementation of the ZIP CPU to another.  Specifically,
//	this file defines where items are on a WISHBONE bus.  In this case, the
//	Zip CPU debug addresses are found at 0x060 and 0x61--but they need not
//	be at those addresses in your application.  The Zip Debugger needs to
//	know these addresses in order to know what addresses to peek and poke
//	to control and access the Zip CPU.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2022, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#ifndef	REGDEFS_H
#define	REGDEFS_H

// Zip CPU Control and Debug registers
#define	R_ZIPCTRL	0x00000060
#define	R_ZIPREGS	(R_ZIPCTRL+32)
#define	R_ZIPUSER	(R_ZIPREGS+16)
#define	R_ZIPSYSTEM	(R_ZIPCTRL+64)

#define	CPU_GO		0x000
#define	CPU_HALT	0x001
#define	CPU_STEP	0x004
#define	CPU_RESET	0x008
#define	CPU_CLRCACHE	0x010
//
#define	R_ZIPS0		32
#define	R_ZIPSSP	45
#define	R_ZIPSCC	46
#define	R_ZIPSPC	47
#define	R_ZIPU0		48
#define	R_ZIPUSP	61
#define	R_ZIPUCC	62
#define	R_ZIPUPC	63

#endif
