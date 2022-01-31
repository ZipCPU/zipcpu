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
#define	R_ZIPDATA	0x00000061

#define	CPU_GO		0x0000
#define	CPU_RESET	0x0040
#define	CPU_INT		0x0080
#define	CPU_STEP	0x0100
#define	CPU_STALL	0x0200
#define	CPU_HALT	0x0400
#define	CPU_CLRCACHE	0x0800
#define	CPU_sR0		(0x0000|CPU_HALT)
#define	CPU_sSP		(0x000d|CPU_HALT)
#define	CPU_sCC		(0x000e|CPU_HALT)
#define	CPU_sPC		(0x000f|CPU_HALT)
#define	CPU_uR0		(0x0010|CPU_HALT)
#define	CPU_uSP		(0x001d|CPU_HALT)
#define	CPU_uCC		(0x001e|CPU_HALT)
#define	CPU_uPC		(0x001f|CPU_HALT)

#endif
