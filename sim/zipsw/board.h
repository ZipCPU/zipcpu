////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/zipsw/board.h
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Describes the hardware available in the test bench, addresses,
//		structures, etc.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2025, Gisselquist Technology, LLC
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
#ifndef	BOARD_H
#define	BOARD_H
#include <stdint.h>
////////////////////////////////////////////////////////////////////////////////
//
// ZipCPU defines and macros
// {{{
//
/*
struct	ZIPSYS_S {
	unsigned	z_pic, z_wdt, z_wbus, z_apic,
			z_tma, z_tmb, z_tmc, z_jiffies,
			m_ck, m_mem, m_pf, m_icnt,
			u_ck, u_mem, u_pf, u_icnt;
};

typedef	struct	ZIPSYS_S	ZIPSYS, AXILP;
*/
typedef	struct	ZIPSYS	AXILP;
// #define	_HAVE_ZIPSYS	// We won't know
// #define	PIC	_zip->z_pic
// #define	_HAVE_ZIPSYS_DMA	// We won't know
// #define	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
// #define	SYSPIC(A)	(1<<(A))
// #define	ALTPIC(A)	(1<<(A))
// }}}

#define	CLKFREQHZ	100000000

////////////////////////////////////////////////////////////////////////////////
//
// SMP access
// {{{
typedef struct  SMP_S {
	volatile unsigned	c_control;
	volatile unsigned	c_unused_0[31];
	volatile unsigned	c_sreg[16];
	volatile unsigned	c_ureg[16];
	volatile unsigned	c_unused_1[64];
} SMP;

// }}}
////////////////////////////////////////////////////////////////////////////////
//
// Console
// {{{
typedef struct  CONSOLE_S {
	unsigned	u_setup;
	unsigned	u_fifo;
	unsigned	u_rx, u_tx;
} CONSOLE;

#define	_uart_txbusy	((_uart->u_fifo & 0x10000)==0)
#define	_uart_txidle	((_uart->u_tx   & 0x100)  ==0)
// }}}
////////////////////////////////////////////////////////////////////////////////
//
// (Optional) Scope
// {{{
typedef struct  SCOPE_S {
	unsigned	s_ctrl;
	unsigned	s_data;
} SCOPE;
// }}}

// (Optional) ZipDMA_Check
// {{{
typedef struct __attribute__((packed)) ZDMACHECK_S {
	char		z_data0[8];
	short		z_data1[4];
	unsigned	z_data2[2];
} ZDMACHECK;

typedef struct __attribute__((packed)) ZDMACHECKST_S {
	char		z_data0[8];
	short		z_data1[4];
	unsigned	z_data2[2];
} ZDMACHECKST;

#define	SCOPE_NO_RESET	0x80000000u
#define	SCOPE_STOPPED	0x40000000u
#define	SCOPE_TRIGGERED	0x20000000u
#define	SCOPE_PRIMED	0x10000000u
#define	SCOPE_TRIGGER	(0x08000000u | SCOPE_NO_RESET)
#define	SCOPE_MANUAL	(SCOPE_TRIGGER)
#define	SCOPE_DISABLE	0x04000000u
// }}}

#define	_BOARD_HAS_BKRAM
extern char	_bkram[0x00100000];

static volatile SCOPE   *const _scope = ((SCOPE   *)0x01000000);
static volatile CONSOLE *const _uart  = ((CONSOLE *)0x02000000);
static volatile SMP     *const _smp   = ((SMP     *)0x03000000);
static volatile ZDMACHECK *const _zdmacheck = ((ZDMACHECK     *)0x09000000);
static volatile ZDMACHECKST *const _zdmastcheck  = ((ZDMACHECKST     *)0x0a000000);
static volatile AXILP   *const _axilp = ((AXILP   *)0xff000000);
// static volatile ZIPSYS  *const _zip   = ((ZIPSYS   *)0xff000000);
#define	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS

#endif	// BOARD_H
