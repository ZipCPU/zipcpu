////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zipsys.h
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
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
#ifndef	ZIPSYS_H
#define	ZIPSYS_H

typedef	struct	{
	unsigned	ac_ck, ac_mem, ac_pf, ac_icnt;
} ZIPTASKCTRS;

typedef	struct	{
	unsigned	d_ctrl;
	char		*d_rd, *d_wr;
	unsigned	d_len;
} ZIPDMA;

#define	DMA_TRIGGER	0x20000000
#define	DMACABORT	0x41425254
#define	DMACLEAR	0x40000000
#define	DMACERR		0x40000000
#define	DMAREQUEST	0x40000000
//
#define	DMA_CONSTSRC	0x00040000
#define	DMA_SRCBYTE	0x00030000
#define	DMA_SRCSHORT	0x00020000
#define	DMA_SRCWORD	0x00010000
#define	DMA_SRCWIDE	0x00000000
//
#define	DMA_CONSTDST	0x00400000
#define	DMA_DSTBYTE	0x00300000
#define	DMA_DSTSHORT	0x00200000
#define	DMA_DSTWORD	0x00100000
#define	DMA_DSTWIDE	0x00000000
#define	DMACCOPY	(DMAREQUEST|DMACLEAR|DMA_SRCWIDE|DMA_DSTWIDE)
#define	DMAONEATATIME	(DMAREQUEST|DMACLEAR|DMA_SRCBYTE|DMA_DSTBYTE|1)
#define	DMA_BUSY	0x80000000
#define	DMA_ERR		0x40000000
#define	DMA_ONINT(INT)	(DMA_TRIGGER|(((INT)&31)<<24))
#define	DMA_ONJIFFIES	DMA_ONINT(1)
#define	DMA_ONTMC	DMA_ONINT(2)
#define	DMA_ONTMB	DMA_ONINT(3)
#define	DMA_ONTMA	DMA_ONINT(4)
#define	DMA_ONAUX	DMA_ONINT(5)

#define	TMR_INTERVAL	0x80000000
typedef	struct	{
	int	z_pic, z_wdt, z_wbus, z_apic, z_tma, z_tmb, z_tmc,
		z_jiffies;
#ifdef	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
	ZIPTASKCTRS	z_m, z_u;
#else
	unsigned	z_nocounters[8];
#endif
#ifdef	_HAVE_ZIPSYS_DMA
	ZIPDMA		z_dma;
#else
	unsigned	z_nodma[4];
#endif
} ZIPSYS;

#define	ZIPSYS_ADDR	0xff000000

#define	SYSINT_DMAC	0x0001
#define	SYSINT_JIFFIES	0x0002
#define	SYSINT_TMC	0x0004
#define	SYSINT_TMB	0x0008
#define	SYSINT_TMA	0x0010
#define	SYSINT_AUX	0x0020
//
#define	SYSINT(INTID)	(1<<(INTID))
#define	ALTINT(INTID)	(1<<(INTID))

#ifdef	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
#define	ALTINT_UIC	ALTINT(0)
#define	ALTINT_UTC	ALTINT(3)
#define	ALTINT_MIC	ALTINT(4)
#define	ALTINT_MTC	ALTINT(7)
#endif

#define	INT_ENABLE	0x80008000
#define	EINT(A)	(INT_ENABLE|((A)<<16))
#define	DINT(A)	((A)<<16)
#define	CLEARPIC	0x7fff7fff
#define	DALLPIC		0x7fff0000	// Disable all PIC interrupt sources
#define	INTNOW		0x08000

static	volatile ZIPSYS *const _zip = (ZIPSYS *)(ZIPSYS_ADDR);

static inline void	DISABLE_INTS(void) {
	_zip->z_pic = 0x80000000;
}

static inline void	ENABLE_INTS(void) {
	_zip->z_pic = INT_ENABLE;
}

typedef	struct	{
	int	c_r[16];
#ifdef	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
	unsigned long	c_ck, c_mem, c_pf, c_icnt;
#endif
} ZSYSCONTEXT;

#ifdef	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
void	save_contextncntrs(ZSYSCONTEXT *c);
void	restore_contextncntrs(ZSYSCONTEXT *c);
#else
#define	save_contextncntrs(CONTEXT)	save_context((int *)CONTEXT)
#define	restore_contextncntrs(CONTEXT)	restore_context((int *)CONTEXT)
#endif

#endif
