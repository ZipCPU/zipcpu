////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilmemsim.cpp
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This creates a memory like device to act on an AXI-lite bus.
//		It doesn't exercise the bus thoroughly, but does give some
//	exercise to the bus to see whether or not the bus master can control it.
//	The formal proof should finish off anything not tested here.
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
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdint.h>
#include "byteswap.h"
#include "axilmemsim.h"

AXILMEMSIM::AXILMEMSIM(const unsigned int nwords, BUSW *memp) {
// {{{
	unsigned int	nxt;

	for(nxt=1; nxt < nwords; nxt<<=1)
		;
	m_len = nxt; m_mask = nxt-1;
	if (memp != NULL)
		m_mem = memp;
	else
		m_mem = new BUSW[m_len];
	m_nxt_rvalid = false;
	m_nxt_bvalid = false;
}
// }}}

AXILMEMSIM::~AXILMEMSIM(void) {
// {{{
	delete[]	m_mem;
}
// }}}

void	AXILMEMSIM::load(const char *fname) {
// {{{
	FILE	*fp;
	unsigned int	nr;

	fp = fopen(fname, "r");
	if (!fp) {
		fprintf(stderr, "Could not open/load file \'%s\'\n",
			fname);
		perror("O/S Err:");
		fprintf(stderr, "\tInitializing memory with zero instead.\n");
		nr = 0;
	} else {
		nr = fread(m_mem, sizeof(BUSW), m_len, fp);
		fclose(fp);

		if (nr != m_len) {
			fprintf(stderr, "Only read %d of %d words\n",
				nr, m_len);
			fprintf(stderr, "\tFilling the rest with zero.\n");
		}
	}

	for(; nr<m_len; nr++)
		m_mem[nr] = 0l;
}
// }}}

void	AXILMEMSIM::load(const unsigned addr, const char *buf, const unsigned len) {
// {{{
	extern FILE *gbl_dbgfp;


	if (gbl_dbgfp)
		fprintf(gbl_dbgfp, "AXILMEMSIM::LOAD(0x%08x, ..., %d)\n",
			addr, len);
	memcpy(&m_mem[addr], buf, len);
	byteswapbuf((len>>2), &m_mem[addr]);

	fprintf(gbl_dbgfp, "AXILMEMSIM[0] = 0x%08x\n", m_mem[0]);
}
// }}}

void	AXILMEMSIM::read(const uchar arvalid, uchar &arready,
				const BUSW araddr, const uchar arprot,
			uchar &rvalid, const uchar rready,
				BUSW &rdata, uchar &rresp) {
// {{{
	if (rvalid && !rready) {
		arready = 0;
		return;
	}

	BUSW addr = araddr >>2;

	arready = 1;
	rvalid = m_nxt_rvalid;
	rdata  = m_nxt_rdata;
	rresp  = 0;
	m_nxt_rvalid = 0;
	m_nxt_rdata  = 0;

	if (arvalid && arready) {
		extern FILE *gbl_dbgfp;

		m_nxt_rvalid = 1;
		m_nxt_rdata  = m_mem[addr & m_mask];

		if (gbl_dbgfp) {
			fprintf(gbl_dbgfp, "AXILMEMSIM::BUS = MEM[%08x & %08x = %08x] = %08x\n", addr, m_mask, addr&m_mask, m_nxt_rdata);
		}
	}
}
// }}}

void	AXILMEMSIM::write(const uchar awvalid, uchar &awready,
				const BUSW awaddr, const uchar awprot,
			const uchar wvalid, uchar &wready,
				const BUSW wdata, const BUSW wstrb,
			uchar &bvalid, const uchar bready,
				uchar &bresp) {

	awready = wready = 1;
	bresp = 0;

	if (bvalid && !bready) {
		awready = wready = 0;
		return;
	} bvalid = m_nxt_bvalid;
	m_nxt_bvalid = 0;

	if (awvalid != wvalid) {
		awready = wready = 0;
		return;
	}

	if (!awvalid && !wvalid)
		// Nothing to do, so return
		return;

	unsigned	sel = 0;
	BUSW addr = awaddr >>2;

	if (wstrb&0x8)
		sel |= 0x0ff000000;
	if (wstrb&0x4)
		sel |= 0x000ff0000;
	if (wstrb&0x2)
		sel |= 0x00000ff00;
	if (wstrb&0x1)
		sel |= 0x0000000ff;

	m_nxt_bvalid = 1;
	if (sel == 0xffffffffu)
		m_mem[addr & m_mask] = wdata;
	else {
		uint32_t memv = m_mem[addr & m_mask];
		memv &= ~sel;
		memv |= (wdata & sel);
		m_mem[addr & m_mask] = memv;
	}


	extern FILE *gbl_dbgfp;
	if (gbl_dbgfp)
		fprintf(gbl_dbgfp, "AXILMEMSIM::MEM[%08x] = %08x\n", addr&m_mask, wdata);
}

