////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memsim.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This creates a memory like device to act on a WISHBONE bus.
//		It doesn't exercise the bus thoroughly, but does give some
//		exercise to the bus to see whether or not the bus master
//		can control it.
//
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
#include <stdio.h>
#include <assert.h>
#include "memsim.h"

MEMSIM::MEMSIM(const unsigned int nwords) {
	unsigned int	nxt;
	for(nxt=1; nxt < nwords; nxt<<=1)
		;
	m_len = nxt; m_mask = nxt-1;
	m_mem = new BUSW[m_len];
	m_nxt_ack = 0;
}

MEMSIM::~MEMSIM(void) {
	delete[]	m_mem;
}

void	MEMSIM::load(const char *fname) {
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

void	MEMSIM::apply(const unsigned int clk, const unsigned char wb_cyc,
			const unsigned char wb_stb, const unsigned char wb_we,
			const BUSW wb_addr, const BUSW wb_data, 
			unsigned char &o_ack, unsigned char &o_stall, BUSW &o_data) {
	o_ack = m_nxt_ack;
	o_data= m_nxt_data;
	m_nxt_data = wb_data;
	o_stall= 0;
	if ((wb_cyc)&&(wb_stb)&&(clk)) {
		if (wb_we)
			m_mem[wb_addr & m_mask] = wb_data;
		m_nxt_ack = 1;
		m_nxt_data = m_mem[wb_addr & m_mask];
		// o_ack  = 1;

		{
			extern FILE *gbl_dbgfp;
			if (gbl_dbgfp) {
				if (wb_we) fprintf(gbl_dbgfp, "MEMSIM::MEM[%08x] = %08x\n", wb_addr&m_mask, wb_data);
				else
					fprintf(gbl_dbgfp, "MEMSIM::BUS = MEM[%08x] = %08x\n", wb_addr&m_mask, m_nxt_data);
			}
		}
		/*
		printf("MEMBUS -- ACK %s 0x%08x - 0x%08x\n",
			(wb_we)?"WRITE":"READ",
			wb_addr, o_data);
		*/
	} else if (clk) {
		m_nxt_ack   = 0;
		o_stall = 0;
	}
}


