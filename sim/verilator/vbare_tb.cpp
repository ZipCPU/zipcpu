////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/verilated/vbare_tb.cpp
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A bare-bones simulation wrapper for the ZipCPU's
//		multi-simulation environments.  All peripherals are implemented
//	via $write internal to the simulation, and this script does nothing
//	to interact with the CPU within.  This makes it easier to support
//	1) multiple CPU configurations, and 2) a common simulation script
//	between both Verilog only simulation environments (such as Icarus
//	or commercial simulators) and Verilated environments.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <stdint.h>
#include "verilated.h"
#include "verilated_vcd_c.h"
#ifdef	VM_COVERAGE
#include "verilated_cov.h"
#endif
#include BASEINC
// }}}

#ifdef	AXI
#define	CLK	i_aclk
#else
#define	CLK	i_clk
#endif

class	BARE_TB {
public:
	BASE		*m_core;
	VerilatedVcdC	*m_trace;
	uint64_t	m_tickcount;

	BARE_TB(void) {
		m_core = new BASE;
		m_trace = NULL;
		m_tickcount = 1l;
	}

	void	reset(void) {
		// {{{
#ifdef	AXI
		m_core->CLK       = 0;
		m_core->i_aresetn = 0;

		m_core->sim_awvalid = 0;
		m_core->sim_awaddr  = 0;
		m_core->sim_awprot  = 0;

		m_core->sim_wvalid = 0;
		m_core->sim_wdata  = 0;
		m_core->sim_wstrb  = 0;

		m_core->sim_bready = 1;

		m_core->sim_arvalid = 0;
		m_core->sim_araddr  = 0;
		m_core->sim_arprot  = 0;

		m_core->sim_rready = 1;

		tick();
		tick();
		m_core->i_aresetn = 1;
		tick();
#else
		m_core->CLK     = 0;
		m_core->i_reset = 1;

		m_core->i_sim_cyc  = 0;
		m_core->i_sim_stb  = 0;
		m_core->i_sim_we   = 0;
		m_core->i_sim_addr = 0;
		m_core->i_sim_data = 0;
		m_core->i_sim_sel  = 0;
		m_core->i_sim_int  = 0;

		tick();
		tick();
		m_core->i_reset = 0;
		tick();
#endif
	}
	// }}}

	void	opentrace(const char *vcdname) {
		// {{{
		if (!m_trace) {
			m_trace = new VerilatedVcdC;
			m_core->trace(m_trace, 99);
			m_trace->open(vcdname);
		}
	}
	// }}}

	void	tick(void) {
		// {{{
		m_core->CLK = 0;
		m_core->eval();
		if (m_trace) m_trace->dump((vluint64_t)(10*m_tickcount-2));

		m_core->CLK = 1;
		m_core->eval();
		if (m_trace) m_trace->dump((vluint64_t)(10*m_tickcount));

		m_core->CLK = 0;
		m_core->eval();
		if (m_trace) m_trace->dump((vluint64_t)(10*m_tickcount+5));

		m_tickcount++;
	}
	// }}}
};

int	main(int argc, char **argv) {
	Verilated::commandArgs(argc, argv);
	Verilated::traceEverOn(true);

	BARE_TB	*tb = new BARE_TB();
#ifdef	VCD_FILE
	tb->opentrace(VCD_FILE);
#endif

	tb->reset();

	while(!Verilated::gotFinish())
		tb->tick();
}
