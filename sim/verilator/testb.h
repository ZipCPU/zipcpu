////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	testb.h
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	A wrapper for a common interface to a clocked FPGA core
//		begin exercised in Verilator.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017, Gisselquist Technology, LLC
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
#ifndef	TESTB_H
#define	TESTB_H

#include <stdio.h>
#include <stdint.h>
#include <verilated_vcd_c.h>

template <class VA>	class TESTB {
public:
	VA	*m_core;
	VerilatedVcdC*	m_trace;
	unsigned long	m_tickcount;

	TESTB(void) : m_trace(NULL), m_tickcount(0l) {
		m_core = new VA;
		Verilated::traceEverOn(true);
	}
	virtual ~TESTB(void) {
		if (m_trace) m_trace->close();
		delete m_core;
		m_core = NULL;
	}

	virtual	void	opentrace(const char *vcdname) {
		m_trace = new VerilatedVcdC;
		m_core->trace(m_trace, 99);
		m_trace->open(vcdname);
	}

	virtual	void	closetrace(void) {
		if (m_trace) {
			m_trace->close();
			m_trace = NULL;
		}
	}

	virtual	void	eval(void) {
		m_core->eval();
	}

	virtual	void	tick(void) {
		m_tickcount++;

		eval();
		if (m_trace) m_trace->dump(10*m_tickcount-2);
		m_core->i_clk = 1;
		eval();
		if (m_trace) m_trace->dump(10*m_tickcount);
		m_core->i_clk = 0;
		eval();
		if (m_trace) m_trace->dump(10*m_tickcount+5);

	}

	virtual	void	reset(void) {
		m_core->i_rst = 1;
		tick();
		m_core->i_rst = 0;
		// printf("RESET\n");
	}
};

#endif
