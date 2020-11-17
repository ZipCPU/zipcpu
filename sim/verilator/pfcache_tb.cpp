////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pfcache_tb.cpp
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Bench testing for the prefetch cache used within the ZipCPU
//		when it is in pipelind mode.  Whether or not this module is
//	used depends upon how the CPU is set up in cpudefs.v.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <assert.h>

#include <stdlib.h>
#include <ctype.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vpfcache.h"

#include "testb.h"
#include "cpudefs.h"
#include "memsim.h"

#define	RAMBASE		(1<<20)
#define	RAMWORDS	RAMBASE
#define	MAXTIMEOUT	128

FILE	*gbl_dbgfp = NULL; // Can also be set to stdout

// class PFCACHE_TB
class	PFCACHE_TB : public TESTB<Vpfcache> {
// {{{
public:
	MEMSIM	m_mem;
	bool	m_bomb;

	// Nothing special to do in a startup.
	PFCACHE_TB(void) : m_mem(RAMWORDS), m_bomb(false) {}

	void	randomize_memory(void) {
		m_mem.load("/dev/urandom");
	}

	// ~CPUOPS_TB(void) {}

	// reset
	// {{{
	// Calls TESTB<>::reset to reset the core.  Makes sure the i_ce line
	// is low during this reset.
	//
	void	reset(void) {
		// {{{
		m_core->i_reset       = 0;
		m_core->i_pc          = RAMBASE<<2;
		m_core->i_new_pc      = 0;
		m_core->i_clear_cache = 1;
		m_core->i_ready       = 1;

		TESTB<Vpfcache>::reset();
		// }}}
	}
	// }}}

	// dbgdump();
	// {{{
	void	dbgdump(void) {
		// {{{
		/*
		char	outstr[2048], *s;
		sprintf(outstr, "Tick %4ld %s%s ",
			m_tickcount,
			(m_core->i_rst)?"R":" ", 
			(m_core->i_ce)?"CE":"  ");
		s = &outstr[strlen(outstr)];

		puts(outstr);
		*/
		// }}}
	}
	// }}}

	// valid_mem
	// {{{
	bool	valid_mem(uint32_t addr) {
		if (addr < RAMBASE)
			return false;
		if (addr >= RAMBASE + RAMWORDS)
			return false;
		return true;
	}
	// }}}

	// tick()
	// {{{
	// Call this to step the module under test.
	//
	void	tick(void) {
		bool	debug = false;

		// Bomb and error checking
		// {{{
		if ((m_core->o_wb_cyc)&&(m_core->o_wb_stb)) {
			if (!valid_mem(m_core->o_wb_addr))
				m_core->i_wb_err = 1;
		} else if (m_core->o_wb_stb) {
			m_bomb = true;
		}

		if (m_core->o_wb_we)
			m_bomb = true;
		if (m_core->o_wb_data != 0)
			m_bomb = true;
		// }}}

		if (debug)
			dbgdump();

		unsigned mask = (RAMBASE-1);

		m_mem(m_core->o_wb_cyc, m_core->o_wb_stb, m_core->o_wb_we,
			m_core->o_wb_addr & mask, m_core->o_wb_data, 0,
			m_core->i_wb_ack, m_core->i_wb_stall,m_core->i_wb_data);

		TESTB<Vpfcache>::tick();

		if (m_core->o_valid) {
			// {{{
			uint32_t	pc, insn;

			pc   = m_core->o_pc;
			insn = m_core->o_insn;
			if (insn != m_mem[(pc>>2) & (RAMWORDS-1)]) {
				fprintf(stderr, "ERR: PF[%08x] = %08x != %08x\n", pc,
					insn, m_mem[(pc>>2) & (RAMWORDS-1)]);
				closetrace();
				assert(insn == m_mem[(pc>>2) & (RAMWORDS-1)]);
			}
			// }}}
		}
	}
	// }}}

	// fetch_insn()
	// {{{
	void fetch_insn(void) {
		uint32_t	timeout = 0;

		if ((m_core->o_valid)&&(m_core->i_ready))
			m_core->i_pc++;

		m_core->i_reset       = 0;
		m_core->i_new_pc      = 0;
		m_core->i_clear_cache = 0;
		m_core->i_ready       = 1;
		do {
			tick();
		} while((!m_core->o_valid)&&(!m_core->o_illegal)&&(timeout++ < MAXTIMEOUT));

		if (timeout >= MAXTIMEOUT)
			m_bomb = true;
	}
	// }}}

	// skip_fetch()
	// {{{
	void	skip_fetch(void) {
		uint32_t	prevalid, insn;

		if ((m_core->o_valid)&&(m_core->i_ready))
			m_core->i_pc++;

		m_core->i_reset       = 0;
		m_core->i_new_pc      = 0;
		m_core->i_clear_cache = 0;
		m_core->i_ready       = 0;
		insn = m_core->o_insn;
		prevalid= m_core->o_valid;

		tick();

		if (prevalid) {
			// if (!m_core->o_valid) {
				// fprintf(stderr, "ERR: VALID dropped on stall!\n");
				// closetrace();
				// assert(m_core->o_valid);
			// }
			if (insn != m_core->o_insn) {
				fprintf(stderr, "ERR: VALID INSN CHANGED on stall!\n");
				closetrace();
				assert(insn == m_core->o_insn);
			}
		}
	}
	// }}}

	// jump
	// {{{
	void	jump(unsigned target) {
		// {{{
		uint32_t	timeout = 0;

		m_core->i_reset       = 0;
		m_core->i_new_pc      = 1;
		m_core->i_clear_cache = 0;
		m_core->i_ready       = 1;
		m_core->i_pc          = target;

		tick();
		m_core->i_pc++;
		m_core->i_new_pc      = 0;
		m_core->i_ready       = 0;

		while((!m_core->o_valid)&&(timeout++ < MAXTIMEOUT))
			tick();

		if (timeout >= MAXTIMEOUT)
			m_bomb = true;
		if (m_core->o_valid)
			assert(m_core->o_pc == target);
		// }}}
	}
	// }}}
// }}}
};

void	usage(void) {
	// {{{
	printf("USAGE: pfcache_tb\n");
	printf("\n");
	// }}}
}

int	main(int argc, char **argv) {
	// Setup verilator
	Verilated::commandArgs(argc, argv);
	// Now, create a test bench.
	PFCACHE_TB	*tb = new PFCACHE_TB();
	int	rcode = EXIT_SUCCESS;

	tb->opentrace("pfcache.vcd");
	tb->randomize_memory();

	tb->jump(RAMBASE<<2);

	// Simulate running straight through code
	// {{{
	for(int i=0; i<130; i++) {
		// printf("FETCH\n");
		tb->fetch_insn();
	}
	// }}}

	// Now, let's bounce around through the cache
	// {{{
	for(int j=0; j<20; j++) {
		tb->jump((RAMBASE+j)<<2);
		for(int i=0; i<130; i++) {
			// printf("FETCH\n");
			tb->fetch_insn();
		}

		if (tb->m_bomb) {
			printf("TEST FAILURE!\n");
			delete	tb;
			exit(EXIT_FAILURE);
		}
	}
	// }}}

	// Now, add in some CIS-type instructions
	// {{{
	for(int i=0; i<130; i++) {
		unsigned v = rand() & 0x0f;

		if ((v&3)==2) {
			// printf("SKIP\n");
			tb->skip_fetch();
		} else {
			// printf("FETCH\n");
			tb->fetch_insn();
		}

		if (tb->m_bomb) {
			printf("TEST FAILURE!\n");
			delete	tb;
			exit(EXIT_FAILURE);
		}
	}
	// }}}

	// Finally, try it all: stalls, CIS, and jumps
	// {{{
	for(int i=0; i<10000; i++) {
		unsigned v = rand() & 0x0f;
		if (v == 0) {
			uint32_t target = rand() & (RAMWORDS-1);
			target += RAMBASE;
			// printf("JUMP TO %08x\n", target);
			tb->jump(target<<2);
		} else if ((v & 3)==2) {
			// printf("SKIP\n");
			tb->skip_fetch();
		} else {
			// printf("FETCH\n");
			tb->fetch_insn();
		}
	
		if (tb->m_bomb) {
			printf("TEST FAILURE!\n");
			delete	tb;
			exit(EXIT_FAILURE);
		}
	}
	// }}}

	printf("SUCCESS!\n");
	exit(rcode);
}

