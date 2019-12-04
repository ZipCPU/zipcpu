////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipcpu_tb.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A bench simulator for the CPU.  Eventually, you should be
//		able to give this program the name of a piece of compiled
//	code to load into memory.  For now, we hand assemble with the computers
//	help.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2018, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <poll.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <ctype.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#ifdef	VM_COVERAGE
#include "verilated_cov.h"
#endif

#ifdef	ZIPBONES
#include "Vzipbones.h"
#define	SIMCLASS	Vzipbones
#else
#define	ZIPSYSTEM
#include "Vzipsystem.h"
#define	SIMCLASS	Vzipsystem
#endif

#include "cpudefs.h"

#include "testb.h"
#include "zipelf.h"
// #include "twoc.h"
// #include "qspiflashsim.h"
#include "byteswap.h"
#include "memsim.h"
#include "zopcodes.h"

#define	CMD_REG		0
#define	CMD_DATA	4
#define	CMD_GO		0
#define	CMD_GIE		(1<<13)
#define	CMD_SLEEP	(1<<12)
#define	CMD_CLEAR_CACHE	(1<<11)
#define	CMD_HALT	(1<<10)
#define	CMD_STALL	(1<<9)
#define	CMD_INT		(1<<7)
#define	CMD_RESET	(1<<6)
#define	CMD_STEP	((1<<8)|CMD_HALT)
#define	CPU_HALT	CMD_HALT
#define	CPU_sPC		15

#define	KEY_ESCAPE	27
#define	KEY_RETURN	10
#define	CTRL(X)		((X)&0x01f)

#define	MAXERR		10000


// Some versions of Verilator require a prefix starting with the top level
// module name, rather than v__DOT__....  For these versions of Verilator,
// you will need to replace these variable prefixes with either
//	zipsystem__DOT__...
// or
//	zipbones__DOT__...
#define	VVAR(A)	zipbones__DOT_ ## A
#define	cpu_halt	VVAR(_cmd_halt)
#define	cmd_reset	VVAR(_cmd_reset)
#define	cmd_step	VVAR(_cmd_step)
#define	cmd_addr	VVAR(_cmd_addr)

/*
// We are just a raw CPU with memory.  There is no flash.
#define	LGFLASHLEN	24
#define	FLASHBASE	0x01000000
#define	FLASHWORDS	(1<<LGFLASHLEN)
*/

#define	LGRAMLEN	28
#define	RAMBASE		(1<<(LGRAMLEN))
#define	RAMLEN		(1<<(LGRAMLEN))
#define	RAMWORDS	((RAMLEN)>>2)

class	SPARSEMEM {
public:
	bool	m_valid;
	unsigned int	m_a, m_d;
};

class	ZIPSTATE {
public:
	bool		m_valid, m_gie, m_last_pc_valid;
	unsigned int	m_sR[16], m_uR[16];
#ifdef	ZIPSYSTEM
	unsigned int	m_p[20];
#endif
	unsigned int	m_last_pc, m_pc, m_sp;
	SPARSEMEM	m_smem[5]; // Nearby stack memory
	SPARSEMEM	m_imem[5]; // Nearby instruction memory
	ZIPSTATE(void) : m_valid(false), m_last_pc_valid(false) {}

	void	step(void) {
		m_last_pc_valid = true;
		m_last_pc = m_pc;
	}
};

extern	FILE	*gbl_dbgfp;
FILE	*gbl_dbgfp = NULL;

// No particular "parameters" need definition or redefinition here.
class	ZIPCPU_TB : public TESTB<SIMCLASS> {
public:
	unsigned long	m_mem_size;
	MEMSIM		m_mem;
	// QSPIFLASHSIM	m_flash;
	FILE		*m_dbgfp, *m_profile_fp;
	bool		dbg_flag, m_bomb, m_show_user_timers, m_console, m_exit;
	int		m_rcode;
	unsigned long	m_last_instruction_tickcount;
	ZIPSTATE	m_state;

	ZIPCPU_TB(void) : m_mem_size(RAMWORDS), m_mem(m_mem_size) {
		m_rcode = 0;
		m_exit  = false;
		if (true) {
			m_dbgfp = fopen("debug.txt", "w");
			dbg_flag = true;
			gbl_dbgfp = m_dbgfp;
		} else {
			m_dbgfp = NULL;
			dbg_flag = false;
			gbl_dbgfp = NULL;
		}

		if(true) {
			opentrace("trace.vcd");
		} else {
			m_trace = NULL;
		}

		m_bomb = false;
		m_show_user_timers = false;

		m_last_instruction_tickcount = 0l;
		if (true) {
			m_profile_fp = fopen("pfile.bin","wb");
		} else {
			m_profile_fp = NULL;
		}
	}

	~ZIPCPU_TB(void) {
		if (m_dbgfp)
			fclose(m_dbgfp);
		if (m_profile_fp)
			fclose(m_profile_fp);
		if (m_trace)
			m_trace->close();
	}

	void	reset(void) {
		// m_flash.debug(false);
		TESTB<SIMCLASS>::reset();
	}

	void	step(void) {
		wb_write(CMD_REG, CMD_STEP);
		m_state.step();
	}

	void	read_raw_state(void) {
		m_state.m_valid = false;
		for(int i=0; i<16; i++)
			m_state.m_sR[i] = cmd_read(i);
		for(int i=0; i<16; i++)
			m_state.m_uR[i] = cmd_read(i+16);
#ifdef	ZIPSYSTEM
		for(int i=0; i<20; i++)
			m_state.m_p[i]  = cmd_read(i+32);
#endif

		m_state.m_gie = wb_read(CMD_REG) & CMD_GIE;
		m_state.m_pc  = (m_state.m_gie) ? (m_state.m_uR[15]):(m_state.m_sR[15]);
		m_state.m_sp  = (m_state.m_gie) ? (m_state.m_uR[13]):(m_state.m_sR[13]);

		if (m_state.m_last_pc_valid)
			m_state.m_imem[0].m_a = m_state.m_last_pc;
		else
			m_state.m_imem[0].m_a = m_state.m_pc - 1;
		m_state.m_imem[0].m_d = m_mem[m_state.m_imem[0].m_a & 0x0fffff];
		m_state.m_imem[0].m_valid = ((m_state.m_imem[0].m_a & 0xfff00000)==0x00100000);
		m_state.m_imem[1].m_a = m_state.m_pc;
		m_state.m_imem[1].m_valid = ((m_state.m_imem[1].m_a & 0xfff00000)==0x00100000);
		m_state.m_imem[1].m_d = m_mem[m_state.m_imem[1].m_a & 0x0fffff];

		for(int i=1; i<4; i++) {
			if (!m_state.m_imem[i].m_valid) {
				m_state.m_imem[i+1].m_valid = false;
				m_state.m_imem[i+1].m_a = m_state.m_imem[i].m_a+1;
				continue;
			}
			m_state.m_imem[i+1].m_a = zop_early_branch(
					m_state.m_imem[i].m_a,
					m_state.m_imem[i].m_d);
			m_state.m_imem[i+1].m_d = m_mem[m_state.m_imem[i].m_a & 0x0fffff];
			m_state.m_imem[i+1].m_valid = ((m_state.m_imem[i].m_a&0xfff00000)==0x00100000);
		}

		m_state.m_smem[0].m_a = m_state.m_sp;
		for(int i=1; i<5; i++)
			m_state.m_smem[i].m_a = m_state.m_smem[i-1].m_a+1;
		for(int i=0; i<5; i++) {
			m_state.m_smem[i].m_valid =
				(m_state.m_imem[i].m_a > 0x10000);
			m_state.m_smem[i].m_d = m_mem[m_state.m_imem[i].m_a & 0x0fffff];
		}
		m_state.m_valid = true;
	}

	void	read_raw_state_cheating(void) {
		m_state.m_valid = false;
	}

	void	showval(int y, int x, const char *lbl, unsigned int v, bool c) {
	}

	void	dispreg(int y, int x, const char *n, unsigned int v, bool c) {
	}

	void	dbgreg(FILE *fp, int id, const char *n, unsigned int v) {
	}

	void	showreg(int y, int x, const char *n, int r, bool c) {
	}

	void	showins(int y, const char *lbl, const int ce, const int valid,
			const int gie, const int stall, const unsigned int pc,
			const bool phase) {
	}

	void	dbgins(const char *lbl, const int ce, const int valid,
			const int gie, const int stall, const unsigned int pc,
			const bool phase, const bool illegal) {
	}

	void	show_state(void);

	void	show_user_timers(bool v) {
		m_show_user_timers = v;
	}

	unsigned int	cmd_read(unsigned int a) {
		int	errcount = 0;
		if (m_dbgfp) {
			dbg_flag= true;
			fprintf(m_dbgfp, "CMD-READ(%d)\n", a);
		}
		wb_write(CMD_REG, CMD_HALT|(a&0x3f));
		while(((wb_read(CMD_REG) & CMD_STALL) == 0)&&(errcount<MAXERR))
			errcount++;
		if (errcount >= MAXERR) {

			printf("ERR: errcount >= MAXERR on wb_read(a=%x)\n", a);
			exit(-2);
		}

		assert(errcount < MAXERR);
		unsigned int v = wb_read(CMD_DATA);

		if (dbg_flag)
			fprintf(m_dbgfp, "CMD-READ(%d) = 0x%08x\n", a, v);
		dbg_flag = false;
		return v;
	}

	void	cmd_write(unsigned int a, int v) {
		int	errcount = 0;
		if ((a&0x0f)==0x0f)
			dbg_flag = true;
		wb_write(CMD_REG, CMD_HALT|(a&0x3f));
		while(((wb_read(CMD_REG) & CMD_STALL) == 0)&&(errcount < MAXERR))
			errcount++;
		assert(errcount < MAXERR);
		if (dbg_flag)
			fprintf(m_dbgfp, "CMD-WRITE(%d) <= 0x%08x\n", a, v);
		wb_write(CMD_DATA, v);
	}

	bool	halted(void) {
		return (m_core->cpu_halt != 0);
	}

	void	read_state(void) {
	}

	void	tick(void) {
		int stb = m_core->o_wb_stb, maskb = (RAMBASE-1);
		unsigned addr = m_core->o_wb_addr<<2;

		m_core->i_wb_err = 0;
		if ((addr & (~maskb))!=RAMBASE)
			stb = 0;
		if ((m_core->o_wb_cyc)&&(m_core->o_wb_stb)&&(!stb)) {
			m_core->i_wb_ack = 1;
			m_core->i_wb_err = 1;
			m_bomb = (m_tickcount > 20);
			if (m_dbgfp) fprintf(m_dbgfp,
				"BOMB!! (Attempting to access %08x/%08x->%08x)\n",
				addr, RAMBASE, ((addr)&(~maskb)));
		} else if ((!m_core->o_wb_cyc)&&(m_core->o_wb_stb)) {
			if (m_dbgfp) fprintf(m_dbgfp,
				"BOMB!! (Strobe high, CYC low)\n");
			m_bomb = true;
		}

		m_mem(m_core->o_wb_cyc, m_core->o_wb_stb, m_core->o_wb_we,
			m_core->o_wb_addr & (maskb>>2), m_core->o_wb_data, m_core->o_wb_sel & 0x0f,
			m_core->i_wb_ack, m_core->i_wb_stall,m_core->i_wb_data);

		TESTB<SIMCLASS>::tick();
	}

#define	r_gie	zipbones__DOT__thecpu__DOT__SET_GIE__02Er_gie
#define	r_sleep	zipbones__DOT__thecpu__DOT__sleep

	bool	test_success(void) {
		if ((m_exit)&&(m_rcode == 0))
			return true;
		return ((!m_core->r_gie)
			&&(m_core->r_sleep));
	}

	bool	test_failure(void) {
		if ((m_exit)&&(m_rcode != 0))
			return true;
		return false;
	}

	void	wb_write(unsigned a, unsigned int v) {
		int	errcount = 0;
		// mvprintw(0,35, "%40s", "");
		// mvprintw(0,40, "wb_write(%d,%x)", a, v);
		m_core->i_dbg_cyc = 1;
		m_core->i_dbg_stb = 1;
		m_core->i_dbg_we  = 1;
		m_core->i_dbg_addr = (a>>2) & 1;
		m_core->i_dbg_data = v;

		while((errcount++ < 100)&&(m_core->o_dbg_stall))
			tick();
		tick();

		m_core->i_dbg_stb = 0;
		while((errcount++ < 100)&&(!m_core->o_dbg_ack))
			tick();

		// Release the bus
		m_core->i_dbg_cyc = 0;
		m_core->i_dbg_stb = 0;
		tick();
		// mvprintw(0,35, "%40s", "");
		// mvprintw(0,40, "wb_write -- complete");


		if (errcount >= 100) {
			if (m_dbgfp) fprintf(m_dbgfp, "WB-WRITE: ERRCount = %d, BOMB!!\n", errcount);
			m_bomb = true;
		}
	}

	unsigned long	wb_read(unsigned a) {
		unsigned int	v;
		int	errcount = 0;
		// mvprintw(0,35, "%40s", "");
		// mvprintw(0,40, "wb_read(0x%08x)", a);
		m_core->i_dbg_cyc = 1;
		m_core->i_dbg_stb = 1;
		m_core->i_dbg_we  = 0;
		m_core->i_dbg_addr = (a>>2) & 1;

		while((errcount++<100)&&(m_core->o_dbg_stall))
			tick();
		tick();

		m_core->i_dbg_stb = 0;
		while((errcount++<100)&&(!m_core->o_dbg_ack))
			tick();
		v = m_core->o_dbg_data;

		// Release the bus
		m_core->i_dbg_cyc = 0;
		m_core->i_dbg_stb = 0;
		tick();

		// mvprintw(0,35, "%40s", "");
		// mvprintw(0,40, "wb_read = 0x%08x", v);

		if (errcount >= 100) {
			if (m_dbgfp) fprintf(m_dbgfp, "WB-READ: ERRCount = %d, BOMB!!\n", errcount);
			m_bomb = true;
		}
		return v;
	}
};

void	get_value(ZIPCPU_TB *tb) {}



void	usage(void) {
	printf("USAGE: zippy_tb [-a] <testfile.out>\n");
	printf("\n");
	printf("\tWhere testfile.out is an output file from the assembler.\n");
	printf("\tThis file needs to be in a raw format and not an ELF\n");
	printf("\texecutable.  It will be inserted into memory at a memory\n");
	printf("\taddress of 0x0100000.  The memory device itself, the only\n");
	printf("\tdevice supported by this simulator, occupies addresses from\n");
	printf("\t0x0100000 to 0x01fffff.\n");
	printf("\n");
	printf("\t-a\tSets the testbench to run automatically without any\n");
	printf("\t\tuser interaction.\n");
	printf("\n");
	printf("\tUser Commands:\n");
	printf("\t\tWhen the test bench is run interactively, the following\n");
	printf("\t\tkey strokes are recognized:\n");
	printf("\t\t\'h\'\tHalt the processor using the external interface.\n");
	printf("\t\t\'g\'\tLet the processor run at full throttle with no.\n");
	printf("\t\t\tuser intervention.\n");
	printf("\t\t\'q\'\tQuit the simulation.\n");
	printf("\t\t\'r\'\tReset the processor.\n");
	printf("\t\t\'s\'\tStep the CPU using the external stepping command\n");
	printf("\t\t\tThis may consume more than one tick.\n");
	printf("\t\t\'t\'\tClock a single tick through the system.\n");
}

bool	signalled = false;

void	sigint(int v) {
	signalled = true;
}

int	main(int argc, char **argv) {
	Verilated::commandArgs(argc, argv);
	ZIPCPU_TB	*tb = new ZIPCPU_TB();
	unsigned	MAX_STEPS = 50000;
	ZIPI		entry = RAMBASE;
#ifdef	MCY
	int		mutsel = 0;
#endif

	signal(SIGINT, sigint);

	if (argc <= 1) {
		usage();
		exit(-1);
	} else {
		for(int argn=1; argn<argc; argn++) {
			if (argv[argn][0] == '-') {
				switch(argv[argn][1]) {
				case 'h':
					usage();
					exit(0);
					break;
				default:
					usage();
					exit(-1);
					break;
				}
#ifdef	MCY
			} else if (isdigit(argv[argn][0])) {
				mutsel = atoi(argv[argn]);
#endif
			} else if ((access(argv[argn], R_OK)==0)
						&&(iself(argv[argn]))) {
				ELFSECTION **secpp = NULL, *secp;

				elfread(argv[argn], entry, secpp);

				for(int i=0; secpp[i]->m_len; i++) {
					const char *data;

					secp = secpp[i];
					assert(secp->m_start >= RAMBASE);
					assert(secp->m_start+secp->m_len <= RAMBASE+RAMWORDS);
					assert((secp->m_len & 3)==0);

					data = &secp->m_data[0];
					tb->m_mem.load((secp->m_start-RAMBASE)>>2, data, secp->m_len);
				}
			} else {
				fprintf(stderr, "No access to %s, or unknown arg\n", argv[argn]);
				exit(-2);
			}
		}
	}


	tb->m_core->mutsel = mutsel;
	bool	done = false;

	printf("Running in non-interactive mode\n");
	tb->m_console = true;
	tb->reset();
	tb->m_core->cpu_halt = 1;
	tb->wb_write(CMD_REG, CMD_HALT|CMD_RESET|15);
	tb->wb_write(CMD_DATA, entry);
	tb->wb_write(CMD_REG, 15);
	tb->m_bomb = false;
	while(!done && tb->tickcount() < MAX_STEPS) {
		tb->tick();

		done = (tb->test_success())||(tb->test_failure());
		done = done || signalled;
	}

	printf("\n");

	int	rcode = 0;
	if (tb->m_bomb) {
		printf("TEST BOMBED\n");
		rcode = -1;
	} else if (tb->test_success()) {
		printf("SUCCESS!\n");
	} else if (tb->test_failure()) {
		rcode = -2;
		printf("TEST FAILED!\n");
	} else if (tb->tickcount() >= MAX_STEPS) {
		rcode = -3;
		printf("TEST TIMED OUT!\n");
	} else
		printf("User quit\n");

	delete tb;
	exit(rcode);
}

