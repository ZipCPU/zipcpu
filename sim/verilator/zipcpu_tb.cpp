////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/verilator/zipcpu_tb.cpp
// {{{
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
// }}}
// Copyright (C) 2015-2025, Gisselquist Technology, LLC
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
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <poll.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <ctype.h>

#include <ncurses.h>

#include "verilated.h"
#include "verilated_vcd_c.h"
#ifdef	VM_COVERAGE
#include "verilated_cov.h"
#endif

// ZipBones includes
#ifdef	ZIPBONES
#include "Vzipbones.h"
#ifdef	ROOT_VERILATOR
#include "Vzipbones___024root.h"
#endif

#define	SIMCLASS	Vzipbones
#else

// ZipSystem includes
#define	ZIPSYSTEM
#include "Vzipsystem.h"

#ifdef	ROOT_VERILATOR
#include "Vzipsystem___024root.h"
#endif

#define	SIMCLASS	Vzipsystem
#endif

#include "testb.h"
#include "zipelf.h"
// #include "twoc.h"
// #include "qspiflashsim.h"
#include "byteswap.h"
#include "memsim.h"
#include "zopcodes.h"

#define	CMD_REG		0x00
#define	CMD_SREG(A)	(0x80 + (A<<2))
#define	CMD_GO		0
#define	CMD_HALT	(1<<0)
#define	CMD_HALTED	(1<<1)
#define	CMD_STEP	(1<<2)
#define	CMD_RESET	(1<<3)
#define	CMD_CLEAR_CACHE	(1<<4)
#define	CMD_CATCH	(1<<5)
#define	CMD_SLEEP	(1<<8)
#define	CMD_GIE		(1<<9)
#define	CMD_INT		(1<<10)
#define	CPU_HALT	CMD_HALT
#define	CPU_sPC		(0x80+(15<<2))

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

#ifdef	ROOT_VERILATOR
// {{{
  #ifdef ZIPBONES
     #ifdef	VM_COVERAGE
      #define	VVAR(A)	rootp->zipbones__DOT____Vtogcov_ ## A
     #else
      #define	VVAR(A)	rootp->zipbones__DOT_ ## A
     #endif // VM_COVERAGE
   #else // Not ZIPBONES, but still under ROOT_VERILATOR
     #ifdef	VM_COVERAGE
      #define	VVAR(A)	rootp->zipsystem__DOT____Vtogcov_ ## A
     #else
      #define	VVAR(A)	rootp->zipsystem__DOT_ ## A
     #endif // VM_COVERAGE
   #endif // ZIPBONES
// }}}
#elif	defined(NEW_VERILATOR)
// NEW_VERILATOR
// {{{
  #ifdef	ZIPBONES
    #ifdef	VM_COVERAGE
      #define	VVAR(A)	zipbones__DOT____Vtogcov_ ## A
    #else
      #define	VVAR(A)	zipbones__DOT_ ## A
    #endif
  #else // Not ZIPBONES, but still under NEW_VERILATOR
    #ifdef	VM_COVERAGE
      #define	VVAR(A)	zipsystem__DOT____Vtogcov_ ## A
    #else
      #define	VVAR(A)	zipsystem__DOT_ ## A
    #endif // VM_COVERAGE
  #endif
// }}}
#else // OLD_VERILATOR used the v__DOT_ prefix
  #define	VVAR(A)	v__DOT_ ## A
#endif

#define	CPUVAR(A)	VVAR(_thecpu__DOT__core__DOT_ ##A)

#ifdef	OPT_DCACHE
///
	// dcache
  #define	MEMVAR(A)	VVAR(_thecpu__DOT__DATA_CACHE__DOT__mem__DOT_ ## A)
///
#elif defined(OPT_PIPELINED_BUS_ACCESS)
///
	// pipemem
  #define	MEMVAR(A) VVAR(_thecpu__DOT__PIPELINED_MEM__DOT__domem__DOT_ ## A)
  #define	mem_wraddr	MEMVAR(_wraddr)
  #define	mem_rdaddr	MEMVAR(_rdaddr)
///
#else
///
	// memops
  #define	MEMVAR(A) VVAR(_thecpu__DOT__BARE_MEM__DOT__domem__DOT_ ## A)
#endif

#define	cpu_halt	VVAR(_cmd_halt)
#define	cmd_reset	VVAR(_cmd_reset)
#define	cmd_step	VVAR(_cmd_step)

#ifdef	ROOT_VERILATOR
  #define	cpu_regs	VVAR(_thecpu__DOT__core__DOT__regset.m_storage)
#else
  #define	cpu_regs	VVAR(_thecpu__DOT__core__DOT__regset)
#endif

#ifdef	ZIPSYSTEM
#else
#define	dbg_cyc		i_dbg_cyc
#define	dbg_stb		i_dbg_stb
#define	dbg_we		i_dbg_we
#define	dbg_idata	i_dbg_data
#define	cpu_stall	i_wb_stall
#define	cpu_interrupt	i_ext_int
#define	cpu_idata	i_wb_data
#define	tick_counter	tickcount()
#define	dbg_addr	i_dbg_addr
#endif

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

// ZIPSTATE
// {{{
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
// }}}

extern	FILE	*gbl_dbgfp;
FILE	*gbl_dbgfp = NULL;

// ZIPCPU_TB
// {{{
// No particular "parameters" need definition or redefinition here.
class	ZIPCPU_TB : public TESTB<SIMCLASS> {
public:
	// Declarations
	// {{{
	unsigned long	m_mem_size;
	MEMSIM		m_mem;
	// QSPIFLASHSIM	m_flash;
	FILE		*m_dbgfp, *m_profile_fp;
	bool		dbg_flag, m_bomb, m_show_user_timers, m_console, m_exit;
	int		m_cursor, m_rcode;
	unsigned long	m_last_instruction_tickcount;
	ZIPSTATE	m_state;
	// }}}

	ZIPCPU_TB(void) : m_mem_size(RAMWORDS), m_mem(m_mem_size) {
		// {{{
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
		m_cursor = 0;
		m_show_user_timers = false;

		m_last_instruction_tickcount = 0l;
		if (true) {
			m_profile_fp = fopen("pfile.bin","wb");
		} else {
			m_profile_fp = NULL;
		}
		// }}}
	}

	~ZIPCPU_TB(void) {
		// {{{
		if (m_dbgfp)
			fclose(m_dbgfp);
		if (m_profile_fp)
			fclose(m_profile_fp);
		if (m_trace)
			m_trace->close();
		// }}}
	}

	void	reset(void) {
		// m_flash.debug(false);
		TESTB<SIMCLASS>::reset();
	}

	void	step(void) {
		wb_write(CMD_REG, CMD_STEP | CMD_CATCH);
		m_state.step();
	}

	void	read_raw_state(void) {
		// {{{
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
			// {{{
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
			// }}}
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
		// }}}
	}

	void	read_raw_state_cheating(void) {
		// {{{
		m_state.m_valid = false;
		for(int i=0; i<16; i++)
			m_state.m_sR[i] = m_core->cpu_regs[i];
		m_state.m_sR[14] = (m_state.m_sR[14]&0xffffe000)|m_core->w_iflags;
		m_state.m_sR[15] = m_core->cpu_ipc;
		for(int i=0; i<16; i++)
			m_state.m_uR[i] = m_core->cpu_regs[i+16];
		m_state.m_uR[14] = (m_state.m_uR[14]&0xffffe000)|m_core->w_uflags;
		m_state.m_uR[15] = m_core->cpu_upc;

		m_state.m_gie = m_core->r_gie;
		m_state.m_pc  = (m_state.m_gie) ? (m_state.m_uR[15]):(m_state.m_sR[15]);
		m_state.m_sp  = (m_state.m_gie) ? (m_state.m_uR[13]):(m_state.m_sR[13]);

#ifdef	ZIPSYSTEM
		// {{{
		m_state.m_p[0] = m_core->pic_data;
		m_state.m_p[1] = m_core->watchdog;
		if (!m_show_user_timers) {
			m_state.m_p[2] = m_core->watchbus;
		} else {
			// The last bus error address
			m_state.m_p[2] = m_core->wdbus_data;
		}

		m_state.m_p[3] = m_core->alt_int_state;
		m_state.m_p[4] = m_core->timer_a;
		m_state.m_p[5] = m_core->timer_b;
		m_state.m_p[6] = m_core->timer_c;
		m_state.m_p[7] = m_core->jiffies;

		m_state.m_p[ 8] = m_core->utc_data;
		m_state.m_p[ 9] = m_core->uoc_data;
		m_state.m_p[10] = m_core->upc_data;
		m_state.m_p[11] = m_core->uic_data;

		m_state.m_p[12] = m_core->mtc_data;
		m_state.m_p[13] = m_core->moc_data;
		m_state.m_p[14] = m_core->mpc_data;
		m_state.m_p[15] = m_core->mic_data;
		// }}}
#endif
		// }}}
	}

	void	showval(int y, int x, const char *lbl, unsigned int v, bool c) {
		// {{{
		if (c)
			mvprintw(y,x, ">%s> 0x%08x<", lbl, v);
		else
			mvprintw(y,x, " %s: 0x%08x ", lbl, v);
		// }}}
	}

	void	dispreg(int y, int x, const char *n, unsigned int v, bool c) {
		// {{{
		// 4,4,8,1 = 17 of 20, +3 = 19
		if (c)
			mvprintw(y, x, ">%s> 0x%08x<", n, v);
		else
			mvprintw(y, x, " %s: 0x%08x ", n, v);
		// }}}
	}

	void	dbgreg(FILE *fp, int id, const char *n, unsigned int v) {
		// {{{
		/*
		if ((id == 14)||(id == 14+16)) {
			//char	buf[64];
			//fprintf(fp, " %s:",
			fprintf(fp, " %s: 0x%08x ", n, v);
		} else
		*/
			fprintf(fp, " %s: 0x%08x ", n, v);
		// }}}
	}

	void	showreg(int y, int x, const char *n, int r, bool c) {
		// {{{
		if (r < 16)
			dispreg(y, x, n, m_state.m_sR[r], c);
		else
			dispreg(y, x, n, m_state.m_uR[r-16], c);
		move(y,x+17);

#ifdef	OPT_PIPELINED
		addch( ((r == (int)(dcd_Aid()&0x01f))&&(m_core->dcd_valid)
				&&(m_core->dcd_rA))
			?'a':((c)?'<':' '));
		addch( ((r == (int)(dcd_Bid()&0x01f))&&(m_core->dcd_valid)
				&&(m_core->dcd_rB))
			?'b':' ');
		addch( ((r == m_core->wr_reg_id)
				&&(m_core->wr_reg_ce))
			?'W':' ');
#else
		addch( ((r == m_core->wr_reg_id)
				&&(m_core->wr_reg_ce))
			?'W':((c)?'<':' '));
#endif
		// }}}
	}

	void	showins(int y, const char *lbl, const int ce, const int valid,
			const int gie, const int stall, const unsigned int pc,
			const bool phase) {
		// {{{
		char	la[80], lb[80];
		unsigned iv = m_mem[pc >> 2];
		bool	cisw = (iv & 0x80000000)?true:false;

		if (ce)
			mvprintw(y, 0, "Ck ");
		else
			mvprintw(y, 0, "   ");
		if (stall)
			printw("Stl ");
		else
			printw("    ");
		printw("%s%c 0x%08x", lbl, ((cisw)&&(phase))?'/':':', pc);

		if (valid) {
			if (gie) attroff(A_BOLD);
			else	attron(A_BOLD);
			zipi_to_double_string(pc, iv, la, lb);
			if ((!cisw)||(phase))
				printw("  %-24s", la);
			else
				printw("  %-24s", lb);
		} else {
			attroff(A_BOLD);
			printw("  (0x%08x)%28s", iv,"");
		}
		attroff(A_BOLD);
		// }}}
	}

	void	dbgins(const char *lbl, const int ce, const int valid,
			const int gie, const int stall, const unsigned int pc,
			const bool phase, const bool illegal) {
		// {{{
		char	la[80], lb[80];

		if (!m_dbgfp)
			return;

		if (ce)
			fprintf(m_dbgfp, "%s Ck ", lbl);
		else
			fprintf(m_dbgfp, "%s    ", lbl);
		if (stall)
			fprintf(m_dbgfp, "Stl ");
		else
			fprintf(m_dbgfp, "    ");
		fprintf(m_dbgfp, "0x%08x%s:  ", pc, (phase)?"/P":"  ");

		if (valid) {
			zipi_to_double_string(pc, m_mem[pc>>2], la, lb);
			if ((phase)||((m_mem[pc>>2]&0x80000000)==0))
				fprintf(m_dbgfp, "  %-24s", la);
			else
				fprintf(m_dbgfp, "  %-24s", lb);
		} else {
			fprintf(m_dbgfp, "  (0x%08x)", m_mem[pc]);
		} if (illegal)
			fprintf(m_dbgfp, " (Illegal)");
		fprintf(m_dbgfp, "\n");
		// }}}
	}

	void	show_state(void) {
		// {{{
		int	ln= 0;

		read_raw_state_cheating();

		mvprintw(ln,0, "Peripherals-SS"); ln++;
		printw(" %s",
			// (m_core->pf_illegal)?"PI":"  ",
			(m_core->dcd_illegal)?"DI":"  "
			);

#ifdef	OPT_EARLY_BRANCHING
		printw(" %s",
			(m_core->early_branch)?"EB":"  ");
		if (m_core->early_branch)
			printw(" 0x%08x", m_core->early_branch_pc);
		else	printw(" %10s", "");
		// printw(" %s", (m_core->v__DOT__thecpu__DOT____Vcellinp__pf____pinNumber3)?"-> P3":"     ");
#endif

#ifdef	ZIPSYSTEM
		showval(ln, 0, "PIC ", m_state.m_p[0], (m_cursor==0));
		showval(ln,20, "WDT ", m_state.m_p[1], (m_cursor==1));
		// showval(ln,40, "CACH", m_core->v__DOT__manualcache__DOT__cache_base, (m_cursor==2));

		if (!m_show_user_timers) {
		showval(ln,40, "WBUS", m_core->watchbus, false);
		} else {
		// showval(ln,40, "UBUS", m_core->v__DOT__r_wdbus_data, false);
		showval(ln,40, "UBUS", m_core->watchbus, false);
		}

		showval(ln,60, "PIC2", m_state.m_p[3], (m_cursor==3));

		ln++;
		showval(ln, 0, "TMRA", m_state.m_p[4], (m_cursor==4));
		showval(ln,20, "TMRB", m_state.m_p[5], (m_cursor==5));
		showval(ln,40, "TMRC", m_state.m_p[6], (m_cursor==6));
		showval(ln,60, "JIF ", m_state.m_p[7], (m_cursor==7));


		if (!m_show_user_timers) {
			// {{{
			ln++;
			showval(ln, 0, "MTSK", m_state.m_p[12], (m_cursor==8));
			showval(ln,20, "MOST", m_state.m_p[13], (m_cursor==9));
			showval(ln,40, "MPST", m_state.m_p[14], (m_cursor==10));
			showval(ln,60, "MICT", m_state.m_p[15], (m_cursor==11));
			// }}}
		} else {
			// {{{
			ln++;
			showval(ln, 0, "UTSK", m_state.m_p[ 8], (m_cursor==8));
			showval(ln,20, "UOST", m_state.m_p[ 9], (m_cursor==9));
			showval(ln,40, "UPST", m_state.m_p[10], (m_cursor==10));
			showval(ln,60, "UICT", m_state.m_p[11], (m_cursor==11));
			// }}}
		}
#else
		ln += 2;
#endif

		ln++;
		mvprintw(ln, 40, "%s %s",
			(m_core->cpu_halt)? "CPU-HALT": "        ",
			(m_core->cmd_reset)?"CPU-RESET":"         "); ln++;
		mvprintw(ln, 40, "%s %s %s %s %s",
			(m_core->cpu_halt)? "HALT": "    ",
			(m_core->cmd_reset)?"RESET":"     ",
			(m_core->cmd_step)? "STEP" :"    ",
			// (m_core->cmd_addr)&0x3f,
			(m_core->master_ce)? "*CE*" :"(ce)",
			(m_core->cmd_reset)? "*RST*" :"(rst)");
		if (m_core->r_gie)
			attroff(A_BOLD);
		else
			attron(A_BOLD);
		mvprintw(ln, 0, "Supervisor Registers");
		ln++;

		// Supervisor registers
		// {{{
		showreg(ln, 0, "sR0 ", 0, (m_cursor==12));
		showreg(ln,20, "sR1 ", 1, (m_cursor==13));
		showreg(ln,40, "sR2 ", 2, (m_cursor==14));
		showreg(ln,60, "sR3 ", 3, (m_cursor==15)); ln++;

		showreg(ln, 0, "sR4 ", 4, (m_cursor==16));
		showreg(ln,20, "sR5 ", 5, (m_cursor==17));
		showreg(ln,40, "sR6 ", 6, (m_cursor==18));
		showreg(ln,60, "sR7 ", 7, (m_cursor==19)); ln++;

		showreg(ln, 0, "sR8 ",  8, (m_cursor==20));
		showreg(ln,20, "sR9 ",  9, (m_cursor==21));
		showreg(ln,40, "sR10", 10, (m_cursor==22));
		showreg(ln,60, "sR11", 11, (m_cursor==23)); ln++;

		showreg(ln, 0, "sR12", 12, (m_cursor==24));
		showreg(ln,20, "sSP ", 13, (m_cursor==25));

		unsigned int cc = m_state.m_sR[14];
		if (false) {
			mvprintw(ln,40, "%ssCC : 0x%08x",
				(m_cursor==26)?">":" ", cc);
		} else {
			char	cbuf[32];

			sprintf(cbuf, "%ssCC :%s%s%s%s%s%s%s",
				(m_cursor==26)?">":" ",
				(cc&0x01000)?"FE":"",
				(cc&0x00800)?"DE":"",
				(cc&0x00400)?"BE":"",
				(cc&0x00200)?"TP":"",
				(cc&0x00100)?"IL":"",
				(cc&0x00080)?"BK":"",
				((m_state.m_gie==0)&&(cc&0x010))?"HLT":"");
			mvprintw(ln,40, "%-14s",cbuf);
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		showval(ln,60, "sPC ", m_state.m_sR[15], (m_cursor==27));
		mvprintw(ln,60,"%s",
			(m_core->wr_reg_id == 0x0e)
				&&(m_core->wr_reg_ce)
				?"V"
			:(((m_core->wr_flags_ce)
				&&(!m_core->alu_gie))?"+"
			:" "));
		ln++;
		// }}}

		// User registers
		// {{{
		if (m_core->r_gie)
			attron(A_BOLD);
		else
			attroff(A_BOLD);
		mvprintw(ln, 0, "User Registers");
		mvprintw(ln, 42, "DCDR=%02x %s%s",
			m_core->dcdR,
			(m_core->dcd_wR)?"W":" ",
			(m_core->dcd_wF)?"F":" ");
		mvprintw(ln, 62, "OPR =%02x %s%s",
			m_core->op_R,
			(m_core->op_wR)?"W":" ",
			(m_core->op_wF)?"F":" ");
		ln++;
		showreg(ln, 0, "uR0 ", 16, (m_cursor==28));
		showreg(ln,20, "uR1 ", 17, (m_cursor==29));
		showreg(ln,40, "uR2 ", 18, (m_cursor==30));
		showreg(ln,60, "uR3 ", 19, (m_cursor==31)); ln++;

		showreg(ln, 0, "uR4 ", 20, (m_cursor==32));
		showreg(ln,20, "uR5 ", 21, (m_cursor==33));
		showreg(ln,40, "uR6 ", 22, (m_cursor==34));
		showreg(ln,60, "uR7 ", 23, (m_cursor==35)); ln++;

		showreg(ln, 0, "uR8 ", 24, (m_cursor==36));
		showreg(ln,20, "uR9 ", 25, (m_cursor==37));
		showreg(ln,40, "uR10", 26, (m_cursor==38));
		showreg(ln,60, "uR11", 27, (m_cursor==39)); ln++;

		showreg(ln, 0, "uR12", 28, (m_cursor==40));
		showreg(ln,20, "uSP ", 29, (m_cursor==41));
		cc = m_state.m_uR[14];
		if (false) {
			mvprintw(ln,40, "%cuCC : 0x%08x",
				(m_cursor == 42)?'>':' ', cc);
		} else {
			char	cbuf[32];
			sprintf(cbuf, "%cuCC :%s%s%s%s%s%s%s",
				(m_cursor == 42)?'>':' ',
				(cc & 0x1000)?"FE":"",
				(cc & 0x0800)?"DE":"",
				(cc & 0x0400)?"BE":"",
				(cc & 0x0200)?"TP":"",
				(cc & 0x0100)?"IL":"",
				(cc & 0x0040)?"ST":"",
				((m_state.m_gie)&&(cc & 0x010))?"SL":"");
			mvprintw(ln,40, "%-14s",cbuf);
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		showval(ln,60, "uPC ", m_state.m_uR[15], (m_cursor==43));
		mvprintw(ln,60,"%s",
			(m_core->wr_reg_id == 0x1e)
				&&(m_core->wr_reg_ce)
				?"V"
			:(((m_core->wr_flags_ce)
				&&(m_core->alu_gie))?"+"
			:" "));

		attroff(A_BOLD);
		ln+=1;
		// }}}

		// Prefetch data line
		// {{{
		ln++;
		mvprintw(ln, 0, "PF BUS: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x",
			(m_core->pf_cyc)?"CYC":"   ",
			(m_core->pf_stb)?"STB":"   ",
			"  ", // (m_core->pf_we )?"WE":"  ",
			(m_core->pf_addr),
			0, // (m_core->v__DOT__thecpu__DOT__pf_data),
			(m_core->pf_ack)?"ACK":"   ",
			"   ",//(m_core->v__DOT__thecpu__DOT__pf_stall)?"STL":"   ",
			(m_core->cpu_idata)); ln++;
		// }}}

		// Data bus info
		// {{{
		mvprintw(ln, 0, "MEMBUS: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x",
			(m_core->wb_cyc_gbl)?"GCY"
				:((m_core->wb_cyc_lcl)?"LCY":"   "),
			(m_core->mem_stb_gbl)?"GSB"
				:((m_core->mem_stb_lcl)?"LSB":"   "),
			(m_core->mem_we )?"WE":"  ",
			(m_core->mem_addr<<2),
			(m_core->mem_data),
			(m_core->mem_ack)?"ACK":"   ",
			(m_core->mem_stall)?"STL":"   ",
			(m_core->mem_result));
// #define	OPT_PIPELINED_BUS_ACCESS
#ifdef	OPT_PIPELINED_BUS_ACCESS
#ifndef	OPT_DCACHE
		printw(" %x%x%c%c",
			(m_core->mem_wraddr),
			(m_core->mem_rdaddr),
			(m_core->op_pipe)?'P':'-',
			(mem_pipe_stalled())?'S':'-'); ln++;
#else
		ln++;
#endif
#else
		ln++;
#endif
		// }}}

		// The outgoing bus info
		// {{{
		mvprintw(ln, 0, "SYSBS%c: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x %s",
			(m_core->pformem_owner)?'M':'P',
			(m_core->o_wb_cyc)?"CYC":"   ",
			(m_core->o_wb_stb)?"STB":"   ",
			(m_core->o_wb_we )?"WE":"  ",
			(m_core->o_wb_addr<<2),
			(m_core->o_wb_data),
			(m_core->i_wb_ack)?"ACK":"   ",
			(m_core->i_wb_stall)?"STL":"   ",
			(m_core->i_wb_data),
			(m_core->i_wb_err)?"(ER!)":"     "); ln+=2;
#ifdef	OPT_PIPELINED_BUS_ACCESS
		mvprintw(ln-1, 0, "Mem CE: %d = %d%d%d%d%d, stall: %d = %d%d(%d|%d%d|..)",
			(m_core->mem_ce),
			(m_core->master_ce),	//1
			(m_core->op_valid_mem),	//0
			(!m_core->new_pc),	//1
			// (!m_core->clear_pipeline),	//1
			(m_core->set_cond),	//1
			(!mem_stalled()),	//1

			(mem_stalled()),
			(m_core->op_valid_mem),
			(m_core->master_ce),
			(mem_pipe_stalled()),
			(!m_core->op_pipe),
			(m_core->mem_busy)
			);
		printw(" op_pipe = %d", m_core->dcd_pipe);
		// mvprintw(4,4,"r_dcdI = 0x%06x",
			// (m_core->v__DOT__thecpu__DOT__dcdI)&0x0ffffff);
#endif
		// }}}
		mvprintw(4,42,"0x%08x", m_core->pf_instruction);
/*
#ifdef	OPT_SINGLE_CYCLE
		printw(" A:%c%c B:%c%c",
			(m_core->op_A_alu)?'A':'-',
			(m_core->op_A_mem)?'M':'-',
			(m_core->op_B_alu)?'A':'-',
			(m_core->op_B_mem)?'M':'-');
#else
		printw(" A:xx B:xx");
#endif
*/
		printw(" PFPC=%08x", m_core->pf_pc);


		showins(ln, "I ",
			// {{{
#ifdef	OPT_PIPELINED
			!m_core->dcd_stalled,
#else
			1,
#endif
			m_core->pf_valid,
			//m_core->v__DOT__thecpu__DOT__instruction_gie,
			m_core->r_gie,
			0,
			(m_core->pf_instruction_pc),
			true); ln++;
			// m_core->pf_pc); ln++;
		// }}}
		showins(ln, "Dc",
			// {{{
			m_core->dcd_ce, m_core->dcd_valid,
			m_core->dcd_gie,
#ifdef	OPT_PIPELINED
			m_core->dcd_stalled,
#else
			0,
#endif
#ifdef	OPT_CIS
			((m_core->dcd_phase) ?
				(m_core->dcd_pc+2):m_core->dcd_pc) -4,
			m_core->dcd_phase
#else
			m_core->dcd_pc - 4,
			false
#endif
			); ln++;
		if (m_core->dcd_illegal)
			mvprintw(ln-1,10,"I");
		else if (m_core->dcd_M)
			mvprintw(ln-1,10,"M");
		// }}}
		showins(ln, "Op",
			// {{{
			m_core->op_ce,
			m_core->op_valid,
			m_core->op_gie,
#ifdef	op_stall
			m_core->op_stall,
#else
			0,
#endif
#ifdef	OPT_CIS
			m_core->op_pc-4+((m_core->op_phase)?2:0),
			m_core->op_phase
#else
			m_core->op_pc-4, false
#endif
			); ln++;
		if (m_core->op_illegal)
			mvprintw(ln-1,10,"I");
		else if (m_core->op_valid_mem)
			mvprintw(ln-1,10,"M");
		else if (m_core->op_valid_alu)
			mvprintw(ln-1,10,"A");
		// }}}
		if (m_core->op_valid_mem) {
			showins(ln, "Mm",
				// {{{
				m_core->mem_ce,
				m_core->mem_pc_valid,
				m_core->alu_gie,
#ifdef	OPT_PIPELINED
				m_core->mem_stall,
#else
				0,
#endif
				alu_pc_fn(),
#ifdef	OPT_CIS
				m_core->alu_phase
#else
				false
#endif
			);
			// }}}
		} else {
			showins(ln, "Al",
				// {{{
				m_core->alu_ce,
				m_core->alu_pc_valid,
				m_core->alu_gie,
#ifdef	OPT_PIPELINED
				alu_stall(),
#else
				0,
#endif
				alu_pc_fn(),
#ifdef	OPT_CIS
				m_core->alu_phase
#else
				false
#endif
			);
			// }}}
		} ln++;

		// Write-back
		// {{{
		if (m_core->wr_reg_ce)
			mvprintw(ln-1,10,"W");
		else if (m_core->alu_valid)
			mvprintw(ln-1,10,(m_core->alu_wR)?"w":"V");
		else if (m_core->mem_valid)
			mvprintw(ln-1,10,"v");
		else if (m_core->alu_illegal)
			mvprintw(ln-1,10,"I");
		// }}}
		// else if (m_core->v__DOT__thecpu__DOT__alu_illegal_op)
			// mvprintw(ln-1,10,"i");

		mvprintw(ln-5, 65,"%s %s",
			(m_core->op_break)?"OB":"  ",
			(m_core->new_pc)?"CLRP":"    ");
		mvprintw(ln-4, 48,
			(m_core->new_pc)?"new-pc":"      ");
		printw("(%s:%02x,%x)",
			(m_core->set_cond)?"SET":"   ",
			(m_core->op_F&0x0ff),
			(m_core->op_gie)
				?  (m_core->w_uflags)
				: (m_core->w_iflags));

		printw("(%s%s%s:%02x)",
			(m_core->op_wF)?"OF":"  ",
			(m_core->alu_wF)?"FL":"  ",
			(m_core->wr_flags_ce)?"W":" ",
			(m_core->alu_flags));
#ifdef	OPT_PIPELINED
		mvprintw(ln-3, 48, "Op(%x)%8x,%8x->",
			m_core->op_opn,
			m_core->op_Aid, m_core->op_Bid);
#else
		mvprintw(ln-3, 48, "");
#endif
		if (m_core->alu_valid)
			printw("%08x", m_core->alu_result);
		else
			printw("%8s","");
		mvprintw(ln-1, 48, "%s%s%s ",
			(m_core->alu_valid)?"A"
			  :((m_core->alu_busy)?"a":" "),
#ifdef	OPT_DIVIDE
			(m_core->div_valid)?"D"
			  :((m_core->div_busy)?"d":" "),
			(m_core->div_valid)?"F"
			  :((m_core->div_busy)?"f":" ")
#else
			  " ", " "
#endif
			  );
		if ((m_core->mem_ce)||(m_core->mem_valid)) {
			printw("MEM: %s%s %s%s %s %-5s",
				(m_core->op_valid_mem)?"M":" ",
				(m_core->mem_ce)?"CE":"  ",
				(m_core->mem_we)?"Wr ":"Rd ",
				(mem_stalled())?"PIPE":"    ",
				(m_core->mem_valid)?"V":" ",
				zip_regstr[(m_core->mem_wreg&0x1f)^0x10]);
		} else {
			printw("%18s", "");
		}
		// }}}
	}

	void	show_user_timers(bool v) {
		m_show_user_timers = v;
	}

	unsigned int	cmd_read(unsigned int a) {
		// {{{
		if (m_dbgfp) {
			dbg_flag= true;
			fprintf(m_dbgfp, "CMD-READ(%d)\n", a);
		}

		unsigned int v = wb_read(CMD_SREG(a));

		if (dbg_flag)
			fprintf(m_dbgfp, "CMD-READ(%d) = 0x%08x\n", a, v);
		dbg_flag = false;
		return v;
		// }}}
	}

	void	cmd_write(unsigned int a, int v) {
		// {{{
		// int	errcount = 0;
		if ((a&0x0f)==0x0f)
			dbg_flag = true;
		if (dbg_flag)
			fprintf(m_dbgfp, "CMD-WRITE(%d) <= 0x%08x\n", a, v);
		wb_write(CMD_SREG(a), v);
		// }}}
	}

	bool	halted(void) {
		return (m_core->cpu_halt != 0);
	}

	void	read_state(void) {
		// {{{
		int	ln= 0;
		bool	gie;

		read_raw_state();
		if (m_cursor < 0)
			m_cursor = 0;
#ifdef	ZIPBONES
		else if (m_cursor >= 32)
			m_cursor = 31;
#else
		else if (m_cursor >= 44)
			m_cursor = 43;
#endif

		mvprintw(ln,0, "Peripherals-RS");
		mvprintw(ln,40,"%-40s", "CPU State: ");
		{
			// {{{
			unsigned int v = wb_read(CMD_REG);
			mvprintw(ln,51, "");
			if (v & 0x010000)
				printw("EXT-INT ");
			if ((v & CMD_HALTED) == CMD_HALTED)
				printw("Halted ");
			else if (v & CMD_SLEEP)
				printw("Sleeping ");
			else if (v & CMD_GIE)
				printw("User Mod ");
			// if (v & CPU_BREAK)
			//	printw("Break-Enabled ");
			// if (v & CMD_INT)
			//	printw("PIC Enabled ");
			// }}}
		} ln++;
#ifdef	ZIPSYSTEM
		showval(ln, 0, "PIC ", m_state.m_p[0], (m_cursor==0));
		showval(ln,20, "WDT ", m_state.m_p[1], (m_cursor==1));
		showval(ln,40, "WBUS", m_state.m_p[2], false);
		showval(ln,60, "PIC2", m_state.m_p[3], (m_cursor==3));
		ln++;
		showval(ln, 0, "TMRA", m_state.m_p[4], (m_cursor==4));
		showval(ln,20, "TMRB", m_state.m_p[5], (m_cursor==5));
		showval(ln,40, "TMRC", m_state.m_p[6], (m_cursor==6));
		showval(ln,60, "JIF ", m_state.m_p[7], (m_cursor==7));

		ln++;
		if (!m_show_user_timers) {
			showval(ln, 0, "MTSK", m_state.m_p[12], (m_cursor==8));
			showval(ln,20, "MMST", m_state.m_p[13], (m_cursor==9));
			showval(ln,40, "MPST", m_state.m_p[14], (m_cursor==10));
			showval(ln,60, "MICT", m_state.m_p[15], (m_cursor==11));
		} else {
			showval(ln, 0, "UTSK", m_state.m_p[ 8], (m_cursor==8));
			showval(ln,20, "UMST", m_state.m_p[ 9], (m_cursor==9));
			showval(ln,40, "UPST", m_state.m_p[10], (m_cursor==10));
			showval(ln,60, "UICT", m_state.m_p[11], (m_cursor==11));
		}
#else
		ln += 2;
#endif

		ln++;
		ln++;
		unsigned int cc = m_state.m_sR[14];
		if (m_dbgfp) fprintf(m_dbgfp, "CC = %08x, gie = %d\n", cc,
			m_core->r_gie);
		gie = (cc & 0x020);
		if (gie)
			attroff(A_BOLD);
		else
			attron(A_BOLD);
		mvprintw(ln, 0, "Supervisor Registers");
		// {{{
		ln++;

		dispreg(ln, 0, "sR0 ", m_state.m_sR[ 0], (m_cursor==12));
		dispreg(ln,20, "sR1 ", m_state.m_sR[ 1], (m_cursor==13));
		dispreg(ln,40, "sR2 ", m_state.m_sR[ 2], (m_cursor==14));
		dispreg(ln,60, "sR3 ", m_state.m_sR[ 3], (m_cursor==15)); ln++;

		dispreg(ln, 0, "sR4 ", m_state.m_sR[ 4], (m_cursor==16));
		dispreg(ln,20, "sR5 ", m_state.m_sR[ 5], (m_cursor==17));
		dispreg(ln,40, "sR6 ", m_state.m_sR[ 6], (m_cursor==18));
		dispreg(ln,60, "sR7 ", m_state.m_sR[ 7], (m_cursor==19)); ln++;

		dispreg(ln, 0, "sR8 ", m_state.m_sR[ 8], (m_cursor==20));
		dispreg(ln,20, "sR9 ", m_state.m_sR[ 9], (m_cursor==21));
		dispreg(ln,40, "sR10", m_state.m_sR[10], (m_cursor==22));
		dispreg(ln,60, "sR11", m_state.m_sR[11], (m_cursor==23)); ln++;

		dispreg(ln, 0, "sR12", m_state.m_sR[12], (m_cursor==24));
		dispreg(ln,20, "sSP ", m_state.m_sR[13], (m_cursor==25));

		if (true) {
			mvprintw(ln,40, "%ssCC : 0x%08x",
				(m_cursor==26)?">":" ", cc);
		} else {
			char	cbuf[32];
			sprintf(cbuf, "%ssCC :%s%s%s%s%s%s%s",
				(m_cursor==26)?">":" ",
				(cc&0x01000)?"FE":"",
				(cc&0x00800)?"DE":"",
				(cc&0x00400)?"BE":"",
				(cc&0x00200)?"TP":"",
				(cc&0x00100)?"IL":"",
				(cc&0x00080)?"BK":"",
				((m_state.m_gie==0)&&(cc&0x010))?"HLT":"");
			mvprintw(ln,40, "%-14s",cbuf);
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		dispreg(ln,60, "sPC ", cmd_read(15), (m_cursor==27));
		ln++;
		// }}}

		if (gie)
			attron(A_BOLD);
		else
			attroff(A_BOLD);
		mvprintw(ln, 0, "User Registers");
		// {{{
		mvprintw(ln, 42, "DCDR=%02x %s",
			m_core->dcdR, (m_core->dcd_wR)?"W":" ");
		mvprintw(ln, 62, "OPR =%02x %s%s",
			m_core->op_R,
			(m_core->op_wR)?"W":" ",
			(m_core->op_wF)?"F":" ");
		ln++;
		dispreg(ln, 0, "uR0 ", m_state.m_uR[ 0], (m_cursor==28));
		dispreg(ln,20, "uR1 ", m_state.m_uR[ 1], (m_cursor==29));
		dispreg(ln,40, "uR2 ", m_state.m_uR[ 2], (m_cursor==30));
		dispreg(ln,60, "uR3 ", m_state.m_uR[ 3], (m_cursor==31)); ln++;

		dispreg(ln, 0, "uR4 ", m_state.m_uR[ 4], (m_cursor==32));
		dispreg(ln,20, "uR5 ", m_state.m_uR[ 5], (m_cursor==33));
		dispreg(ln,40, "uR6 ", m_state.m_uR[ 6], (m_cursor==34));
		dispreg(ln,60, "uR7 ", m_state.m_uR[ 7], (m_cursor==35)); ln++;

		dispreg(ln, 0, "uR8 ", m_state.m_uR[ 8], (m_cursor==36));
		dispreg(ln,20, "uR9 ", m_state.m_uR[ 9], (m_cursor==37));
		dispreg(ln,40, "uR10", m_state.m_uR[10], (m_cursor==38));
		dispreg(ln,60, "uR11", m_state.m_uR[11], (m_cursor==39)); ln++;

		dispreg(ln, 0, "uR12", m_state.m_uR[12], (m_cursor==40));
		dispreg(ln,20, "uSP ", m_state.m_uR[13], (m_cursor==41));
		cc = m_state.m_uR[14];
		if (false) {
			mvprintw(ln,40, "%cuCC : 0x%08x",
				(m_cursor == 42)?'>':' ', cc);
		} else {
			char	cbuf[32];
			sprintf(cbuf, "%cuCC :%s%s%s%s%s%s%s",
				(m_cursor == 42)?'>':' ',
				(cc & 0x1000)?"FE":"",
				(cc & 0x0800)?"DE":"",
				(cc & 0x0400)?"BE":"",
				(cc & 0x0200)?"TP":"",
				(cc & 0x0100)?"IL":"",
				(cc & 0x0040)?"ST":"",
				((m_state.m_gie)&&(cc & 0x010))?"SL":"");
			mvprintw(ln,40, "%-14s", cbuf);
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		dispreg(ln,60, "uPC ", m_state.m_uR[15], (m_cursor==43));
		// }}}

		attroff(A_BOLD);
		ln+=2;

		ln+=3;

		showins(ln, "I ",
			// {{{
#ifdef	OPT_PIPELINED
			!m_core->dcd_stalled,
#else
			1,
#endif
			m_core->pf_valid,
			m_core->r_gie,
			0,
			m_core->pf_instruction_pc,
			true); ln++;
			// m_core->pf_pc); ln++;
			// }}}
		showins(ln, "Dc",
			// {{{
			m_core->dcd_ce, m_core->dcd_valid,
			m_core->dcd_gie,
#ifdef	OPT_PIPELINED
			m_core->dcd_stalled,
#else
			0,
#endif
#ifdef	OPT_CIS
			((m_core->dcd_phase) ?
				(m_core->dcd_pc+2):m_core->dcd_pc) -4,
			m_core->dcd_phase
#else
			m_core->dcd_pc-4,
			false
#endif
			); ln++;
			// }}}
		showins(ln, "Op",
			// {{{
			m_core->op_ce,
			m_core->op_valid,
			m_core->op_gie,
#ifdef	OPT_PIPELINED
			m_core->op_stall,
#else
			0,
#endif
#ifdef	OPT_CIS
			m_core->op_pc-4+((m_core->op_phase)?2:0),
			m_core->op_phase
#else
			m_core->op_pc-4,
			false
#endif
			); ln++;
			// }}}
		if (m_core->op_valid_mem) {
			showins(ln, "Mm",
				// {{{
				m_core->mem_ce,
				m_core->mem_pc_valid,
				m_core->alu_gie,
#ifdef	OPT_PIPELINED
				m_core->mem_stall,
#else
				0,
#endif
				alu_pc_fn(),
#ifdef	OPT_CIS
				m_core->alu_phase
#else
				false
#endif
			);
			// }}}
		} else {
			showins(ln, "Al",
				// {{{
				m_core->alu_ce,
				m_core->alu_pc_valid,
				m_core->alu_gie,
#ifdef	OPT_PIPELINED
				alu_stall(),
#else
				0,
#endif
				alu_pc_fn(),
#ifdef	OPT_CIS
				m_core->alu_phase
#else
				false
#endif
			);
			// }}}
		} ln++;
		// }}}
	}

	void	tick(void) {
		// {{{
		int gie = m_core->r_gie;
		/*
		m_core->i_qspi_dat = m_flash(m_core->o_qspi_cs_n,
						m_core->o_qspi_sck,
						m_core->o_qspi_dat);
		*/

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

		// Bus information
		if ((dbg_flag)&&(m_dbgfp)) {
			// {{{
			fprintf(m_dbgfp, "BUS  %s %s %s @0x%08x/[0x%08x 0x%08x] %s %s\n",
				(m_core->o_wb_cyc)?"CYC":"   ",
				(m_core->o_wb_stb)?"STB":"   ",
				(m_core->o_wb_we)?"WE":"  ",
				(m_core->o_wb_addr<<2),
				(m_core->o_wb_data),
				(m_core->i_wb_data),
				(m_core->i_wb_stall)?"STALL":"     ",
				(m_core->i_wb_ack)?"ACK":"   ");
			fprintf(m_dbgfp, "DBG  %s %s %s @0x%08x/%d[0x%08x] %s %s [0x%08x] %s %s %s%s%s%s%s%s%s%s%s\n",
				(m_core->i_dbg_cyc)?"CYC":"   ",
				(m_core->i_dbg_stb)?"STB":
					((m_core->dbg_stb)?"DBG":"   "),
				((m_core->i_dbg_we)?"WE":"  "),
				(m_core->i_dbg_addr),0,
				m_core->i_dbg_data,
				(m_core->o_dbg_ack)?"ACK":"   ",
				(m_core->o_dbg_stall)?"STALL":"     ",
				(m_core->o_dbg_data),
				(m_core->cpu_halt)?"CPU-HALT ":"",
				"", // (m_core->r_halted)?"CPU-DBG_STALL":"",
				(m_core->dcd_valid)?"DCDV ":"",
				(m_core->op_valid)?"OPV ":"",
				(m_core->pf_cyc)?"PCYC ":"",
				(m_core->wb_cyc_gbl)?"GC":"  ",
				(m_core->wb_cyc_lcl)?"LC":"  ",
				(m_core->alu_wR)?"ALUW ":"",
				(m_core->alu_ce)?"ALCE ":"",
				(m_core->alu_valid)?"ALUV ":"",
				(m_core->mem_valid)?"MEMV ":"");
#ifdef	ZIPSYSTEM
			fprintf(m_dbgfp, " SYS %s %s %s @0x%08x/%d[0x%08x] %s [0x%08x]\n",
				(m_core->sys_cyc)?"CYC":"   ",
				(m_core->sys_stb)?"STB":"   ",
				(m_core->sys_we)?"WE":"  ",
				(m_core->sys_addr<<2),
				(m_core->dbg_addr<<2),
				(m_core->sys_data),
				(m_core->dbg_ack)?"ACK":"   ",
				(m_core->cpu_idata));
#endif
			// }}}
		}

		if (m_dbgfp)
			fprintf(m_dbgfp, "CEs %d/0x%08x,%d/0x%08x DCD: ->%02x, OP: ->%02x, ALU: halt=%d ce=%d, valid=%d, wr=%d  Reg=%02x, IPC=%08x, UPC=%08x\n",
				m_core->dcd_ce,
				m_core->dcd_pc,
				m_core->op_ce,
				m_core->op_pc-4,
				dcd_Aid()&0x01f,
				m_core->op_R,
				m_core->cpu_halt,
				m_core->alu_ce,
				m_core->alu_valid,
				m_core->alu_wR,
				m_core->alu_reg,
				m_core->cpu_ipc,
				m_core->cpu_upc);

		// Interrupt debugging
		// {{{
		if ((m_dbgfp)&&(!gie)&&(m_core->release_from_interrupt)) {
			// {{{
			fprintf(m_dbgfp, "RELEASE: int=%d, %d/%02x[%08x] ce=%d %d,%d,%d\n",
				m_core->cpu_interrupt,
				m_core->wr_reg_ce,
				m_core->wr_reg_id,
				m_core->wr_spreg_vl,
				// m_core->cmd_addr<<2,
				// m_core->dbg_idata,
				m_core->master_ce,
				m_core->alu_wR,
				m_core->alu_valid,
				m_core->mem_valid);
			// }}}
		} else if ((m_dbgfp)&&(gie)&&(m_core->switch_to_interrupt)) {
			// {{{
			fprintf(m_dbgfp, "SWITCH: %d/%02x[%08x] ce=%d %d,%d,%d, F%02x,%02x\n",
				m_core->wr_reg_ce,
				m_core->wr_reg_id,
				m_core->wr_spreg_vl,
				// m_core->cmd_addr<<2,
				// m_core->dbg_idata,
				m_core->master_ce,
				m_core->alu_wR,
				m_core->alu_valid,
				m_core->mem_valid,
				m_core->w_iflags,
				m_core->w_uflags);
			fprintf(m_dbgfp, "\tbrk=%s %d,%d\n",
				(m_core->master_ce)?"CE":"  ",
				m_core->break_en,
				m_core->op_break);
		} else if ((m_dbgfp)&&
				((m_core->op_break)
				||(m_core->alu_illegal)
				||(m_core->dcd_break))) {
			fprintf(m_dbgfp, "NOT SWITCHING TO GIE (gie = %d)\n", gie);
			fprintf(m_dbgfp, "\tbrk=%s breaken=%d,dcdbreak=%d,opbreak=%d,alu_illegal=%d\n",
				(m_core->master_ce)?"CE":"  ",
				m_core->break_en,
				m_core->dcd_break,
				m_core->op_break,
				m_core->alu_illegal);

			// }}}
		}
		// }}}

		if (m_dbgfp) {
			// if(m_core->v__DOT__thecpu__DOT__clear_pipeline)
				// fprintf(m_dbgfp, "\tClear Pipeline\n");
			if(m_core->new_pc)
				fprintf(m_dbgfp, "\tNew PC\n");
		}

		if (m_dbgfp) {
			unsigned long	v = m_tickcount;
			fprintf(m_dbgfp, "-----------  TICK (%08lx) ----------%s\n",
				v, (m_bomb)?" BOMBED!!":"");
		}
		m_mem(m_core->o_wb_cyc, m_core->o_wb_stb, m_core->o_wb_we,
			m_core->o_wb_addr & (maskb>>2), m_core->o_wb_data, m_core->o_wb_sel & 0x0f,
			m_core->i_wb_ack, m_core->i_wb_stall,m_core->i_wb_data);

		TESTB<SIMCLASS>::tick();

		if (m_core->cpu_sim) {
			execsim(m_core->cpu_sim_immv);
		}

		if ((m_dbgfp)&&(gie != m_core->r_gie)) {
			// {{{
			fprintf(m_dbgfp, "SWITCH FROM %s to %s: sPC = 0x%08x uPC = 0x%08x pf_pc = 0x%08x\n",
				(gie)?"User":"Supervisor",
				(gie)?"Supervisor":"User",
				m_core->cpu_ipc,
				m_core->cpu_upc,
				m_core->pf_pc);
			// }}}
		} if (m_dbgfp) {
			// {{{
			// Prefetch instruction feedback
			// {{{
#ifdef	OPT_TRADITIONAL_PFCACHE
			fprintf(m_dbgfp, "PFCACHE %s(%08x,%08x%s),%08x - %08x %s%s%s\n",
				(m_core->new_pc)?"N":" ",
				m_core->pf_pc,
				m_core->early_branch_pc,
				((m_core->early_branch)
				&&(m_core->dcd_valid)
				&&(!m_core->new_pc))?"V":"-",
				0, // m_core->pf_lastpc,
				m_core->pf_instruction_pc,
				" ", // (m_core->pf_r_v)?"R":" ",
				(m_core->pf_valid)?"V":" ",
				(m_core->pf_illegal)?"I":" ");
#endif
			// }}}

			// Instruction in decode stage
			// {{{
			dbgins("Dc - ",
				m_core->dcd_ce, m_core->dcd_valid,
				m_core->dcd_gie,
#ifdef	OPT_PIPELINED
				m_core->dcd_stalled,
#else
				0,
#endif
#ifdef	OPT_CIS
				(m_core->dcd_phase)?(m_core->dcd_pc-2)
					:(m_core->dcd_pc-4),
				m_core->dcd_phase,
#else
				m_core->dcd_pc-4, false,
#endif
				m_core->dcd_illegal);
			if (m_dbgfp) {
				fprintf(m_dbgfp, "\t\t\tR[%2d] = (*Dc=%d%s)[ A[%2d], B[%2d] + %08x], dcd_pc = %08x\n",
					m_core->dcdR,
					m_core->dcd_opn,
					(m_core->dcd_M)?"M":" ",
#define	dcd_I	CPUVAR(_dcd_I)
					m_core->dcdB &0x0f,
					m_core->dcdA &0x0f,
					m_core->dcd_I,
					m_core->dcd_pc);
			}
			// }}}

			// Read operands instruction
			// {{{
			dbgins("Op - ",
				m_core->op_ce,
				m_core->op_valid,
				m_core->op_gie,
#ifdef	OPT_PIPELINED
				m_core->op_stall,
#else
				0,
#endif
				m_core->op_pc-4,
#ifdef	OPT_CIS
				m_core->op_phase,
#else
				false,
#endif
				m_core->op_illegal);
			if (m_dbgfp) {
				fprintf(m_dbgfp, "\t\t\t(*OP=%d)[ A = 0x%08x , B = 0x%08x ], op_pc= %08x\n",
					m_core->op_opn,
					m_core->op_Av,
					m_core->op_Bv,
					m_core->op_pc);
			}
			// }}}

			// ALU instruction
			// {{{
			dbgins("Al - ",
				m_core->alu_ce,
				m_core->alu_pc_valid,
				m_core->alu_gie,
#ifdef	OPT_PIPELINED
				alu_stall(),
#else
				0,
#endif
				alu_pc_fn(),
#ifdef	OPT_CIS
				m_core->alu_phase,
#else
				false,
#endif
				m_core->alu_illegal);
			// }}}
			if (m_core->wr_reg_ce)
				fprintf(m_dbgfp, "WB::Reg[%2x] <= %08x\n",
					m_core->wr_reg_id,
					m_core->wr_gpreg_vl);
			if (m_core->wr_flags_ce)
				fprintf(m_dbgfp, "WB::Flags <= %02x\n",
					m_core->alu_flags);
			// }}}
		}

		// Divide unit info
		// {{{
#ifdef	OPT_DIVIDE
		if ((m_dbgfp)&&((m_core->div_valid)
			||(m_core->div_ce)
			||(m_core->div_busy)
			)) {
			fprintf(m_dbgfp, "DIV: %s %s %s %s[%2x] GP:%08x/SP:%08x %s:0x%08x\n",
				(m_core->div_ce)?"CE":"  ",
				(m_core->div_busy)?"BUSY":"    ",
				(m_core->div_valid)?"VALID":"     ",
				(m_core->wr_reg_ce)?"REG-CE":"      ",
				m_core->wr_reg_id,
				m_core->wr_gpreg_vl,
				m_core->wr_spreg_vl,
				(m_core->alu_pc_valid)?"PCV":"   ",
				alu_pc_fn());

			fprintf(m_dbgfp, "ALU-PC: %08x %s %s\n",
				alu_pc_fn(),
				(m_core->alu_pc_valid)?"VALID":"",
				(m_core->alu_gie)?"ALU-GIE":"");
		}
#endif
		// }}}

		if (((m_core->alu_pc_valid)
			||(m_core->mem_pc_valid))
			&&(!m_core->new_pc)) {
			// {{{
			unsigned long iticks = m_tickcount - m_last_instruction_tickcount;
			if (m_profile_fp) {
				unsigned buf[2];
				buf[0] = alu_pc_fn();
				buf[1] = iticks;
				fwrite(buf, sizeof(unsigned), 2, m_profile_fp);
			}
			m_last_instruction_tickcount = m_tickcount;
			// }}}
		}
		// }}}
	}

	bool	test_success(void) {
		// {{{
		if ((m_exit)&&(m_rcode == 0))
			return true;
		return ((!m_core->r_gie)
			&&(m_core->r_sleep));
		// }}}
	}

	bool	pfstall(void) {
		return((!(m_core->pformem_owner))
			||(m_core->cpu_stall));
	}
	unsigned	dcd_Aid(void) {
		return (m_core->dcdA & 0x1f);
	}
	unsigned	dcd_Bid(void) {
		return (m_core->dcdB & 0x1f);
	}

	bool	op_valid_fn(void) {
		return (m_core->op_valid !=0);
	}

	bool	mem_stalled(void) {
		// {{{
		bool	a, b, c, d, wr_write_cc, wr_write_pc, op_gieb;

		wr_write_cc=((m_core->wr_reg_id&0x0f)==0x0e);
		wr_write_pc=((m_core->wr_reg_id&0x0f)==0x0f);
		op_gieb = m_core->op_gie;

#ifdef	OPT_PIPELINED_BUS_ACCESS
		//a = m_core->v__DOT__thecpu__DOT__mem_pipe_stalled;
		a = mem_pipe_stalled();
		b = (!m_core->op_pipe)&&(m_core->mem_busy);
#else
		a = false;
		b = false;
#endif
		d = ((wr_write_pc)||(wr_write_cc));
		c = ((m_core->wr_reg_ce)
			&&(((m_core->wr_reg_id&0x010)?true:false)==op_gieb)
			&&d);
		d =(m_core->op_valid_mem)&&((a)||(b)||(c));
		return ((!m_core->master_ce)||(d));
		// }}}
	}

	unsigned	alu_pc_fn(void) {
		// {{{
		/*
		unsigned	r = op_pc();
		if (m_core->op_valid)
			r--;
		return r;
		*/
		return m_core->alu_pc-4;
		// }}}
	}

	int	alu_stall(void) {
		// {{{
		bool	stall;
#ifdef	OP_PIPELINED
		stall = (m_core->master_stall)||(m_core->mem_rdbusy);
		stall = (stall)&& m_core->op_valid_alu;
		stall = (stall)|| ((m_core->wr_reg_ce)&&(m_core->wr_write_cc));
#else
		stall = (m_core->master_stall)&&(m_core->op_valid_alu);
#endif
		/*
		unsigned	r = op_pc();
		if (m_core->op_valid)
			r--;
		return r;
		*/
		return (stall)?1:0;
		// }}}
	}

#ifdef	OPT_PIPELINED_BUS_ACCESS
	// {{{
	bool	mem_pipe_stalled(void) {
		int	r = 0;
		r = ((m_core->wb_cyc_gbl)
		 ||(m_core->wb_cyc_lcl));
		r = r && ((m_core->mem_stall)
			||(
				((!m_core->mem_stb_gbl)
				&&(!m_core->mem_stb_lcl))));
		return r;
		// return m_core->v__DOT__thecpu__DOT__mem_pipe_stalled;
	}
	// }}}
#endif

	bool	test_failure(void) {
		// {{{
		if ((m_exit)&&(m_rcode != 0))
			return true;
		if (m_core->r_sleep)
			return false;
		return false;
		// }}}
	}

	void	wb_write(unsigned a, unsigned int v) {
		// {{{
		int	errcount = 0;
		if (m_dbgfp)
			fprintf(m_dbgfp, "WB-WRITE(%04x, %08x)\n", a, v);
		mvprintw(0,35, "%40s", "");
		mvprintw(0,40, "wb_write(%d,%x)", a, v);
		m_core->i_dbg_cyc = 1;
		m_core->i_dbg_stb = 1;
		m_core->i_dbg_we  = 1;
		m_core->i_dbg_sel = 15;
		m_core->i_dbg_addr = (a>>2);
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
		mvprintw(0,35, "%40s", "");
		mvprintw(0,40, "wb_write -- complete");


		if (errcount >= 100) {
			if (m_dbgfp) fprintf(m_dbgfp, "WB-WRITE: ERRCount = %d, BOMB!!\n", errcount);
			m_bomb = true;
		}
		// }}}
	}

	unsigned long	wb_read(unsigned a) {
		// {{{
		unsigned int	v;
		int	errcount = 0;
		mvprintw(0,35, "%40s", "");
		mvprintw(0,40, "wb_read(0x%08x)", a);
		m_core->i_dbg_cyc = 1;
		m_core->i_dbg_stb = 1;
		m_core->i_dbg_we  = 0;
		m_core->i_dbg_addr = (a>>2);

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

		mvprintw(0,35, "%40s", "");
		mvprintw(0,40, "wb_read = 0x%08x", v);

		if (errcount >= 100) {
			if (m_dbgfp) fprintf(m_dbgfp, "WB-READ: ERRCount = %d, BOMB!!\n", errcount);
			m_bomb = true;
		}
		return v;
		// }}}
	}

	void	cursor_up(void) {
		// {{{
#ifdef	ZIPSYSTEM
		if (m_cursor > 3)
			m_cursor -= 4;
#else
		if (m_cursor > 12+3)
			m_cursor =- 4;
#endif
		// }}}
	} void	cursor_down(void) {
		// {{{
		if (m_cursor < 40)
			m_cursor += 4;
		// }}}
	} void	cursor_left(void) {
		// {{{
#ifdef	ZIPSYSTEM
		if (m_cursor > 0)
			m_cursor--;
#else
		if (m_cursor > 12)
			m_cursor--;
#endif
		else	m_cursor = 43;
		// }}}
	} void	cursor_right(void) {
		// {{{
#ifdef	ZIPSYSTEM
		if (m_cursor < 43)
			m_cursor++;
		else	m_cursor = 0;
#else
		if (m_cursor < 43)
			m_cursor++;
		else	m_cursor = 12;
#endif
		// }}}
	}

	int	cursor(void) { return m_cursor; }

	void	jump_to(ZIPI address) {
		// {{{
		if (m_dbgfp)
			fprintf(m_dbgfp, "JUMP_TO(%08x) ... Setting PC to %08x\n", address, address & -4);
		wb_write(CMD_REG, CMD_HALT | CMD_CATCH);
		wb_write(CPU_sPC, address & -4);
		// }}}
	}

	void	dump_state(void) {
		// {{{
		if (m_dbgfp)
			dump_state(m_dbgfp);
		// }}}
	}

	void	dump_state(FILE *fp) {
		// {{{
		if (!fp)
			return;
		fprintf(fp, "FINAL STATE: %s\n",
			(m_state.m_gie)?"GIE(User-Mode)":"Supervisor-mode");
		fprintf(fp, "Supervisor Registers\n");
		for(int i=0; i<16; i++) {
			char str[16];
			if (i==13)
				sprintf(str, "sSP");
			else if (i==14)
				sprintf(str, "sCC");
			else if (i==15)
				sprintf(str, "sPC");
			else // if (i<=12)
				sprintf(str, "s-%2d", i);
			dbgreg(fp, i, str, m_state.m_sR[i]);
			if ((i&3)==3)
				fprintf(fp, "\n");
		}
		fprintf(fp, "User Registers\n");
		for(int i=0; i<16; i++) {
			char str[16];
			if (i==13)
				sprintf(str, "uSP");
			else if (i==14)
				sprintf(str, "uCC");
			else if (i==15)
				sprintf(str, "uPC");
			else // if (i<=12)
				sprintf(str, "u-%2d", i);
			dbgreg(fp, i, str, m_state.m_uR[i]);
			if ((i&3)==3)
				fprintf(fp, "\n");
		}
		// }}}
	}

	void dump(const uint32_t *regp) {
		// {{{
		uint32_t	uccv, iccv;

		if (!m_console)
			return;

		fflush(stderr);
		fflush(stdout);
		printf("ZIPM--DUMP: ");
		if (m_core->r_gie)
			printf("Interrupts-enabled\n");
		else
			printf("Supervisor mode\n");
		printf("\n");

		iccv = m_core->w_iflags;
		uccv = m_core->w_uflags;

		printf("sR0 : %08x ", regp[0]);
		printf("sR1 : %08x ", regp[1]);
		printf("sR2 : %08x ", regp[2]);
		printf("sR3 : %08x\n",regp[3]);
		printf("sR4 : %08x ", regp[4]);
		printf("sR5 : %08x ", regp[5]);
		printf("sR6 : %08x ", regp[6]);
		printf("sR7 : %08x\n",regp[7]);
		printf("sR8 : %08x ", regp[8]);
		printf("sR9 : %08x ", regp[9]);
		printf("sR10: %08x ", regp[10]);
		printf("sR11: %08x\n",regp[11]);
		printf("sR12: %08x ", regp[12]);
		printf("sSP : %08x ", regp[13]);
		printf("sCC : %08x ", iccv);
		printf("sPC : %08x\n",regp[15]);

		printf("\n");

		printf("uR0 : %08x ", regp[16]);
		printf("uR1 : %08x ", regp[17]);
		printf("uR2 : %08x ", regp[18]);
		printf("uR3 : %08x\n",regp[19]);
		printf("uR4 : %08x ", regp[20]);
		printf("uR5 : %08x ", regp[21]);
		printf("uR6 : %08x ", regp[22]);
		printf("uR7 : %08x\n",regp[23]);
		printf("uR8 : %08x ", regp[24]);
		printf("uR9 : %08x ", regp[25]);
		printf("uR10: %08x ", regp[26]);
		printf("uR11: %08x\n",regp[27]);
		printf("uR12: %08x ", regp[28]);
		printf("uSP : %08x ", regp[29]);
		printf("uCC : %08x ", uccv);
		printf("uPC : %08x\n",regp[31]);
		printf("\n");
		fflush(stderr);
		fflush(stdout);
		// }}}
	}


	void	execsim(const uint32_t imm) {
		// {{{
		uint32_t	*regp = m_core->cpu_regs;
		int		rbase;
		rbase = (m_core->r_gie)?16:0;

		if ((dbg_flag)&&(m_dbgfp)) {
			fprintf(m_dbgfp, "EXECSIM(0x%05x)\n", imm);
		}

		fflush(stdout);
		if ((imm & 0x03fffff)==0)
			// Ignore a NOOP
			return;
		// fprintf(stderr, "SIM-INSN(0x%08x)\n", imm);
		if ((imm & 0x0fffff)==0x00100) {
			// SIM Exit(0)
			// {{{
			m_rcode = 0;
			m_exit = true;
			if ((dbg_flag)&&(m_dbgfp))
				fprintf(m_dbgfp, "\tEXECSIM: SIM Exit(0)\n");
			// }}}
		} else if ((imm & 0x0ffff0)==0x00310) {
			// SIM Exit(User-Reg)
			// {{{
			int	rcode;
			rcode = regp[(imm&0x0f)+16] & 0x0ff;
			m_rcode = rcode;
			m_exit = true;
			if ((dbg_flag)&&(m_dbgfp))
				fprintf(m_dbgfp, "\tEXECSIM: SIM Exit(%d)\n", m_rcode);
			// }}}
		} else if ((imm & 0x0ffff0)==0x00300) {
			// SIM Exit(Reg)
			// {{{
			int	rcode;
			rcode = regp[(imm&0x0f)+rbase] & 0x0ff;
			m_rcode = rcode;
			m_exit = true;
			if ((dbg_flag)&&(m_dbgfp))
				fprintf(m_dbgfp, "\tEXECSIM: SIM Exit(%d)\n", m_rcode);
			// }}}
		} else if ((imm & 0x0fff00)==0x00100) {
			// SIM Exit(Imm)
			// {{{
			int	rcode;
			rcode = imm & 0x0ff;
			m_exit = true;
			m_rcode = rcode;
			if ((dbg_flag)&&(m_dbgfp))
				fprintf(m_dbgfp, "\tEXECSIM: SIM Exit(%d)\n", m_rcode);
			// }}}
		} else if ((imm & 0x0fffff)==0x002ff) {
			// Full/unconditional dump -- Now handled internally
			// {{{
			if (0 && m_console) {
				printf("SIM-DUMP\n");
				dump(regp);
			}
			// }}}
		} else if ((imm & 0x0ffff0)==0x00200) {
			// Dump a register -- Now handled internally
			// {{{
			if (0 && m_console) {
				int rid = (imm&0x0f)+rbase;
				//printf("%8lu @%08x R[%2d] = 0x%08x\n",
				//	m_time_ps/1000,
				//	m_core->cpu_ipc, rid, regp[rid]);
				printf("R[%2d] = 0x%08x\n", rid&0x0f,regp[rid]);
			}
			// }}}
		} else if ((imm & 0x0ffff0)==0x00210) {
			// Dump a user register -- Now handled internally
			// {{{
			if (0 && m_console) {
				int rid = (imm&0x0f);
				/*
				printf("%8lu @%08x uR[%2d] = 0x%08x\n",
					m_time_ps/1000, m_core->cpu_ipc,
					rid, regp[rid+16]);
				*/
				printf("uR[%2d] = 0x%08x\n",
					rid, regp[rid+16]);
			}
			// }}}
		} else if ((imm & 0x0ffff0)==0x00230) {
			// SOUT[User Reg] -- Handled internally
			// {{{
			if (0 && m_console) {
				int rid = (imm&0x0f)+16;
				printf("%c", regp[rid]&0x0ff);
			}
			// }}}
		} else if ((imm & 0x0fffe0)==0x00220) {
			// SOUT[User Reg] -- Handled internally
			// {{{
			if (0 && m_console) {
				int rid = (imm&0x0f)+rbase;
				printf("%c", regp[rid]&0x0ff);
			}
			// }}}
		} else if ((imm & 0x0fff00)==0x00400) {
			// SOUT[User Reg] -- Handled internally
			// {{{
			if (0 && m_console) {
				// SOUT[Imm]
				printf("%c", imm&0x0ff);
			}
			// }}}
		} else { // if ((insn & 0x0f7c00000)==0x77800000)
			if (m_console) {
				uint32_t	immv = imm & 0x03fffff;
				// Simm instruction that we dont recognize
				// if (imm)
				// printf("SIM 0x%08x\n", immv);
				printf("SIM 0x%08x (ipc = %08x, upc = %08x)\n", immv,
					m_core->cpu_ipc,
					m_core->cpu_upc);
			}
		} if (m_console)
			fflush(stdout);
		// }}}
	}
};
// }}}

// get_value
// {{{
void	get_value(ZIPCPU_TB *tb) {
	int	wy, wx, ra;
	int	c = tb->cursor();

	wx = (c & 0x03) * 20 + 9;
	wy = (c>>2);
	if (wy >= 3+4)
		wy++;
	if (wy > 3)
		wy += 2;
	wy++;

	if (c >= 12)
		ra = c - 12;
	else
		ra = c + 32;

	bool	done = false;
	char	str[16];
	int	pos = 0; str[pos] = '\0';
	while(!done) {
		int	chv = getch();
		switch(chv) {
		case KEY_ESCAPE:
			pos = 0; str[pos] = '\0'; done = true;
			break;
		case KEY_RETURN: case KEY_ENTER: case KEY_UP: case KEY_DOWN:
			done = true;
			break;
		case KEY_LEFT: case KEY_BACKSPACE:
			if (pos > 0) pos--;
			break;
		case CTRL('L'): redrawwin(stdscr); break;
		case KEY_CLEAR:
			pos = 0;
			break;
		case '0': case ' ': str[pos++] = '0'; break;
		case '1': str[pos++] = '1'; break;
		case '2': str[pos++] = '2'; break;
		case '3': str[pos++] = '3'; break;
		case '4': str[pos++] = '4'; break;
		case '5': str[pos++] = '5'; break;
		case '6': str[pos++] = '6'; break;
		case '7': str[pos++] = '7'; break;
		case '8': str[pos++] = '8'; break;
		case '9': str[pos++] = '9'; break;
		case 'A': case 'a': str[pos++] = 'A'; break;
		case 'B': case 'b': str[pos++] = 'B'; break;
		case 'C': case 'c': str[pos++] = 'C'; break;
		case 'D': case 'd': str[pos++] = 'D'; break;
		case 'E': case 'e': str[pos++] = 'E'; break;
		case 'F': case 'f': str[pos++] = 'F'; break;
		}

		if (pos > 8)
			pos = 8;
		str[pos] = '\0';

		attron(A_NORMAL | A_UNDERLINE);
		mvprintw(wy, wx, "%-8s", str);
		if (pos > 0) {
			attron(A_NORMAL | A_UNDERLINE | A_BLINK);
			mvprintw(wy, wx+pos-1, "%c", str[pos-1]);
		}
		attrset(A_NORMAL);
	}

	if (pos > 0) {
		int	v;
		v = strtoul(str, NULL, 16);
		if (!tb->halted()) { // Set the register
			// {{{
			tb->m_core->cpu_halt = 1;
			tb->wb_write(ra, v);
			tb->wb_write(CMD_REG, CMD_CATCH | CMD_GO);
			// }}}
		} else
			tb->cmd_write(ra, v);
	}
}
// }}}

void	usage(void) {
	// {{{
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
	// }}}
}

bool	signalled = false;

void	sigint(int v) {
	signalled = true;
}

int	main(int argc, char **argv) {
	Verilated::commandArgs(argc, argv);
	ZIPCPU_TB	*tb = new ZIPCPU_TB();
	bool		autorun = false, exit_on_done = false, autostep=false;
	ZIPI		entry = RAMBASE;

	signal(SIGINT, sigint);

	if (argc <= 1) {
		// {{{
		usage();
		exit(-1);
		// }}}
	} else for(int argn=1; argn<argc; argn++) {
		// {{{
		if (argv[argn][0] == '-') {
			switch(argv[argn][1]) {
			case 'a':
				autorun = true;
				break;
			case 'e':
				exit_on_done = true;
				break;
			case 'h':
				usage();
				exit(0);
				break;
			case 's':
				autostep = true;
				break;
			default:
				usage();
				exit(-1);
				break;
			}
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
		// }}}
	}


	if (autorun) {
		// {{{
		bool	done = false;

		printf("Running in non-interactive mode\n");
		tb->m_console = true;
		tb->reset();
		// tb->m_core->cpu_halt = 1;
		tb->wb_write(CMD_REG, CMD_HALT|CMD_RESET|CMD_CATCH);
		tb->wb_write(CPU_sPC, entry);
		// Wait for the reset to release, leaving the CPU halted
		while(tb->wb_read(CMD_REG) & CMD_RESET)
			;
		// Then release the CPU
		tb->wb_write(CMD_REG, CMD_GO|CMD_CATCH);	// Release from halt and reset
		tb->m_bomb = false;
		while(!done) {
			tb->tick();

			/*
			printf("PC = %08x:%08x (%08x)\n",
				tb->m_core->cpu_ipc,
				tb->m_core->cpu_upc,
				tb->m_core->alu_pc);
			*/

			done = (tb->test_success())||(tb->test_failure());
			done = done || signalled;
		}
		// }}}
	} else if (autostep) {
		// {{{
		bool	done = false;

		printf("Running in non-interactive mode, via step commands\n");
		tb->m_console = true;
		tb->reset();
		tb->wb_write(CMD_REG, CMD_HALT|CMD_RESET|CMD_CATCH);
		tb->wb_write(CPU_sPC, entry);
		tb->wb_write(CMD_REG, CMD_GO|CMD_CATCH);	// Release from reset
		tb->m_bomb = false;
		while(!done) {
			tb->wb_write(CMD_REG, CMD_STEP|CMD_CATCH);
			/*
			printf("PC = %08x:%08x (%08x)\n",
				tb->m_core->cpu_ipc, tb->m_core->cpu_upc,
				tb->m_core->alu_pc);
			*/
			done = (tb->test_success())||(tb->test_failure());
			done = done || signalled;
		}
		// }}}
	} else { // Interactive
		// {{{
		initscr();
		raw();
		noecho();
		keypad(stdscr, true);

		tb->reset();
		tb->wb_write(CMD_REG, CMD_HALT|CMD_RESET|CMD_CATCH);
		tb->wb_write(CPU_sPC, entry);
		tb->wb_write(CMD_REG, CMD_GO|CMD_CATCH);	// Release from reset

		int	chv = 'q';

		bool	done = false, halted = true, manual = true,
			high_speed = false;

		halfdelay(1);
			// tb->show_state();

		while(!done) {
			// {{{
			if ((high_speed)&&(!manual)&&(!halted)) {
				// {{{
				// chv = getch();

				struct	pollfd	fds[1];
				fds[0].fd = STDIN_FILENO;
				fds[0].events = POLLIN;

				if (poll(fds, 1, 0) > 0)
					chv = getch();
				else
					chv = ERR;
				// }}}
			} else
				chv = getch();

			switch(chv) {
			// {{{
			case 'h': case 'H':
				tb->wb_write(CMD_REG, CMD_HALT|CMD_CATCH);
				if (!halted)
					erase();
				halted = true;
				break;
			case 'G':
				high_speed = true;
				// cbreak();
			case 'g':
				tb->wb_write(CMD_REG, CMD_GO|CMD_CATCH);
				if (halted)
					erase();
				halted = false;
				manual = false;
				break;
			case 'm':
				tb->show_user_timers(false);
				break;
			case 'q': case 'Q':
				done = true;
				break;
			case 'r': case 'R':
				if (manual)
					tb->reset();
				else
					tb->wb_write(CMD_REG, CMD_RESET|CMD_HALT|CMD_CATCH);
				halted = true;
				erase();
				break;
			case 's':
				if (!halted)
					erase();
				tb->step();
				manual = false;
				halted = true;
				// if (high_speed)
					// halfdelay(1);
				high_speed = false;
				break;
			case 'S':
				if ((!manual)||(halted))
					erase();
				manual = true;
				halted = true;
				// if (high_speed)
					// halfdelay(1);
				high_speed = false;
				tb->m_core->cpu_halt = 0;
				tb->m_core->cmd_step = 1;
				tb->eval();
				tb->tick();
				break;
			case 'T': //
				if ((!manual)||(halted))
					erase();
				manual = true;
				halted = true;
				// if (high_speed)
					// halfdelay(1);
				high_speed = false;
				tb->m_core->cpu_halt = 1;
				tb->m_core->cmd_step = 0;
				tb->eval();
				tb->tick();
				break;
			case 't':
				if ((!manual)||(halted))
					erase();
				manual = true;
				halted = false;
				// if (high_speed)
					// halfdelay(1);
				high_speed = false;
				tb->m_core->cpu_halt = 0;
				tb->tick();
				break;
			case 'u':
				tb->show_user_timers(true);
				break;
			case	KEY_IC: case KEY_ENTER: case KEY_RETURN:
				get_value(tb);
				break;
			case	KEY_UP:		tb->cursor_up();	break;
			case	KEY_DOWN:	tb->cursor_down();	break;
			case	KEY_LEFT:	tb->cursor_left();	break;
			case	KEY_RIGHT:	tb->cursor_right();	break;
			case CTRL('L'):	redrawwin(stdscr); break;
			case ERR: case KEY_CLEAR:
			default:
				if (!manual)
					tb->tick();
			// }}}
			}

			if (manual) {
				tb->show_state();
			} else if (halted) {
				if (tb->m_dbgfp)
					fprintf(tb->m_dbgfp, "\n\nREAD-STATE ******\n");
				tb->read_state();
			} else
				tb->show_state();

			if (tb->m_core->i_reset)
				done =true;
			if ((tb->m_bomb)||(signalled))
				done = true;

			if (exit_on_done) {
				if (tb->test_success())
					done = true;
				if (tb->test_failure())
					done = true;
			}
			// }}}
		}
		endwin();
		// }}}
	}
#ifdef	MANUAL_STEPPING_MODE
	 else { // Manual stepping mode
		// {{{
		tb->jump_to(entry);
		tb->show_state();

		while('q' != tolower(chv = getch())) {
			// {{{
			tb->tick();
			tb->show_state();

			if (tb->test_success())
				break;
			else if (tb->test_failure())
				break;
			else if (signalled)
				break;
			// }}}
		}
		// }}}
	}
#endif

	printf("\n");
	if (tb->test_failure()) {
		tb->dump_state();
	}

#ifdef	ZIPSYSTEM
	printf("Clocks used         : %08x\n", tb->m_core->mtc_data);
	printf("Instructions Issued : %08x\n", tb->m_core->mic_data);
	printf("Tick Count          : %08lx\n", tb->m_tickcount);
	if (tb->m_core->mtc_data != 0)
		printf("Instructions / Clock: %.2f\n",
			(double)tb->m_core->mic_data
			/ (double)tb->m_core->mtc_data);
#endif

	int	rcode = 0;
	if (tb->m_bomb) {
		printf("TEST BOMBED\n");
		rcode = -1;
	} else if (tb->test_success()) {
		printf("SUCCESS!\n");
	} else if (tb->test_failure()) {
		rcode = -2;
		printf("TEST FAILED!\n");
	} else
		printf("User quit\n");

#ifdef	VM_COVERAGE
	VerilatedCov::write("vlt_coverage.dat");
#endif
	delete tb;
	exit(rcode);
}

