///////////////////////////////////////////////////////////////////////////////
//
// Filename:	zippy_tb.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A bench simulator for the CPU.  Eventually, you should be
//		able to give this program the name of a piece of compiled
//		code to load into memory.  For now, we hand assemble with the
//		computers help.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
///////////////////////////////////////////////////////////////////////////////
//
//
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <poll.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <ctype.h>
#include <ncurses.h>

#include "verilated.h"
#include "Vzipsystem.h"
#include "cpudefs.h"

#include "testb.h"
// #include "twoc.h"
// #include "qspiflashsim.h"
#include "memsim.h"
#include "zopcodes.h"
#include "zparser.h"

#define	CMD_REG		0
#define	CMD_DATA	1
#define	CMD_GIE		(1<<13)
#define	CMD_SLEEP	(1<<12)
#define	CMD_CLEAR_CACHE	(1<<11)
#define	CMD_HALT	(1<<10)
#define	CMD_STALL	(1<<9)
#define	CMD_INT		(1<<7)
#define	CMD_RESET	(1<<6)
#define	CMD_STEP	((1<<8)|CMD_HALT)

#define	KEY_ESCAPE	27
#define	KEY_RETURN	10
#define	CTRL(X)		((X)&0x01f)

#define	MAXERR		10000

#define	LGRAMLEN	20
#define	RAMBASE		0x100000
#define	MEMWORDS	(1<<LGRAMLEN)

class	SPARSEMEM {
public:
	bool	m_valid;
	unsigned int	m_a, m_d;
};

class	ZIPSTATE {
public:
	bool		m_valid, m_gie, m_last_pc_valid;
	unsigned int	m_sR[16], m_uR[16];
	unsigned int	m_p[20];
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
class	ZIPPY_TB : public TESTB<Vzipsystem> {
public:
	unsigned long	m_mem_size;
	MEMSIM		m_mem;
	// QSPIFLASHSIM	m_flash;
	FILE		*m_dbgfp, *m_profile_fp;
	bool		dbg_flag, bomb, m_show_user_timers;
	int		m_cursor;
	unsigned long	m_last_instruction_tickcount;
	ZIPSTATE	m_state;

	ZIPPY_TB(void) : m_mem_size(MEMWORDS), m_mem(m_mem_size) {
		if (false) {
			m_dbgfp = fopen("dbg.txt", "w");
			dbg_flag = true;
			gbl_dbgfp = m_dbgfp;
		} else {
			m_dbgfp = NULL;
			dbg_flag = false;
			gbl_dbgfp = NULL;
		}
		bomb = false;
		m_cursor = 0;
		m_show_user_timers = false;

		m_last_instruction_tickcount = 0l;
		if (true) {
			m_profile_fp = fopen("pfile.bin","wb");
		} else {
			m_profile_fp = NULL;
		}
	}

	~ZIPPY_TB(void) {
		if (m_dbgfp)
			fclose(m_dbgfp);
		if (m_profile_fp)
			fclose(m_profile_fp);
	}

	void	reset(void) {
		// m_flash.debug(false);
		TESTB<Vzipsystem>::reset();
	}

	bool	on_tick(void) {
		tick();
		return true;
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
		for(int i=0; i<20; i++)
			m_state.m_p[i]  = cmd_read(i+32);

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
		for(int i=0; i<16; i++)
			m_state.m_sR[i] = m_core->v__DOT__thecpu__DOT__regset[i];
		m_state.m_sR[14] = (m_state.m_sR[14]&0xffffe000)|m_core->v__DOT__thecpu__DOT__w_iflags;
		m_state.m_sR[15] = m_core->v__DOT__thecpu__DOT__ipc;
		for(int i=0; i<16; i++)
			m_state.m_uR[i] = m_core->v__DOT__thecpu__DOT__regset[i+16];
		m_state.m_uR[14] = (m_state.m_uR[14]&0xffffe000)|m_core->v__DOT__thecpu__DOT__w_uflags;
		m_state.m_uR[15] = m_core->v__DOT__thecpu__DOT__upc;

		m_state.m_gie = m_core->v__DOT__thecpu__DOT__gie;
		m_state.m_pc  = (m_state.m_gie) ? (m_state.m_uR[15]):(m_state.m_sR[15]);
		m_state.m_sp  = (m_state.m_gie) ? (m_state.m_uR[13]):(m_state.m_sR[13]);

		m_state.m_p[0] = m_core->v__DOT__pic_data;
		m_state.m_p[1] = m_core->v__DOT__watchdog__DOT__r_value;
		if (!m_show_user_timers) {	
			m_state.m_p[2] = m_core->v__DOT__watchbus__DOT__r_value;
		} else {
			m_state.m_p[2] = m_core->v__DOT__r_wdbus_data;
		}

		m_state.m_p[3] = m_core->v__DOT__genblk7__DOT__ctri__DOT__r_int_state;
		m_state.m_p[4] = m_core->v__DOT__timer_a__DOT__r_value;
		m_state.m_p[5] = m_core->v__DOT__timer_b__DOT__r_value;
		m_state.m_p[6] = m_core->v__DOT__timer_c__DOT__r_value;
		m_state.m_p[7] = m_core->v__DOT__jiffies__DOT__r_counter;

		m_state.m_p[ 8] = m_core->v__DOT__utc_data;
		m_state.m_p[ 9] = m_core->v__DOT__uoc_data;
		m_state.m_p[10] = m_core->v__DOT__upc_data;
		m_state.m_p[11] = m_core->v__DOT__uic_data;

		m_state.m_p[12] = m_core->v__DOT__mtc_data;
		m_state.m_p[13] = m_core->v__DOT__moc_data;
		m_state.m_p[14] = m_core->v__DOT__mpc_data;
		m_state.m_p[15] = m_core->v__DOT__mic_data;

	}

	void	showval(int y, int x, const char *lbl, unsigned int v, bool c) {
		if (c)
			mvprintw(y,x, ">%s> 0x%08x<", lbl, v);
		else
			mvprintw(y,x, " %s: 0x%08x ", lbl, v);
	}

	void	dispreg(int y, int x, const char *n, unsigned int v, bool c) {
		// 4,4,8,1 = 17 of 20, +3 = 19
		if (c)
			mvprintw(y, x, ">%s> 0x%08x<", n, v);
		else
			mvprintw(y, x, " %s: 0x%08x ", n, v);
	}

	void	dbgreg(FILE *fp, int id, const char *n, unsigned int v) {
		/*
		if ((id == 14)||(id == 14+16)) {
			//char	buf[64];
			//fprintf(fp, " %s:", 
			fprintf(fp, " %s: 0x%08x ", n, v);
		} else
		*/
			fprintf(fp, " %s: 0x%08x ", n, v);
	}

	void	showreg(int y, int x, const char *n, int r, bool c) {
		if (r < 16)
			dispreg(y, x, n, m_state.m_sR[r], c);
		else
			dispreg(y, x, n, m_state.m_uR[r-16], c);
		move(y,x+17);

#ifdef	OPT_PIPELINED
		addch( ((r == (int)(dcdA()&0x01f))&&(dcdvalid())
				&&(m_core->v__DOT__thecpu__DOT__dcdA_rd))
			?'a':((c)?'<':' '));
		addch( ((r == (int)(dcdB()&0x01f))&&(dcdvalid())
				&&(m_core->v__DOT__thecpu__DOT__dcdB_rd))
			?'b':' ');
		addch( ((r == m_core->v__DOT__thecpu__DOT__wr_reg_id)
				&&(m_core->v__DOT__thecpu__DOT__wr_reg_ce))
			?'W':' ');
#else
		addch( ((r == m_core->v__DOT__thecpu__DOT__wr_reg_id)
				&&(m_core->v__DOT__thecpu__DOT__wr_reg_ce))
			?'W':((c)?'<':' '));
#endif
	}

	void	showins(int y, const char *lbl, const int ce, const int valid,
			const int gie, const int stall, const unsigned int pc,
			const bool phase) {
		char	la[80], lb[80];

		if (ce)
			mvprintw(y, 0, "Ck ");
		else
			mvprintw(y, 0, "   ");
		if (stall)
			printw("Stl ");
		else
			printw("    ");
		printw("%s: 0x%08x", lbl, pc);

		if (valid) {
			if (gie) attroff(A_BOLD);
			else	attron(A_BOLD);
			zipi_to_string(m_mem[pc], la, lb);
			if ((phase)||((m_mem[pc]&0x80000000)==0))
				printw("  %-24s", la);
			else
				printw("  %-24s", lb);
		} else {
			attroff(A_BOLD);
			printw("  (0x%08x)%28s", m_mem[pc],"");
		}
		attroff(A_BOLD);
	}

	void	dbgins(const char *lbl, const int ce, const int valid,
			const int gie, const int stall, const unsigned int pc,
			const bool phase, const bool illegal) {
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
		fprintf(m_dbgfp, "0x%08x:  ", pc);

		if (valid) {
			zipi_to_string(m_mem[pc], la, lb);
			if ((phase)||((m_mem[pc]&0x80000000)==0))
				fprintf(m_dbgfp, "  %-24s", la);
			else
				fprintf(m_dbgfp, "  %-24s", lb);
		} else {
			fprintf(m_dbgfp, "  (0x%08x)", m_mem[pc]);
		} if (illegal)
			fprintf(m_dbgfp, " (Illegal)");
		fprintf(m_dbgfp, "\n");
	}

	void	show_state(void) {
		int	ln= 0;

		read_raw_state_cheating();

		mvprintw(ln,0, "Peripherals-SS"); ln++;
#ifdef	OPT_ILLEGAL_INSTRUCTION
		printw(" %s",
			// (m_core->v__DOT__thecpu__DOT__pf_illegal)?"PI":"  ",
			(m_core->v__DOT__thecpu__DOT__dcd_illegal)?"DI":"  "
			);
#endif

#ifdef	OPT_EARLY_BRANCHING
		printw(" %s",
			(m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__genblk3__DOT__r_early_branch)?"EB":"  ");
		if (m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__genblk3__DOT__r_early_branch)
			printw(" 0x%08x", m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__genblk3__DOT__r_branch_pc);
		else	printw(" %10s", "");
		printw(" %s", 
			(m_core->v__DOT__thecpu__DOT____Vcellinp__pf____pinNumber3)?"-> P3":"     ");
#endif
			
		/*
		showval(ln, 1, "TRAP", m_core->v__DOT__trap_data);
			mvprintw(ln, 17, "%s%s",
				((m_core->v__DOT__sys_cyc)
				&&(m_core->v__DOT__sys_we)
				&&(m_core->v__DOT__sys_addr == 0))?"W":" ",
				(m_core->v__DOT__trap_int)?"I":" ");
		*/
		showval(ln, 0, "PIC ", m_state.m_p[0], (m_cursor==0));
		showval(ln,20, "WDT ", m_state.m_p[1], (m_cursor==1));
		// showval(ln,40, "CACH", m_core->v__DOT__manualcache__DOT__cache_base, (m_cursor==2));

		if (!m_show_user_timers) {	
		showval(ln,40, "WBUS", m_core->v__DOT__watchbus__DOT__r_value, false);
		} else {
		showval(ln,40, "UBUS", m_core->v__DOT__r_wdbus_data, false);
		}

		showval(ln,60, "PIC2", m_state.m_p[3], (m_cursor==3));

		ln++;
		showval(ln, 0, "TMRA", m_state.m_p[4], (m_cursor==4));
		showval(ln,20, "TMRB", m_state.m_p[5], (m_cursor==5));
		showval(ln,40, "TMRC", m_state.m_p[6], (m_cursor==6));
		showval(ln,60, "JIF ", m_state.m_p[7], (m_cursor==7));

	
		if (!m_show_user_timers) {	
			ln++;
			showval(ln, 0, "MTSK", m_state.m_p[12], (m_cursor==8));
			showval(ln,20, "MOST", m_state.m_p[13], (m_cursor==9));
			showval(ln,40, "MPST", m_state.m_p[14], (m_cursor==10));
			showval(ln,60, "MICT", m_state.m_p[15], (m_cursor==11));
		} else {
			ln++;
			showval(ln, 0, "UTSK", m_state.m_p[ 8], (m_cursor==8));
			showval(ln,20, "UOST", m_state.m_p[ 9], (m_cursor==9));
			showval(ln,40, "UPST", m_state.m_p[10], (m_cursor==10));
			showval(ln,60, "UICT", m_state.m_p[11], (m_cursor==11));
		}

		ln++;
		mvprintw(ln, 40, "%s %s",
			(m_core->v__DOT__cpu_halt)? "CPU-HALT": "        ",
			(m_core->v__DOT__cpu_reset)?"CPU-RESET":"         "); ln++;
		mvprintw(ln, 40, "%s %s %s 0x%02x %s %s",
			(m_core->v__DOT__cmd_halt)? "HALT": "    ",
			(m_core->v__DOT__cmd_reset)?"RESET":"     ",
			(m_core->v__DOT__cmd_step)? "STEP" :"    ",
			(m_core->v__DOT__cmd_addr)&0x3f,
			(m_core->v__DOT__thecpu__DOT__master_ce)? "*CE*" :"(ce)",
			(m_core->v__DOT__cpu_reset)? "*RST*" :"(rst)");
		if (m_core->v__DOT__thecpu__DOT__gie)
			attroff(A_BOLD);
		else
			attron(A_BOLD);
		mvprintw(ln, 0, "Supervisor Registers");
		ln++;

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
			mvprintw(ln,40, "%ssCC :%s%s%s%s%s%s%s",
				(m_cursor==26)?">":" ",
				(cc&0x01000)?"FE":"",
				(cc&0x00800)?"DE":"",
				(cc&0x00400)?"BE":"",
				(cc&0x00200)?"TP":"",
				(cc&0x00100)?"IL":"",
				(cc&0x00080)?"BK":"",
				((m_state.m_gie==0)&&(cc&0x010))?"HLT":"");
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		showval(ln,60, "sPC ", m_state.m_sR[15], (m_cursor==27));
		mvprintw(ln,60,"%s",
			(m_core->v__DOT__thecpu__DOT__wr_reg_id == 0x0e)
				&&(m_core->v__DOT__thecpu__DOT__wr_reg_ce)
				?"V"
			:(((m_core->v__DOT__thecpu__DOT__wr_flags_ce)
				&&(!m_core->v__DOT__thecpu__DOT__r_alu_gie))?"+"
			:" "));
		ln++;

		if (m_core->v__DOT__thecpu__DOT__gie)
			attron(A_BOLD);
		else
			attroff(A_BOLD);
		mvprintw(ln, 0, "User Registers");
		mvprintw(ln, 42, "DCDR=%02x %s%s",
			dcdR(),
			(m_core->v__DOT__thecpu__DOT__dcdR_wr)?"W":" ",
			(m_core->v__DOT__thecpu__DOT__dcdF_wr)?"F":" ");
		mvprintw(ln, 62, "OPR =%02x %s%s",
			m_core->v__DOT__thecpu__DOT__r_opR,
			(m_core->v__DOT__thecpu__DOT__opR_wr)?"W":" ",
			(m_core->v__DOT__thecpu__DOT__opF_wr)?"F":" ");
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
			mvprintw(ln,40, "%cuCC :%s%s%s%s%s%s%s",
				(m_cursor == 42)?'>':' ',
				(cc & 0x1000)?"FE":"",
				(cc & 0x0800)?"DE":"",
				(cc & 0x0400)?"BE":"",
				(cc & 0x0200)?"TP":"",
				(cc & 0x0100)?"IL":"",
				(cc & 0x0040)?"ST":"",
				((m_state.m_gie)&&(cc & 0x010))?"SL":"");
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		showval(ln,60, "uPC ", m_state.m_uR[15], (m_cursor==43));
		mvprintw(ln,60,"%s",
			(m_core->v__DOT__thecpu__DOT__wr_reg_id == 0x1e)
				&&(m_core->v__DOT__thecpu__DOT__wr_reg_ce)
				?"V"
			:(((m_core->v__DOT__thecpu__DOT__wr_flags_ce)
				&&(m_core->v__DOT__thecpu__DOT__r_alu_gie))?"+"
			:" "));

		attroff(A_BOLD);
		ln+=1;

#ifdef	OPT_SINGLE_FETCH
		ln++;
		mvprintw(ln, 0, "PF BUS: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x",
			(m_core->v__DOT__thecpu__DOT__pf_cyc)?"CYC":"   ",
			(m_core->v__DOT__thecpu__DOT__pf_stb)?"STB":"   ",
			"  ", // (m_core->v__DOT__thecpu__DOT__pf_we )?"WE":"  ",
			(m_core->v__DOT__thecpu__DOT__pf_addr),
			0, // (m_core->v__DOT__thecpu__DOT__pf_data),
			(m_core->v__DOT__thecpu__DOT__pf_ack)?"ACK":"   ",
			"   ",//(m_core->v__DOT__thecpu__DOT__pf_stall)?"STL":"   ",
			(m_core->v__DOT__wb_data)); ln++;
#else

		mvprintw(ln, 0, "PFCACH: v=%08x, %s%s, tag=%08x, pf_pc=%08x, lastpc=%08x",
			m_core->v__DOT__thecpu__DOT__pf__DOT__vmask,
			(m_core->v__DOT__thecpu__DOT__pf__DOT__r_v)?"V":" ",
			(m_core->v__DOT__thecpu__DOT__pf_illegal)?"I":" ",
			(m_core->v__DOT__thecpu__DOT__pf__DOT__tagsrc)
			?(m_core->v__DOT__thecpu__DOT__pf__DOT__tagvalipc)
			:(m_core->v__DOT__thecpu__DOT__pf__DOT__tagvallst),
			m_core->v__DOT__thecpu__DOT__pf_pc,
			m_core->v__DOT__thecpu__DOT__pf__DOT__lastpc);

		ln++;
		mvprintw(ln, 0, "PF BUS: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x",
			(m_core->v__DOT__thecpu__DOT__pf_cyc)?"CYC":"   ",
			(m_core->v__DOT__thecpu__DOT__pf_stb)?"STB":"   ",
			"  ", // (m_core->v__DOT__thecpu__DOT__pf_we )?"WE":"  ",
			(m_core->v__DOT__thecpu__DOT__pf_addr),
			0, // (m_core->v__DOT__thecpu__DOT__pf_data),
			(m_core->v__DOT__thecpu__DOT__pf_ack)?"ACK":"   ",
			(pfstall())?"STL":"   ",
			(m_core->v__DOT__wb_data)); ln++;
#endif

		mvprintw(ln, 0, "MEMBUS: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x",
			(m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_gbl)?"GCY"
				:((m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_lcl)?"LCY":"   "),
			(m_core->v__DOT__thecpu__DOT__mem_stb_gbl)?"GSB"
				:((m_core->v__DOT__thecpu__DOT__mem_stb_lcl)?"LSB":"   "),
			(m_core->v__DOT__thecpu__DOT__mem_we )?"WE":"  ",
			(m_core->v__DOT__thecpu__DOT__mem_addr),
			(m_core->v__DOT__thecpu__DOT__mem_data),
			(m_core->v__DOT__thecpu__DOT__mem_ack)?"ACK":"   ",
			(m_core->v__DOT__thecpu__DOT__mem_stall)?"STL":"   ",
			(m_core->v__DOT__thecpu__DOT__mem_result));
// #define	OPT_PIPELINED_BUS_ACCESS
#ifdef	OPT_PIPELINED_BUS_ACCESS
		printw(" %x%x%c%c",
			(m_core->v__DOT__thecpu__DOT__domem__DOT__wraddr),
			(m_core->v__DOT__thecpu__DOT__domem__DOT__rdaddr),
			(m_core->v__DOT__thecpu__DOT__r_op_pipe)?'P':'-',
			(mem_pipe_stalled())?'S':'-'); ln++;
#else
		ln++;
#endif

		mvprintw(ln, 0, "SYSBS%c: %3s %3s %s @0x%08x[0x%08x] -> %s %s %08x %s",
			(m_core->v__DOT__thecpu__DOT__pformem__DOT__r_a_owner)?'M':'P',
			(m_core->o_wb_cyc)?"CYC":"   ",
			(m_core->o_wb_stb)?"STB":"   ",
			(m_core->o_wb_we )?"WE":"  ",
			(m_core->o_wb_addr),
			(m_core->o_wb_data),
			(m_core->i_wb_ack)?"ACK":"   ",
			(m_core->i_wb_stall)?"STL":"   ",
			(m_core->i_wb_data),
			(m_core->i_wb_err)?"(ER!)":"     "); ln+=2;
#ifdef	OPT_PIPELINED_BUS_ACCESS
		mvprintw(ln-1, 0, "Mem CE: %d = %d%d%d%d%d, stall: %d = %d%d(%d|%d%d|..)",			
			(m_core->v__DOT__thecpu__DOT__mem_ce),
			(m_core->v__DOT__thecpu__DOT__master_ce),	//1
			(m_core->v__DOT__thecpu__DOT__opvalid_mem),	//0
			(!m_core->v__DOT__thecpu__DOT__new_pc),	//1
			// (!m_core->v__DOT__thecpu__DOT__clear_pipeline),	//1
			(m_core->v__DOT__thecpu__DOT__set_cond),	//1
			(!mem_stalled()),	//1

			(mem_stalled()),
			(m_core->v__DOT__thecpu__DOT__opvalid_mem),
			(m_core->v__DOT__thecpu__DOT__master_ce),
			(mem_pipe_stalled()),
			(!m_core->v__DOT__thecpu__DOT__r_op_pipe),
			(m_core->v__DOT__thecpu__DOT__domem__DOT__cyc)
			);
		printw(" op_pipe = %d", m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__r_pipe);
		// mvprintw(4,4,"r_dcdI = 0x%06x",
			// (m_core->v__DOT__thecpu__DOT__dcdI)&0x0ffffff);
#endif
		mvprintw(4,42,"0x%08x", m_core->v__DOT__thecpu__DOT__instruction);
#ifdef	OPT_SINGLE_CYCLE
		printw(" A:%c%c B:%c%c",
			(m_core->v__DOT__thecpu__DOT__opA_alu)?'A':'-',
			(m_core->v__DOT__thecpu__DOT__opA_mem)?'M':'-',
			(m_core->v__DOT__thecpu__DOT__opB_alu)?'A':'-',
			(m_core->v__DOT__thecpu__DOT__opB_mem)?'M':'-');
#else
		printw(" A:xx B:xx");
#endif
		printw(" PFPC=%08x", m_core->v__DOT__thecpu__DOT__pf_pc);


		showins(ln, "I ",
#ifdef	OPT_PIPELINED
			!m_core->v__DOT__thecpu__DOT__dcd_stalled,
#else
			1,
#endif
			m_core->v__DOT__thecpu__DOT__pf_valid,
			//m_core->v__DOT__thecpu__DOT__instruction_gie,
			m_core->v__DOT__thecpu__DOT__gie,
			0,
			m_core->v__DOT__thecpu__DOT__instruction_pc,
			true); ln++;
			// m_core->v__DOT__thecpu__DOT__pf_pc); ln++;

		showins(ln, "Dc",
			dcd_ce(), dcdvalid(),
			m_core->v__DOT__thecpu__DOT__dcd_gie,
#ifdef	OPT_PIPELINED
			m_core->v__DOT__thecpu__DOT__dcd_stalled,
#else
			0,
#endif
			m_core->v__DOT__thecpu__DOT__dcd_pc-1,
#ifdef	OPT_VLIW
			m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__r_phase
#else
			false
#endif
			); ln++;
#ifdef	OPT_ILLEGAL_INSTRUCTION
		if (m_core->v__DOT__thecpu__DOT__dcd_illegal)
			mvprintw(ln-1,10,"I");
		else
#endif
		if (m_core->v__DOT__thecpu__DOT__dcdM)
			mvprintw(ln-1,10,"M");

		showins(ln, "Op",
			op_ce(),
			m_core->v__DOT__thecpu__DOT__opvalid,
			m_core->v__DOT__thecpu__DOT__r_op_gie,
			m_core->v__DOT__thecpu__DOT__op_stall,
			op_pc(),
#ifdef	OPT_VLIW
			m_core->v__DOT__thecpu__DOT__r_op_phase
#else
			false
#endif
			); ln++;
#ifdef	OPT_ILLEGAL_INSTRUCTION
		if (m_core->v__DOT__thecpu__DOT__op_illegal)
			mvprintw(ln-1,10,"I");
		else
#endif
		if (m_core->v__DOT__thecpu__DOT__opvalid_mem)
			mvprintw(ln-1,10,"M");
		else if (m_core->v__DOT__thecpu__DOT__opvalid_alu)
			mvprintw(ln-1,10,"A");

		if (m_core->v__DOT__thecpu__DOT__opvalid_mem) {
			showins(ln, "Mm",
				m_core->v__DOT__thecpu__DOT__mem_ce,
				m_core->v__DOT__thecpu__DOT__mem_pc_valid,
				m_core->v__DOT__thecpu__DOT__r_alu_gie,
#ifdef	OPT_PIPELINED
				m_core->v__DOT__thecpu__DOT__mem_stall,
#else
				0,
#endif
				alu_pc(),
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__r_alu_phase
#else
				false
#endif
			);
		} else {
			showins(ln, "Al",
				m_core->v__DOT__thecpu__DOT__alu_ce,
				m_core->v__DOT__thecpu__DOT__alu_pc_valid,
				m_core->v__DOT__thecpu__DOT__r_alu_gie,
#ifdef	OPT_PIPELINED
				m_core->v__DOT__thecpu__DOT__alu_stall,
#else
				0,
#endif
				alu_pc(),
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__r_alu_phase
#else
				false
#endif
			);
		} ln++;
		if (m_core->v__DOT__thecpu__DOT__wr_reg_ce)
			mvprintw(ln-1,10,"W");
		else if (m_core->v__DOT__thecpu__DOT__alu_valid)
			mvprintw(ln-1,10,(m_core->v__DOT__thecpu__DOT__alu_wr)?"w":"V");
		else if (m_core->v__DOT__thecpu__DOT__mem_valid)
			mvprintw(ln-1,10,"v");
#ifdef	OPT_ILLEGAL_INSTRUCTION
		else if (m_core->v__DOT__thecpu__DOT__r_alu_illegal)
			mvprintw(ln-1,10,"I");
#endif
		// else if (m_core->v__DOT__thecpu__DOT__alu_illegal_op)
			// mvprintw(ln-1,10,"i");

		mvprintw(ln-5, 65,"%s %s",
			(m_core->v__DOT__thecpu__DOT__r_op_break)?"OB":"  ",
			(m_core->v__DOT__thecpu__DOT__new_pc)?"CLRP":"    ");
		mvprintw(ln-4, 48,
			(m_core->v__DOT__thecpu__DOT__new_pc)?"new-pc":"      ");
		printw("(%s:%02x,%x)",
			(m_core->v__DOT__thecpu__DOT__set_cond)?"SET":"   ",
			(m_core->v__DOT__thecpu__DOT__opF&0x0ff),
			(m_core->v__DOT__thecpu__DOT__r_op_gie)
				?  (m_core->v__DOT__thecpu__DOT__w_uflags)
				: (m_core->v__DOT__thecpu__DOT__w_iflags));

		printw("(%s%s%s:%02x)",
			(m_core->v__DOT__thecpu__DOT__opF_wr)?"OF":"  ",
			(m_core->v__DOT__thecpu__DOT__alF_wr)?"FL":"  ",
			(m_core->v__DOT__thecpu__DOT__wr_flags_ce)?"W":" ",
			(m_core->v__DOT__thecpu__DOT__alu_flags));
		/*
		mvprintw(ln-3, 48, "dcdI : 0x%08x",
			m_core->v__DOT__thecpu__DOT__dcdI);
		mvprintw(ln-2, 48, "r_opB: 0x%08x",
			m_core->v__DOT__thecpu__DOT__opB);
		*/
		mvprintw(ln-3, 48, "Op(%x)%8x,%8x->",
			m_core->v__DOT__thecpu__DOT__r_opn,
			m_core->v__DOT__thecpu__DOT__opA,
			m_core->v__DOT__thecpu__DOT__opB);
		if (m_core->v__DOT__thecpu__DOT__alu_valid)
			printw("%08x", m_core->v__DOT__thecpu__DOT__alu_result);
		else
			printw("%8s","");
		mvprintw(ln-1, 48, "%s%s%s ",
			(m_core->v__DOT__thecpu__DOT__alu_valid)?"A"
			  :((m_core->v__DOT__thecpu__DOT__doalu__DOT__genblk2__DOT__r_busy)?"a":" "),
			(m_core->v__DOT__thecpu__DOT__div_valid)?"D"
			  :((m_core->v__DOT__thecpu__DOT__div_busy)?"d":" "),
			(m_core->v__DOT__thecpu__DOT__div_valid)?"F"
			  :((m_core->v__DOT__thecpu__DOT__div_busy)?"f":" "));
		printw("MEM: %s%s %s%s %s %-5s",
			(m_core->v__DOT__thecpu__DOT__opvalid_mem)?"M":" ",
			(m_core->v__DOT__thecpu__DOT__mem_ce)?"CE":"  ",
			(m_core->v__DOT__thecpu__DOT__mem_we)?"Wr ":"Rd ",
			(mem_stalled())?"PIPE":"    ",
			(m_core->v__DOT__thecpu__DOT__mem_valid)?"V":" ",
			zop_regstr[(m_core->v__DOT__thecpu__DOT__mem_wreg&0x1f)^0x10]);
	}

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
			endwin();

			printf("ERR: errcount >= MAXERR on wb_read(a=%x)\n", a);
			// printf("Clear-Pipeline = %d\n", m_core->v__DOT__thecpu__DOT__clear_pipeline);
			printf("cpu-dbg-stall  = %d\n", m_core->v__DOT__thecpu__DOT__r_halted);
			printf("pf_cyc         = %d\n", m_core->v__DOT__thecpu__DOT__pf_cyc);
			printf("mem_cyc_gbl    = %d\n", (m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_gbl));
			printf("mem_cyc_lcl    = %d\n", m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_lcl);
			printf("opvalid        = %d\n", m_core->v__DOT__thecpu__DOT__opvalid);
			printf("dcdvalid       = %d\n", dcdvalid()?1:0);
			printf("dcd_ce         = %d\n", dcd_ce()?1:0);
#ifdef	OPT_PIPELINED
			printf("dcd_stalled    = %d\n", m_core->v__DOT__thecpu__DOT__dcd_stalled);
#endif
			printf("pf_valid       = %d\n", m_core->v__DOT__thecpu__DOT__pf_valid);
// #ifdef	OPT_EARLY_BRANCHING
			// printf("dcd_early_branch=%d\n", m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__genblk1__DOT__r_early_branch);
// #endif

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
		return (m_core->v__DOT__cmd_halt != 0);
	}

	void	read_state(void) {
		int	ln= 0;
		bool	gie;

		read_raw_state();
		if (m_cursor < 0)
			m_cursor = 0;
		else if (m_cursor >= 44)
			m_cursor = 43;

		mvprintw(ln,0, "Peripherals-RS");
		mvprintw(ln,40,"%-40s", "CPU State: ");
		{
			unsigned int v = wb_read(CMD_REG);
			mvprintw(ln,51, "");
			if (v & 0x010000)
				printw("EXT-INT ");
			if ((v & 0x003000) == 0x03000)
				printw("Halted ");
			else if (v & 0x001000)
				printw("Sleeping ");
			else if (v & 0x002000)
				printw("User Mod ");
			if (v & 0x008000)
				printw("Break-Enabled ");
			if (v & 0x000080)
				printw("PIC Enabled ");
		} ln++;
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

		ln++;
		ln++;
		unsigned int cc = m_state.m_sR[14];
		if (m_dbgfp) fprintf(m_dbgfp, "CC = %08x, gie = %d\n", cc,
			m_core->v__DOT__thecpu__DOT__gie);
		gie = (cc & 0x020);
		if (gie)
			attroff(A_BOLD);
		else
			attron(A_BOLD);
		mvprintw(ln, 0, "Supervisor Registers");
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
			mvprintw(ln,40, "%ssCC :%s%s%s%s%s%s%s",
				(m_cursor==26)?">":" ",
				(cc&0x01000)?"FE":"",
				(cc&0x00800)?"DE":"",
				(cc&0x00400)?"BE":"",
				(cc&0x00200)?"TP":"",
				(cc&0x00100)?"IL":"",
				(cc&0x00080)?"BK":"",
				((m_state.m_gie==0)&&(cc&0x010))?"HLT":"");
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		dispreg(ln,60, "sPC ", cmd_read(15), (m_cursor==27));
		ln++;

		if (gie)
			attron(A_BOLD);
		else
			attroff(A_BOLD);
		mvprintw(ln, 0, "User Registers");
		mvprintw(ln, 42, "DCDR=%02x %s",
			dcdR(), (m_core->v__DOT__thecpu__DOT__dcdR_wr)?"W":" ");
		mvprintw(ln, 62, "OPR =%02x %s%s",
			m_core->v__DOT__thecpu__DOT__r_opR,
			(m_core->v__DOT__thecpu__DOT__opR_wr)?"W":" ",
			(m_core->v__DOT__thecpu__DOT__opF_wr)?"F":" ");
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
			mvprintw(ln,40, "%cuCC :%s%s%s%s%s%s%s",
				(m_cursor == 42)?'>':' ',
				(cc & 0x1000)?"FE":"",
				(cc & 0x0800)?"DE":"",
				(cc & 0x0400)?"BE":"",
				(cc & 0x0200)?"TP":"",
				(cc & 0x0100)?"IL":"",
				(cc & 0x0040)?"ST":"",
				((m_state.m_gie)&&(cc & 0x010))?"SL":"");
			mvprintw(ln, 54, "%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		dispreg(ln,60, "uPC ", m_state.m_uR[15], (m_cursor==43));

		attroff(A_BOLD);
		ln+=2;

		ln+=3;

		showins(ln, "I ",
#ifdef	OPT_PIPELINED
			!m_core->v__DOT__thecpu__DOT__dcd_stalled,
#else
			1,
#endif
			m_core->v__DOT__thecpu__DOT__pf_valid,
			m_core->v__DOT__thecpu__DOT__gie,
			0,
			m_core->v__DOT__thecpu__DOT__instruction_pc,
			true); ln++;
			// m_core->v__DOT__thecpu__DOT__pf_pc); ln++;

		showins(ln, "Dc",
			dcd_ce(), dcdvalid(),
			m_core->v__DOT__thecpu__DOT__dcd_gie,
#ifdef	OPT_PIPELINED
			m_core->v__DOT__thecpu__DOT__dcd_stalled,
#else
			0,
#endif
			m_core->v__DOT__thecpu__DOT__dcd_pc-1,
#ifdef	OPT_VLIW
			m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__r_phase
#else
			false
#endif
			); ln++;

		showins(ln, "Op",
			op_ce(),
			m_core->v__DOT__thecpu__DOT__opvalid,
			m_core->v__DOT__thecpu__DOT__r_op_gie,
			m_core->v__DOT__thecpu__DOT__op_stall,
			op_pc(),
#ifdef	OPT_VLIW
			m_core->v__DOT__thecpu__DOT__r_alu_phase
#else
			false
#endif
			); ln++;

		if (m_core->v__DOT__thecpu__DOT__opvalid_mem) {
			showins(ln, "Mm",
				m_core->v__DOT__thecpu__DOT__mem_ce,
				m_core->v__DOT__thecpu__DOT__mem_pc_valid,
				m_core->v__DOT__thecpu__DOT__r_alu_gie,
#ifdef	OPT_PIPELINED
				m_core->v__DOT__thecpu__DOT__mem_stall,
#else
				0,
#endif
				alu_pc(),
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__r_alu_phase
#else
				false
#endif
			);
		} else {
			showins(ln, "Al",
				m_core->v__DOT__thecpu__DOT__alu_ce,
				m_core->v__DOT__thecpu__DOT__alu_pc_valid,
				m_core->v__DOT__thecpu__DOT__r_alu_gie,
#ifdef	OPT_PIPELINED
				m_core->v__DOT__thecpu__DOT__alu_stall,
#else
				0,
#endif
				alu_pc(),
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__r_alu_phase
#else
				false
#endif
			);
		} ln++;
	}

	void	tick(void) {
		int gie = m_core->v__DOT__thecpu__DOT__gie;
		/*
		m_core->i_qspi_dat = m_flash(m_core->o_qspi_cs_n,
						m_core->o_qspi_sck,
						m_core->o_qspi_dat);
		*/

		int stb = m_core->o_wb_stb;
		m_core->i_wb_err = 0;
		if ((m_core->o_wb_addr & (-1<<20))!=(1<<20))
			stb = 0;
		if ((m_core->o_wb_cyc)&&(m_core->o_wb_stb)&&(!stb)) {
			m_core->i_wb_ack = 1;
			m_core->i_wb_err = 1;
			bomb = true;
			if (m_dbgfp) fprintf(m_dbgfp, "BOMB!! (Attempting to access %08x/%08x->%08x)\n", m_core->o_wb_addr,
				(-1<<20), ((m_core->o_wb_addr)&(-1<<20)));
		}

		if ((dbg_flag)&&(m_dbgfp)) {
			fprintf(m_dbgfp, "DBG  %s %s %s @0x%08x/%d[0x%08x] %s %s [0x%08x] %s %s %s%s%s%s%s%s%s%s%s\n",
				(m_core->i_dbg_cyc)?"CYC":"   ",
				(m_core->i_dbg_stb)?"STB":
					((m_core->v__DOT__dbg_stb)?"DBG":"   "),
				((m_core->i_dbg_we)?"WE":"  "),
				(m_core->i_dbg_addr),0,
				m_core->i_dbg_data,
				(m_core->o_dbg_ack)?"ACK":"   ",
				(m_core->o_dbg_stall)?"STALL":"     ",
				(m_core->o_dbg_data),
				(m_core->v__DOT__cpu_halt)?"CPU-HALT ":"",
				(m_core->v__DOT__thecpu__DOT__r_halted)?"CPU-DBG_STALL":"",
				(dcdvalid())?"DCDV ":"",
				(m_core->v__DOT__thecpu__DOT__opvalid)?"OPV ":"",
				(m_core->v__DOT__thecpu__DOT__pf_cyc)?"PCYC ":"",
				(m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_gbl)?"GC":"  ",
				(m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_lcl)?"LC":"  ",
				(m_core->v__DOT__thecpu__DOT__alu_wr)?"ALUW ":"",
				(m_core->v__DOT__thecpu__DOT__alu_ce)?"ALCE ":"",
				(m_core->v__DOT__thecpu__DOT__alu_valid)?"ALUV ":"",
				(m_core->v__DOT__thecpu__DOT__mem_valid)?"MEMV ":"");
			fprintf(m_dbgfp, " SYS %s %s %s @0x%08x/%d[0x%08x] %s [0x%08x]\n",
				(m_core->v__DOT__sys_cyc)?"CYC":"   ",
				(m_core->v__DOT__sys_stb)?"STB":"   ",
				(m_core->v__DOT__sys_we)?"WE":"  ",
				(m_core->v__DOT__sys_addr),
				(m_core->v__DOT__dbg_addr),
				(m_core->v__DOT__sys_data),
				(m_core->v__DOT__dbg_ack)?"ACK":"   ",
				(m_core->v__DOT__wb_data));
		}

		if (m_dbgfp)
			fprintf(m_dbgfp, "CEs %d/0x%08x,%d/0x%08x DCD: ->%02x, OP: ->%02x, ALU: halt=%d,%d ce=%d, valid=%d, wr=%d  Reg=%02x, IPC=%08x, UPC=%08x\n",
				dcd_ce(),
				m_core->v__DOT__thecpu__DOT__dcd_pc,
				op_ce(),
				op_pc(),
				dcdA()&0x01f,
				m_core->v__DOT__thecpu__DOT__r_opR,
				m_core->v__DOT__cmd_halt,
				m_core->v__DOT__cpu_halt,
				m_core->v__DOT__thecpu__DOT__alu_ce,
				m_core->v__DOT__thecpu__DOT__alu_valid,
				m_core->v__DOT__thecpu__DOT__alu_wr,
				m_core->v__DOT__thecpu__DOT__alu_reg,
				m_core->v__DOT__thecpu__DOT__ipc,
				m_core->v__DOT__thecpu__DOT__upc);
				
		if ((m_dbgfp)&&(!gie)&&(m_core->v__DOT__thecpu__DOT__w_release_from_interrupt)) {
			fprintf(m_dbgfp, "RELEASE: int=%d, %d/%02x[%08x] ?/%02x[0x%08x], ce=%d %d,%d,%d\n",
				m_core->v__DOT__genblk9__DOT__pic__DOT__r_interrupt,
				m_core->v__DOT__thecpu__DOT__wr_reg_ce,
				m_core->v__DOT__thecpu__DOT__wr_reg_id,
				m_core->v__DOT__thecpu__DOT__wr_spreg_vl,
				m_core->v__DOT__cmd_addr,
				m_core->v__DOT__dbg_idata,
				m_core->v__DOT__thecpu__DOT__master_ce,
				m_core->v__DOT__thecpu__DOT__alu_wr,
				m_core->v__DOT__thecpu__DOT__alu_valid,
				m_core->v__DOT__thecpu__DOT__mem_valid);
		} else if ((m_dbgfp)&&(gie)&&(m_core->v__DOT__thecpu__DOT__w_switch_to_interrupt)) {
			fprintf(m_dbgfp, "SWITCH: %d/%02x[%08x] ?/%02x[0x%08x], ce=%d %d,%d,%d, F%02x,%02x\n",
				m_core->v__DOT__thecpu__DOT__wr_reg_ce,
				m_core->v__DOT__thecpu__DOT__wr_reg_id,
				m_core->v__DOT__thecpu__DOT__wr_spreg_vl,
				m_core->v__DOT__cmd_addr,
				m_core->v__DOT__dbg_idata,
				m_core->v__DOT__thecpu__DOT__master_ce,
				m_core->v__DOT__thecpu__DOT__alu_wr,
				m_core->v__DOT__thecpu__DOT__alu_valid,
				m_core->v__DOT__thecpu__DOT__mem_valid,
				m_core->v__DOT__thecpu__DOT__w_iflags,
				m_core->v__DOT__thecpu__DOT__w_uflags);
			fprintf(m_dbgfp, "\tbrk=%s %d,%d\n",
				(m_core->v__DOT__thecpu__DOT__master_ce)?"CE":"  ",
				m_core->v__DOT__thecpu__DOT__break_en,
				m_core->v__DOT__thecpu__DOT__r_op_break);
		} else if ((m_dbgfp)&&
				((m_core->v__DOT__thecpu__DOT__r_op_break)
				||(m_core->v__DOT__thecpu__DOT__r_alu_illegal)
				||(m_core->v__DOT__thecpu__DOT__dcd_break))) {
			fprintf(m_dbgfp, "NOT SWITCHING TO GIE (gie = %d)\n", gie);
			fprintf(m_dbgfp, "\tbrk=%s breaken=%d,dcdbreak=%d,opbreak=%d,alu_illegal=%d\n",
				(m_core->v__DOT__thecpu__DOT__master_ce)?"CE":"  ",
				m_core->v__DOT__thecpu__DOT__break_en,
				m_core->v__DOT__thecpu__DOT__dcd_break,
				m_core->v__DOT__thecpu__DOT__r_op_break,
				m_core->v__DOT__thecpu__DOT__r_alu_illegal);
		}

		if (m_dbgfp) {
			// if(m_core->v__DOT__thecpu__DOT__clear_pipeline)
				// fprintf(m_dbgfp, "\tClear Pipeline\n");
			if(m_core->v__DOT__thecpu__DOT__new_pc)
				fprintf(m_dbgfp, "\tNew PC\n");
		}

		if (m_dbgfp)
			fprintf(m_dbgfp, "-----------  TICK (%08x) ----------%s\n",
				m_core->v__DOT__jiffies__DOT__r_counter,
				(bomb)?" BOMBED!!":"");
		if (false) {
			m_core->i_clk = 1;
			m_mem(m_core->i_clk, m_core->o_wb_cyc, m_core->o_wb_stb, m_core->o_wb_we,
				m_core->o_wb_addr & ((1<<20)-1), m_core->o_wb_data,
				m_core->i_wb_ack, m_core->i_wb_stall,m_core->i_wb_data);
			eval();
			m_core->i_clk = 0;
			m_mem(m_core->i_clk, m_core->o_wb_cyc, m_core->o_wb_stb, m_core->o_wb_we,
				m_core->o_wb_addr & ((1<<20)-1), m_core->o_wb_data,
				m_core->i_wb_ack, m_core->i_wb_stall,m_core->i_wb_data);
			eval();
			m_tickcount++;
		} else {
			m_mem(1, m_core->o_wb_cyc, m_core->o_wb_stb, m_core->o_wb_we,
				m_core->o_wb_addr & ((1<<20)-1), m_core->o_wb_data,
				m_core->i_wb_ack, m_core->i_wb_stall,m_core->i_wb_data);
			if ((m_core->o_wb_cyc)&&(m_core->o_wb_stb)
				&&((m_core->o_wb_addr & (~((1<<20)-1))) != 0x100000))
				m_core->i_wb_err = 1;
			else
				m_core->i_wb_err = 0;
			TESTB<Vzipsystem>::tick();
		}
		if ((m_dbgfp)&&(gie != m_core->v__DOT__thecpu__DOT__gie)) {
			fprintf(m_dbgfp, "SWITCH FROM %s to %s: sPC = 0x%08x uPC = 0x%08x pf_pc = 0x%08x\n",
				(gie)?"User":"Supervisor",
				(gie)?"Supervisor":"User",
				m_core->v__DOT__thecpu__DOT__ipc,
				m_core->v__DOT__thecpu__DOT__upc,
				m_core->v__DOT__thecpu__DOT__pf_pc);
		} if (m_dbgfp) {
#ifdef	OPT_TRADITIONAL_PFCACHE
			fprintf(m_dbgfp, "PFCACHE %s(%08x,%08x%s),%08x - %08x %s%s%s\n",
				(m_core->v__DOT__thecpu__DOT__new_pc)?"N":" ",
				m_core->v__DOT__thecpu__DOT__pf_pc,
				m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__genblk3__DOT__r_branch_pc,
				((m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__genblk3__DOT__r_early_branch)
				&&(dcdvalid())
				&&(!m_core->v__DOT__thecpu__DOT__new_pc))?"V":"-",
				m_core->v__DOT__thecpu__DOT__pf__DOT__lastpc,
				m_core->v__DOT__thecpu__DOT__instruction_pc,
				(m_core->v__DOT__thecpu__DOT__pf__DOT__r_v)?"R":" ",
				(m_core->v__DOT__thecpu__DOT__pf_valid)?"V":" ",
				(m_core->v__DOT__thecpu__DOT__pf_illegal)?"I":" ");
#endif
			dbgins("Dc - ",
				dcd_ce(), dcdvalid(),
				m_core->v__DOT__thecpu__DOT__dcd_gie,
#ifdef	OPT_PIPELINED
				m_core->v__DOT__thecpu__DOT__dcd_stalled,
#else
				0,
#endif
				m_core->v__DOT__thecpu__DOT__dcd_pc-1,
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__instruction_decoder__DOT__r_phase,
#else
				false,
#endif
#ifdef	OPT_ILLEGAL_INSTRUCTION
				m_core->v__DOT__thecpu__DOT__dcd_illegal
#else
				false
#endif
				);
			dbgins("Op - ",
				op_ce(),
				m_core->v__DOT__thecpu__DOT__opvalid,
				m_core->v__DOT__thecpu__DOT__r_op_gie,
				m_core->v__DOT__thecpu__DOT__op_stall,
				op_pc(),
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__r_op_phase,
#else
				false,
#endif
#ifdef	OPT_ILLEGAL_INSTRUCTION
				m_core->v__DOT__thecpu__DOT__op_illegal
#else
				false
#endif
				);
			dbgins("Al - ",
				m_core->v__DOT__thecpu__DOT__alu_ce,
				m_core->v__DOT__thecpu__DOT__alu_pc_valid,
				m_core->v__DOT__thecpu__DOT__r_alu_gie,
#ifdef	OPT_PIPELINED
				m_core->v__DOT__thecpu__DOT__alu_stall,
#else
				0,
#endif
				alu_pc(),
#ifdef	OPT_VLIW
				m_core->v__DOT__thecpu__DOT__r_alu_phase,
#else
				false,
#endif
#ifdef	OPT_ILLEGAL_INSTRUCTION
				m_core->v__DOT__thecpu__DOT__r_alu_illegal
#else
				false
#endif
				);
			if (m_core->v__DOT__thecpu__DOT__wr_reg_ce)
				fprintf(m_dbgfp, "WB::Reg[%2x] <= %08x\n",
					m_core->v__DOT__thecpu__DOT__wr_reg_id,
					m_core->v__DOT__thecpu__DOT__wr_gpreg_vl);

		}

		if ((m_dbgfp)&&((m_core->v__DOT__thecpu__DOT__div_valid)
			||(m_core->v__DOT__thecpu__DOT__div_ce)
			||(m_core->v__DOT__thecpu__DOT__div_busy)
			)) {
			fprintf(m_dbgfp, "DIV: %s %s %s %s[%2x] GP:%08x/SP:%08x %s:0x%08x\n",
				(m_core->v__DOT__thecpu__DOT__div_ce)?"CE":"  ",
				(m_core->v__DOT__thecpu__DOT__div_busy)?"BUSY":"    ",
				(m_core->v__DOT__thecpu__DOT__div_valid)?"VALID":"     ",
				(m_core->v__DOT__thecpu__DOT__wr_reg_ce)?"REG-CE":"      ",
				m_core->v__DOT__thecpu__DOT__wr_reg_id,
				m_core->v__DOT__thecpu__DOT__wr_gpreg_vl,
				m_core->v__DOT__thecpu__DOT__wr_spreg_vl,
				(m_core->v__DOT__thecpu__DOT__alu_pc_valid)?"PCV":"   ",
				alu_pc());

			fprintf(m_dbgfp, "ALU-PC: %08x %s %s\n",
				alu_pc(),
				(m_core->v__DOT__thecpu__DOT__r_alu_pc_valid)?"VALID":"",
				(m_core->v__DOT__thecpu__DOT__r_alu_gie)?"ALU-GIE":"");
		}

		if (m_core->v__DOT__dma_controller__DOT__dma_state) {
			fprintf(m_dbgfp, "DMA[%d]%s%s%s%s@%08x,%08x [%d%d/%4d/%4d] -> [%d%d/%04d/%04d]\n",
				m_core->v__DOT__dma_controller__DOT__dma_state,
				(m_core->v__DOT__dc_cyc)?"C":" ",
				(m_core->v__DOT__dc_stb)?"S":" ",
				(m_core->v__DOT__dc_ack)?"A":" ",
				(m_core->v__DOT__dc_err)?"E":" ",
				m_core->v__DOT__dc_addr,
				(m_core->v__DOT__dc_data),
				m_core->v__DOT__dma_controller__DOT__last_read_request,
				m_core->v__DOT__dma_controller__DOT__last_read_ack,
				m_core->v__DOT__dma_controller__DOT__nracks,
				m_core->v__DOT__dma_controller__DOT__nread,
				m_core->v__DOT__dma_controller__DOT__last_write_request,
				m_core->v__DOT__dma_controller__DOT__last_write_ack,
				m_core->v__DOT__dma_controller__DOT__nwacks,
				m_core->v__DOT__dma_controller__DOT__nwritten);
		}
		if (((m_core->v__DOT__thecpu__DOT__alu_pc_valid)
			||(m_core->v__DOT__thecpu__DOT__mem_pc_valid))
			&&(!m_core->v__DOT__thecpu__DOT__new_pc)) {
			unsigned long iticks = m_tickcount - m_last_instruction_tickcount;
			if (m_profile_fp) {
				unsigned buf[2];
				buf[0] = alu_pc();
				buf[1] = iticks;
				fwrite(buf, sizeof(unsigned), 2, m_profile_fp);
			}
			m_last_instruction_tickcount = m_tickcount;
		}
	}

	bool	test_success(void) {
		return ((!m_core->v__DOT__thecpu__DOT__gie)
			&&(m_core->v__DOT__thecpu__DOT__sleep));
	}

	unsigned	op_pc(void) {
		/*
		unsigned r = m_core->v__DOT__thecpu__DOT__dcd_pc-1;
		if (m_core->v__DOT__thecpu__DOT__dcdvalid)
			r--;
		return r;
		*/
		return m_core->v__DOT__thecpu__DOT__op_pc-1;
	}

	bool	dcd_ce(void) {
#ifdef	OPT_PIPELINED
		// return (m_core->v__DOT__thecpu__DOT__dcd_ce != 0);
		return ((!m_core->v__DOT__thecpu__DOT__r_dcdvalid)
			||(!m_core->v__DOT__thecpu__DOT__dcd_stalled))
			&&(m_core->v__DOT__thecpu__DOT__new_pc);
#else
		return (m_core->v__DOT__thecpu__DOT__pf_valid);
#endif
	} bool	dcdvalid(void) {
		return (m_core->v__DOT__thecpu__DOT__r_dcdvalid !=0);
	}
	bool	pfstall(void) {
		return((!(m_core->v__DOT__thecpu__DOT__pformem__DOT__r_a_owner))
			||(m_core->v__DOT__cpu_stall));
	}
	unsigned	dcdR(void) {
		return (m_core->v__DOT__thecpu__DOT____Vcellout__instruction_decoder____pinNumber14);
	}
	unsigned	dcdA(void) {
		return (m_core->v__DOT__thecpu__DOT____Vcellout__instruction_decoder____pinNumber15);
	}
	unsigned	dcdB(void) {
		return (m_core->v__DOT__thecpu__DOT____Vcellout__instruction_decoder____pinNumber16);
	}

	bool	op_ce(void) {
#ifdef	OPT_PIPELINED
		return (m_core->v__DOT__thecpu__DOT__op_ce != 0);
#else
		// return (dcdvalid())&&(opvalid())
		// 	&&(m_core->v__DOT__thecpu__DOT__op_stall);
		return 	dcdvalid();
#endif
	} bool	opvalid(void) {
		return (m_core->v__DOT__thecpu__DOT__opvalid !=0);
	}

	bool	mem_busy(void) {
		// return m_core->v__DOT__thecpu__DOT__mem_busy;
#ifdef	OPT_PIPELINED
		return m_core->v__DOT__thecpu__DOT__domem__DOT__cyc;
#else
		return 0;
#endif
	}

	bool	mem_stalled(void) {
		bool	a, b, c, d, wr_write_cc, wr_write_pc, op_gie;

		wr_write_cc=((m_core->v__DOT__thecpu__DOT__wr_reg_id&0x0f)==0x0e);
		wr_write_pc=((m_core->v__DOT__thecpu__DOT__wr_reg_id&0x0f)==0x0f);
		op_gie = m_core->v__DOT__thecpu__DOT__r_op_gie;

#ifdef	OPT_PIPELINED_BUS_ACCESS
		//a = m_core->v__DOT__thecpu__DOT__mem_pipe_stalled;
		a = mem_pipe_stalled();
		b = (!m_core->v__DOT__thecpu__DOT__r_op_pipe)&&(mem_busy());
#else
		a = false;
		b = false;
#endif
		d = ((wr_write_pc)||(wr_write_cc));
		c = ((m_core->v__DOT__thecpu__DOT__wr_reg_ce)
			&&(((m_core->v__DOT__thecpu__DOT__wr_reg_id&0x010)?true:false)==op_gie)
			&&d);
		d =(m_core->v__DOT__thecpu__DOT__opvalid_mem)&&((a)||(b)||(c));
		return ((!m_core->v__DOT__thecpu__DOT__master_ce)||(d));
	}

	unsigned	alu_pc(void) {
		/*
		unsigned	r = op_pc();
		if (m_core->v__DOT__thecpu__DOT__opvalid)
			r--;
		return r;
		*/
		return m_core->v__DOT__thecpu__DOT__r_alu_pc-1;
	}

#ifdef	OPT_PIPELINED_BUS_ACCESS
	bool	mem_pipe_stalled(void) {
		int	r = 0;
		r = ((m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_gbl)
		 ||(m_core->v__DOT__thecpu__DOT__domem__DOT__r_wb_cyc_lcl));
		r = r && ((m_core->v__DOT__thecpu__DOT__mem_stall)
			||(
				((!m_core->v__DOT__thecpu__DOT__mem_stb_gbl)
				&&(!m_core->v__DOT__thecpu__DOT__mem_stb_lcl))));
		return r;
		// return m_core->v__DOT__thecpu__DOT__mem_pipe_stalled;
	}
#endif

	bool	test_failure(void) {
		if (m_core->v__DOT__thecpu__DOT__sleep)
			return 0;
		else if (m_core->v__DOT__thecpu__DOT__gie)
			return (m_mem[m_core->v__DOT__thecpu__DOT__upc] == 0x7bc3dfff);
		else if (m_mem[m_core->v__DOT__thecpu__DOT__ipc] == 0x7883ffff)
			return true; // ADD to PC instruction
		else // MOV to PC instruction
			return (m_mem[m_core->v__DOT__thecpu__DOT__ipc] == 0x7bc3dfff);
		/*
		return ((m_core->v__DOT__thecpu__DOT__alu_pc_valid)
			&&(m_mem[alu_pc()] == 0x2f0f7fff)
			&&(!m_core->v__DOT__thecpu__DOT__clear_pipeline));
		*/
	}

	void	wb_write(unsigned a, unsigned int v) {
		int	errcount = 0;
		mvprintw(0,35, "%40s", "");
		mvprintw(0,40, "wb_write(%d,%x)", a, v);
		m_core->i_dbg_cyc = 1;
		m_core->i_dbg_stb = 1;
		m_core->i_dbg_we  = 1;
		m_core->i_dbg_addr = a & 1;
		m_core->i_dbg_data = v;

		tick();
		while((errcount++ < 100)&&(m_core->o_dbg_stall))
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
			bomb = true;
		}
	}

	unsigned long	wb_read(unsigned a) {
		unsigned int	v;
		int	errcount = 0;
		mvprintw(0,35, "%40s", "");
		mvprintw(0,40, "wb_read(0x%08x)", a);
		m_core->i_dbg_cyc = 1;
		m_core->i_dbg_stb = 1;
		m_core->i_dbg_we  = 0;
		m_core->i_dbg_addr = a & 1;

		tick();
		while((errcount++<100)&&(m_core->o_dbg_stall))
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
			if (m_dbgfp) fprintf(m_dbgfp, "WB-WRITE: ERRCount = %d, BOMB!!\n", errcount);
			bomb = true;
		}
		return v;
	}

	void	cursor_up(void) {
		if (m_cursor > 3)
			m_cursor -= 4;
	} void	cursor_down(void) {
		if (m_cursor < 40)
			m_cursor += 4;
	} void	cursor_left(void) {
		if (m_cursor > 0)
			m_cursor--;
		else	m_cursor = 43;
	} void	cursor_right(void) {
		if (m_cursor < 43)
			m_cursor++;
		else	m_cursor = 0;
	}

	int	cursor(void) { return m_cursor; }

	void	jump_to(ZIPI address) {
		m_core->v__DOT__thecpu__DOT__pf_pc = address;
		// m_core->v__DOT__thecpu__DOT__clear_pipeline = 1;
		m_core->v__DOT__thecpu__DOT__new_pc = 1;
	}

	void	dump_state(void) {
		if (m_dbgfp)
			dump_state(m_dbgfp);
	}

	void	dump_state(FILE *fp) {
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
	}
};

void	get_value(ZIPPY_TB *tb) {
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
		if (!tb->halted()) {
			switch(ra) {
			case 15:
				tb->m_core->v__DOT__thecpu__DOT__ipc = v;
				if (!tb->m_core->v__DOT__thecpu__DOT__gie) {
					tb->m_core->v__DOT__thecpu__DOT__pf_pc = v;
					tb->m_core->v__DOT__thecpu__DOT__new_pc = 1;
					// tb->m_core->v__DOT__thecpu__DOT__clear_pipeline = 1;
					tb->m_core->v__DOT__thecpu__DOT__alu_pc_valid = 0;
#ifdef	OPT_PIPELINED
					// tb->m_core->v__DOT__thecpu__DOT__dcd_ce = 0;
					tb->m_core->v__DOT__thecpu__DOT__r_dcdvalid = 0;
#endif
					tb->m_core->v__DOT__thecpu__DOT__opvalid = 0;
				}
				break;
			case 31:
				tb->m_core->v__DOT__thecpu__DOT__upc = v; 
				if (tb->m_core->v__DOT__thecpu__DOT__gie) {
					tb->m_core->v__DOT__thecpu__DOT__pf_pc = v;
					tb->m_core->v__DOT__thecpu__DOT__new_pc = 1;
					// tb->m_core->v__DOT__thecpu__DOT__clear_pipeline = 1;
					tb->m_core->v__DOT__thecpu__DOT__alu_pc_valid = 0;
#ifdef	OPT_PIPELINED
					// tb->m_core->v__DOT__thecpu__DOT__dcd_ce = 0;
					tb->m_core->v__DOT__thecpu__DOT__r_dcdvalid = 0;
#endif
					tb->m_core->v__DOT__thecpu__DOT__opvalid = 0;
				}
				break;
			case 32: tb->m_core->v__DOT__pic_data = v; break;
			case 33: tb->m_core->v__DOT__watchdog__DOT__r_value = v; break;
			// case 34: tb->m_core->v__DOT__manualcache__DOT__cache_base = v; break;
			case 35: tb->m_core->v__DOT__genblk7__DOT__ctri__DOT__r_int_state = v; break;
			case 36: tb->m_core->v__DOT__timer_a__DOT__r_value = v; break;
			case 37: tb->m_core->v__DOT__timer_b__DOT__r_value = v; break;
			case 38: tb->m_core->v__DOT__timer_c__DOT__r_value = v; break;
			case 39: tb->m_core->v__DOT__jiffies__DOT__r_counter = v; break;
			case 44: tb->m_core->v__DOT__utc_data = v; break;
			case 45: tb->m_core->v__DOT__uoc_data = v; break;
			case 46: tb->m_core->v__DOT__upc_data = v; break;
			case 47: tb->m_core->v__DOT__uic_data = v; break;
			default:
				tb->m_core->v__DOT__thecpu__DOT__regset[ra] = v;
				break;
			}
		} else
			tb->cmd_write(ra, v);
	}
}


bool	iself(const char *fname) {
	FILE	*fp;
	bool	ret = true;
	fp = fopen(fname, "rb");

	if (!fp)	return false;
	if (0x7f != fgetc(fp))	ret = false;
	if ('E'  != fgetc(fp))	ret = false;
	if ('L'  != fgetc(fp))	ret = false;
	if ('F'  != fgetc(fp))	ret = false;
	fclose(fp);
	return 	ret;
}

long	fgetwords(FILE *fp) {
	// Return the number of words in the current file, and return the 
	// file as though it had never been adjusted
	long	fpos, flen;
	fpos = ftell(fp);
	if (0 != fseek(fp, 0l, SEEK_END)) {
		fprintf(stderr, "ERR: Could not determine file size\n");
		perror("O/S Err:");
		exit(-2);
	} flen = ftell(fp);
	if (0 != fseek(fp, fpos, SEEK_SET)) {
		fprintf(stderr, "ERR: Could not seek on file\n");
		perror("O/S Err:");
		exit(-2);
	} flen /= sizeof(ZIPI);
	return flen;
}

class	SECTION {
public:
	unsigned	m_start, m_len;
	ZIPI		m_data[1];
};

SECTION	**singlesection(int nwords) {
	fprintf(stderr, "NWORDS = %d\n", nwords);
	size_t	sz = (2*(sizeof(SECTION)+sizeof(SECTION *))
		+(nwords-1)*(sizeof(ZIPI)));
	char	*d = (char *)malloc(sz);
	SECTION **r = (SECTION **)d;
	memset(r, 0, sz);
	r[0] = (SECTION *)(&d[2*sizeof(SECTION *)]);
	r[0]->m_len   = nwords;
	r[1] = (SECTION *)(&r[0]->m_data[r[0]->m_len]);
	r[0]->m_start = 0;
	r[1]->m_start = 0;
	r[1]->m_len   = 0;

	return r;
}

SECTION **rawsection(const char *fname) {
	SECTION		**secpp, *secp;
	unsigned	num_words;
	FILE		*fp;
	int		nr;

	fp = fopen(fname, "r");
	if (fp == NULL) {
		fprintf(stderr, "Could not open: %s\n", fname);
		exit(-1);
	}

	if ((num_words=fgetwords(fp)) > MEMWORDS) {
		fprintf(stderr, "File overruns Block RAM\n");
		exit(-1);
	}
	secpp = singlesection(num_words);
	secp = secpp[0];
	secp->m_start = RAMBASE;
	secp->m_len = num_words;
	nr= fread(secp->m_data, sizeof(ZIPI), num_words, fp);
	if (nr != (int)num_words) {
		fprintf(stderr, "Could not read entire file\n");
		perror("O/S Err:");
		exit(-2);
	} assert(secpp[1]->m_len == 0);

	return secpp;
}

unsigned	byteswap(unsigned n) {
	unsigned	r;

	r = (n&0x0ff); n>>= 8;
	r = (r<<8) | (n&0x0ff); n>>= 8;
	r = (r<<8) | (n&0x0ff); n>>= 8;
	r = (r<<8) | (n&0x0ff); n>>= 8;

	return r;
}

#include <libelf.h>
#include <gelf.h>

void	elfread(const char *fname, unsigned &entry, SECTION **&sections) {
	Elf	*e;
	int	fd, i;
	size_t	n;
	char	*id;
	Elf_Kind	ek;
	GElf_Ehdr	ehdr;
	GElf_Phdr	phdr;
	const	bool	dbg = false;

	if (elf_version(EV_CURRENT) == EV_NONE) {
		fprintf(stderr, "ELF library initialization err, %s\n", elf_errmsg(-1));
		perror("O/S Err:");
		exit(EXIT_FAILURE);
	} if ((fd = open(fname, O_RDONLY, 0)) < 0) {
		fprintf(stderr, "Could not open %s\n", fname);
		perror("O/S Err:");
		exit(EXIT_FAILURE);
	} if ((e = elf_begin(fd, ELF_C_READ, NULL))==NULL) {
		fprintf(stderr, "Could not run elf_begin, %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	}

	ek = elf_kind(e);
	if (ek == ELF_K_ELF) {
		; // This is the kind of file we should expect
	} else if (ek == ELF_K_AR) {
		fprintf(stderr, "Cannot run an archive!\n");
		exit(EXIT_FAILURE);
	} else if (ek == ELF_K_NONE) {
		;
	} else {
		fprintf(stderr, "Unexpected ELF file kind!\n");
		exit(EXIT_FAILURE);
	}

	if (gelf_getehdr(e, &ehdr) == NULL) {
		fprintf(stderr, "getehdr() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if ((i=gelf_getclass(e)) == ELFCLASSNONE) {
		fprintf(stderr, "getclass() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if ((id = elf_getident(e, NULL)) == NULL) {
		fprintf(stderr, "getident() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if (i != ELFCLASS32) {
		fprintf(stderr, "This is a 64-bit ELF file, ZipCPU ELF files are all 32-bit\n");
		exit(EXIT_FAILURE);
	}

	if (dbg) {
	printf("    %-20s 0x%jx\n", "e_type", (uintmax_t)ehdr.e_type);
	printf("    %-20s 0x%jx\n", "e_machine", (uintmax_t)ehdr.e_machine);
	printf("    %-20s 0x%jx\n", "e_version", (uintmax_t)ehdr.e_version);
	printf("    %-20s 0x%jx\n", "e_entry", (uintmax_t)ehdr.e_entry);
	printf("    %-20s 0x%jx\n", "e_phoff", (uintmax_t)ehdr.e_phoff);
	printf("    %-20s 0x%jx\n", "e_shoff", (uintmax_t)ehdr.e_shoff);
	printf("    %-20s 0x%jx\n", "e_flags", (uintmax_t)ehdr.e_flags);
	printf("    %-20s 0x%jx\n", "e_ehsize", (uintmax_t)ehdr.e_ehsize);
	printf("    %-20s 0x%jx\n", "e_phentsize", (uintmax_t)ehdr.e_phentsize);
	printf("    %-20s 0x%jx\n", "e_shentsize", (uintmax_t)ehdr.e_shentsize);
	printf("\n");
	}


	// Check whether or not this is an ELF file for the ZipCPU ...
	if (ehdr.e_machine != 0x0dadd) {
		fprintf(stderr, "This is not a ZipCPU ELF file\n");
		exit(EXIT_FAILURE);
	}

	// Get our entry address
	entry = ehdr.e_entry;


	// Now, let's go look at the program header
	if (elf_getphdrnum(e, &n) != 0) {
		fprintf(stderr, "elf_getphdrnum() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	}

	unsigned total_octets = 0, current_offset=0, current_section=0;
	for(i=0; i<(int)n; i++) {
		total_octets += sizeof(SECTION *)+sizeof(SECTION);

		if (gelf_getphdr(e, i, &phdr) != &phdr) {
			fprintf(stderr, "getphdr() failed: %s\n", elf_errmsg(-1));
			exit(EXIT_FAILURE);
		}

		if (dbg) {
		printf("    %-20s 0x%x\n", "p_type",   phdr.p_type);
		printf("    %-20s 0x%jx\n", "p_offset", phdr.p_offset);
		printf("    %-20s 0x%jx\n", "p_vaddr",  phdr.p_vaddr);
		printf("    %-20s 0x%jx\n", "p_paddr",  phdr.p_paddr);
		printf("    %-20s 0x%jx\n", "p_filesz", phdr.p_filesz);
		printf("    %-20s 0x%jx\n", "p_memsz",  phdr.p_memsz);
		printf("    %-20s 0x%x [", "p_flags",  phdr.p_flags);

		if (phdr.p_flags & PF_X)	printf(" Execute");
		if (phdr.p_flags & PF_R)	printf(" Read");
		if (phdr.p_flags & PF_W)	printf(" Write");
		printf("]\n");
		printf("    %-20s 0x%jx\n", "p_align", phdr.p_align);
		}

		total_octets += phdr.p_memsz;
	}

	char	*d = (char *)malloc(total_octets + sizeof(SECTION)+sizeof(SECTION *));
	memset(d, 0, total_octets);

	SECTION **r = sections = (SECTION **)d;
	current_offset = (n+1)*sizeof(SECTION *);
	current_section = 0;

	for(i=0; i<(int)n; i++) {
		r[i] = (SECTION *)(&d[current_offset]);

		if (gelf_getphdr(e, i, &phdr) != &phdr) {
			fprintf(stderr, "getphdr() failed: %s\n", elf_errmsg(-1));
			exit(EXIT_FAILURE);
		}

		if (dbg) {
		printf("    %-20s 0x%jx\n", "p_offset", phdr.p_offset);
		printf("    %-20s 0x%jx\n", "p_vaddr",  phdr.p_vaddr);
		printf("    %-20s 0x%jx\n", "p_paddr",  phdr.p_paddr);
		printf("    %-20s 0x%jx\n", "p_filesz", phdr.p_filesz);
		printf("    %-20s 0x%jx\n", "p_memsz",  phdr.p_memsz);
		printf("    %-20s 0x%x [", "p_flags",  phdr.p_flags);

		if (phdr.p_flags & PF_X)	printf(" Execute");
		if (phdr.p_flags & PF_R)	printf(" Read");
		if (phdr.p_flags & PF_W)	printf(" Write");
		printf("]\n");

		printf("    %-20s 0x%jx\n", "p_align", phdr.p_align);
		}

		current_section++;

		r[i]->m_start = phdr.p_vaddr;
		r[i]->m_len   = phdr.p_filesz/ sizeof(ZIPI);

		current_offset += phdr.p_memsz + sizeof(SECTION);

		// Now, let's read in our section ...
		if (lseek(fd, phdr.p_offset, SEEK_SET) < 0) {
			fprintf(stderr, "Could not seek to file position %08lx\n", phdr.p_offset);
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		} if (phdr.p_filesz > phdr.p_memsz)
			phdr.p_filesz = 0;
		if (read(fd, r[i]->m_data, phdr.p_filesz) != (int)phdr.p_filesz) {
			fprintf(stderr, "Didnt read entire section\n");
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}

		// Next, we need to byte swap it from big to little endian
		for(unsigned j=0; j<r[i]->m_len; j++)
			r[i]->m_data[j] = byteswap(r[i]->m_data[j]);

		if (dbg) for(unsigned j=0; j<r[i]->m_len; j++)
			fprintf(stderr, "ADR[%04x] = %08x\n", r[i]->m_start+j,
			r[i]->m_data[j]);
	}

	r[i] = (SECTION *)(&d[current_offset]);
	r[current_section]->m_start = 0;
	r[current_section]->m_len   = 0;

	elf_end(e);
	close(fd);
}

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
	ZIPPY_TB	*tb = new ZIPPY_TB();
	bool		autorun = false, exit_on_done = false, autostep=false;
	ZIPI		entry = RAMBASE;

	// mem[0x00000] = 0xbe000010; // Halt instruction
	unsigned int mptr = 0;

	signal(SIGINT, sigint);

	if (argc <= 1) {
		usage();
		exit(-1);
	} else {
		for(int argn=1; argn<argc; argn++) {
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
			} else if (access(argv[argn], R_OK)==0) {
				if (iself(argv[argn])) {
					SECTION **secpp = NULL, *secp;
					elfread(argv[argn], entry, secpp);
					for(int i=0; secpp[i]->m_len; i++) {
						secp = secpp[i];
						assert(secp->m_start >= RAMBASE);
						assert(secp->m_start+secp->m_len <= RAMBASE+MEMWORDS);
						memcpy(&tb->m_mem[secp->m_start-RAMBASE],
							&secp->m_data,
							secp->m_len*sizeof(ZIPI));
						mptr = secp->m_start+secp->m_len;
					}
				} else {
				FILE *fp = fopen(argv[argn], "r");
				int	nr, nv = 0;
				if (fp == NULL) {
					printf("Cannot open %s\n", argv[argn]);
					perror("O/S Err: ");
					exit(-1);
				} nr = fread(&tb->m_mem[mptr], sizeof(ZIPI), tb->m_mem_size - mptr, fp);
				fclose(fp);
				mptr+= nr;
				if (nr == 0) {
					printf("Could not read from %s, only read 0 words\n", argv[argn]);
					perror("O/S  Err?:");
					exit(-2);
				} for(int i=0; i<nr; i++) {
					if (tb->m_mem[mptr-nr+i])
						nv++;
				} if (nv == 0) {
					printf("Read nothing but zeros from %s\n", argv[argn]);
					perror("O/S  Err?:");
					exit(-2);
				}
				}
			} else {
				fprintf(stderr, "No access to %s, or unknown arg\n", argv[argn]);
				exit(-2);
			}
		}
	}


	assert(mptr > 0);

	if (autorun) {
		bool	done = false;

		printf("Running in non-interactive mode\n");
		tb->reset();
		for(int i=0; i<2; i++)
			tb->tick();
		tb->m_core->v__DOT__cmd_halt = 0;
		tb->wb_write(CMD_REG, CMD_HALT|CMD_RESET|15);
		tb->wb_write(CMD_DATA, entry);
		tb->wb_write(CMD_REG, 15);
		while(!done) {
			tb->tick();

				// tb->m_core->v__DOT__thecpu__DOT__step = 0;
				// tb->m_core->v__DOT__cmd_halt = 0;
				// tb->m_core->v__DOT__cmd_step = 0;

			/*
			printf("PC = %08x:%08x (%08x)\n",
				tb->m_core->v__DOT__thecpu__DOT__ipc,
				tb->m_core->v__DOT__thecpu__DOT__upc,
				tb->m_core->v__DOT__thecpu__DOT__alu_pc);
			*/

			done = (tb->test_success())||(tb->test_failure());
			done = done || signalled;
		}
	} else if (autostep) {
		bool	done = false;

		printf("Running in non-interactive mode, via step commands\n");
		tb->wb_write(CMD_REG, CMD_HALT|CMD_RESET|15);
		tb->wb_write(CMD_DATA, entry);
		tb->wb_write(CMD_REG, 15);
		while(!done) {
			tb->wb_write(CMD_REG, CMD_STEP);
			done = (tb->test_success())||(tb->test_failure());
			done = done || signalled;
		}
	} else { // Interactive
		initscr();
		raw();
		noecho();
		keypad(stdscr, true);

		// tb->reset();
		// for(int i=0; i<2; i++)
			// tb->tick();
		tb->m_core->v__DOT__cmd_reset = 1;
		tb->m_core->v__DOT__cmd_halt = 0;

		tb->jump_to(entry);

		// For debugging purposes: do we wish to skip some number of
		// instructions to fast forward to a time of interest??
		for(int i=0; i<0; i++) {
			tb->m_core->v__DOT__cmd_halt = 0;
			tb->tick();
		}

		int	chv = 'q';

		bool	done = false, halted = true, manual = true,
			high_speed = false;

		halfdelay(1);
		// tb->wb_write(CMD_REG, CMD_HALT | CMD_RESET);
		// while((tb->wb_read(CMD_REG) & (CMD_HALT|CMD_STALL))==(CMD_HALT|CMD_STALL))
			// tb->show_state();

		while(!done) {
			if ((high_speed)&&(!manual)&&(!halted)) {
				// chv = getch();

				struct	pollfd	fds[1];
				fds[0].fd = STDIN_FILENO;
				fds[0].events = POLLIN;

				if (poll(fds, 1, 0) > 0)
					chv = getch();
				else
					chv = ERR;

			} else {
				chv = getch();
			}
			switch(chv) {
			case 'h': case 'H':
				tb->wb_write(CMD_REG, CMD_HALT);
				if (!halted)
					erase();
				halted = true;
				break;
			case 'G':
				high_speed = true;
				// cbreak();
			case 'g':
				tb->wb_write(CMD_REG, 0);
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
					tb->wb_write(CMD_REG, CMD_RESET|CMD_HALT);
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
				tb->m_core->v__DOT__cmd_halt = 0;
				tb->m_core->v__DOT__cmd_step = 1;
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
				tb->m_core->v__DOT__cmd_halt = 1;
				tb->m_core->v__DOT__cmd_step = 0;
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
		//		tb->m_core->v__DOT__thecpu__DOT__step = 0;
				tb->m_core->v__DOT__cmd_halt = 0;
		//		tb->m_core->v__DOT__cmd_step = 0;
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
			}

			if (manual) {
				tb->show_state();
			} else if (halted) {
				if (tb->m_dbgfp)
					fprintf(tb->m_dbgfp, "\n\nREAD-STATE ******\n");
				tb->read_state();
			} else
				tb->show_state();

			if (tb->m_core->i_rst)
				done =true;
			if ((tb->bomb)||(signalled))
				done = true;

			if (exit_on_done) {
				if (tb->test_success())
					done = true;
				if (tb->test_failure())
					done = true;
			}
		}
		endwin();
	}
#ifdef	MANUAL_STEPPING_MODE
	 else { // Manual stepping mode
		tb->show_state();

		while('q' != tolower(chv = getch())) {
			tb->tick();
			tb->show_state();

			if (tb->test_success())
				break;
			else if (tb->test_failure())
				break;
			else if (signalled)
				break;
		}
	}
#endif

	printf("\n");
	if (tb->test_failure()) {
		tb->dump_state();
	}

	printf("Clocks used         : %08x\n", tb->m_core->v__DOT__mtc_data);
	printf("Instructions Issued : %08x\n", tb->m_core->v__DOT__mic_data);
	printf("Tick Count          : %08lx\n", tb->m_tickcount);
	if (tb->m_core->v__DOT__mtc_data != 0)
		printf("Instructions / Clock: %.2f\n",
			(double)tb->m_core->v__DOT__mic_data
			/ (double)tb->m_core->v__DOT__mtc_data);

	int	rcode = 0;
	if (tb->bomb) {
		printf("TEST BOMBED\n");
		rcode = -1;
	} else if (tb->test_success()) {
		printf("SUCCESS!\n");
	} else if (tb->test_failure()) {
		rcode = -2;
		printf("TEST FAILED!\n");
	} else
		printf("User quit\n");
	delete tb;
	exit(rcode);
}

