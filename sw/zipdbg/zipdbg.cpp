///////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdbg.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Provide a simple debugger for the Zip CPU.  This allows you
//		to halt the CPU, examine the registers, and even single step
//	the CPU.  It's not fully functional yet, as I would like to implement
//	breakpoints and the ability to modify registers, but it's a good
//	start.
//
//	Commands while in the debugger are:
//	'r'	- RESET the CPU
//	'g'	- Go.  Release the CPU and exit the debugger.
//	'q'	- Quit.  Leave the debugger, while leaving the CPU halted.
//	's'	- Single Step.  Allows the CPU to advance by one instruction.
//
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Tecnhology, LLC
//
///////////////////////////////////////////////////////////////////////////////
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
///////////////////////////////////////////////////////////////////////////////
//
//
#include <stdlib.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <string.h>

#include <ctype.h>
#include <ncurses.h>

#include "zopcodes.h"
#include "zparser.h"
#include "devbus.h"
#include "regdefs.h"

#define	KEY_ESCAPE	27
#define	KEY_RETURN	10
#define	CTRL(X)		((X)&0x01f)

class	SPARSEMEM {
public:
	bool	m_valid;
	unsigned int	m_a, m_d;
};

bool	gbl_err = false;
class	ZIPSTATE {
public:
	bool		m_valid, m_gie, m_last_pc_valid;
	unsigned int	m_sR[16], m_uR[16];
	unsigned int	m_p[20];
	unsigned int	m_last_pc, m_pc, m_sp;
	SPARSEMEM	m_smem[5];
	SPARSEMEM	m_imem[5];
	ZIPSTATE(void) : m_valid(false), m_last_pc_valid(false) {}

	void	step(void) {
		m_last_pc_valid = true;
		m_last_pc = m_pc;
	}
};

// No particular "parameters" need definition or redefinition here.
class	ZIPPY : public DEVBUS {
	static	const	int	MAXERR;
	typedef	DEVBUS::BUSW	BUSW;
	DEVBUS	*m_fpga;
	int	m_cursor;
	ZIPSTATE	m_state;
	bool	m_user_break, m_show_users_timers, m_show_cc;
public:
	ZIPPY(DEVBUS *fpga) : m_fpga(fpga), m_cursor(0), m_user_break(false),
		m_show_users_timers(false), m_show_cc(false) {}

	void	read_raw_state(void) {
		m_state.m_valid = false;
		for(int i=0; i<16; i++)
			m_state.m_sR[i] = cmd_read(i);
		for(int i=0; i<16; i++)
			m_state.m_uR[i] = cmd_read(i+16);
		for(int i=0; i<20; i++)
			m_state.m_p[i]  = cmd_read(i+32);

		m_state.m_gie = (m_state.m_sR[14] & 0x020);
		m_state.m_pc  = (m_state.m_gie) ? (m_state.m_uR[15]):(m_state.m_sR[15]);
		m_state.m_sp  = (m_state.m_gie) ? (m_state.m_uR[13]):(m_state.m_sR[13]);

		if (m_state.m_last_pc_valid)
			m_state.m_imem[0].m_a = m_state.m_last_pc;
		else
			m_state.m_imem[0].m_a = m_state.m_pc - 1;
		try {
			m_state.m_imem[0].m_d = readio(m_state.m_imem[0].m_a);
			m_state.m_imem[0].m_valid = true;
		} catch(BUSERR be) {
			m_state.m_imem[0].m_valid = false;
		}
		m_state.m_imem[1].m_a = m_state.m_pc;
		try {
			m_state.m_imem[1].m_d = readio(m_state.m_imem[1].m_a);
			m_state.m_imem[1].m_valid = true;
		} catch(BUSERR be) {
			m_state.m_imem[1].m_valid = false;
		}

		for(int i=1; i<4; i++) {
			if (!m_state.m_imem[i].m_valid) {
				m_state.m_imem[i+1].m_valid = false;
				m_state.m_imem[i+1].m_a = m_state.m_imem[i].m_a+1;
				continue;
			}
			m_state.m_imem[i+1].m_a = zop_early_branch(
					m_state.m_imem[i].m_a,
					m_state.m_imem[i].m_d);
			try {
				m_state.m_imem[i+1].m_d = readio(m_state.m_imem[i+1].m_a);
				m_state.m_imem[i+1].m_valid = true;
			} catch(BUSERR be) {
				m_state.m_imem[i+1].m_valid = false;
			}
		}

		m_state.m_smem[0].m_a = m_state.m_sp;
		for(int i=1; i<5; i++)
			m_state.m_smem[i].m_a = m_state.m_smem[i-1].m_a+1;
		for(int i=0; i<5; i++) {
			m_state.m_smem[i].m_valid = true;
			if (m_state.m_smem[i].m_a < 0x2000)
				m_state.m_smem[i].m_valid = false;
			else if (m_state.m_smem[i].m_a < 0x4000)
				m_state.m_smem[i].m_valid = true;
			else if (m_state.m_smem[i].m_a < 0x800000)
				m_state.m_smem[i].m_valid = false;
			else if (m_state.m_smem[i].m_a < 0x1000000)
				m_state.m_smem[i].m_valid = true;
			else
				m_state.m_smem[i].m_valid = false;
			if (m_state.m_smem[i].m_valid)
			try {
				m_state.m_smem[i].m_d = readio(m_state.m_smem[i].m_a);
				m_state.m_smem[i].m_valid = true;
			} catch(BUSERR be) {
				m_state.m_smem[i].m_valid = false;
			}
		}
		m_state.m_valid = true;
	}

	void	kill(void) { m_fpga->kill(); }
	void	close(void) { m_fpga->close(); }
	void	writeio(const BUSW a, const BUSW v) { m_fpga->writeio(a, v); }
	BUSW	readio(const BUSW a) { return m_fpga->readio(a); }
	void	readi(const BUSW a, const int len, BUSW *buf) {
		return m_fpga->readi(a, len, buf); }
	void	readz(const BUSW a, const int len, BUSW *buf) {
		return m_fpga->readz(a, len, buf); }
	void	writei(const BUSW a, const int len, const BUSW *buf) {
		return m_fpga->writei(a, len, buf); }
	void	writez(const BUSW a, const int len, const BUSW *buf) {
		return m_fpga->writez(a, len, buf); }
	bool	poll(void) { return m_fpga->poll(); }
	void	usleep(unsigned ms) { m_fpga->usleep(ms); }
	void	wait(void) { m_fpga->wait(); }
	bool	bus_err(void) const { return m_fpga->bus_err(); }
	void	reset_err(void) { m_fpga->reset_err(); }
	void	clear(void) { m_fpga->clear(); }

	void	reset(void) { writeio(R_ZIPCTRL, CPU_RESET|CPU_HALT); }
	void	step(void) { writeio(R_ZIPCTRL, CPU_STEP); m_state.step(); }
	void	go(void) { writeio(R_ZIPCTRL, CPU_GO); }
	void	halt(void) {	writeio(R_ZIPCTRL, CPU_HALT); }
	bool	stalled(void) { return ((readio(R_ZIPCTRL)&CPU_STALL)==0); }

	void	show_user_timers(bool v) {
		m_show_users_timers = v;
	}

	void	toggle_cc(void) {
		m_show_cc = !m_show_cc;
	}

	void	showval(int y, int x, const char *lbl, unsigned int v, bool c) {
		if (c)
			mvprintw(y,x, ">%s> 0x%08x<", lbl, v);
		else
			mvprintw(y,x, " %s: 0x%08x ", lbl, v);
	}

	void	dispreg(int y, int x, const char *n, unsigned int v, bool c) {
		// 4,4,8,1 = 17 of 20, +2 = 18
		if (c)
			mvprintw(y, x, ">%s> 0x%08x<", n, v);
		else
			mvprintw(y, x, " %s: 0x%08x ", n, v);
	}

	int	showins(int y, const char *lbl, const unsigned int pcidx) {
		char	la[80], lb[80];
		int	r = y-1;

		mvprintw(y, 0, "%s0x%08x", lbl, m_state.m_imem[pcidx].m_a);

		if (m_state.m_gie) attroff(A_BOLD);
		else	attron(A_BOLD);

		la[0] = '\0';
		lb[0] = '\0';
		if (m_state.m_imem[pcidx].m_valid) {
			zipi_to_string(m_state.m_imem[pcidx].m_d, la, lb);
			printw(" 0x%08x", m_state.m_imem[pcidx].m_d);
			printw("  %-25s", la);
			if (lb[0]) {
				mvprintw(y-1, 0, "%s", lbl);
				mvprintw(y-1, strlen(lbl)+10+3+8+2, "%-25s", lb);
				r--;
			}
		} else {
			printw(" 0x--------  %-25s", "(Bus Error)");
		}
		attroff(A_BOLD);

		return r;
	}

	void	showstack(int y, const char *lbl, const unsigned int idx) {
		mvprintw(y, 27+26, "%s%08x ", lbl, m_state.m_smem[idx].m_a);

		if (m_state.m_gie) attroff(A_BOLD);
		else	attron(A_BOLD);

		if (m_state.m_smem[idx].m_valid)
			printw("0x%08x", m_state.m_smem[idx].m_d);
		else
			printw("(Bus Err)");
		attroff(A_BOLD);
	}

	unsigned int	cmd_read(unsigned int a) {
		int errcount = 0;
		unsigned int	s;

		writeio(R_ZIPCTRL, CMD_HALT|(a&0x3f));
		while((((s=readio(R_ZIPCTRL))&CPU_STALL)== 0)&&(errcount<MAXERR)
				&&(!m_user_break))
			errcount++;
		if (m_user_break) {
			endwin();
			exit(EXIT_SUCCESS);
		} else if (errcount >= MAXERR) {
			endwin();
			printf("ERR: errcount(%d) >= MAXERR on cmd_read(a=%2x)\n", errcount, a);
			printf("ZIPCTRL = 0x%08x", s);
			if ((s & 0x0200)==0) printf(" STALL");
			if  (s & 0x0400) printf(" HALTED");
			if ((s & 0x03000)==0x01000)
				printf(" SW-HALT");
			else {
				if (s & 0x01000) printf(" SLEEPING");
				if (s & 0x02000) printf(" GIE(UsrMode)");
			} printf("\n");
			exit(EXIT_FAILURE);
		}
		return readio(R_ZIPDATA);
	}

	void	cmd_write(unsigned int a, int v) {
		int errcount = 0;
		unsigned int	s;

		writeio(R_ZIPCTRL, CMD_HALT|(a&0x3f));
		while((((s=readio(R_ZIPCTRL))&CPU_STALL)== 0)&&(errcount<MAXERR)
				&&(!m_user_break))
			errcount++;
		if (m_user_break) {
			endwin();
			exit(EXIT_SUCCESS);
		} else if (errcount >= MAXERR) {
			endwin();
			printf("ERR: errcount(%d) >= MAXERR on cmd_read(a=%2x)\n", errcount, a);
			printf("ZIPCTRL = 0x%08x", s);
			if ((s & 0x0200)==0) printf(" STALL");
			if  (s & 0x0400) printf(" HALTED");
			if ((s & 0x03000)==0x01000)
				printf(" SW-HALT");
			else {
				if (s & 0x01000) printf(" SLEEPING");
				if (s & 0x02000) printf(" GIE(UsrMode)");
			} printf("\n");
			exit(EXIT_FAILURE);
		}

		writeio(R_ZIPDATA, (unsigned int)v);
	}

	void	read_state(void) {
		int	ln= 0;
		bool	gie;

		read_raw_state();

		if (m_cursor < 0)
			m_cursor = 0;
		else if (m_cursor >= 44)
			m_cursor = 43;

		mvprintw(ln,0, "Peripherals");
		mvprintw(ln,30,"%-50s", "CPU State: ");
		{
			unsigned int v = readio(R_ZIPCTRL);
			mvprintw(ln,41, "0x%08x ", v);
			// if (v & 0x010000)
				// printw("INT ");
			if ((v & 0x003000) == 0x03000)
				printw("Sleeping ");
			else if (v & 0x001000)
				printw("Halted ");
			else if (v & 0x002000)
				printw("User Mode ");
			else
				printw("Supervisor mode ");
			if (v& 0x0200) {
				v = m_state.m_sR[15];
				
			} else printw("Stalled ");
			// if (v & 0x008000)
				// printw("Break-Enabled ");
			// if (v & 0x000080)
				// printw("PIC Enabled ");
		} ln++;
		showval(ln, 0, "PIC ", m_state.m_p[0], (m_cursor==0));
		showval(ln,20, "WDT ", m_state.m_p[1], (m_cursor==1));
		showval(ln,40, "WBUS", m_state.m_p[2], (m_cursor==2));
		showval(ln,60, "PIC2", m_state.m_p[3], (m_cursor==3));
		ln++;
		showval(ln, 0, "TMRA", m_state.m_p[4], (m_cursor==4));
		showval(ln,20, "TMRB", m_state.m_p[5], (m_cursor==5));
		showval(ln,40, "TMRC", m_state.m_p[6], (m_cursor==6));
		showval(ln,60, "JIF ", m_state.m_p[7], (m_cursor==7));

		ln++;
		if (!m_show_users_timers) {
			showval(ln, 0, "MTSK", m_state.m_p[ 8], (m_cursor==8));
			showval(ln,20, "MOST", m_state.m_p[ 9], (m_cursor==9));
			showval(ln,40, "MPST", m_state.m_p[10], (m_cursor==10));
			showval(ln,60, "MICT", m_state.m_p[11], (m_cursor==11));
		} else {
			showval(ln, 0, "UTSK", m_state.m_p[12], (m_cursor==8));
			showval(ln,20, "UMST", m_state.m_p[13], (m_cursor==9));
			showval(ln,40, "UPST", m_state.m_p[14], (m_cursor==10));
			showval(ln,60, "UICT", m_state.m_p[15], (m_cursor==11));
		}

		ln++;
		ln++;
		unsigned int cc = m_state.m_sR[14];
		gie = (cc & 0x020);
		if (gie)
			attroff(A_BOLD);
		else
			attron(A_BOLD);
		mvprintw(ln, 0, "Supervisor Registers");
		ln++;

		dispreg(ln, 0, "sR0 ", m_state.m_sR[0], (m_cursor==12));
		dispreg(ln,20, "sR1 ", m_state.m_sR[1], (m_cursor==13));
		dispreg(ln,40, "sR2 ", m_state.m_sR[2], (m_cursor==14));
		dispreg(ln,60, "sR3 ", m_state.m_sR[3], (m_cursor==15)); ln++;

		dispreg(ln, 0, "sR4 ", m_state.m_sR[4], (m_cursor==16));
		dispreg(ln,20, "sR5 ", m_state.m_sR[5], (m_cursor==17));
		dispreg(ln,40, "sR6 ", m_state.m_sR[6], (m_cursor==18));
		dispreg(ln,60, "sR7 ", m_state.m_sR[7], (m_cursor==19)); ln++;

		dispreg(ln, 0, "sR8 ", m_state.m_sR[ 8], (m_cursor==20));
		dispreg(ln,20, "sR9 ", m_state.m_sR[ 9], (m_cursor==21));
		dispreg(ln,40, "sR10", m_state.m_sR[10], (m_cursor==22));
		dispreg(ln,60, "sR11", m_state.m_sR[11], (m_cursor==23)); ln++;

		dispreg(ln, 0, "sR12", m_state.m_sR[12], (m_cursor==24));
		dispreg(ln,20, "sSP ", m_state.m_sR[13], (m_cursor==25));

		if (m_show_cc) {
			mvprintw(ln,40, " sCC :%16s", "");
			dispreg(ln, 40, "sCC ", m_state.m_sR[14], (m_cursor==26));
		} else {
			mvprintw(ln,40, " sCC :%16s", "");
			mvprintw(ln,40, "%ssCC :%s%s%s%s%s%s%s",
				(m_cursor == 26)?">":" ",
				(cc&0x1000)?"FE":"", // Floating point exception
				(cc&0x0800)?"DV":"", // Division by zero
				(cc&0x0400)?"BE":"", // Bus Error
				(cc&0x0200)?"TP":"", // Trap
				(cc&0x0100)?"IL":"", // Illegal instruction
				(cc&0x0080)?"BK":"", // Break
				((gie==0)&&(cc&0x0010))?"HLT":""); // Halted
			mvprintw(ln,54,"%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		dispreg(ln,60, "sPC ", m_state.m_sR[15], (m_cursor==27));
		ln++;

		if (gie)
			attron(A_BOLD);
		else
			attroff(A_BOLD);
		mvprintw(ln, 0, "User Registers"); ln++;
		dispreg(ln, 0, "uR0 ", m_state.m_uR[0], (m_cursor==28));
		dispreg(ln,20, "uR1 ", m_state.m_uR[1], (m_cursor==29));
		dispreg(ln,40, "uR2 ", m_state.m_uR[2], (m_cursor==30));
		dispreg(ln,60, "uR3 ", m_state.m_uR[3], (m_cursor==31)); ln++;

		dispreg(ln, 0, "uR4 ", m_state.m_uR[4], (m_cursor==32));
		dispreg(ln,20, "uR5 ", m_state.m_uR[5], (m_cursor==33));
		dispreg(ln,40, "uR6 ", m_state.m_uR[6], (m_cursor==34));
		dispreg(ln,60, "uR7 ", m_state.m_uR[7], (m_cursor==35)); ln++;

		dispreg(ln, 0, "uR8 ", m_state.m_uR[8], (m_cursor==36));
		dispreg(ln,20, "uR9 ", m_state.m_uR[9], (m_cursor==37));
		dispreg(ln,40, "uR10", m_state.m_uR[10], (m_cursor==38));
		dispreg(ln,60, "uR11", m_state.m_uR[11], (m_cursor==39)); ln++;

		dispreg(ln, 0, "uR12", m_state.m_uR[12], (m_cursor==40));
		dispreg(ln,20, "uSP ", m_state.m_uR[13], (m_cursor==41));
		cc = m_state.m_uR[14];
		if (m_show_cc) {
			mvprintw(ln,40, " uCC :%16s", "");
			dispreg(ln, 40, "uCC ", m_state.m_uR[14], (m_cursor==42));
		} else {
			mvprintw(ln,40, " uCC :%16s", "");
			mvprintw(ln,40, "%suCC :%s%s%s%s%s%s%s",
				(m_cursor == 42)?">":" ",
				(cc&0x1000)?"FE":"", // Floating point Exception
				(cc&0x0800)?"DV":"", // Division by zero
				(cc&0x0400)?"BE":"", // Bus Error
				(cc&0x0200)?"TP":"", // Trap
				(cc&0x0100)?"IL":"", // Illegal instruction
				(cc&0x0040)?"ST":"", // Single-step
				((gie)&&(cc&0x0010))?"SL":""); // Sleep
			mvprintw(ln,54,"%s%s%s%s",
				(cc&8)?"V":" ",
				(cc&4)?"N":" ",
				(cc&2)?"C":" ",
				(cc&1)?"Z":" ");
		}
		dispreg(ln,60, "uPC ", m_state.m_uR[15], (m_cursor==43));

		attroff(A_BOLD);
		ln+=3;

		showins(ln+4, " ", 0);
		{
			int	lclln = ln+3;
			for(int i=1; i<5; i++)
				lclln = showins(lclln, (i==1)?">":" ", i);
			for(int i=0; i<5; i++)
				showstack(ln+i, (i==0)?">":" ", i);
		}
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
};

const	int ZIPPY::MAXERR = 100000;

DEVBUS	*m_fpga;

void	get_value(ZIPPY *zip) {
	int	wy, wx, ra;
	int	c = zip->cursor();

	wx = (c & 0x03) * 20 + 9 + 1;
	wy = (c >> 2);
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
	attron(A_NORMAL | A_UNDERLINE);
	mvprintw(wy, wx, "%-8s", "");
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
		zip->cmd_write(ra, v);
	}
}

void	on_sigint(int v) {
	endwin();

	fprintf(stderr, "Interrupted!\n");
	exit(-2);
}

void	stall_screen(void) {
	erase();
	mvprintw(0,0, "CPU is stalled.  (Q to quit)\n");
}

int	main(int argc, char **argv) {
//	FPGAOPEN(m_fpga);
	ZIPPY	*zip = new ZIPPY(m_fpga);

	initscr();
	raw();
	noecho();
	keypad(stdscr, true);

	signal(SIGINT, on_sigint);

	int	chv;
	bool	done = false;

	zip->halt();
	for(int i=0; (i<5)&&(zip->stalled()); i++)
		;
	if (!zip->stalled())
		zip->read_state();
	else
		stall_screen();
	while((!done)&&(!gbl_err)) {
		chv = getch();
		switch(chv) {
		case 'c': case 'C':
			zip->toggle_cc();
			break;
		case 'g': case 'G':
			m_fpga->writeio(R_ZIPCTRL, CPU_GO);
			// We just released the CPU, so we're now done.
			done = true;
			break;
		case 'l': case 'L': case CTRL('L'):
			redrawwin(stdscr);
		case 'm': case 'M':
			zip->show_user_timers(false);
			break;
		case 'q': case 'Q': case CTRL('C'):
		case KEY_CANCEL: case KEY_CLOSE: case KEY_EXIT:
		case KEY_ESCAPE:
			done = true;
			break;
		case 'r': case 'R':
			zip->reset();
			erase();
			break;
		case 't': case 'T':
		case 's': case 'S':
			zip->step();
			break;
		case 'u': case 'U':
			zip->show_user_timers(true);
			break;
		case '\r': case  '\n':
		case KEY_IC: case KEY_ENTER:
			get_value(zip);
			break;
		case KEY_UP:
			zip->cursor_up();
			break;
		case KEY_DOWN:
			zip->cursor_down();
			break;
		case KEY_LEFT:
			zip->cursor_left();
			break;
		case KEY_RIGHT:
			zip->cursor_right();
			break;
		case ERR: case KEY_CLEAR:
		default:
			;
		}

		if ((done)||(gbl_err))
			break;
		else if (zip->stalled())
			stall_screen();
		else
			zip->read_state();
	}

	endwin();

	if (gbl_err) {
		printf("Killed on error: could not access bus!\n");
		exit(-2);
	}
}

