////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipmmu_tb.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A quick test bench to determine if the zipmmu module works.
//		This test bench does nothing to determine whether or not it
//	is connected properly, but only tests whether or not the zipmmu works
//	as it is supposed to.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
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
////////////////////////////////////////////////////////////////////////////////
//
//
#include <stdio.h>

#include "verilated.h"
#include "Vzipmmu_tb.h"

#define	MMUFLAG_RONW	8 // Read only (not writeable)
#define	MMUFLAG_ACCS	4 // Accessed
#define	MMUFLAG_CCHE	2 // Cachable
#define	MMUFLAG_THSP	1 // Page has this context

const int	BOMBCOUNT = 32,
		LGMEMSIZE = 15;

class	ZIPMMU_TB {
	long		m_tickcount;
	Vzipmmu_tb	*m_core;
	bool		m_bomb, m_miss, m_err, m_debug;
	int		m_last_tlb_index;
public:

	ZIPMMU_TB(void) {
		m_core = new Vzipmmu_tb;
		m_debug = true;
		m_last_tlb_index = 0;
	}

#define	v__DOT__mem_stb	v__DOT__mut__DOT__r_valid
	void	tick(void) {

		m_core->eval();
		m_core->i_clk = 1;

		bool	writeout = true;

		if ((m_debug)&&(writeout)) {
			printf("%08lx-MMU: ", m_tickcount);
			printf("(%s%s%s%s) %08x (%s%s%s)%08x%s %s %08x/%08x %s%s%s%s%s",
				(m_core->i_ctrl_cyc_stb)?"CT":"  ",
				(m_core->i_wbm_cyc)?"CYC":"   ",
				(m_core->i_wbm_stb)?"STB":"   ",
				(m_core->i_wb_we)?"WE":"  ",
				(m_core->i_wb_addr),
				(m_core->v__DOT__mem_cyc)?"CYC":"   ",
				(m_core->v__DOT__mem_stb)?"STB":"   ",
#define	v__DOT__mem_we	v__DOT__mut__DOT__r_we
				(m_core->v__DOT__mem_we)?"WE":"  ",
				(m_core->v__DOT__mem_addr),
				(m_core->v__DOT__mem_err)?"ER":"  ",
				(m_core->i_wb_we)?"<-":"->",
				(m_core->i_wb_we)?m_core->i_wb_data:m_core->o_rtn_data,
				(m_core->v__DOT__mem_we)?m_core->v__DOT__mut__DOT__r_data:m_core->v__DOT__mem_odata,
				(m_core->o_rtn_stall)?"STALL":"     ",
				(m_core->v__DOT__mut__DOT__setup_ack)?"S":" ",
				(m_core->o_rtn_ack )?"ACK":"   ",
				(m_core->o_rtn_miss)?"MISS":"    ",
				(m_core->o_rtn_err )?"ERR":"   ");

			printf("[%d,%d]",
				m_core->v__DOT__mut__DOT__wr_vtable,
				m_core->v__DOT__mut__DOT__wr_ptable);
			printf("[%d,%d,%04x]",
				m_core->v__DOT__mut__DOT__wr_control,
				m_core->v__DOT__mut__DOT__z_context,
				m_core->v__DOT__mut__DOT__r_context_word);
			/*
			printf("[%08x,%08x-%08x]", 
				m_core->v__DOT__mut__DOT__w_vtable_reg,
				m_core->v__DOT__mut__DOT__w_ptable_reg,
				m_core->v__DOT__mut__DOT__setup_data);
			*/
			printf(" %s[%s%s@%08x,%08x]",
				(m_core->v__DOT__mut__DOT__r_pending)?"R":" ",
				(m_core->v__DOT__mut__DOT__r_we)?"W":" ",
				(m_core->v__DOT__mut__DOT__r_valid)?"V":" ",
				(m_core->v__DOT__mut__DOT__r_addr),
				(m_core->v__DOT__mut__DOT__r_data));
			printf("@%2x[%s%s%s][%s%s%s%s]",
				(m_core->v__DOT__mut__DOT__s_tlb_addr),
				(m_core->v__DOT__mut__DOT__s_pending)?"P":" ",
				(m_core->v__DOT__mut__DOT__s_tlb_hit)?"HT":"  ",
				(m_core->v__DOT__mut__DOT__s_tlb_miss)?"MS":"  ",
				(m_core->v__DOT__mut__DOT__ro_flag)?"RO":"  ",
				(m_core->v__DOT__mut__DOT__simple_miss)?"SM":"  ",
				(m_core->v__DOT__mut__DOT__ro_miss)?"RM":"  ",
				(m_core->v__DOT__mut__DOT__table_err)?"TE":"  ");
				//(m_core->v__DOT__mut__DOT__cachable)?"CH":"  ");
			/*
			printf(" M[%016lx]",
				m_core->v__DOT__mut__DOT__r_tlb_match);
			printf(" P[%3d] = 0x%08x, V=0x%08x, C=0x%08x, CTXT=%04x",
				m_last_tlb_index,
				m_core->v__DOT__mut__DOT__tlb_pdata[m_last_tlb_index],
				m_core->v__DOT__mut__DOT__tlb_vdata[m_last_tlb_index],
				m_core->v__DOT__mut__DOT__tlb_cdata[m_last_tlb_index],
				m_core->v__DOT__mut__DOT__r_context_word);
			*/
			printf("\n");
		}

		m_core->eval();
		m_core->i_clk = 0;
		m_core->eval();

		m_tickcount++;
	}

	void reset(void) {
		m_core->i_reset    = 1;
		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc  = 0;
		m_core->i_wbm_stb  = 0;
		tick();
		m_core->i_reset  = 0;
	}

	void wb_tick(void) {
		m_core->i_reset  = 0;
		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc  = 0;
		m_core->i_wbm_stb  = 0;
		tick();
		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_err);
	}

	unsigned operator[](unsigned a) {
		a &= ((1<<LGMEMSIZE)-1);
		return m_core->v__DOT__ram__DOT__mem[a];
	}

	unsigned setup_read(unsigned a) {
		int		errcount = 0;
		unsigned	result;
		m_miss = false; m_err = false;

		printf("WB-READS(%08x)\n", a);

		m_core->i_ctrl_cyc_stb = 1;
		m_core->i_wbm_cyc = 0;
		m_core->i_wbm_stb = 0;
		m_core->i_wb_we  = 0;
		m_core->i_wb_addr= a;

		if (m_core->o_rtn_stall) {
			while((errcount++ < BOMBCOUNT)&&(m_core->o_rtn_stall))
				tick();
		} tick();

		m_core->i_ctrl_cyc_stb = 0;

		while((errcount++ <  BOMBCOUNT)&&(!m_core->o_rtn_ack)) {
			tick();
		}


		result = m_core->o_rtn_data;
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_miss);

		if(errcount >= BOMBCOUNT) {
			printf("SETTING ERR TO TRUE!!!!! (BOMB)\n");
			m_bomb = true;
		} else if (!m_core->o_rtn_ack) {
			printf("SETTING ERR TO TRUE--NO ACK, NO TIMEOUT\n");
			m_bomb = true;
		}
		tick();

		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_miss);
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_stall);

		return result;
	}

	void setup_write(unsigned a, unsigned v) {
		int		errcount = 0;
		m_miss = false; m_err = false;

		printf("WB-WRITES(%08x,%08x)\n", a,v);

		m_core->i_ctrl_cyc_stb = 1;
		m_core->i_wbm_cyc = 0;
		m_core->i_wbm_stb = 0;
		m_core->i_wb_we  = 1;
		m_core->i_wb_addr= a;
		m_core->i_wb_data= v;

		if (a & 0x080)
			m_last_tlb_index = (a>>1)&0x3f;

		if (m_core->o_rtn_stall) {
			while((errcount++ < BOMBCOUNT)&&(m_core->o_rtn_stall))
				tick();
		} tick();

		m_core->i_ctrl_cyc_stb = 0;

		while((errcount++ <  BOMBCOUNT)&&(!m_core->o_rtn_ack)) {
			tick();
		}


		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_miss);

		if(errcount >= BOMBCOUNT) {
			printf("SETTING ERR TO TRUE!!!!! (BOMB)\n");
			m_bomb = true;
		} else if (!m_core->o_rtn_ack) {
			printf("SETTING ERR TO TRUE--NO ACK, NO TIMEOUT\n");
			m_bomb = true;
		}
		tick();

		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_miss);
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_stall);
	}

	unsigned wb_read(unsigned a, bool *err) {
		int		errcount = 0;
		unsigned	result;
		if (err)	*err = false;

		printf("WB-READM(%08x)\n", a);

		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc = 1;
		m_core->i_wbm_stb = 1;
		m_core->i_wb_we  = 0;
		m_core->i_wb_addr= a;

		if (m_core->o_rtn_stall) {
			while((errcount++ < BOMBCOUNT)&&(m_core->o_rtn_stall)) {
				tick();
				if ((err)&&((m_core->o_rtn_err)||(m_core->o_rtn_miss))) {
					if (!*err) {
						m_miss = (m_core->o_rtn_miss);
						m_err  = (m_core->o_rtn_err);
					} *err = true;
					m_core->i_ctrl_cyc_stb = 0;
					m_core->i_wbm_cyc = 0;
					m_core->i_wbm_stb = 0;
					tick();
					return 0;
				}
			}
		} tick();

		m_core->i_wbm_stb = 0;

		while((errcount++ <  BOMBCOUNT)&&(!m_core->o_rtn_ack)) {
			tick();
			if ((err)&&((m_core->o_rtn_err)||(m_core->o_rtn_miss))) {
				if (!*err) {
					m_miss = (m_core->o_rtn_miss);
					m_err  = (m_core->o_rtn_err);
				} *err = true;
				m_core->i_ctrl_cyc_stb = 0;
				m_core->i_wbm_cyc = 0;
					m_core->i_wbm_stb = 0;
				tick();
				return 0;
			}
		}


		result = m_core->o_rtn_data;
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_miss);

		// Release the bus?
		m_core->i_wbm_cyc = 0;
		m_core->i_wbm_stb = 0;

		if(errcount >= BOMBCOUNT) {
			printf("SETTING ERR TO TRUE!!!!! (BOMB)\n");
			m_bomb = true;
		} else if (!m_core->o_rtn_ack) {
			printf("SETTING ERR TO TRUE--NO ACK, NO TIMEOUT\n");
			m_bomb = true;
		}
		tick();

		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_miss);
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_stall);

		return result;
	}

	void	wb_read(unsigned a, int len, unsigned *buf, bool *err) {
		int		errcount = 0;
		int		THISBOMBCOUNT = BOMBCOUNT * len;
		int		cnt, rdidx, inc;

		if (err)	*err = false;
		printf("WB-READM(%08x, %d)\n", a, len);

		while((errcount++ < BOMBCOUNT)&&(m_core->o_rtn_stall))
			wb_tick();

		if (errcount >= BOMBCOUNT) {
			printf("WB-READ(%d): Setting bomb to true (errcount = %d)\n", __LINE__, errcount);
			m_bomb = true;
			return;
		}

		errcount = 0;
		
		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc = 1;
		m_core->i_wbm_stb = 1;
		m_core->i_wb_we   = 0;
		m_core->i_wb_addr = a;

		rdidx =0; cnt = 0;
		inc = 1;

		do {
			int	s;
			s = (m_core->o_rtn_stall==0)?0:1;
			tick();
			if (!s)
				m_core->i_wb_addr += inc;
			cnt += (s==0)?1:0;
			if (m_core->o_rtn_ack)
				buf[rdidx++] = m_core->o_rtn_data;
			if ((err)&&((m_core->o_rtn_err)||(m_core->o_rtn_miss))) {
				if (!*err) {
					m_miss = (m_core->o_rtn_miss);
					m_err  = (m_core->o_rtn_err);
				} *err = true;
				m_core->i_ctrl_cyc_stb = 0;
				m_core->i_wbm_cyc = 0;
					m_core->i_wbm_stb = 0;
				tick();
				return;
			}
		} while((cnt < len)&&(errcount++ < THISBOMBCOUNT));

		m_core->i_wbm_stb = 0;

		while((rdidx < len)&&(errcount++ < THISBOMBCOUNT)) {
			tick();
			if ((err)&&((m_core->o_rtn_err)||(m_core->o_rtn_miss))) {
				if (!*err) {
					m_miss = (m_core->o_rtn_miss);
					m_err  = (m_core->o_rtn_err);
				} *err = true;
				m_core->i_ctrl_cyc_stb = 0;
				m_core->i_wbm_cyc = 0;
					m_core->i_wbm_stb = 0;
				tick();
				return;
			}
			if (m_core->o_rtn_ack)
				buf[rdidx++] = m_core->o_rtn_data;
		}

		// Release the bus?
		m_core->i_wbm_cyc = 0;

		if(errcount >= THISBOMBCOUNT) {
			printf("SETTING ERR TO TRUE!!!!! (errcount=%08x, THISBOMBCOUNT=%08x)\n", errcount, THISBOMBCOUNT);
			m_bomb = true;
		} else if (!m_core->o_rtn_ack) {
			printf("SETTING ERR TO TRUE--NO ACK, NO TIMEOUT\n");
			m_bomb = true;
		}
		tick();
		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_miss);
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_stall);
	}

	void	wb_write(unsigned a, unsigned v, bool *err) {
		int errcount = 0;

		if (err)	*err = false;
		printf("WB-WRITEM(%08x) <= %08x\n", a, v);
		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc = 1;
		m_core->i_wbm_stb = 1;
		m_core->i_wb_we  = 1;
		m_core->i_wb_addr= a;
		m_core->i_wb_data= v;

		if (m_core->o_rtn_stall)
			while((errcount++ < BOMBCOUNT)&&(m_core->o_rtn_stall)) {
				printf("Stalled, so waiting, errcount=%d\n", errcount);
				tick();
				if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
					if (!*err) {
						m_miss = (m_core->o_rtn_miss);
						m_err  = (m_core->o_rtn_err);
					} *err = true;
					m_core->i_wbm_cyc = 0;
					m_core->i_wbm_stb = 0;
					tick();
					return;
				}
			}
		tick();
		if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
			if (!*err) {
				m_miss = (m_core->o_rtn_miss);
				m_err  = (m_core->o_rtn_err);
			} *err = true;
			m_core->i_wbm_cyc = 0;
			m_core->i_wbm_stb = 0;
			tick();
			return;
		}

		m_core->i_wbm_stb = 0;

		while((errcount++ <  BOMBCOUNT)&&(!m_core->o_rtn_ack)) {
			tick();
			if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
				if (!*err) {
					m_miss = (m_core->o_rtn_miss);
					m_err  = (m_core->o_rtn_err);
				} *err = true;
				m_core->i_wbm_cyc = 0;
				m_core->i_wbm_stb = 0;
				tick();
				return;
			}
		} tick();
		if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
			if (!*err) {
				m_miss = (m_core->o_rtn_miss);
				m_err  = (m_core->o_rtn_err);
			} *err = true;
			m_core->i_wbm_cyc = 0;
			m_core->i_wbm_stb = 0;
			tick();
			return;
		}

		// Release the bus?
		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc = 0;
		m_core->i_wbm_stb = 0;

		if(errcount >= BOMBCOUNT) {
			printf("SETTING ERR TO TRUE!!!!! (BOMB) (LINE=%d, count=%d)\n",__LINE__, errcount);
			m_bomb = true;
		} tick();
		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_miss);
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_stall);
	}

	void	wb_write(unsigned a, unsigned int ln, unsigned *buf, bool *err) {
		unsigned errcount = 0, nacks = 0;
		if (err)	*err = false;

		printf("WB-WRITEM(%08x, %d, ...)\n", a, ln);
		m_core->i_ctrl_cyc_stb = 0;
		m_core->i_wbm_cyc = 1;
		m_core->i_wbm_stb = 1;
		m_core->i_wb_we  = 1;
		for(unsigned stbcnt=0; stbcnt<ln; stbcnt++) {
			m_core->i_wb_addr= a+stbcnt;
			m_core->i_wb_data= buf[stbcnt];
			errcount = 0;

			while((errcount++ < BOMBCOUNT)&&(m_core->o_rtn_stall)) {
				tick();
				if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
					if (!*err) {
						m_miss = (m_core->o_rtn_miss);
						m_err  = (m_core->o_rtn_err);
					} *err = true;
					m_core->i_wbm_cyc = 0;
					m_core->i_wbm_stb = 0;
					tick();
					return;
				}
				if (m_core->o_rtn_ack) nacks++;
			}
			// Tick, now that we're not stalled.  This is the tick
			// that gets accepted.
			tick(); if (m_core->o_rtn_ack) nacks++;
			if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
				if (!*err) {
					m_miss = (m_core->o_rtn_miss);
					m_err  = (m_core->o_rtn_err);
				} *err = true;
				m_core->i_wbm_cyc = 0;
				m_core->i_wbm_stb = 0;
				tick();
				return;
			}
		}

		m_core->i_wbm_stb = 0;

		errcount = 0;
		while((nacks < ln)&&(errcount++ < BOMBCOUNT)) {
			tick();
			if (m_core->o_rtn_ack) {
				nacks++;
				errcount = 0;
			}
			if ((err)&&((m_core->o_rtn_miss)||(m_core->o_rtn_err))) {
				if (!*err) {
					m_miss = (m_core->o_rtn_miss);
					m_err  = (m_core->o_rtn_err);
				} *err = true;
				m_core->i_wbm_cyc = 0;
				m_core->i_wbm_stb = 0;
				tick();
				return;
			}
		}

		// Release the bus
		m_core->i_wbm_cyc = 0;
		m_core->i_wbm_stb = 0;

		if(errcount >= BOMBCOUNT) {
			printf("SETTING ERR TO TRUE!!!!! (BOMB)\n");
			m_bomb = true;
		} tick();
		assert(!m_core->o_rtn_ack);
		assert(!m_core->o_rtn_miss);
		assert(!m_core->o_rtn_err);
		assert(!m_core->o_rtn_stall);
	}

	bool	miss(void) {
		return m_miss;
	} bool	err(void) {
		return m_err;
	}

	bool	bombed(void) const { return m_bomb; }

	bool	debug(void) const { return m_debug; }
	bool	debug(bool nxtv) { return m_debug = nxtv; }
};

void	uload(unsigned len, unsigned *buf) {
	FILE	*fp = fopen("/dev/urandom", "r");

	if ((NULL == fp)||(len != fread(buf, sizeof(unsigned), len, fp))) {
		for(int i=0; i<(int)len; i++)
			buf[i] = ((unsigned)rand());
	} if (NULL == fp)
		fclose(fp);
}

void	install_page(ZIPMMU_TB *tb, int idx, unsigned va, unsigned pa, int flags) {
	int	LGTBL, LGPGSZ, LGCTXT;
	int	c;
	unsigned base;
	bool	hdebug = tb->debug();

	tb->debug(false);
	c=tb->setup_read(0);
	printf("CONTEXT-REG = %08x\n", c);
	LGTBL  = ((c>>24)&15);
	LGPGSZ= (((c>>20)&15)+8)&31;
	LGCTXT= (((c>>16)&15)+1)&31;
	c &= ((1<<LGCTXT)-1);
	base  = (2<<LGTBL)+(idx<<1);
	va &= -(1<<LGPGSZ);
	pa &= -(1<<LGPGSZ);

	printf("INSTALL[%2d] %04x:%08xV -> %08xP %s%s\n",
		idx, c, va, pa,
		(flags&MMUFLAG_RONW)?"RO":"  ",
		(flags&MMUFLAG_CCHE)?"Cachable":"");
	tb->setup_write(base  , va|(( c    &0x0ff)<<4)|flags);
	tb->setup_write(base+1, pa|(((c>>8)&0x0ff)<<4)|flags);
	tb->debug(hdebug);
}

int main(int  argc, char **argv) {
	Verilated::commandArgs(argc, argv);
	ZIPMMU_TB	*tb = new ZIPMMU_TB;
	unsigned 	*rdbuf; // *mbuf;
	unsigned	mlen = (1<<LGMEMSIZE), c, blen;

	tb->opentrace("zipmmu_tb.vcd");
	printf("Giving the core 2 cycles to start up\n");
	// Before testing, let's give the unit time enough to warm up
	tb->reset();
	for(int i=0; i<2; i++)
		tb->wb_tick();

	mlen = 1<<16;

	printf("Getting some memory ...\n");
	rdbuf = new unsigned[mlen];
	// mbuf  = new unsigned[mlen]; // Match buffer
	printf("Charging my memory with random values\n");
	uload(mlen, rdbuf);


	int	LGADR, LGTBL, LGPGSZ, LGCTXT, sr;

	c=tb->setup_read(0);
	printf("CONTROL-REG = %08x\n = %2d\n", c, c);
	sr = tb->setup_read(1);
	printf("STATUS-REG  = %08x = %2d\n", sr, sr);
	LGADR = (((c>>28)&15)+17)&31;
	LGTBL = ((c>>24)&15);
	LGPGSZ= (((c>>20)&15)+8)&31;
	LGCTXT= (((c>>16)&15)+1)&31;
	printf("LGADR       = %08x = %2d\n", LGADR, LGADR);
	printf("LGTBL       = %08x = %2d\n", LGTBL, LGTBL);
	printf("LGPGSZ      = %08x = %2d\n", LGPGSZ, LGPGSZ);
	printf("LGCTXT      = %08x = %2d\n", LGCTXT, LGCTXT);

	// First, let's make sure we can read/write the context
	printf("\n\nTest: Can we read/write the context register?\n");
	tb->setup_write(0,0x01fec);
	c=tb->setup_read(0);
	printf("CONTEXT     = %08x (0x1fec?)\n", c&0x0ffff);
	if ((c&0x0ffff) != 0x01fec)
		goto test_failure;

	// Load the table with TLB misses
	printf("\n\nTest: Can we load the table with TLB misses? (%d entries)\n", (1<<LGTBL));
	for(int i=0; i<(1<<LGTBL); i++) {
		c = 0x0f70; // Context: 0xfef7
		tb->setup_write((2<<LGTBL)+(i<<1)  , c+(((1<<LGTBL)-1-i)<<LGPGSZ));
		c = 0x0fe2; // CCHE flag only
		tb->setup_write((2<<LGTBL)+(i<<1)+1, c+(((1<<LGTBL)-1-i)<<LGPGSZ));
	}

	// Dump the table, make sure we got it right
	for(int i=0; i<(1<<LGTBL); i++) {
		unsigned v, p;
		v=tb->setup_read((2<<LGTBL)+(i<<1)  );
		p=tb->setup_read((2<<LGTBL)+(i<<1)+1);

		printf("TBL[%2d] = %08x -> %08x\n", i, v, p);
		if (v != (unsigned)(0x00f72+(((1<<LGTBL)-1-i)<<LGPGSZ)))
			goto test_failure;
		if (p != (unsigned)(0x00fe2+(((1<<LGTBL)-1-i)<<LGPGSZ)))
			goto test_failure;
	}

	// Now, let's create a fictitious process, context 1, with no pages.
	// See what happens when we try to access his stack at 0xffffffff
	bool	tberr;
	printf("\n\nTest: Do we get a TLB miss when attempting to find a non-existent page?\n");
	tberr = false;
	tb->wb_write(0xffffffff, 0x0fe, &tberr);
	if ((!tberr)||(!tb->miss())||(tb->err())) {
		printf("TBERR = %s\nMISS  = %s\nERR   = %s\n",
			(tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		goto test_failure;
	}

	tberr = false;
	install_page(tb, 0, 0x0ffffffff, (1<<LGMEMSIZE)+0*(1<<LGPGSZ),
			MMUFLAG_RONW);
	printf("\n\nTest: Do we get a TLB miss when attempting to write a RO page?\n");
	tb->wb_write(0xffffffff, 0x0fe, &tberr);
	if ((!tberr)||(!tb->miss())||(tb->err())) {
		printf("TBERR = %s\nMISS  = %s\nERR   = %s\n",
			(tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		goto test_failure;
	}

	tberr = false;
	printf("\n\nTest: What if we make this into a writeable page?\n");
	install_page(tb, 0, 0xffffffff, (1<<LGMEMSIZE)+0*(1<<LGPGSZ), 0);
	tb->wb_write(0xffffffff, 0x0fe, &tberr);
	if (tberr) {
		printf("TBERR = %s\nMISS  = %s\nERR   = %s\n",
			(tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		goto test_failure;
	}
	printf("\n\nTest: Is the next access done w/in a single clock?\n");
	tb->wb_write(0xfffffff7, 0xdeadbeef, &tberr);
	if (tberr) {
		printf("TBERR = %s\nMISS  = %s\nERR   = %s\n",
			(tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		goto test_failure;
	}


	tberr = false;
	printf("\n\nTest: What if we make this into a writeable page?\n");
	install_page(tb, 0, 0xffffffff, (1<<LGMEMSIZE)+0*(1<<LGPGSZ), 0);
	tb->wb_write(0xffffffff, 0x0fe, &tberr);
	if ((tberr)||((*tb)[0x0fff]!=0x0fe)) {
		unsigned v;
		v = ((*tb)[0x0fff]!=0x0fe);
		printf("V     = 0x%08x (!= 0x0fe?)\nTBERR = %s\nMISS  = %s\nERR   = %s\n",
			v, (tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		goto test_failure;
	}

	tberr = false;
	printf("\n\nTest: How about a read from the same location?\n");
	{
		unsigned	v;
		v = tb->wb_read(0xffffffff, &tberr);
		if ((tberr)||(v != 0x0fe)) {
			printf("V     = 0x%08x (!= 0x0fe?)\nTBERR = %s\nMISS  = %s\nERR   = %s\n",
				v,
				(tberr)?"true":"false", (tb->miss())?"true":"false",
				(tb->err())?"true":"false");
			goto test_failure;
		}
	}

	printf("Test: Burst write, within page\n");
	tb->setup_write(0, 0x0dad);
	install_page(tb, 0, ((0x0ffffffffl)&(-(1l<<LGPGSZ)))-2*(1<<LGPGSZ), (1<<LGMEMSIZE)+0*(1<<LGPGSZ), 0);
	install_page(tb, 1, ((0x0ffffffffl)&(-(1l<<LGPGSZ)))-1*(1<<LGPGSZ), (1<<LGMEMSIZE)+1*(1<<LGPGSZ), 0);
	install_page(tb, 2, ((0x0ffffffffl)&(-(1l<<LGPGSZ)))+0*(1<<LGPGSZ), (1<<LGMEMSIZE)+2*(1<<LGPGSZ), 0);

	tberr = false;
	blen = (1<<(LGPGSZ-2));
	tb->wb_write(((0xffffffff)&(-(1l<<LGPGSZ)))-2*(1<<LGPGSZ), blen, rdbuf, &tberr);
	if (tberr) {
		printf("TBERR = %s\nMISS  = %s\nERR   = %s\n",
			(tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		printf("STATUS= %08x\n", tb->setup_read(1));
		goto test_failure;
	} for(unsigned i=0; i<blen; i++) {
		if ((*tb)[i] != rdbuf[i]) {
			printf("MEM[%04x] = %08x (!= %08x as expected)\n",
				i, (*tb)[i], rdbuf[i]);
			goto test_failure;
		}
	}

	printf("Test: Burst read\n");
	// Try somewhere within that last page
	tberr = false;
	tb->wb_read(((0xffffffff)&(-(1<<LGPGSZ)))-2*(1<<LGPGSZ)+18, blen, rdbuf, &tberr);
	if (tberr) {
		printf("TBERR = %s\nMISS  = %s\nERR   = %s\n",
			(tberr)?"true":"false", (tb->miss())?"true":"false",
			(tb->err())?"true":"false");
		printf("STATUS= %08x\n", tb->setup_read(1));
		goto test_failure;
	} for(unsigned i=0; i<blen; i++) {
		if ((*tb)[i+18] != rdbuf[i]) {
			printf("MEM[%04x] = %08x (!= %08x as expected)\n",
				i+18, (*tb)[i+18], rdbuf[i]);
			goto test_failure;
		}
	}


	printf("Tests not (yet) implemented\n");
	printf("Test: Burst read crossing pages, second page valid\n");
	printf("Test: Burst read crossing pages, second page invalid\n");

	printf("SUCCESS!!\n");
	exit(0);
test_failure:
	printf("FAIL-HERE\n");
	for(int i=0; i<4; i++)
		tb->tick();
	printf("TEST FAILED\n");
	exit(-1);
}
