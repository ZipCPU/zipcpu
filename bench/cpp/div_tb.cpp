///////////////////////////////////////////////////////////////////////////////
//
// Filename:	div_tb.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Bench testing for the divide unit found within the Zip CPU.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
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
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <assert.h>

#include <ctype.h>

#include "verilated.h"
#include "Vdiv.h"

#include "testb.h"
// #include "twoc.h"

class	DIV_TB : public TESTB<Vdiv> {
public:
	DIV_TB(void) {
	}

	~DIV_TB(void) {}

	void	reset(void) {
		// m_flash.debug(false);
		TESTB<Vdiv>::reset();
	}

	bool	on_tick(void) {
		tick();
		return true;
	}

	void	bprint(char *str, int nbits, unsigned long v) {
		while(*str)
			str++;
		for(int i=0; i<nbits; i++) {
			if ((1l<<(nbits-1-i))&v)
				*str++ = '1';
			else
				*str++ = '0';
			if (((nbits-1-i)&3)==0)
				*str++ = ' ';
		} *str = '\0';
	}

	void	dbgdump(void) {
		char	outstr[2048], *s;
		sprintf(outstr, "Tick %4ld %s%s%s%s%s%s%s %2d(%s= 0)",
			m_tickcount,
			(m_core->o_busy)?"B":" ", 
			(m_core->v__DOT__r_busy)?"R":" ", 
			(m_core->o_valid)?"V":" ",
			(m_core->i_wr)?"W":" ",
			(m_core->v__DOT__pre_sign)?"+":" ",
			(m_core->v__DOT__r_sign)?"-":" ",
			(m_core->v__DOT__r_z)?"Z":" ",
			m_core->v__DOT__r_bit,
			(m_core->v__DOT__last_bit)?"=":"!");
		s = &outstr[strlen(outstr)];
		sprintf(s, "%s\n%10s %40s",s, "Div","");
			s = &s[strlen(s)];
		bprint( s, 32, m_core->v__DOT__r_dividend); 
			s=&s[strlen(s)];
		sprintf(s, "%s\n%10s ",s, "Div"); s = &s[strlen(s)];
		bprint( s, 64, m_core->v__DOT__r_divisor);
			s=&s[strlen(s)];
		sprintf(s, "%s\n%10s %40s",s, "Q",""); s=&s[strlen(s)];
		bprint( s, 32, m_core->o_quotient); s = &s[strlen(s)];
		sprintf(s, "%s\n%10s %38s",s, "Diff","");
			s=&s[strlen(s)];
		bprint( s, 33, m_core->v__DOT__diff); s = &s[strlen(s)];
		strcat(s, "\n");
		puts(outstr);
	}

	void	tick(void) {
		bool	debug = false;

		if (debug)
			dbgdump();
		TESTB<Vdiv>::tick();
	}

	void	divs(int n, int d) {
		bool	dbg = false;
		int	ans;
		ans = (d==0)?0:	(n / d);
		assert(m_core->o_busy == 0);

		m_core->i_rst = 0;
		m_core->i_wr = 1;
		m_core->i_signed = 1;
		m_core->i_numerator = n;
		m_core->i_denominator = d;

		tick();

		m_core->i_wr = 0;
		m_core->i_signed = 0;
		m_core->i_numerator = 0;
		m_core->i_denominator = 0;

		// Make certain busy is immediately true upon the first clock
		// after we issue the divide.
		assert(m_core->o_busy);
		assert(m_core->o_valid == 0);

		// while((!m_core->o_valid)&&(!m_core->o_err))
		while(!m_core->o_valid) {
			if (!m_core->o_busy) {
				// Make certain busy is asserted whenever
				// valid is false and we're ... well, busy
				dbgdump();
				assert(m_core->o_busy);
			}
			tick();
		} if (dbg) dbgdump();
		assert(!m_core->o_busy);

		if (dbg) {
			printf("%s%s: %d / %d =? %d\n",
				(m_core->o_valid)?"V":" ",
				(m_core->o_err)?"E":" ",
				n, d, m_core->o_quotient);
		}
		if ((m_core->o_err)||(d==0)) {
			if (d==0)
				assert(m_core->o_err);
			else	assert(!m_core->o_err);
		} else
			assert(ans == (int)m_core->o_quotient);
	}

	void	divu(unsigned n, unsigned d) {
		bool	dbg = false;
		unsigned	ans;
		ans = (d==0)?0:	(n / d);
		assert(m_core->o_busy == 0);

		m_core->i_rst = 0;
		m_core->i_wr = 1;
		m_core->i_signed = 0;
		m_core->i_numerator = n;
		m_core->i_denominator = d;

		tick();

		m_core->i_wr = 0;
		m_core->i_signed = 0;
		m_core->i_numerator = 0;
		m_core->i_denominator = 0;

		assert(m_core->o_busy);
		assert(m_core->o_valid == 0);

		while(!m_core->o_valid) {
			assert(m_core->o_busy);
			tick();
		} assert(!m_core->o_busy);

		if (dbg) {
			printf("%s%s: %u / %u =? %d (Expecting %u)\n",
				(m_core->o_valid)?"V":" ",
				(m_core->o_err)?"E":" ",
				n, d, m_core->o_quotient, ans);
		}
		if ((m_core->o_err)||(d==0)) {
			if (d==0)
				assert(m_core->o_err);
			else	assert(!m_core->o_err);
		} else
			assert(ans == (unsigned)m_core->o_quotient);
	}

	void	divide(int n, int d) {
		divs(n,d);
	}
};

void	usage(void) {
	printf("USAGE: div_tb\n");
	printf("\n");
	printf("\t\n");
}

int	main(int argc, char **argv) {
	Verilated::commandArgs(argc, argv);
	DIV_TB	*tb = new DIV_TB();
	int	rcode = EXIT_SUCCESS;

	tb->reset();
	tb->opentrace("div_tb.vcd");
	tb->divide(125,7);
	tb->tick();
	tb->divide(125,-7);
	tb->tick();
	tb->divu((1u<<31),7);
	tb->divu((7u<<29),(1u<<31));
	tb->tick();
	tb->divs(32768,0);
	tb->tick();
	tb->divu((1u<<31),0);
	tb->tick();
	tb->divs((1u<<30),0);
	tb->tick();
	for(int i=32767; i>=0; i--) {
		tb->divs((1u<<30),i);
		tb->tick();
	} for(int i=32767; i>=0; i--) {
		// tb->divu(-1, i);
		tb->divu((1u<<31), i);
		tb->tick();
	} for(int i=32767; i>=0; i--) {
		tb->divide(32768, i);
		tb->tick();
	}
	/*
	 * While random data is a nice test idea, the following just never
	 * really tested the divide unit thoroughly enough.
	 *
	tb->divide(rand(),rand()/2);
	tb->tick();
	tb->divide(rand(),rand()/2);
	tb->tick();
	tb->divide(rand(),rand()/2);
	tb->tick();
	tb->divide(rand(),rand()/2);
	*/

	delete	tb;

	printf("SUCCESS!\n");
	exit(rcode);
}

