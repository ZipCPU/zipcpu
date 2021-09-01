////////////////////////////////////////////////////////////////////////////////
//
// Filename:	mpy_tb.cpp
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Bench testing for the multiply ALU instructions used within the
//		Zip CPU.  This depends upon the cpuops.v module, but should be
//	independent of the internal settings within the module.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
#include <stdint.h>

#include <stdlib.h>
#include <ctype.h>

#include "verilated.h"
#include "Vcpuops.h"

#ifdef	ROOT_VERILATOR
#include "Vcpuops___024root.h"

#define	VVAR(A)	rootp->cpuops__DOT_ ## A
#elif	defined(NEW_VERILATOR)
#define	VVAR(A)	cpuops__DOT_ ## A
#else
#define	VVAR(A)	v__DOT_ ## A
#endif


#include "testb.h"
#include "cpudefs.h"
// #include "twoc.h"

// class CPUOPS_TB declaration
// {{{
class	CPUOPS_TB : public TESTB<Vcpuops> {
public:
	// Nothing special to do in a startup.
	CPUOPS_TB(void) {}

	// ~CPUOPS_TB(void) {}

	// reset
	// {{{
	// Calls TESTB<>::reset to reset the core.  Makes sure the i_stb line
	// is low during this reset.
	//
	void	reset(void) {
		// m_flash.debug(false);
		m_core->i_stb = 0;

		TESTB<Vcpuops>::reset();
	}
	// }}}

	// dbgdump();
	// {{{
	// Just before the positive edge of every clock, we call this function
	// (if the debug flag is set).  This prints out a line of information
	// telling us what is going on within the logic, allowing us access
	// for debugging purposes to inspect things.
	//
	// Other than debugging, this isn't necessary for the functioning of the
	// test bench.  At the same time, what are you using a test bench for if
	// not for debugging?
	//
	void	dbgdump(void) {
		char	outstr[2048], *s;
		sprintf(outstr, "Tick %4lld %s%s ",
			(unsigned long long)m_tickcount,
			(m_core->i_reset)?"R":" ", 
			(m_core->i_stb)?"CE":"  ");
		switch(m_core->i_op) {
		case  0: strcat(outstr, "   SUB"); break;
		case  1: strcat(outstr, "   AND"); break;
		case  2: strcat(outstr, "   ADD"); break;
		case  3: strcat(outstr, "    OR"); break;
		case  4: strcat(outstr, "   XOR"); break;
		case  5: strcat(outstr, "   LSR"); break;
		case  6: strcat(outstr, "   LSL"); break;
		case  7: strcat(outstr, "   ASR"); break;
		case  8: strcat(outstr, "   MPY"); break;
		case  9: strcat(outstr, "LODILO"); break;
		case 10: strcat(outstr, "MPYUHI"); break;
		case 11: strcat(outstr, "MPYSHI"); break;
		case 12: strcat(outstr, "  BREV"); break;
		case 13: strcat(outstr, "  POPC"); break;
		case 14: strcat(outstr, "   ROL"); break;
		case 15: strcat(outstr, "   MOV"); break;
		default: strcat(outstr, "UNKWN!"); break;
		} s = &outstr[strlen(outstr)];
		sprintf(s, "(%x) 0x%08x 0x%08x -> 0x%08x [%x] %s%s",
			m_core->i_op,
			m_core->i_a, m_core->i_b,
			m_core->o_c, m_core->o_f,
			(m_core->o_valid)?"V":" ",
			(m_core->o_busy)?"B":" ");
		s = &outstr[strlen(outstr)];

#if(OPT_MULTIPLY==1)
#define	mpy_result	VVAR(_mpy_result)
		sprintf(s, "1,MPY[][][%016lx]",
			(unsigned long)m_core->mpy_result);
		s = &outstr[strlen(outstr)];
#elif(OPT_MULTIPLY==2)
		sprintf(s, "2,MPY[%016lx][%016lx][%016lx]",
#define	MPY2VAR(A)	VVAR(_thempy__DOT__IMPY__DOT__MPN1__DOT__MPY2CK__DOT_ ## A)
#define	r_mpy_a_input	MPY2VAR(_r_mpy_a_input)
#define	r_mpy_b_input	MPY2VAR(_r_mpy_b_input)
#define	mpy_result	VVAR(_mpy_result)
			m_core->r_mpy_a_input,
			m_core->r_mpy_b_input,
			m_core->mpy_result);
		s = &outstr[strlen(outstr)];
#elif(OPT_MULTIPLY==3)
#define	MPY3VAR(A)	VVAR(_thempy__DOT__IMPY__DOT__MPN1__DOT__MPN2__DOT__MPY3CK__DOT_ ## A)
#define	r_mpy_a_input	MPY3VAR(_r_mpy_a_input)
#define	r_mpy_b_input	MPY3VAR(_r_mpy_b_input)
#define	r_smpy_result	MPY3VAR(_r_smpy_result)
#define	mpypipe		MPY3VAR(_mpypipe)
		sprintf(s, "3,MPY[%08x][%08x][%016llx], P[%d]",
			m_core->r_mpy_a_input,
			m_core->r_mpy_b_input,
			(long long)m_core->r_smpy_result,
			m_core->mpypipe);

#endif

#if(OPT_MULTIPLY != 1)
#define	this_is_a_multiply_op	((m_core->i_stb)&&(((m_core->i_op&0xe) == 5)||((m_core->i_op&0x0f)==0xc))) // VVAR(_this_is_a_multiply_op)
		if (this_is_a_multiply_op)
			strcat(s, " MPY-OP");
#endif
		puts(outstr);
	}
	// }}}

	// tick()
	// {{{
	// Call this to step the processor.
	//
	// This is a bit unusual compared to other tick() functions I have in
	// my simulators in that there are a lot of calls to eval() with clk==0.
	// This is because the multiply logic for OPT_MULTIPLY < 3 depends upon
	// it to be valid.  I assume any true Xilinx, or even higher level,
	// implementation wouldn't have this problem.
	//
	void	tick(void) {
		bool	debug = false;

		// Insist that we are never both busy and producing a valid
		// result at the same time.  One or the other may be true,
		// but never both.
		assert((!m_core->o_busy)||(!m_core->o_valid));
		//
		TESTB<Vcpuops>::tick();

		if (debug)
			dbgdump();
	}
	// }}}

	// clear_ops()
	// {{{
	// Runs enough clocks through the device until it is neither busy nor
	// valid.  At this point, the ALU should be thoroughly clear.  Then
	// we tick things once more.
	//
	void	clear_ops(void) {
		m_core->i_stb    = 0;
		m_core->i_op    = 0;

		do {
			tick();
		} while((m_core->o_busy)||(m_core->o_valid));
		tick();
	}
	// }}}

	// op(op, a, b)
	// {{{
	// This is a fairly generic CPU operation call.  What makes it less
	// than generic are two things: 1) the ALU is cleared before any
	// new instruction, and 2) the tick count at the end is compared
	// against the tick count OPT_MULTIPLY says we should be getting.
	// A third difference between this call in simulation and a real
	// call within the CPU is that we never set the reset mid-call, whereas
	// the CPU may need to do that if a jump is made and the pipeline needs
	// to be cleared.
	//
	uint32_t	op(int op, int a, int b) {
		// Make sure we start witht he core idle
		if (m_core->o_valid)
			clear_ops();

		// Set the arguments to the CPUOPS core to get a multiple
		// started
		m_core->i_stb    = 1;
		m_core->i_op    = op;
		m_core->i_a     = a;
		m_core->i_b     = b;

		uint64_t now = m_tickcount;

		// Tick once to get it going
		tick();

		// Clear the input arguments to the multiply
		m_core->i_stb    = 0;
		m_core->i_a     = 0;
		m_core->i_b     = 0;

		// Wait for the result to be valid
		while(!m_core->o_valid)
			tick();

		// Check that we used the number of clock ticks we said we'd
		// be using.  OPT_MULTIPLY is *supposed* to be equal to this
		// number.
		if((m_tickcount - now)!=OPT_MULTIPLY) {
			printf("%lld ticks seen, %d ticks expected\n",
				(unsigned long long)(m_tickcount-now), OPT_MULTIPLY);
			dbgdump();
			printf("TEST-FAILURE!\n");
			closetrace();
			exit(EXIT_FAILURE);
		}

		return m_core->o_c;
	}
	// }}}

	// test(a,b)
	// {{{
	// Here's our testing function.  Pardon the verbosity of the error
	// messages within it, but ...  well, hopefully you won't ever encounter
	// any of those errors. ;)
	//
	// The function works by applying the two inputs to all three of the
	// multiply functions, MPY, MPSHI, and MPYUHI.  Results are compared
	// against a local multiply on the local (host) machine.  If there's
	// any mismatch, an error message is printed and the test fails.
	void	mpy_test(int a, int b) {
		// {{{
		const	int OP_MPY = 0x0c, OP_MPYSHI=0xb, OP_MPYUHI=0x0a;
		const	bool	debug = false;
		int64_t		ia, ib, sv;
		uint64_t	ua, ub, uv;
		unsigned	r, s, u;
		// }}}

		clear_ops();

		if (debug)
			printf("MPY-TEST: 0x%08x x 0x%08x\n", a, b);

		ia = (long)a; ib = (long)b; sv = ia * ib;
		ua = ((uint64_t)a)&0x0ffffffffu;
		ub = ((uint64_t)b)&0x0ffffffffu;
		uv = ua * ub;

		r = op(OP_MPY, a, b);
		s = op(OP_MPYSHI, a, b);
		u = op(OP_MPYUHI, a, b);
		tick();

		// Let's check our answers, and see if we got the right results
		// {{{
		if ((r ^ sv)&0x0ffffffffu) {
			printf("TEST FAILURE(MPY), MPY #1\n");
			printf("Comparing 0x%08x to 0x%016llx\n", r, (long long)sv);
			printf("TEST-FAILURE!\n");
			closetrace();
			exit(EXIT_FAILURE);
		} if ((r ^ uv)&0x0ffffffffu) {
			printf("TEST FAILURE(MPY), MPY #2\n");
			printf("Comparing 0x%08x to 0x%016llx\n", r, (unsigned long long)uv);
			printf("TEST-FAILURE!\n");
			closetrace();
			exit(EXIT_FAILURE);
		}

		if ((s^(sv>>32))&0x0ffffffffu) {
			printf("TEST FAILURE(MPYSHI), MPY #3\n");
			printf("Comparing 0x%08x to 0x%016llx\n", s, (long long)sv);
			printf("TEST-FAILURE!\n");
			closetrace();
			exit(EXIT_FAILURE);
		} if ((u^(uv>>32))&0x0ffffffffu) {
			printf("TEST FAILURE(MPYUHI), MPY #4\n");
			printf("Comparing 0x%08x to 0x%016llx\n", u, (unsigned long long)uv);
			printf("TEST-FAILURE!\n");
			closetrace();
			exit(EXIT_FAILURE);
		}
		// }}}
	}
	// }}}
};
// }}}

void	usage(void) {
// {{{
	printf("USAGE: mpy_tb [a b]\n");
	printf("\n");
	printf(
"The test is intended to be run with no arguments.  When run in this fashion,\n"
"a series of multiplcation tests will be conducted using all three multiply\n"
"instructions.  Any test failure will terminate the program with an exit\n"
"condition.  Test success will terminate with a clear test condition.  \n"
"During the test, you may expect a large amount of debug output to be\n"
"produced.  This is a normal part of testing.  For the meaning of the debug\n"
"output, please consider the source code.  The last line of the debug output,\n"
"however, will always include either the word \"FAIL\" or \"SUCCESS\"\n"
"depending on whether the test succeeds or fails.\n\n"
"If the two arguments a and b are given, they will be interpreted according\n"
"to the form of strtol, and the test will only involve testing those two\n"
"parameters\n\n");
// }}}
}

int	main(int argc, char **argv) {
	// Setup verilator
	Verilated::commandArgs(argc, argv);
	// Now, create a test bench.
	CPUOPS_TB	*tb = new CPUOPS_TB();
	int	rcode = EXIT_SUCCESS;
	// tb->opentrace("mpy_tb.vcd");

	// Get us started by a couple of clocks past reset.
	// {{{
	// This isn't that unreasonable, since the CPU needs to load up the
	//  pipeline before any first instruction will be executed.
	tb->reset();
	tb->tick();
	tb->tick();
	tb->tick();
	// }}}

	// Look for options, such as '-h'.
	// {{{
	// Trap those here, and produce a usage statement.
	if ((argc > 1)&&(argv[1][0]=='-')&&(isalpha(argv[1][1]))) {
		usage();
		exit(EXIT_SUCCESS);
	}
	// }}}

	if (argc == 3) {
		// Were we given enough arguments to run a user-specified test?
		// {{{
		tb->mpy_test(
			strtol(argv[1], NULL, 0),
			strtol(argv[2], NULL, 0));
		// }}}
	} else {
		// Otherwise we run through a canned set of tests.
		// {{{
		tb->mpy_test(0,0);
		tb->mpy_test(-1,0);
		tb->mpy_test(-1,-1);
		tb->mpy_test(1,-1);
		tb->mpy_test(1,0);
		tb->mpy_test(0,1);
		tb->mpy_test(1,1);

		for(int a=0; ((a&0xfff00000)==0); a+=137)
			tb->mpy_test(139, a);

		for(int a=0; ((a&0x80000000)==0); a+=0x197e2)
			tb->mpy_test(0xf97e27ab, a);
		// }}}
	}

	printf("SUCCESS!\n");
	exit(rcode);
}

