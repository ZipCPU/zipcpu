////////////////////////////////////////////////////////////////////////////////
//
// Filename:	cputest.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To test the CPU, it's instructions, cache, and pipeline, to make
//		certain that it works.  This includes testing that each of the
//	instructions works, as well as any strange instruction combinations.
//
//	This test does not check the LOCK instruction.  This capability is
//	tested via the lockcheck program also found in the same directory.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2022, Gisselquist Technology, LLC
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
#include <stdint.h>
#include "board.h"
#include "zipcpu.h"
#include "zipsys.h"

#ifndef	NULL
#define NULL	(void *)0
#endif

#define	_ZIP_HAS_WBUART
#define	PIC	_zip->z_pic

#define	UARTTX		_uart->u_tx
#define	UART_CTRL	_uart->u_setup
#define	TXBUSY		(UARTTX & 0x0100)

#define	HAVE_COUNTER
#define	COUNTER		_zip->z_m.ac_ck

// #define	HAVE_SCOPE
// #define	SCOPEc			_sys->io_scope[0].s_ctrl
// #define	SCOPE_DELAY		4
// #define	TRIGGER_SCOPE_NOW	(WBSCOPE_TRIGGER|SCOPE_DELAY)
// #define	PREPARE_SCOPE		SCOPE_DELAY

unsigned	zip_ucc(void);
unsigned	zip_cc(void);
void		zip_save_context(void *);
void		zip_halt(void);


void	txchr(char v);
void	txstr(const char *str);
void	txhex(int num);
void	tx4hex(int num);

#ifdef	COUNTER
#define	MARKSTART	start_time = COUNTER
#define	MARKSTOP	stop_time  = COUNTER
#else
#ifdef	TIMER
#define	MARKSTART	start_time = TIMER
#define	MARKSTOP	stop_time  = TIMER
#else
#define	MARKSTART
#define	MARKSTOP
#endif
#endif


extern	int	run_test(void *pc, void *stack);
// {{{
asm("\t.text\n\t.global\trun_test\n"
	"\t.type\trun_test,@function\n"
"run_test:\n"
	"\tCLR\tR3\n"
	"\tMOV\ttest_return(PC),uR0\n"
	"\tMOV\tR3,uR1\n"
	"\tMOV\tR3,uR2\n"
	"\tMOV\tR3,uR3\n"
	"\tMOV\tR3,uR4\n"
	"\tMOV\tR3,uR5\n"
	"\tMOV\tR3,uR6\n"
	"\tMOV\tR3,uR7\n"
	"\tMOV\tR3,uR8\n"
	"\tMOV\tR3,uR9\n"
	"\tMOV\tR3,uR10\n"
	"\tMOV\tR3,uR11\n"
	"\tMOV\tR3,uR12\n"
	"\tMOV\tR2,uSP\n"	// uSP = stack
	"\tMOV\t0x20+R3,uCC\n"	// Clear uCC of all but the GIE bit
	"\tMOV\tR1,uPC\n"	// uPC = pc
	"\tRTU\n"
"test_return:\n"
	"\tMOV\tuR1,R1\n"
	"\tAND\t0xffffffdf,CC\n"
	// Works with 5 NOOPS, works with 3 NOOPS, works with 1 NOOP
	"\tJMP\tR0\n");
// }}}

extern	int	idle_test(void);
// {{{
asm("\t.text\n\t.global\tidle_test\n"
	"\t.type\tidle_test,@function\n"
"idle_test:\n"
	"\tCLR\tR1\n"
	"\tMOV\tidle_loop(PC),uR0\n"
	"\tMOV\tR1,uR1\n"
	"\tMOV\tR1,uR2\n"
	"\tMOV\tR1,uR3\n"
	"\tMOV\tR1,uR4\n"
	"\tMOV\tR1,uR5\n"
	"\tMOV\tR1,uR6\n"
	"\tMOV\tR1,uR7\n"
	"\tMOV\tR1,uR8\n"
	"\tMOV\tR1,uR9\n"
	"\tMOV\tR1,uR10\n"
	"\tMOV\tR1,uR11\n"
	"\tMOV\tR1,uR12\n"
	"\tMOV\tR1,uSP\n"
	"\tMOV\t0x20+R1,uCC\n"
	"\tMOV\tidle_loop(PC),uPC\n"
	"\tWAIT\n"
	"\tMOV uPC,R1\n"
	"\tCMP idle_loop(PC),R1\n"
	"\tLDI   0,R1\n"
	"\tLDI.NZ 1,R1\n"
	"\nRETN\n"
"idle_loop:\n"
	"\tWAIT\n"
	"\tBRA idle_loop\n");
// }}}

void	break_one(void);
// {{{
asm("\t.text\n\t.global\tbreak_one\n"
	"\t.type\tbreak_one,@function\n"
"break_one:\n"
	"\tLDI\t0,R1\n"
	"\tBREAK\n"
	"\tLDI\t1,R1\n"	// Test fails
	"\tJMP\tR0");
// }}}

void	break_two(void);
// {{{
	// Can we stop a break before we hit it?
asm("\t.text\n\t.global\tbreak_two\n"
	"\t.type\tbreak_two,@function\n"
"break_two:\n"
	"\tLDI\t0,R1\n"
	"\tJMP\tR0\n"
	"\tBREAK\n");
// }}}

void	break_three(void);
// {{{
	// Can we jump to a break, and still have the uPC match
asm("\t.text\n\t.global\tbreak_three\n"
	"\t.type\tbreak_three,@function\n"
	// R1 = 0 by default from calling.  This will return as though
	// we had succeeded.
"break_three:\n"
	"\tBREAK\n");
// }}}

void	early_branch_test(void);
// {{{
asm("\t.text\n\t.global\tearly_branch_test\n"
	"\t.type\tearly_branch_test,@function\n"
"early_branch_test:\n"
	"\tLDI\t1,R1\n"
	"\tBRA\t_eb_a\n"
	"\tBREAK\n"	
"_eb_a:\n"
	"\tLDI\t2,R1\n"
	"\tBRA\t_eb_b\n"
	"\tNOP\n"
	"\tBREAK\n"
"_eb_b:\n"
	"\tLDI\t3,R1\n"
	"\tBRA\t_eb_c\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tBREAK\n"
"_eb_c:\n"
	"\tLDI\t4,R1\n"
	"\tBRA\t_eb_d\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tBREAK\n"
"_eb_d:\n"
	"\tLDI\t5,R1\n"
	"\tBRA\t_eb_e\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tBREAK\n"
"_eb_e:\n"
	"\tLDI\t6,R1\n"
	"\tBRA\t_eb_f\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tNOP\n"
	"\tBREAK\n"
"_eb_f:\n"
	"\tLDI\t0,R1\n"
	"\tJMP\tR0");
// }}}

void	trap_test_and(void);
// {{{
asm("\t.text\n\t.global\ttrap_test_and\n"
	"\t.type\ttrap_test_and,@function\n"
"trap_test_and:\n"
	"\tLDI\t0,R1\n"
	"\tAND\t0xffffffdf,CC\n"
	"\tLDI\t1,R1\n"	// Test fails
	"\tJMP\tR0");
// }}}

void	trap_test_clr(void);
// {{{
asm("\t.text\n\t.global\ttrap_test_clr\n"
	"\t.type\ttrap_test_clr,@function\n"
"trap_test_clr:\n"
	"\tLDI\t0,R1\n"
	"\tCLR\tCC\n"
	"\tLDI\t1,R1\n"	// Test fails
	"\tJMP\tR0");
// }}}

void	overflow_test(void);
// {{{
asm("\t.text\n\t.global\toverflow_test\n"
	"\t.type\toverflow_test,@function\n"
"overflow_test:\n"
	"\tLDI\t0,R1\n"
	"\tLDI\t0,R3\n"		// Clear our scorecard
// First test: does adding one to the maximum integer cause an overflow?
	"\tLDI\t-1,R2\n"
	"\tLSR\t1,R2\n"
	"\tADD\t1,R2\n"
	"\tOR.V\t1,R3\n"
// Second test: does subtracting one to the minimum integer cause an overflow?
	"\tLDI\t0x80000000,R2\n"
	"\tSUB\t1,R2\n"
	"\tOR.V\t2,R3\n"
// Third test, overflow from LSR
	"\tLDI\t0x80000000,R2\n"
	"\tLSR\t1,R2\n"		// Overflows 'cause the sign changes
	"\tOR.V\t4,R3\n"
// Fourth test, overflow from LSL
	"\tLDI\t0x40000000,R2\n"
	"\tLSL\t1,R2\n"
	"\tOR.V\t8,R3\n"
// Fifth test, overflow from LSL, negative to positive
	"\tLDI\t0x80000000,R2\n"
	"\tLSL\t1,R2\n"
	"\tOR.V\t16,R3\n"
// Record our scores
	"\tXOR\t31,R3\n"
	"\tOR\tR3,R1\n"
// And return the results
	"\tJMP\tR0");
// }}}

void	carry_test(void);
// {{{
asm("\t.text\n\t.global\tcarry_test\n"
	"\t.type\tcarry_test,@function\n"
"carry_test:\n"
	"\tLDI\t0,R1\n"
	"\tLDI\t0,R3\n"
// First, in adding
	"\tLDI\t-1,R2\n"
	"\tADD\t1,R2\n"
	"\tOR.C\t1,R3\n"
// Then, in subtraction
	"\tSUB\t1,R2\n"
	"\tOR.C\t2,R3\n"
// From a right shift
	"\tLDI\t1,R2\n"
	"\tLSR\t1,R2\n"
	"\tOR.C\t4,R3\n"
	"\tLDI\t1,R2\n"
	"\tASR\t1,R2\n"
	"\tOR.C\t8,R3\n"
// Or from a compare
	"\tLDI\t0,R2\n"
	"\tCMP\t1,R2\n"
	"\tOR.C\t16,R3\n"
// Set our return and clean up
	"\tXOR\t31,R3\n"
	"\tOR\tR3,R1\n"
	"\tJMP\tR0");
// }}}

void	loop_test(void);
// {{{
asm("\t.text\n\t.global\tloop_test\n"
	"\t.type\tloop_test,@function\n"
"loop_test:\n"
	"\tLDI\t0,R1\n"
// Let's try a loop: for(i=0; i<5; i++)
	"\tLDI\t0,R2\n"
	"\tLDI\t0,R3\n"
	"\tCMP\t5,R2\n"
	"\tBGE\tend_for_loop_test\n"
"for_loop_test:"
	"\tADD\t1,R2\n"
	"\tADD\t1,R3\n"
	"\tCMP\t5,R2\n"
	"\tBLT\tfor_loop_test\n"
"end_for_loop_test:"
	"\tCMP\t5,R3\n"
	"\tOR.NZ\t1,R1\n"
// How about a reverse do{} while loop?  These are usually cheaper than for()
// loops.
	"\tLDI\t0,R2\n"
// What if we use >=?
	"\tLDI\t5,R3\n"
"bge_loop_test:\n"
	"\tADD\t1,R2\n"
	"\tSUB\t1,R3\n"
	"\tBGE\tbge_loop_test\n"
	"\tCMP\t6,R2\n"
	"\tOR.NZ\t4,R1\n"
// Once more with the reverse loop, this time storing the loop variable in
// memory
	"\tSUB\t4,SP\n"
	"\tLDI\t0,R2\n"
	"\tLDI\t4,R3\n"
	"\tSW\tR3,(SP)\n"
"mem_loop_test:\n"
	"\tADD\t1,R2\n"	// Keep track of the number of times loop is executed
	"\tADD\t14,R3\n"
	"\tLW\t(SP),R3\n"
	"\tSUB\t1,R3\n"
	"\tSW\tR3,(SP)\n"
	"\tBGE\tmem_loop_test\n"
	"\tCMP\t5,R2\n"
	"\tOR.NZ\t8,R1\n"
	"\tADD\t4,SP\n"
//
	"\tJMP\tR0\n");
// }}}

void	shift_test(void);
// {{{
// Test whether or not LSL, LSR, and ASR instructions work, together with their
// carry flags
asm("\t.text\n\t.global\tshift_test\n"
	"\t.type\tshift_test,@function\n"
"shift_test:\n"
	"\tLDI\t0,R1\n"	// Bit-field of tests that have failed
	"\tLDI\t0,R3\n"	// Bit-field of tests that have worked
	"\tLDI\t0,R4\n"	// Upper 16-bits of the same bit field
	"\tLDI\t0,R5\n"	// Upper 16-bits of tests that have failed
// Does shifting right by 32 result in a zero?
	"\tLDI\t-1,R2\n"
	"\tLSR\t32,R2\n"
	"\tOR.Z\t1,R3\n"
	"\tOR.C\t2,R3\n"
	"\tCMP\t0,R2\n"
	"\tOR.Z\t4,R3\n"
// Does shifting a -1 right arithmetically by 32 result in a -1?
	"\tLDI\t-1,R2\n"
	"\tASR\t32,R2\n"
	"\tOR.LT\t8,R3\n"
	"\tOR.C\t16,R3\n"
	"\tCMP\t-1,R2\n"
	"\tOR.Z\t32,R3\n"
// Does shifting a -4 right arithmetically by 2 result in a -1?
	"\tLDI\t-4,R2\n"
	"\tASR\t2,R2\n"
	"\tOR.LT\t64,R3\n"
	"\tOR.C\t128,R1\n"
	"\tOR\t128,R3\n" // Artificially declare passing, so as not to fail it
	"\tCMP\t-1,R2\n"
	"\tOR.Z\t256,R3\n"
// Does one more set the carry flag as desired?
	"\tASR\t1,R2\n"
	"\tOR.LT\t512,R3\n"
	"\tOR.C\t1024,R3\n"
	"\tCMP\t-1,R2\n"
	"\tOR.Z\t2048,R3\n"
// Does shifting -1 left by 32 result in a zero?
	"\tLDI\t-1,R2\n"
	"\tLSL\t32,R2\n"
	"\tOR.Z\t4096,R3\n"
	"\tOR.C\t8192,R3\n"	
	"\tCMP\t0,R2\n"
	"\tOR.Z\t16384,R3\n"
// How about shifting by zero?
	"\tLDI\t-1,R2\n"
	"\tASR\t0,R2\n"
	"\tOR.C\t32768,R1\n"
	"\tOR\t32768,R3\n"
	"\tCMP\t-1,R2\n"
	"\tOR.Z\t1,R4\n"
// 
	"\tLSR\t0,R2\n"
	"\tLDI\t131072,R5\n"
	"\tOR.C\tR5,R1\n"
	"\tCMP\t-1,R2\n"
	"\tOR.Z\t2,R4\n"
//
	"\tLSL\t0,R2\n"
	"\tLDI\t524288,R5\n"
	"\tOR.C\tR5,R1\n"
	"\tCMP\t-1,R2\n"
	"\tOR.Z\t4,R4\n"
// Tally up our results and return
	"\tXOR\t7,R4\n"
	"\tXOR\t65535,R3\n"
	"\tLSL\t16,R4\n"
	"\tOR\tR4,R3\n"
	"\tOR\tR3,R1\n"
	"\tJMP\tR0");
// }}}

int	sw_brev(int v);
// {{{
asm("\t.text\n\t.global\tsw_brev\n"
	"\t.type\tsw_brev,@function\n"
"sw_brev:\n"
	"\tSUB\t8,SP\n"
	"\tSW\tR2,(SP)\n"
	"\tSW\tR3,4(SP)\n"
	"\tLDI\t-1,R2\n"
	"\tCLR\tR3\n"
"sw_brev_loop:\n"
	"\tLSL\t1,R3\n"
	"\tLSR\t1,R1\n"
	"\tOR.C\t1,R3\n"
	"\tLSR\t1,R2\n"
	"\tBZ\tsw_brev_endloop\n"
	"\tBRA\tsw_brev_loop\n"
"sw_brev_endloop:\n"
	"\tMOV\tR3,R1\n"
	"\tLW\t(SP),R2\n"
	"\tLW\t4(SP),R3\n"
	"\tADD\t8,SP\n"
	"\tJMP\tR0");
// }}}

void	pipeline_stack_test(void);
// {{{
asm("\t.text\n\t.global\tpipeline_stack_test\n"
	"\t.type\tpipeline_stack_test,@function\n"
"pipeline_stack_test:\n"
	"\tSUB\t4,SP\n"
	"\tSW\tR0,(SP)\n"
	"\tLDI\t0,R0\n"
	"\tMOV\t1(R0),R1\n"
	"\tMOV\t1(R1),R2\n"
	"\tMOV\t1(R2),R3\n"
	"\tMOV\t1(R3),R4\n"
	"\tMOV\t1(R4),R5\n"
	"\tMOV\t1(R5),R6\n"
	"\tMOV\t1(R6),R7\n"
	"\tMOV\t1(R7),R8\n"
	"\tMOV\t1(R8),R9\n"
	"\tMOV\t1(R9),R10\n"
	"\tMOV\t1(R10),R11\n"
	"\tMOV\t1(R11),R12\n"
	"\tMOV\tpipeline_stack_test_component_return(PC),R0\n"
	// "\tLJMP\tpipeline_stack_test_component\n"
	"\tBRA\tpipeline_stack_test_component\n"
"pipeline_stack_test_component_return:\n"
	"\tCMP\t1,R1\n"
	"\tLDI.Z\t0,R1\n"
	"\tCMP\t2,R2\n"
	"\tCMP.Z\t3,R3\n"
	"\tCMP.Z\t4,R4\n"
	"\tCMP.Z\t5,R5\n"
	"\tCMP.Z\t6,R6\n"
	"\tCMP.Z\t7,R7\n"
	"\tCMP.Z\t8,R8\n"
	"\tCMP.Z\t9,R9\n"
	"\tCMP.Z\t10,R10\n"
	"\tCMP.Z\t11,R11\n"
	"\tCMP.Z\t12,R12\n"
	"\tBREV.NZ\t-1,R1\n"
	"\tLW\t(SP),R0\n"
	"\tADD\t4,SP\n"
	"\tJMP\tR0\n"
	);
// }}}

void	pipeline_stack_test_component(void);
// {{{
asm("\t.text\n\t.global\tpipeline_stack_test_component\n"
	"\t.type\tpipeline_stack_test_component,@function\n"
"pipeline_stack_test_component:\n"
	"\tSUB\t52,SP\n"
	"\tSW\tR0,(SP)\n"
	"\tSW\tR1,4(SP)\n"
	"\tSW\tR2,8(SP)\n"
	"\tSW\tR3,12(SP)\n"
	"\tSW\tR4,16(SP)\n"
	"\tSW\tR5,20(SP)\n"
	"\tSW\tR6,24(SP)\n"
	"\tSW\tR7,28(SP)\n"
	"\tSW\tR8,32(SP)\n"
	"\tSW\tR9,36(SP)\n"
	"\tSW\tR10,40(SP)\n"
	"\tSW\tR11,44(SP)\n"
	"\tSW\tR12,48(SP)\n"
	"\tXOR\t-1,R0\n"
	"\tXOR\t-1,R1\n"
	"\tXOR\t-1,R2\n"
	"\tXOR\t-1,R3\n"
	"\tXOR\t-1,R4\n"
	"\tXOR\t-1,R5\n"
	"\tXOR\t-1,R6\n"
	"\tXOR\t-1,R7\n"
	"\tXOR\t-1,R8\n"
	"\tXOR\t-1,R9\n"
	"\tXOR\t-1,R10\n"
	"\tXOR\t-1,R11\n"
	"\tXOR\t-1,R12\n"
	"\tLW\t(SP),R0\n"
	"\tLW\t4(SP),R1\n"
	"\tLW\t8(SP),R2\n"
	"\tLW\t12(SP),R3\n"
	"\tLW\t16(SP),R4\n"
	"\tLW\t20(SP),R5\n"
	"\tLW\t24(SP),R6\n"
	"\tLW\t28(SP),R7\n"
	"\tLW\t32(SP),R8\n"
	"\tLW\t36(SP),R9\n"
	"\tLW\t40(SP),R10\n"
	"\tLW\t44(SP),R11\n"
	"\tLW\t48(SP),R12\n"
	"\tADD\t52,SP\n"
	"\tJMP\tR0\n");
// }}}

void	mpy_test(void);
// {{{
asm("\t.text\n\t.global\tmpy_test\n"
	"\t.type\tmpy_test,@function\n"
"mpy_test:\n"
	"\tCLR\tR1\n"
	// First test: let's count multiples of 137
	"\tLDI\t137,R2\n"	// What we're doing multiples of
	"\tCLR\tR3\n"		// Our accumulator via addition
	"\tCLR\tR4\n"		// Our index for multiplication
	"mpy_137_test_loop:\n"
	"\tMOV\tR2,R5\n"
	"\tMPY\tR4,R5\n"
	"\tCMP\tR3,R5\n"
	"\tBNZ\tend_mpy_137_test_loop_failed\n"
	// Let's try negative while we are at it
	"\tMOV\tR2,R6\n"
	"\tNEG\tR6\n"
	"\tMPY\tR4,R6\n"
	"\tNEG\tR6\n"
	"\tCMP\tR3,R6\n"
	"\tBNZ\tend_mpy_137_test_loop_failed\n"
	"\tCLR\tR6\n"
	"\tTEST\t0xffff0000,R3\n"
	"\tBNZ\tend_mpy_137_test_loop\n"
	"\tADD\tR2,R3\n"
	"\tADD\t1,R4\n"
	"\tBRA\tmpy_137_test_loop\n"
"end_mpy_137_test_loop_failed:\n"
	"\tOR\t1,R1\n"
"end_mpy_137_test_loop:\n"
	// Second test ... whatever that might be
	"\tJMP\tR0\n");
// }}}

unsigned	soft_mpyuhi(unsigned, unsigned);
int		soft_mpyshi(int,int);

unsigned	hard_mpyuhi(unsigned, unsigned);
// {{{
asm("\t.text\n\t.global\thard_mpyuhi\n"
	"\t.type\thard_mpyuhi,@function\n"
"hard_mpyuhi:\n"
	"\tMPYUHI\tR2,R1\n"
	"\tRETN\n");
// }}}

int	hard_mpyshi(int, int);
// {{{
asm("\t.text\n\t.global\thard_mpyshi\n"
	"\t.type\thard_mpyshi,@function\n"
"hard_mpyshi:\n"
	"\tMPYSHI\tR2,R1\n"
	"\tRETN\n");
// }}}

void	debugmpy(char *str, int a, int b, int s, int r) {
	// {{{
#ifdef	HAVE_SCOPE
	// Trigger the scope, if it hasn't been triggered yet
	// but ... dont reset it if it has been.
	SCOPEc = TRIGGER_SCOPE_NOW;
#endif
	txstr("\r\n"); txstr(str); txhex(a);
	txstr(" x "); txhex(b);
	txstr(" = "); txhex(s);
	txstr("(Soft) = "); txhex(r);
	txstr("(Hard)\r\n");
}
// }}}

int	mpyhi_test(void) {
	// {{{
	int	a = 0xf97e27ab, b = 0;

	while(b<0x6fffffff) {
		int	r, sr;

		sr = soft_mpyuhi(a, b);
		r = hard_mpyuhi(a,b);
		if (r != sr) {
			debugmpy("MPYUHI: ", a,b,sr,r);
			return 1;
		}

		sr = soft_mpyshi(a, b);
		r = hard_mpyshi(a,b);
		if (r != sr) {
			debugmpy("MPYSHI: ", a,b,sr,r);
			return 2;
		}

		sr = soft_mpyshi(-a, b);
		r = hard_mpyshi(-a,b);
		if (r != sr) {
			debugmpy("MPYSHI-NEG: ", -a,b,sr,r);
			return 3;
		}

		b += 0x197e2*7;
	}

	return 0;
}
// }}}

unsigned	soft_mpyuhi(unsigned a, unsigned b) {
	// {{{
	unsigned	alo, ahi;
	unsigned	rhi, rlhi, rllo;

	alo = (a     & 0x0ffff);
	ahi = (a>>16)& 0x0ffff;

	rhi = 0;
	rlhi = 0;
	rllo = 0;

	for(int i=0; i<16; i++) {
		if (b&(1<<i)) {
			unsigned slo, shi, sup;
			slo = (alo << i);
			shi = (ahi << i);
			shi |= (slo>>16) & 0x0ffff;
			slo &= 0x0ffff;
			sup = (shi>>16)&0x0ffff;
			shi &= 0x0ffff;

			rhi  += sup;
			rlhi += shi;
			rllo += slo;

			rlhi += (rllo >> 16)&0x0ffff;
			rllo &= 0x0ffff;

			rhi  += (rlhi >> 16)&0x0ffff;
			rlhi &= 0x0ffff;
		}
	}

	for(int i=16; i<32; i++) {
		if (b&(1<<i)) {
			unsigned slo, shi, sup;
			slo = (alo << (i-16));
			shi = (ahi << (i-16));
			shi |= (slo>>16) & 0x0ffff;
			slo &= 0x0ffff;
			sup = (shi>>16)&0x0ffff;
			shi &= 0x0ffff;

			rhi  += sup << 16;
			rhi  += shi;
			rlhi += slo;

			rhi  += (rlhi >> 16)&0x0ffff;
			rlhi &= 0x0ffff;
		}
	}

	return rhi;
}
// }}}

int	soft_mpyshi(int a, int b) {
	// {{{
	unsigned	sgn, r, p;

	sgn = ((a^b)>>31)&0x01;

	if (a<0)	a = -a;
	if (b<0)	b = -b;

	p = a * b;

	// This will only fail if the lower 32-bits of of a*b are 0,
	// at which point our following negation won't capture the carry it
	// needs.
	r = soft_mpyuhi(a, b);

	r = (sgn)?(r^-1):r;
	if ((sgn)&&(p==0))
		r += 1;
	return r;
}
// }}}

int	divu_test(void);
// {{{
asm("\t.text\n\t.global\tdivu_test\n"
	"\t.type\tdivu_test,@function\n"
"divu_test:\n"
	"\tLDI\t0x4881a7,R4\n"
	"\tLDI\t0x2d5108b,R2\n"
	"\tLDI\t10,R3\n"
	"\tDIVU\tR3,R2\n"	// R3 = 0x2d5108b /= 10
	"\tCMP\tR4,R2\n"	// Compare DIVU result to 0x4881a7
	"\tLDILO.NZ\t1,R1\n"
	"\tRETN.NZ\n"
	"\tLDI\t0x2d5108b,R2\n"
	"\tDIVU\t10,R2\n"	// R2 = 0x2d5108b /= 10
	"\tCMP\tR4,R2\n"	// Compare R2 to 0x4881a7
	"\tLDILO.NZ\t1,R1\n"
	"\tRETN\n");
// }}}

int	divs_test(void);
// {{{
asm("\t.text\n\t.global\tdivs_test\n"
	"\t.type\tdivs_test,@function\n"
"divs_test:\n"
	"\tLDI\t-26,R4\n"	// Expected result
	"\tLDI\t131,R2\n"
	"\tLDI\t-5,R3\n"
	"\tDIVS\tR3,R2\n"	// 131 / -5
	"\tCMP\tR4,R2\n"
	"\tLDILO.NZ\t1,R1\n"
	"\tRETN.NZ\n"
	// 0x2653 * 0x098953d = 0x16d79_f70c7
	// -883 * -999671 = -882709493
	// 
	"\tLDI\t883,R2\n"	// R2 = A
	"\tLDI\t999671,R3\n"	// R3 = B
	"\tMOV\tR3,R4\n"	
	"\tMPY\tR2,R4\n"	// R4 = A*B
	//
	"\tMOV\tR4,R5\n"	// R5 = R4 = A*B
	"\tDIVS\tR2,R5\n"	// R5 = A * B / A
	"\tCMP\tR3,R5\n"
	"\tLDILO.NZ\t3,R1\n"
	"\tRETN.NZ\n"
	//
	//	-(A*B) / B
	"\tMOV\tR4,R5\n"	// R5 =  R4 = A*B
	"\tNEG\tR5\n"		// R5 = -R4 = -A*B
	"\tMOV\tR3,R6\n"	// R6 = B
	"\tNEG\tR6\n"		// R6 = -B
	"\tDIVS\tR2,R5\n"	// R5 = A * B / A
	"\tCMP\tR6,R5\n"
	"\tLDILO.NZ\t5,R1\n"
	"\tRETN.NZ\n"
	//
	//	-(A*B) / -B
	"\tMOV\tR4,R5\n"	// R5 =  R4 = A*B
	"\tNEG\tR5\n"		// R5 = -R4 = -A*B
	"\tMOV\tR2,R6\n"	// R6 = B
	"\tNEG\tR6\n"		// R6 = -B
	"\tDIVS\tR6,R5\n"	// R5 = A * B / A
	"\tCMP\tR3,R5\n"
	"\tLDILO.NZ\t7,R1\n"
	// "\tRETN.NZ\n"
	//
	"\tRETN\n");
// }}}

void	pipeline_test(void);
// {{{
//pipeline_test -- used to be called pipeline memory race conditions
asm("\t.text\n\t.global\tpipeline_test\n"
	"\t.type\tpipeline_test,@function\n"
"pipeline_test:\n"
	"\tSUB\t12,SP\n"
	// Test setup
	"\tLDI\t275,R2\n"
	"\tSW\tR2,4(SP)\n"
	"\tMOV\t4(SP),R2\n"
	"\tSW\tR2,(SP)\n"
	"\tCLR\tR2\n"
	//
	"\tMOV\tSP,R2\n"
	"\tLW\t(R2),R2\n"
	"\tLW\t(R2),R2\n"
	"\tCMP\t275,R2\n"
	"\tOR.NZ\t1,R1\n"
	//
	"\tMOV\tSP,R2\n"
	// Here's the test sequence
	"\tLW\t(R2),R3\n"
	"\tLW\t4(R2),R4\n"
	"\tSW\tR4,4(R3)\n"
	// Make sure we clear the load pipeline
	"\tLW\t(R2),R3\n"
	// Load our written value
	"\tLW\t8(R2),R4\n"
	"\tCMP\t275,R4\n"
	"\tOR.NZ\t2,R1\n"
	//
	//
	// Next (once upon a time) failing sequence:
	//	LOD -x(R12),R0
	//	LOD y(R0),R0
	"\tMOV\tSP,R2\n"
	"\tMOV\t4(R2),R3\n"
	"\tSW\tR3,4(R2)\n"
	"\tLDI\t3588,R4\n"	// Just some random value
	"\tSW\tR4,8(R2)\n"
	"\tMOV\tR2,R3\n"
	// Here's the test sequence
	"\tLW\t(R2),R3\n"
	"\tLW\t4(R3),R3\n"
	"\tCMP\tR4,R3\n"
	"\tOR.NZ\t4,R1\n"
	//
	"\tADD\t12,SP\n"
	"\tJMP\tR0\n");
// }}}

void	mempipe_test(void);
// {{{
//mempipe_test
asm("\t.text\n\t.global\tmempipe_test\n"
	"\t.type\tmempipe_test,@function\n"
"mempipe_test:\n"
	"\tSUB\t16,SP\n"
	"\tSW\tR0,(SP)\n"
	"\tLDI\t0x1000,R11\n"
	// Test #1 ... Let's start by writing a value to memory
	"\tLDI\t-1,R2\n"
	"\tCLR\tR3\n"
	"\tSW\tR2,8(SP)\n"
	"\tLW\t8(SP),R3\n"
	"\tCMP\tR3,R2\n"
	"\tOR.NZ\t1,R1\n"
	// Test #2, reading and then writing a value from memory
	"\tNOOP\n"
	"\tNOOP\n"
	"\tCLR\tR2\n"
	"\tCLR\tR3\n"
	"\tLW\t8(SP),R2\n"	// This should load back up our -1 value
	"\tSW\tR2,12(SP)\n"
	// Insist that the pipeline clear
	"\tLW\t8(SP),R2\n"
	// Now let's try loading into R3
	"\tNOOP\n"
	"\tNOOP\n"
	"\tNOOP\n"
	"\tNOOP\n"
	"\tLW\t12(SP),R3\n"
	"\tCMP\tR3,R2\n"
	"\tOR.NZ\t2,R1\n"
	//
	"\tLW\t(SP),R0\n"
	"\tADD\t16,SP\n"
	"\tJMP\tR0\n");
// }}}

void	cexec_test(void);
// {{{
//cexec_test
asm("\t.text\n\t.global\tcexec_test\n"
	"\t.type\tcexec_test,@function\n"
"cexec_test:\n"
	"\tSUB\t4,SP\n"
	"\tSW\tR0,(SP)\n"
	//
	"\tXOR\tR2,R2\n"
	"\tADD.Z\t1,R2\n"
	"\tADD.NZ\t1,R1\n"
	"\tCMP.Z\t0,R2\n"
	"\tOR.Z\t2,R1\n"
	//
	"\tLW\t(SP),R0\n"
	"\tADD\t4,SP\n"
	"\tJMP\tR0\n");
// }}}

void	nowaitpipe_test(void);
// {{{
// Pipeline stalls have been hideous problems for me.  The CPU has been modified
// with special logic to keep stages from stalling.  For the most part, this
// means that ALU and memory results may be accessed either before or as they
// are written to the register file.  This set of code is designed to test
// whether this bypass logic works.
//
asm("\t.text\n\t.global\tnowaitpipe_test\n"
	"\t.type\tnowaitpipe_test,@function\n"
"nowaitpipe_test:\n"
	"\tSUB\t8,SP\n"
	//
	// Let's start with ALU-ALU testing
	//	AA: result->input A
	"\tLDI\t-1,R2\n"
	"\tCLR\tR2\n"
	"\tADD\t1,R2\n"
	"\tCMP\t1,R2\n"
	"\tOR.NZ\t1,R1\n"
	//
	//	AA: result -> input B
	"\tCLR\tR2\n"
	"\tCLR\tR3\n"
	"\tADD\t1,R2\n"
	"\tCMP\tR2,R3\n"
	"\tOR.Z\t2,R1\n"
	//	AA: result -> input A on condition
	"\tXOR\tR2,R2\n"
	"\tADD.Z\t5,R2\n"
	"\tCMP\t5,R2\n"
	"\tOR.NZ\t4,R1\n"
	//	AA: result -> input B on condition
	"\tCLR\tR2\n"
	"\tXOR\tR3,R3\n"
	"\tADD.Z\t5,R2\n"
	"\tCMP\tR2,R3\n"
	"\tOR.Z\t8,R1\n"
	//	AA: result->input B plus offset
	"\tCLR\tR2\n"
	"\tXOR\tR3,R3\n"
	"\tADD\t5,R2\n"
	"\tCMP\t-5(R2),R3\n"
	"\tOR.NZ\t16,R1\n"
	//	AA: result->input B plus offset on condition
	"\tCLR\tR2\n"
	"\tXOR\tR3,R3\n"
	"\tADD.Z\t5,R2\n"
	"\tCMP\t-5(R2),R3\n"
	"\tOR.NZ\t32,R1\n"
	//
	// Then we need to do the ALU-MEM input testing
	//
	"\tCLR\tR2\n"
	"\tSW\tR2,4(SP)\n"
	"\tLDI\t8352,R2\n"
	"\tLW\t4(SP),R2\n"
	"\tTST\t-1,R2\n"
	"\tOR.NZ\t64,R1\n"
	// Let's try again, this time with something that's not zero
	"\tLDI\t937,R2\n"
	"\tSW\tR2,4(SP)\n"
	"\tNOOP\n"
	"\tLW\t4(SP),R2\n"
	"\tCMP\t938,R2\n"
	"\tOR.GE\t128,R1\n"
	"\tCMP\t936,R2\n"
	"\tOR.LT\t256,R1\n"
	// Mem output->ALU input testing
	//	Okay, we just did that as part of our last test
	// Mem output->mem input testing
	"\tLDI\t5328,R2\n"
	"\tLW\t4(SP),R2\n"
	"\tSW\tR2,4(SP)\n"
	"\tLW\t4(SP),R3\n"
	"\tCMP\t937,R3\n"
	"\tOR.NZ\t512,R1\n"
	//
	"\tADD\t8,SP\n"
	"\tJMP\tR0\n");
// }}}

void	bcmem_test(void);
// {{{
asm("\t.text\n\t.global\tbcmem_test\n"
	"\t.type\tbcmem_test,@function\n"
"bcmem_test:\n"
	"\tSUB\t4,SP\n"
	"\tCLR\tR1\n"
	"\tCLR\tR2\n"
	"\tLDI\t-1,R3\n"
	"\tLDI\t0x13000,R4\n"
	"\tSW\tR2,(SP)\n"
	"\tLW\t(SP),R3\n"
	"\tCMP\tR2,R3\n"
	"\tOR.NZ\t1,R1\n"
	"\tCMP\t0x13000,R4\n"
	"\tBZ\tbcmem_test_cmploc_1\n"
	"\tSW\tR4,(SP)\n"
"bcmem_test_cmploc_1:\n"
	"\tLW\t(SP),R2\n"
	"\tCMP\tR2,R4\n"
	"\tOR.Z\t2,R1\n"
	"\tCLR\tR2\n"
	"\tCMP\tR2,R4\n"
	"\tBZ\tbcmem_test_cmploc_2\n"
	"\tSW.NZ\tR4,(SP)\n"
"bcmem_test_cmploc_2:\n"
	"\tLW\t(SP),R2\n"
	"\tCMP\tR2,R4\n"
	"\tOR.NZ\t4,R1\n"
//
	"\tADD\t4,SP\n"
	"\tJMP\tR0\n");
// }}}

void	membyte_test(void);
// {{{
unsigned	memword;

asm("\t.text\n\t.global\tmembyte_test\n"
	"\t.type\tmembyte_test,@function\n"
"membyte_test:\n"
	"\tCLR\tR1\n"		// Return result
	"\tLDI\tmemword,R2\n"	// Data pointer
	"\tMOV\tR2,R3\n"	// Byte pointer
	"\tCLR\tR4\n"		// Zero word
	"\tCLR\tR6\n"		// Memory return value
"membyte_addr:\n"
	"\tCLR\tR5\n"		// Clear the Loop index
"membyte_loop:\n"
	"\tSW\tR4,(R2)\n"	// Clear the full word
	"\tSB\tR5,(R3)\n"	// Store a byte
	"\tLB\t(R3),R6\n"	// Read the byte back
	"\tCMP\tR5,R6\n"
	"\tBNZ\tmembyte_fail\n"
	"\tADD\t1,R5\n"
	"\tTEST\t0x0100,R5\n"	// This will force a signedness test as well
	"\tBZ\tmembyte_loop\n"
	//
	"\tADD\t1,R3\n"
	"\tMOV\tR3,R6\n"
	"\tTEST\t3,R6\n"
	"\tBNZ\tmembyte_addr\n"
	"\tRTN\n"
"membyte_fail:\n"
	"\tLDI\t1,R1\n"
	"\tRTN\n");
// }}}

void	memhalf_test(void);
// {{{
asm("\t.text\n\t.global\tmemhalf_test\n"
	"\t.type\tmemhalf_test,@function\n"
"memhalf_test:\n"
	"\tCLR\tR1\n"		// Return result
	"\tLDI\tmemword,R2\n"	// Data pointer
	"\tMOV\tR2,R3\n"	// Byte pointer
	"\tCLR\tR4\n"		// Zero word
	"\tCLR\tR6\n"		// Memory return value
"memhalf_addr:\n"
	"\tCLR\tR5\n"		// Loop index
"memhalf_loop:\n"
	"\tSW\tR4,(R2)\n"	// Clear the full word
	"\tSH\tR5,(R3)\n"	// Store a half-word
	"\tLH\t(R3),R6\n"	// Read the half-word back
	"\tXOR\tR5,R6\n"
	"\tBNZ\tmemhalf_fail\n"
	"\tADD\t5,R5\n"
	"\tTEST\t0x010000,R5\n"	//
	"\tBZ\tmemhalf_loop\n"
	//
	"\tADD\t2,R3\n"
	"\tMOV\tR3,R6\n"
	"\tTEST\t3,R6\n"
	"\tBNZ\tmemhalf_addr\n"
	"\tRTN\n"
"memhalf_fail:\n"
	"\tLDI\t1,R1\n"
	"\tRTN\n");
// }}}

void	ill_test(void);
// {{{
// The illegal instruction test.  Specifically, illegal instructions cannot be
// allowed to execute.  The PC must, upon completion, point to the illegal
// instruction that caused the exception.
//
// To create our illegal instruction, we assume that the only the three
// operations without arguments are NOOP, BREAK, LOCK, and so we envision a
// fourth instruction to create.
asm("\t.text\n\t.global\till_test\n"
	"\t.type\till_test,@function\n"
"ill_test:\n"	// 0.111_1.110_11......
	"\t.int\t0x7ec00000\n"
	"\tJMP\tR0\n");
// }}}

void	sim_test(void);
// {{{
// Are sim instructions considered valid?  Just hit the illegal instruction
// so we can report the result
asm("\t.text\n\t.global\tsim_test\n"
	"\t.type\tsim_test,@function\n"
"sim_test:\n"	// 0.111_1.111_10......
	"\t.int\t0x7f800000\n"
	"\tJMP\tR0\n");
// }}}

void	cis_test(void);
// {{{
// Are CIS (Compound Instruction Set) instructions considered valid?  Try two
// compare instructions to see if CIS instruction support is built into our CPU.
asm("\t.text\n\t.global\tcis_test\n"
	"\t.type\tcis_test,@function\n"
"cis_test:\n"	// 1.000_0.011._1.101_0.000 ... 1.000_1.011._1.110_0.000
	"\t.int\t0x83d08be0\n"
	"\tJMP\tR0\n");
// }}}

void	cmpeq_test(void);
// {{{
asm("\t.text\n\t.global\tcmpeq_test\n"
	"\t.type\tcmpeq_test,@function\n"
"cmpeq_test:\n"
	"\tCMP\tR1,R2\n"
	"\tCMP.Z\tR3,R4\n"
	"\tLDILO.NZ\t1,R1\n"
	"\tJMP\tR0\n");
// }}}

void	cmpneq_test(void);
// {{{
asm("\t.text\n\t.global\tcmpneq_test\n"
	"\t.type\tcmpneq_test,@function\n"
"cmpneq_test:\n"
	"\tLDI\t1,R4\n"
	"\tCMP\tR1,R2\n"
	"\tCMP.Z\tR3,R4\n"
	"\tLDILO.Z\t1,R0\n"
	"\tJMP\tR0\n");
// }}}

void	ccreg_test(void);
// {{{
// The CC register has some ... unique requirements associated with it.
// Particularly, flags are unavailable until after an ALU operation completes,
// and they can't really be bypassed for the CC register.  After writeback,
// the "new" CC register isn't really available for another clock.  Trying to
// bypass this extra clock can have problems, since ... some bits are fixed,
// some bits can only be changed by the supervisor, and others can/will change
// and even have effects--like sending the CPU to supervisor mode or
// alternatively to sleep.
//
// Here, let's see if our pipeline can successfully navigate any of these
// issues.
//
asm("\t.text\n\t.global\tccreg_test\n"
	"\t.type\tccreg_test,@function\n"
"ccreg_test:\n"
	// First test: If we try to change the fixed bits, will they change
	// because the pipeline tries to bypass the write-back stage
	"\tCLR\tR1\n"	// We'll start with an "answer" of success
	"\tMOV\tCC,R2\n"
	"\tMOV\tR2,R4\n"	// Keep a copy
	"\tBREV\t0x0ff,R3\n"	// Attempt to change the top fixed bits
	"\tXOR\tR3,R2\n"	// Arrange for the changes
	"\tMOV\tR2,CC\n"	// Set the changes (they won't take)
	"\tMOV\tCC,R5\n"	// See if the pipeline makes them take
	"\tXOR\tR4,R5\n"	// Let's look for anything that has changed
	"\tOR.NZ\t1,R1\n"	// If anything has changed, then we fail the tst
	// 
	// Test #2: Can we set the flags?
	"\tMOV\tCC,R6\n"
	"\tOR\t15,R6\n"
	"\tMOV\tR6,CC\n"
	"\tMOV\tCC,R7\n"
	"\tAND\t15,R7\n"
	"\tCMP\t15,R7\n"
	"\tOR.NZ\t2,R1\n"
	//
	// Test #3: How about setting specific flags, and immediately acting
	// on them?
	"\tXOR\t1+R8,R8\n"	// Turn off the Z bit
	"\tOR\t1,CC\n"		// Turn on the Z bit
	"\tOR.NZ\t4,R1\n"
	//
	// Test #4: Can we load the CC plus a value into a register?
	//	I don't think so ...
	"\tJMP\tR0\n");
// }}}

__attribute__((noinline))
int	multiarg_subroutine(int a, int b, int c, int d, int e, int f, int g) {
// {{{
// Multiple argument test
	if (a!=0)	return 1;
	if (b!=1)	return 2;
	if (c!=2)	return 4;
	if (d!=3)	return 8;
	if (e!=4)	return 16;
	if (f!=5)	return 32;
	if (g!=6)	return 64;
	return 0;
}
// }}}

int	multiarg_test(void) {
	// {{{
	return multiarg_subroutine(0,1,2,3,4,5,6);
}
// }}}

int	step_alu_test(void);
// {{{
asm("\t.text\n\t.global\tstep_mpy_test\n"
	"\t.type\tstep_alu_test,@function\n"
"step_alu_test:\n"
	"\tXOR	R1,R0\n"
	"\tBREAK\n"
);
// }}}

int	step_cis_test(void);
// {{{
asm("\t.text\n\t.global\tstep_cis_test\n"
	"\t.type\tstep_cis_test,@function\n"
"step_cis_test:\n"
	"\tADD	1,R1\n"
	"\tADD	1,R2\n"
	"\tBREAK\n"
);
// }}}

int	step_break_test(void);
// {{{
asm("\t.text\n\t.global\tstep_break_test\n"
	"\t.type\tstep_break_test,@function\n"
"step_break_test:\n"
	"\tBREAK\n"
	"\tSW	R1,(R1)\n"	// Should generate a bus error, if ever executed
);
// }}}

int	step_mpy_test(void);
// {{{
asm("\t.text\n\t.global\tstep_mpy_test\n"
	"\t.type\tstep_mpy_test,@function\n"
"step_mpy_test:\n"
	"\tMPY	R6,R7\n"
	"\tBREAK\n"
);
// }}}

int	step_div_test(void);
// {{{
asm("\t.text\n\t.global\tstep_div_test\n"
	"\t.type\tstep_div_test,@function\n"
"step_div_test:\n"
	"\tDIVU	R6,R5\n"
	"\tBREAK\n"
);
// }}}

int	step_diverr_test(void);
// {{{
asm("\t.text\n\t.global\tstep_diverr_test\n"
	"\t.type\tstep_diverr_test,@function\n"
"step_diverr_test:\n"
	"\tDIVU	R0,R5\n"
	"\tBREAK\n"
);
// }}}

int	step_lod_test(void);
// {{{
asm("\t.text\n\t.global\tstep_lod_test\n"
	"\t.type\tstep_lod_test,@function\n"
"step_lod_test:\n"
	"\tLW	(R4),R0\n"
	"\tBREAK\n"
);
// }}}

int	step_sto_test(void);
// {{{
asm("\t.text\n\t.global\tstep_sto_test\n"
	"\t.type\tstep_sto_test,@function\n"
"step_sto_test:\n"
	"\tSW	R0,(R4)\n"
	"\tBREAK\n"
);
// }}}

int	step_loderr_test(void);
// {{{
asm("\t.text\n\t.global\tstep_loderr_test\n"
	"\t.type\tstep_loderr_test,@function\n"
"step_loderr_test:\n"
	"\tLW	(R1),R0\n"
	"\tBREAK\n"
);
// }}}

int	step_stoerr_test(void);
// {{{
asm("\t.text\n\t.global\tstep_stoerr_test\n"
	"\t.type\tstep_stoerr_test,@function\n"
"step_stoerr_test:\n"
	"\tSW	R0,(R1)\n"
	"\tBREAK\n"
);
// }}}

int	step_word = 0;

int	smp_count(void);
// {{{
asm("\t.text\n\t.global\tsmp_count\n"
	"\t.type\tsmp_count,@function\n"
"smp_count:\n"
	"\tCLR	R1\n"
	// "\tLDI	_smp,R2\n"
	"\tLDI	50332160,R2\n"
"smp_count_loop:\n"
	"\tLW	(R2),R3\n"
	"\tADD	1,R1\n"
	"\tADD	512,R2\n"
	"\tJMP	smp_count_loop\n"
);
// }}}

extern	int	step_test(void *pc, void *stack);
// {{{
asm("\t.text\n\t.global\tstep_test\n"
	"\t.type\tstep_test,@function\n"
"step_test:\n"
	"\tCLR\tR3\n"
	"\tMOV\tR3,uR0\n"
	"\tMOV\tR3,uR1\n"
	"\tMOV\tR3,uR2\n"
	"\tMOV\tR3,uR3\n"
	"\tMOV\tR3,uR5\n"
	"\tMOV\tR3,uR6\n"
	"\tMOV\tR3,uR7\n"
	"\tMOV\tR3,uR8\n"
	"\tMOV\tR3,uR9\n"
	"\tMOV\tR3,uR10\n"
	"\tMOV\tR3,uR11\n"
	"\tMOV\tR3,uR12\n"
	// Put a some useful multiply values into uR5, uR6, and uR7
	// (Implied) CLR R3
	"\tMOV\t15+R3,uR5\n"	// uR5 = 15
	"\tMOV\t5+R3,uR6\n"	// uR6 = 5
	"\tMOV\t3+R3,uR7\n"	// uR7 = 3
	//
	// Put a valid address into uR4
	"\tLDI\tstep_word,R3\n"
	"\tMOV\tR3,uR4\n"
	//
	"\tMOV\tR2,uSP\n"	// uSP = stack
	"\tLDI\t0x60,R3\n"
	"\tMOV\tR3,uCC\n"	// Set the STEP ang GIE bits of uCC
	"\tMOV\tR1,uPC\n"	// uPC = pc
	"\tRTU\n"
	// Return from running "a single" instruction
	"\tLDI\t0,R1\n"
	// If we step more or less than one word, it's an error
	"\tMOV\tuPC,R3\n"
	"\tSUB\tR1,R3\n"
	"\tCMP\t4,R3\n"
	"\tLDI.NZ\t1,R3\n"
	// If we hit break, it's an error
	"\tMOV\tuCC,R2\n"
	"\tTEST\t0x80,R2\n"
	"\tOR.NZ\t2,R1\n"
	//
	"\tRTN\n");
// }}}

__attribute__((noinline))
void	wait(unsigned int msk) {
	// {{{
	PIC = 0x7fff0000|msk;
	asm("MOV\tidle_task(PC),uPC\n");
	PIC = 0x80000000|(msk<<16);
	asm("WAIT\n");
	PIC = 0; // Turn interrupts back off, lest they confuse the test
}
// }}}

asm("\n\t.text\nidle_task:\n\tWAIT\n\tBRA\tidle_task\n");

__attribute__((noinline))
void	txchr(char v) {
	// {{{
	while(TXBUSY)
		;
	uint8_t c = v;
	_uart->u_tx = (unsigned)c;
}
// }}}

void	wait_for_uart_idle(void) {
	// {{{
	while(TXBUSY)	// While the transmitter is non-idle
		;
}
// }}}

__attribute__((noinline))
void	txstr(const char *str) {
	// {{{
	const char *ptr = str;
	while(*ptr)
		txchr(*ptr++);
}
// }}}

__attribute__((noinline))
void	txhex(int num) {
	// {{{
	for(int ds=28; ds>=0; ds-=4) {
		int	ch;
		ch = (num >> ds)&0x0f;
		if (ch >= 10)
			ch = 'A'+ch-10;
		else
			ch += '0';
		txchr(ch);
	}
}
// }}}

__attribute__((noinline))
void	tx4hex(int num) {
	// {{{
	if (num & 0xffff0000){
		txhex(num);
		return;
	} for(int ds=12; ds>=0; ds-=4) {
		int	ch;
		ch = (num >> ds)&0x0f;
		if (ch >= 10)
			ch = 'A'+ch-10;
		else
			ch += '0';
		txchr(ch);
	}
}
// }}}

__attribute__((noinline))
void	txreg(const char *name, int val) {
	// {{{
	txstr(name);	// 4 characters
	txstr("0x");	// 2 characters
	txhex(val);	// 8 characters
	txstr("    ");	// 4 characters
}
// }}}

void	txunsigned(unsigned uv) {
	// {{{
	unsigned	i, d;
	char		str[32];

	if (uv == 0)
		txchr('0');
	else {
		for(i=0; i<31 && (d = (uv % 10)); i++) {
			str[i] = '0'+d;
			uv /= 10;
		} for(d=0; d<i; d++)
			txchr(str[i-d-1]);
	}
}
// }}}

void	txdecimal(int val) {
	// {{{
	if (val < 0) {
		txchr('-');
		txunsigned((unsigned)-val);
	} else
		txunsigned((unsigned)val);
}
// }}}

__attribute__((noinline))
void	save_context(int *context) {
	// {{{
	zip_save_context(context);
}
// }}}

__attribute__((noinline))
void	test_fails(int start_time, int *listno) {
	// {{{
	int	context[16], stop_time;

	// Trigger the scope, if it hasn't already triggered.  Otherwise,
	// if it has triggered, don't clear it.
#ifdef	HAVE_SCOPE
	SCOPEc = TRIGGER_SCOPE_NOW;
#endif

	MARKSTOP;
	save_context(context);
#ifdef	HAVE_COUNTER
	*listno   = stop_time;
#endif

	txstr("FAIL!\r\n\r\n");
	txstr("Between 0x"); txhex(start_time);
		txstr(" and 0x"); txhex(stop_time); txstr("\r\n\r\n");
	txstr("Core-dump:\r\n");
	txreg("uR0 : ", context[0]);
	txreg("uR1 : ", context[1]);
	txreg("uR2 : ", context[2]);
	txreg("uR3 : ", context[3]);
	txstr("\r\n");

	txreg("uR4 : ", context[4]);
	txreg("uR5 : ", context[5]);
	txreg("uR6 : ", context[6]);
	txreg("uR7 : ", context[7]);
	txstr("\r\n");

	txreg("uR8 : ", context[8]);
	txreg("uR9 : ", context[9]);
	txreg("uR10: ", context[10]);
	txreg("uR11: ", context[11]);
	txstr("\r\n");

	txreg("uR12: ", context[12]);
	txreg("uSP : ", context[13]);
	txreg("uCC : ", context[14]);
	txreg("uPC : ", context[15]);
	txstr("\r\n\r\n");

	wait_for_uart_idle();
	asm("NEXIT -1");
	// While previous versions of cputest.c called zip_busy(), here we
	// reject that notion for the simple reason that zip_busy may not
	// necessarily halt any Verilator simulation.  Instead, we try to 
	// halt the CPU.
	while(1)
		zip_halt();
}
// }}}

void	testid(const char *str) {
	// {{{
	const int	WIDTH=32;
	txstr(str);
	const char *ptr = str;
	int	i = 0;
	while(0 != *ptr++)
		i++;
	i = WIDTH-i;
	while(i-- > 0)
		txchr(' ');
}
// }}}

#define	MAXTESTS	40
int	testlist[MAXTESTS];

void entry(void) {
	int		context[16];
	int		user_stack[256], *user_stack_ptr = &user_stack[256];
	int		start_time, i;
	int		cc_fail, cis_insns = 0;
	unsigned	cc;


	for(i=0; i<MAXTESTS; i++)
		testlist[i] = -1;

#ifdef	TIMER
	TIMER = 0x7fffffff;
#endif
#ifdef	COUNTER
	COUNTER = 0;
#endif
#ifdef	HAVE_SCOPE
	SCOPEc = PREPARE_SCOPE;
#endif

	// UART_CTRL = 82;	// 1MBaud, given n 82.5MHz clock
	// UART_CTRL = 705; // 115200 Baud, given n 81.25MHz clock
	// *UART_CTRL = 8333; // 9600 Baud, 8-bit chars, no parity, one stop bit
	// *UART_CTRL = 25; // 9600 Baud, 8-bit chars, no parity, one stop bit
	//

	txstr("\r\n");
	txstr("Running CPU self-test\r\n");
	txstr("-----------------------------------\r\n");

	int	tnum = 0;

	// Check whether or not this CPU correctly identifies SIM instructions
	// as illegal instructions
	testid("SIM Instructions"); MARKSTART;
	cc_fail = CC_MMUERR|CC_FPUERR|CC_DIVERR|CC_BUSERR|CC_STEP|CC_SLEEP;
	if ((run_test(sim_test, user_stack_ptr))||(zip_ucc()&cc_fail))
		test_fails(start_time, &testlist[tnum]);
	else if (zip_ucc() & CC_ILL) {
		txstr("Pass\r\n"); testlist[tnum++] = 0; // 0
	} else
		txstr("Is this a simulator?\r\n");

	testid("CIS Instructions"); MARKSTART;
	cc_fail = CC_MMUERR|CC_FPUERR|CC_DIVERR|CC_BUSERR|CC_STEP|CC_SLEEP;
	if ((run_test(cis_test, user_stack_ptr))||(zip_ucc()&cc_fail))
		test_fails(start_time, &testlist[tnum]);
	else if (zip_ucc() & CC_ILL)
		txstr("Not supported\r\n");
	else {
		txstr("Supported\r\n");
		cis_insns = 1;
	}

	// Break instructions
	// {{{
	// Test break instruction in user mode
	// Make sure the break works as designed
	testid("Break test #1"); MARKSTART;

	cc_fail = CC_MMUERR|CC_FPUERR|CC_DIVERR|CC_BUSERR|CC_TRAP|CC_ILL|CC_STEP|CC_SLEEP;
	if ((run_test(break_one, user_stack_ptr))||(zip_ucc()&cc_fail))
		test_fails(start_time, &testlist[tnum]);
	save_context(context);
	if ((context[15] != (int)break_one+4)||(0==(zip_ucc()&CC_BREAK)))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #1


	// Test break instruction in user mode
	// Make sure that a decision on the clock prior won't still cause a 
	// break condition
	cc_fail = CC_MMUERR|CC_FPUERR|CC_DIVERR|CC_BUSERR|CC_ILL|CC_BREAK|CC_STEP|CC_SLEEP;
	testid("Break test #2"); MARKSTART;
	if ((run_test(break_two, user_stack_ptr))||(zip_ucc()&cc_fail))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #2

	// Test break instruction in user mode
	// Make sure that a decision on the clock prior won't still cause a 
	// break condition
	cc_fail = (CC_FAULT)|CC_MMUERR|CC_TRAP|CC_STEP|CC_SLEEP;
	testid("Break test #3"); MARKSTART;
	run_test(break_three, user_stack_ptr);
	save_context(context);
	if ((context[15] != (int)break_three)	// Insist we stop at the break
			||(0==(zip_ucc()&CC_BREAK))//insn,that the break flag is
			||(zip_ucc()&cc_fail))	// set, and no other excpt flags
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #3
	// }}}

	// LJMP test ... not (yet) written

	// Branch testing
	// {{{
	// Test the early branching capability
	//	Does it successfully clear whatever else is in the pipeline?
	testid("Early Branch test"); MARKSTART;
	if ((run_test(early_branch_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #4
	// }}}

	// TRAP test
	// {{{
	testid("Trap test/AND"); MARKSTART;
	if ((run_test(trap_test_and, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	if ((zip_ucc() & 0x0200)==0)
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #5

	testid("Trap test/CLR"); MARKSTART;
	if ((run_test(trap_test_clr, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	if ((zip_ucc() & 0x0200)==0)
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #6
	// }}}

	// Overflow test
	testid("Overflow test"); MARKSTART;
	if ((run_test(overflow_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #7

	// Carry test
	testid("Carry test"); MARKSTART;
	if ((run_test(carry_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #8

	// LOOP_TEST
	testid("Loop test"); MARKSTART;
	if ((run_test(loop_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #9

	// SHIFT_TEST
	testid("Shift test"); MARKSTART;
	if ((run_test(shift_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #10

	// BREV_TEST
	//testid("BREV/stack test"); MARKSTART;
	//if ((run_test(brev_test, user_stack_ptr))||(zip_ucc()&0x01d90))
		//test_fails(start_time);		// #10
	//txstr("Pass\r\n");

	// PIPELINE_TEST
	testid("Pipeline test"); MARKSTART;
	if ((run_test(pipeline_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #11

	// MEM_PIPELINE_STACK_TEST
	testid("Mem-Pipeline test"); MARKSTART;
	if ((run_test(mempipe_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #12

	// CONDITIONAL EXECUTION test
	testid("Conditional Execution test"); MARKSTART;
	if ((run_test(cexec_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #13

	// NOWAIT pipeline test
	testid("No-waiting pipeline test"); MARKSTART;
	if ((run_test(nowaitpipe_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #14

	// BCMEM test
	testid("Conditional Branching test"); MARKSTART;
	if ((run_test(bcmem_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #15

	// Illegal instruction testing
	// {{{
	// Illegal Instruction test
	testid("Ill Instruction test, NULL PC"); MARKSTART;
	if ((run_test(NULL, user_stack_ptr))||((zip_ucc()^CC_ILL)&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #16

	// Illegal Instruction test
	cc_fail = CC_BUSERR|CC_DIVERR|CC_FPUERR|CC_BREAK|CC_MMUERR;
	testid("Ill Instruction test, two"); MARKSTART;
	if ((run_test(ill_test, user_stack_ptr))||(zip_ucc()&cc_fail))
		test_fails(start_time, &testlist[tnum]);
	save_context(context);
	if (context[15] != (int)&ill_test)
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #17
	// }}}

	// Comparison instruction testing
	// {{{
	// Compare EQuals test
	testid("Comparison test, =="); MARKSTART;
	if ((run_test(cmpeq_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #18

	// Compare !EQuals test
	testid("Comparison test, !="); MARKSTART;
	if ((run_test(cmpneq_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #19
	// }}}

	// Pipeline memory race condition test
	// DIVIDE test

	// CC Register test
	// {{{
	testid("CC Register test"); MARKSTART;
	if ((run_test(ccreg_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #20
	// }}}

	// Multiple argument test
	testid("Multi-Arg test"); MARKSTART;
	if ((run_test(multiarg_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #21

	// Load/store testing
	// {{{
	// Memory byte-level access test
	testid("LB/SB test"); MARKSTART;
	if ((run_test(membyte_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #22

	// Memory half-word-level access test
	testid("LH/SH test"); MARKSTART;
	if ((run_test(memhalf_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #23
	// }}}

	// Step testing
	// {{{
	// Step test: ALU
	testid("Step ALU test"); MARKSTART;
	if ((step_test(step_alu_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #24

	if (cis_insns!=0) {
	// Step test: 2 CIS Add Insns
	testid("Step CIS test"); MARKSTART;
	if ((step_test(step_cis_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #25
	}

	// Step test: BREAK
	testid("Step BREAK test"); MARKSTART;
	step_test(step_break_test, user_stack_ptr);	// Ignore the return
	if ((zip_ucc()^CC_BREAK)&CC_EXCEPTION)
		test_fails(start_time, &testlist[tnum]);
	else {
		unsigned	upc;
		GETUREG(upc, "uPC");
		upc = upc - (unsigned)step_break_test;
		if (upc != 0)
			test_fails(start_time, &testlist[tnum]);
	}
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #26


	if ((zip_cc() & 0x40000000)!=0) {
	// Step test: MPY
	testid("Step MPY test"); MARKSTART;
	if ((step_test(step_mpy_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #27
	}

	if ((zip_cc() & 0x20000000)!=0) {
	// Step test: Divide
	testid("Step DIV test"); MARKSTART;
	if ((step_test(step_div_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #28
	}

	// Step test: Divide by zero
	if ((zip_cc() & 0x20000000)!=0) {
	testid("Step DIVERR test"); MARKSTART;
	if ((step_test(step_diverr_test, user_stack_ptr))
					||((zip_ucc()^CC_DIVERR)&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #29
	}

	// Step test: Load
	testid("Step LOD test"); MARKSTART;
	if ((step_test(step_lod_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #30

	// Step test: Store
	testid("Step STO test"); MARKSTART;
	if ((step_test(step_sto_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #31

	// Step test: Load, bus err
	testid("Step LOD/ERR test"); MARKSTART;
	if ((step_test(step_loderr_test, user_stack_ptr))
					||((zip_ucc()^CC_BUSERR)&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #32

	// Step test: Store, bus err
	testid("Step STO/ERR test"); MARKSTART;
	if ((step_test(step_stoerr_test, user_stack_ptr))
					||((zip_ucc()^CC_BUSERR)&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	txstr("Pass\r\n"); testlist[tnum++] = 0;	// #33
	// }}}

	// Multiply
	// {{{
	if ((zip_cc() & 0x40000000)==0) {
		testid("Multiply test"); MARKSTART;
		if ((run_test(mpy_test, user_stack_ptr))
				|| (zip_ucc()&CC_ILL))
			txstr("Pass (No MPY, MPY traps)\r\n");
		else
			test_fails(start_time, &testlist[tnum]);
	} else {
		// MPY_TEST
		testid("Multiply test"); MARKSTART;
		if ((run_test(mpy_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
			test_fails(start_time, &testlist[tnum]);
		txstr("Pass\r\n"); testlist[tnum++] = 0;	// #34

		// MPYxHI_TEST
		testid("Multiply HI-word test"); MARKSTART;
		if ((run_test(mpyhi_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
			test_fails(start_time, &testlist[tnum]);
		txstr("Pass\r\n"); testlist[tnum++] = 0;	// #35
	}
	// }}}

	// DIV_TEST
	// {{{
	testid("(Unsigned) Divide test");
	if ((zip_cc() & 0x20000000)==0) {
		txstr("No divide unit installed\r\n");
	} else { MARKSTART;
	if ((run_test(divu_test, user_stack_ptr))||(zip_ucc()&CC_EXCEPTION))
		test_fails(start_time, &testlist[tnum]);
	} txstr("Pass\r\n"); testlist[tnum++] = 0;	// #36

	testid("(Signed)   Divide test");
	MARKSTART;
	if ((run_test(divs_test, user_stack_ptr))
			||((cc = zip_ucc())&CC_EXCEPTION)) {
		if ((zip_cc() & 0x20000000) && (cc & CC_ILL))
			txstr("Pass (No div, Divide traps)\r\n");
		else
			test_fails(start_time, &testlist[tnum]);
	} else
		txstr("Pass\r\n");
	testlist[tnum++] = 0;	// #37
	// }}}

	// SMP_TEST
	// {{{
#define	OPT_SMP
#ifdef	OPT_SMP
	{
		unsigned	count, cc;

		testid("SMP Count");
		MARKSTART;
		count = run_test(smp_count, user_stack_ptr);
		if ((cc=zip_ucc())&(CC_ILL|CC_DIVERR|CC_FPUERR
							|CC_BREAK|CC_MMUERR))
			test_fails(start_time, &testlist[tnum]);
		txdecimal(count+1); txstr(" CPUs\r\n");
		testlist[tnum++] = 0;	// #38
	}
#endif
	// }}}


	txstr("\r\n");
	txstr("-----------------------------------\r\n");
	txstr("All tests passed.  Halting CPU.\r\n");
	wait_for_uart_idle();
	txstr("\r\n");
	wait_for_uart_idle();
	// for(int k=0; k<50000; k++)
	//	asm("NOOP");
	asm("NEXIT 0");
	zip_halt();
}

int	main(int argc, char **argv) {
	entry();
}

