;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Filename:	test.S
;
; Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
;
; Purpose:	A disorganized test, just showing some initial operation of
;		the CPU.  As a disorganized test, it doesn't prove anything
;		beyond the generic operation of the CPU.
;
; Status:	As of August, 2015, this file assembles, builds, and passes
;		all of its tests in the Verilator simulator.
;
;	Okay, as of 15 August, there are now some tests that don't pass.
;	In particular, the #include test used to pass but didn't pass today.
;	Likewise the PUSH() macro test hasn't passed yet.  Finally, be aware
;	that this implementation is specific to where it loads on a board.
;	I tried loading it on my Basys development board, where I had placed
;	RAM in a different location and ... things didn't work out so well.
;	So grep the __here__ line and adjust it for where you intend to load
;	this file.
;
;	In general, as I'm building the CPU, I'm modifying this file to place
;	more and more capability tests within the file.  If the Lord is
;	willing, this will become the proof that the CPU completely works.
;	
;
; Creator:	Dan Gisselquist, Ph.D.
;		Gisselquist Technology, LLC
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Copyright (C) 2015, Gisselquist Technology, LLC
;
; This program is free software (firmware): you can redistribute it and/or
; modify it under the terms of  the GNU General Public License as published
; by the Free Software Foundation, either version 3 of the License, or (at
; your option) any later version.
;
; This program is distributed in the hope that it will be useful, but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
; for more details.
;
; License:	GPL, v3, as defined and found on www.gnu.org,
;		http://www.gnu.org/licenses/gpl.html
;
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
#include "sys.i"
	sys.bus		equ	0xc0000000
	sys.breaken	equ	0x080
	sys.step	equ	0x040
	sys.gie		equ	0x020
	sys.sleep	equ	0x010
	sys.ccv		equ	0x008
	sys.ccn		equ	0x004
	sys.ccc		equ	0x002
	sys.ccz		equ	0x001
	sys.cctrap	equ	0x200
	sys.bu.pic	equ	0x000
	sys.bus.wdt	equ	0x001
	sys.bus.cache	equ	0x002
	sys.bus.ctrpic	equ	0x003
	sys.bus.tma	equ	0x004
	sys.bus.tmb	equ	0x005
	sys.bus.tmc	equ	0x006
	sys.bus.jiffies	equ	0x007
	sys.bus.mtask	equ	0x008
	sys.bus.mpstl	equ	0x009
	sys.bus.mastl	equ	0x00a
	sys.bus.mstl	equ	0x00b
	sys.bus.utask	equ	0x00c
	sys.bus.upstl	equ	0x00d
	sys.bus.uastl	equ	0x00e
	sys.bus.ustl	equ	0x00f
#define	DO_TEST_ASSEMBLER
#define	LJMP_TEST
#define	EARLY_BRANCH_TEST
#define	BREAK_TEST
#define	OVERFLOW_TEST
#define	CARRY_TEST
#define	LOOP_TEST
#define	SHIFT_TEST
#define	TRAP_TEST
;
; Since updating our multiplies, the old MPY_TEST doesn't work anymore.  It
; really needs to be rebuilt.  For now, we just disable it.  I know, this is the
; wrong approach.  Test first and don't get surprised later.  Yes.  I need to
; come back to this--hopefully before getting surprised.
;
; #define	MPY_TEST
#define	PUSH_TEST
#define	PIPELINE_STACK_TEST
#define	MEM_PIPELINE_TEST
#define	CONDITIONAL_EXECUTION_TEST
#define	NOWAIT_PIPELINE_TEST	// Were wait states btwn regs removed properly?
#define	BCMEM_TEST	// Do memory and conditions work well together?
#define	PIPELINE_MEMORY_RACE_CONDITIONS
test:
#ifdef	DO_TEST_ASSEMBLER
; We start out by testing our assembler.  We give it some instructions, which
; are then manually checked  by disassembling/dumping the result and making
; certain they match.  This is not an automated test, but it is an important
; one.
	noop
	bra	continue_test_with_testable_instructions
	break
	wait
	break
	busy
	rtu
continue_test_with_testable_instructions:
	; Now, let's place the assembler into a known state
	clr	r0
	clr	r1
	clr	r2
	clr	r3
	clr	r4
	clr	r5
	clr	r6
	clr	r7
	clr	r8
	clr	r9
	clr	r10
	clr	r11
	clr	r12
	clr	r13
	; Don't clear the CC register
	; Don't clear the SP register
	; And repeat for the user registers
	mov	R0,uR0
	mov	R0,uR1
	mov	R0,uR2
	mov	R0,uR3
	mov	R0,uR4
	mov	R0,uR5
	mov	R0,uR6
	mov	R0,uR7
	mov	R0,uR8
	mov	R0,uR9
	mov	R0,uR10
	mov	R0,uR11
	mov	R0,uR12
	mov	R0,uR13
	mov	R0,uCC
	; Don't clear the user PC register
	; Now, let's try loading some constants into registers
	; Specifically, we're testing the LDI, LDIHI, and LDILO instructions
dead_beef	equ	0xdeadbeef
	ldi	0x0dead,r5
	ldi	0x0beef,r6
	ldi	0xdeadbeef,r7
	brev	0xb57b, r8
	ldilo	0xbeef, r8
	ldi	dead_beef,r9
	cmp	r5,r6
	bz	test_failure
	cmp	r7,r8
	bnz	test_failure
	ldi	$deadbeefh,r7	; Try loading with the $[HEX]h mneumonic
	cmp	r7,r8
	bnz	test_failure
	cmp	r7,r9
	bnz	test_failure
	bra	skip_dead_beef
dead_beef.base:
	word	0
	fill	5,dead_beef
	word	0
dead_beef.zero		equ	0
dead_beef.values	equ	1
skip_dead_beef:
	lod	dead_beef.base(pc),r10	; Should load a zero here
	cmp	r10,r11			; r11 should still be zero from init abv
	bnz	test_failure
	mov	dead_beef.base(pc),r10	; Now, let's get the address
	lod	dead_beef.values(r10),r10	; r10 now equals 0xdeadbeef
	cmp	r10,r9
	bnz	test_failure

; Test whether or not our operator precedence rules work
	ldi	5+3*8,r0
	ldi	3*8+5,r1
	cmp	r0,r1
	bnz	test_failure
	ldi	(5+3)*8,r0
	ldi	8*(3+5),r1
	cmp	r0,r1
	bnz	test_failure

; Test whether or not we can properly decode OCTAL values
	clr	r0	; Re-clear our register set first
	clr	r1
	clr	r2
	clr	r3
	clr	r4
	clr	r5
	clr	r6
	clr	r7
	clr	r8
	clr	r9
	clr	r10
	clr	r11
	clr	r12
	clr	r13
	;
	ldi	$024o,r0
	ldi	$20,r1
	cmp	r0,r1
	bnz	test_failure
	ldi	$024,r0
	cmp	r0,r1
	bnz	test_failure
	clr	r0
	clr	r1
	mov	$1+r0,r2
	mov	$2+r0,r3
	mov	$22h+r0,r4
	mov	$377h+r0,ur5
	noop
	nop
	add	r2,r0
	add	$32,r0
	add	$-33,r0
	bnz	test_failure
	not	r0
	bge	test_failure
junk_address:
	clrf	r0
	bnz	test_failure
	ldi	$5,r1
	cmp	$0+r0,r1
	not.lt	r0
	not.ge	r1
	mov	junk_address(pc),r2	; Test pc-relative addressing
	mov	junk_address(pc),r3
	cmp	r2,r3
	bnz	test_failure
	lod	junk_address(pc),r5	; Test loads with pc-relative addressing
	lod	junk_address(pc),r6
	cmp	r5,r6
	bnz	test_failure
#endif

#ifdef	NOONE // Testing comments after ifdef
#else	; After else
#endif /* and after endif */

#ifdef	LJMP_TEST
	// A long jump is a 32-bit instruction followed by a 32-bit address.
	// The CPU is supposed to jump to this address.  At issue in this test,
	// which can only really be verified by watching it in person currently,
	// is how fast this branch can take place.  Currently, it takes four
	// clocks--not that bad.
	//
	// Although really long jumps, we also test some of our early branching
	// forms here as well:
	//	1. Add to PC
	//	2. LOD (PC),PC (the long jump itself)
	//	3. LDI x,PC	// An early branch target not tested elsewhere
	//
	CLR	R0
	CLR	R1
	LJMP
	.dat	__here__+0x0100000+4
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	CMP	3,R0
	BNZ	test_failure
	LOD.Z	__here__+2(PC),PC
	BRA	test_failure
	.dat	__here__+0x0100000+2
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	CMP	5,R0
	BNZ	test_failure
// And our last early branching test
	LDI	0x0100000+__here__+4,PC
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	SUB	1,R0
	CMP	4,R0
	BNZ	test_failure
#endif
#ifdef	EARLY_BRANCH_TEST
	// Unlike the previous test, this test is going to see whether or not
	// early branching messes with the pipeline.
	BRA	eb_a
	BUSY
eb_a:
	BRA	eb_b
	NOP
	BUSY
eb_b:
	BRA	eb_c
	NOP
	NOP
	BUSY
eb_c:
	BRA	eb_d
	NOP
	NOP
	NOP
	BUSY
eb_d:
	BRA	eb_e
	NOP
	NOP
	NOP
	NOP
	BUSY
eb_e:
	NOOP
	// Only problem is, I don't expect it to mess with the pipeline unless
	// the pipeline is full.  Therefore we are interested in something which
	// is not an early branch, conflicting with early branches.  So let's
	// try loading our pipeline in all kinds of different configurations,
	// just to see which if the conditional branch always annihilates the
	// early branch as desired.
	//
	CLR	R0
	BZ	ebz_a
	BUSY
ebz_a:
	BZ	ebz_b
	NOP
	BUSY
ebz_b:
	BZ	ebz_c
	NOP
	NOP
	BUSY	
	// Let's repeat that last test, just in case the cache reloaded itself
	// in the middle and we didn't get our proper test.
ebz_c:
	BZ	ebz_d
	NOP
	NOP
	BUSY
ebz_d:
	BZ	ebz_e
	NOP
	NOP
	NOP
	BUSY
ebz_e:
	BZ	ebz_f
	NOP
	NOP
	NOP
	NOP
	BUSY
ebz_f:
	NOOP
#endif

#ifdef	BREAK_TEST
breaktest:
	bra	breaksupervisor
breakuser:
	clr	r0
	mov	1+r0,r1
	mov	1+r1,r2
	mov	1+r2,r3
	break		; At address 0x0100097
	mov	1+r4,r5
	mov	1+r5,r6
	clr	cc
	busy
breaksupervisor:
	ldi	-1,r0
	mov	breakuser(pc),upc
	rtu	; Should just keep returning immediately
	mov	upc,r0	
	rtu
	rtu
	mov	upc,r1
	cmp	r0,r1	
	bnz	test_failure
#endif

#ifdef	TRAP_TEST
traptest:
	bra	traptest_supervisor
	busy
traptest_user:
	trap	0
	busy
traptest_supervisor:
	mov	traptest_user(pc),upc
	rtu
	mov	ucc,r0
	tst	sys.cctrap,r0
	tst.nz	sys.gie,r0
	bz	test_failure
#endif

testbench:
	// Let's build a software test bench.
	ldi	$c0000000h,r12	; Set R12 to point to our peripheral address
	mov	r12,ur12
	mov	test_start(pc),upc
	mov	stack(pc),usp
	ldi	0x8000ffff,r0	; Clear interrupts, turn all vectors off
	sto	r0,(r12)
	rtu
	mov	ucc,r0
	and	0x0ffff,r0
	CMP	sys.cctrap+sys.gie,r0
	bnz	test_failure
	halt
// Go into an infinite loop if the trap fails
// Permanent loop instruction -- a busy halt if you will
test_failure:
	busy

; Now for a series of tests.  If the test fails, call the trap
; interrupt with the test number that failed.  Upon completion,
; call the trap with #0.

; Test LDI to PC
; Some data registers
test_data:
	.dat	__here__+0x0100000+5
test_start:
	ldi	$0x01000,r11
	ldi	-1,r10
	lod	test_data+pc,pc
	clr	r10
	noop
	cmp	$0,r10
	trap.z	r11
	add	$1,r0
	add	$1,r0

#ifdef	OVERFLOW_TEST
// Let's test whether overflow works
	ldi	$0x02000,r11
	ldi	$-1,r0
	lsr	$1,r0
	add	$1,r0
	bv	first_overflow_passes
	trap	r11
first_overflow_passes:
// Overflow set from subtraction
	ldi	$0x03000,r11
	ldi	$1,r0
	rol	$31,r0			; rol $31,r0
	sub	$1,r0
	bv	subtraction_overflow_passes
	trap	r11
subtraction_overflow_passes:
// Overflow set from LSR
	ldi	$0x04000,r11
	ldi	$1,r0
	rol	$31,r0			; rol $31,r0
	lsr	$1,r0
	bv	lsr_overflow_passes
	trap	r11
lsr_overflow_passes:
// Overflow set from LSL
	ldi	$0x05000,r11
	ldi	$1,r0
	rol	$30,r0
	lsl	$1,r0
	bv	lsl_overflow_passes
	trap	r11
lsl_overflow_passes:
// Overflow set from LSL, negative to positive
	ldi	$0x06000,r11
	ldi	$1,r0
	rol	$31,r0
	lsl	$1,r0
	bv	second_lsl_overflow_passes
	trap	r11
#endif // OVERFLOW_TEST
#ifdef	CARRY_TEST
second_lsl_overflow_passes:
// Test carry
	ldi	$0x07000,r11
	ldi	$-1,r0
	add	$1,r0
	tst	sys.ccc,cc
	trap.z	r11
// and carry from subtraction
	ldi	$0x08000,r11
	clr	r0
	sub	$1,r0
	tst	sys.ccc,cc
	trap.z	r11
// Carry from right shift
	clr	r0		; r0 = 0
	lsr	1,r0		; r0 = 0, c = 0
	add.c	1,r0		; r0 = 0
	cmp	1,r0		; r0 ?= 1
	trap.z	r11
	LDI	1,r0		; r0 = 1
	lsr	1,r0		; r0 = 0, c = 1
	add.c	1,r0		; r0 = 1
	cmp	1,r0
	trap.nz	r11

	ldi	0x070eca6,r0
	ldi	0x0408b85,r1
	ldi	0x0387653,r2
	lsr	1,r0
	xor.c	r1,r0
	cmp	r2,r0
	trap.nz	r11
#endif

#ifdef	LOOP_TEST

// Let's try a loop: for i=0; i<5; i++)
//	We'll use R0=i, Immediates for 5
	ldi	$0x09000,r11
	clr	r0
for_loop:
	noop
	add	$1,r0
	cmp	$5,r0
	blt	for_loop
//
// Let's try a reverse loop.  Such loops are usually cheaper to
// implement, and this one is no different: 2 loop instructions 
// (minus setup instructions) vs 3 from before.
// R0 = 5; (from before)
// do {
// } while (R0 > 0);
	ldi	$0x0a000,r11
bgt_loop:
	noop
	sub	$1,r0
	bgt	bgt_loop

// How about the same thing with a >= comparison?
// R1 = 5; // Need to do this explicitly
// do {
// } while(R1 >= 0);
	ldi	$20,r0
	ldi	$5,r1
bge_loop:
	noop
	sub	$1,r1
	bge	bge_loop

// Let's try the reverse loop again, only this time we'll store our
// loop variable in memory.
// R0 = 5; (from before)
// do {
// } while (R0 > 0);
	ldi	$0x0b000,r11
	bra	mem_loop_test
loop_var:
	.dat	0
mem_loop_test:
	mov	loop_var(pc),r1
	ldi	$5,r0
	clr	r2
	sto	r0,(r1)
mem_loop:
	add	$1,r2
	add	$14,r0
	lod	(r1),r0
	sub	$1,r0
	sto	r0,(r1)
	bgt	mem_loop
	cmp	$5,r2
	trap.ne	r11
#endif

#ifdef	SHIFT_TEST
; Now, let's test whether or not our LSR and carry flags work
	ldi	$0x0c000,r11
	ldi	-1,r0	; First test: shifting all the way should yield zero
	lsr	32,r0
	cmp	0,r0
	bnz	test_failure
	ldi	-1,r0	; Second test: anything greater than zero should set
	lsr	0,r0	; the carry flag
	bc	test_failure
	lsr	1,r0
	tst	sys.ccc,cc
	bz	test_failure
	lsr	31,r0
	tst	sys.ccc,cc
	bz	test_failure
	lsr	1,r0
	bc	test_failure
; Now repeat the above tests, looking to see whether or not ASR works
	ldi	-1,r0
	asr	32,r0
	cmp	-1,r0
	bnz	test_failure
	ldi	-1,r0
	asr	0,r0
	bc	test_failure
	cmp	-1,r0
	bnz	test_failure
	asr	1,r0
	tst	sys.ccc,r14
	bz	test_failure
	asr	30,r0
	tst	sys.ccc,r14
	bz	test_failure
	ldi	-1,r0
	asr	1,r0
	cmp	-1,r0
	bnz	test_failure

// Let's test whether LSL works
	ldi	0x035,r2
	lsl	8,r2
	ldi	0x03500,r1
	cmp	r2,r1
	trap.ne	r11
	ldi	0x074,r0
	and	0x0ff,r0
	or	r0,r2
	cmp	0x03574,r2
	trap.ne	r11
#endif

#ifdef	MPY_TEST

// We have two multiply instructions.  Let's see if those work
	ldi	$0x0d000,r11	// Mark our test
	ldi	23171,r0	// = sqrt(2)/2 * 32768
	mpyu	r0,r0		// Should = 2/4 * 2^30 = 2^29 or thereabouts
	ldi	536895241,r2
	cmp	r0,r2
	trap.ne	r11
	ldi	0x0ffff,r0
	mpyu	r0,r0
	ldi	0xfffe0001,r1
	cmp	r1,r0
	trap.ne	r11
	ldi	0x08001,r0
	ldi	0x07fff,r1
	mpys	r0,r1		// FAILS: result is 0x008001 ??? (pipeline prob)
	ldi	0x3fff0001,r2
	neg	r2
	cmp	r2,r1		// @0x010011c
	trap.ne	r11		//TRAP FAILS TO TRIGGER ????? (R2=0x0c000ffff,R1=0x0008001 -- did mpy even happen?)
	mpys	r0,r0		// FAILS: result is 0x40010001
	ldi	0x3fff0001,r2
	cmp	r2,r0
	trap.ne	r11		// TRAP FAILS TO TRIGGER AGAIN
	ldi	0x08000,r0
	mpys	r0,r0		// R0 now equals 0x40000000
	ldi	0x40000000,r1
	cmp	r0,r1
	trap.ne	r11
//
// And from our eyeball test ...
	LDI	0x01ff01ff,R0
	MOV	R0,R7
	MOV	8(SP),R6
	LSR	7,R0
	AND	7,R0
	LDI	7,R1
	SUB	R0,R1
	MOV	R1,R0
	MPYU	5,R0
	CMP	20,R0
	TRAP.NE	R11
#endif

#ifdef	PUSH_TEST
	ldi	$0x0e000,r11	// Mark our test
	ldi	0x01248cab,r0
	ldi	0xd5312480,r1	// Let's see if we can preserve this as well
	mov	r1,r7
	FJSR(reverse_bit_order,R4);	// *SP = 0x010013d
	cmp	r0,r1
	trap.ne	r11
	cmp	r0,r7
	trap.ne	r11
#endif

#ifdef	PIPELINE_STACK_TEST
	ldi	$0x0f000,r11	// Mark our test
	LDI	1,R0
	MOV	1(R0),R1
	MOV	1(R1),R2
	MOV	1(R2),R3
	MOV	1(R3),R4
	MOV	1(R4),R5
	MOV	1(R5),R6
	FJSR(pipeline_stack_test,R7)
	CMP	1,R0
	trap.ne	R11
	CMP	2,R1
	trap.ne	R11
	CMP	3,R2
	trap.ne	R11
	CMP	4,R3
	trap.ne	R11
	CMP	5,R4
	trap.ne	R11
	CMP	6,R5
	trap.ne	R11
	CMP	7,R6
	trap.ne	R11
#endif

#ifdef	MEM_PIPELINE_TEST
	LDI	0x10000,R11
	FJSR(mem_pipeline_test,R0)
#endif	// MEM_PIPELINE_TEST

#ifdef	CONDITIONAL_EXECUTION_TEST
	LDI	0x11000,R11
	FJSR(conditional_execution_test,R0)
#endif	// CONDITIONAL_EXECUTION_TEST

#ifdef	NOWAIT_PIPELINE_TEST
	LDI	0x12000,R11
	FJSR(nowait_pipeline_test,R0)
#endif	// NOWAIT_PIPELINE_TEST

#ifdef	BCMEM_TEST
	LDI	0x13000,R11
	CLR	R0
	LDI	-1,R1
	STO	R0,bcmemtestloc(PC)
	LOD	bcmemtestloc(PC),R1
	CMP	R0,R1
	TRAP.NZ	R11
	CMP	0x13000,R11
	BZ	bcmemtest_cmploc_1
	STO	R11,bcmemtestloc(PC)
bcmemtest_cmploc_1:
	LOD	bcmemtestloc(PC),R0
	CMP	R0,R11
	TRAP.Z	R11
	CLR	R0
	CMP	R0,R11
	BZ	bcmemtest_cmploc_2
	STO.NZ	R11,bcmemtestloc(PC)
bcmemtest_cmploc_2:
	NOOP
	LOD	bcmemtestloc(PC),R0
	CMP	R0,R11
	TRAP.NZ	R11
	BRA	end_bcmemtest
bcmemtestloc:
	WORD	0
end_bcmemtest:
#endif

#ifdef	PIPELINE_MEMORY_RACE_CONDITIONS
	LDI	0x14000,R11
	FJSR(pipeline_memory_race_test,R0)
#endif // PIPELINE_MEMORY_RACE_CONDITIONS

// Return success / Test the trap interrupt
	clr	r11
	trap	r11	// FAILS HERE FAILS FAILS FAILS !!!!!!!!!!!
	noop
	noop

	busy

// And, in case we miss a halt ...
	halt

// Now, let's test whether or not we can handle a subroutine
#ifdef	PUSH_TEST
reverse_bit_order:
	SUB	3,SP
	STO	R1,(SP)		; R1 will be our loop counter
	STO	R2,1(SP)	; R2 will be our accumulator and eventual result
	STO	R4,2(SP)
	LDI	32,R1
	CLR	R2
reverse_bit_order_loop:
	LSL	1,R2
	LSR	1,R0
	OR.C	1,R2
	SUB	1,R1
	BNZ	reverse_bit_order_loop
	MOV	R2,R0
	LOD	(SP),R1
	LOD	1(SP),R2
	LOD	2(SP),R4
	ADD	3,SP
	JMP	R4
#endif

; The pipeline stack test examines whether or not a series of memory commands
; can be evaluated right after the other without problems.  This depends upon
; the calling routine to properly set up registers to be tested.
;
; This is also an incomplete test, as nothing is done to test how these
; pipeline reads/writes are affected by condition codes.
;
#ifdef	PIPELINE_STACK_TEST
pipeline_stack_test:
	SUB	13,SP
	STO	R0,(SP)
	STO	R1,1(SP)
	STO	R2,2(SP)
	STO	R3,3(SP)
	STO	R4,4(SP)
	STO	R5,5(SP)
	STO	R6,6(SP)
	STO	R7,7(SP)
	STO	R8,8(SP)
	STO	R9,9(SP)
	STO	R10,10(SP)
	STO	R11,11(SP)
	STO	R12,12(SP)
	XOR	-1,R0
	XOR	-1,R1
	XOR	-1,R2
	XOR	-1,R3
	XOR	-1,R4
	XOR	-1,R5
	XOR	-1,R6
	XOR	-1,R7
	XOR	-1,R8
	XOR	-1,R9
	XOR	-1,R10
	XOR	-1,R11
	XOR	-1,R12
	LOD	(SP),R0
	LOD	1(SP),R1
	LOD	2(SP),R2
	LOD	3(SP),R3
	LOD	4(SP),R4
	LOD	5(SP),R5
	LOD	6(SP),R6
	LOD	7(SP),R7
	LOD	8(SP),R8
	LOD	9(SP),R9
	LOD	10(SP),R10
	LOD	11(SP),R11
	LOD	12(SP),R12
	ADD	13,SP
	JMP	R7
#endif // PIPELINE_STACK_TEST

#ifdef	MEM_PIPELINE_TEST
mem_pipeline_test:
	SUB	4,SP
	STO	R0,(SP)
	STO	R1,1(SP)
	LDI	0x10000,R11
	;
	; Test #1 ... Let's start by writing a value to memory
	LDI	-1,R0
	CLR	R1
	STO	R0,2(SP)
	LOD	2(SP),R1
	CMP	R1,R0
	MOV.NZ	R11,CC

	; Test #2, reading and then writing a value from memory
	NOP
	NOP
	CLR	R0
	CLR	R1
	LOD	2(SP),R0	; This should load back up our -1 value
	STO	R0,3(SP)
	; Insist that the pipeline clear
	LOD	2(SP),R0
	; Now let's try loading into R1
	NOP
	NOP
	NOP
	NOP
	LOD	3(SP),R1
	CMP	R1,R0
	MOV.NZ	R11,CC
	
	LOD	(SP),R0
	LOD	1(SP),R1
	ADD	4,SP
	JMP	R0
#endif

#ifdef	CONDITIONAL_EXECUTION_TEST
conditional_execution_test:
	SUB	1,SP
	STO	R0,(SP)
	;
	CLRF	R0
	ADD.Z	1,R0
	TRAP.NZ	R11
	CMP.Z	0,R0
	TRAP.Z	R11

	LOD	(SP),R0
	ADD	1,SP
	JMP	R0
#endif

;
; Pipeline stalls have been hideous problems for me.  The CPU has been modified
; with special logic to keep stages from stalling.  For the most part, this
; means that ALU and memory results may be accessed either before or as they
; are written to the register file.  This set of code is designed to test
; whether this bypass logic works.
#ifdef	NOWAIT_PIPELINE_TEST
nowait_pipeline_test:
	; Allocate for us some number of registers
	;
	SUB	6,SP
	; Leave a spot open on the stack for a local variable,
	; kept in memory.
	STO	R0,(SP)
	STO	R1,1(SP)
	STO	R2,2(SP)
	STO	R3,3(SP)
	STO	R4,4(SP)
	;
	; Let's start with ALU-ALU testing
	;	AA: result->input A
	CLR	R0
	ADD	1,R0
	CMP	1,R0
	TRAP.NZ	R11

	;	AA: result->input B
	CLR	R0
	CLR	R1
	ADD	1,R0
	CMP	R0,R1
	TRAP.Z	R11

	;	AA: result->input A on condition
	CLRF	R0
	ADD.Z	5,R0
	CMP	5,R0
	TRAP.NZ	R11

	;	AA: result->input B on condition
	CLR	R0
	CLRF	R1
	ADD.Z	5,R0
	CMP	R0,R1
	TRAP.Z	R11

	;	AA: result->input B plus offset
	CLR	R0
	CLRF	R1
	ADD	5,R0
	CMP	-5(R0),R1
	TRAP.NZ	R11

	;	AA: result->input B plus offset on condition
	CLR	R0
	CLRF	R1
	ADD.Z	5,R0
	CMP	-5(R0),R1
	TRAP.NZ	R11

	;
	; Then we need to do ALU-Mem input testing
	;
	CLR	R0
	STO	R0,5(SP)
	LDI	8352,R0
	LOD	5(SP),R0
	TST	-1,R0
	TRAP.NZ R11

	LDI	937,R0		; Let's try again, this time something that's
	STO	R0,5(SP)	; not zero
	NOOP
	LOD	5(SP),R0
	CMP	938,R0		; Let's not compare with self, let's that
	TRAP.GE R11		; masks a problem--compare with a different
	CMP	936,R0		; number instead.
	TRAP.LT R11

	; Mem output->ALU input testing
	;	We just did that as partof our last test
	; Mem output->MEM input testing
	;
	LDI	5328,R2
	LOD	5(SP),R2
	STO	R2,5(SP)
	LOD	5(SP),R1
	CMP	937,R1
	TRAP.NZ	R11
	;
	LOD	(SP),R0
	LOD	1(SP),R1
	LOD	2(SP),R2
	LOD	3(SP),R3
	LOD	4(SP),R4
	ADD	6,SP
	JMP	R0
#endif	// NOWAIT_PIPELINE_TEST

#ifdef	PIPELINE_MEMORY_RACE_CONDITIONS
pipeline_memory_race_test:
	SUB	3,SP
	STO	R0,(SP)
	STO	R1,1(SP)
	STO	R2,2(SP)

	MOV	pipeline_memory_test_data(PC),R0	
	LOD	(R0),R0
	LOD	(R0),R0
	CMP	275,R0
	MOV.NZ	R11,CC

	MOV	pipeline_memory_test_data(PC),R0	
	; Here's the test sequence
	LOD	(R0),R1
	LOD	1(R0),R2
	STO	R2,1(R1)
	; Make sure we clear the load pipeline
	LOD	(R0),R1
	; Load our written value
	LOD	2(R0),R2
	CMP	275,R2
	MOV.NZ	R11,CC

	;
	; Next failing sequence:
	;	LOD -x(R12),R0
	;	LOD y(R0),R0
	MOV	pipeline_memory_test_data(PC),R0
	MOV	1(R0),R1
	STO	R1,1(R0)
	LDI	3588,R2		; Just some random value
	STO	R2,2(R0)
	MOV	R0,R1
	; Here's the test sequence
	LOD	(R0),R1
	LOD	1(R1),R1
	CMP	R2,R1	
	MOV.NZ	R11,CC

	LOD	(SP),R0
	LOD	1(SP),R1
	LOD	2(SP),R2
	ADD	3,SP
	JMP	R0
pipeline_memory_test_data:
	.dat	__here__+0x0100000+1
	.dat	275
	.dat	0
#endif
	

	fill	512,0
stack:	// Must point to a valid word initially
	word	0
