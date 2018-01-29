;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Filename:	
;;
;; Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
;;
;; Purpose:	Our goal will be to test all of the ZipCPU instructions via
;;		simulation mode, to ensure that the instructions work.  This
;;	is going to be an all assembler test, so that we can remain *REALLY*
;;	low level, before trying to step up and test/prove whether or not the
;;	compiler and/or C-library work.
;;
;;	This is in many ways a rewrite of the original CPU test program.
;;
;; Creator:	Dan Gisselquist, Ph.D.
;;		Gisselquist Technology, LLC
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Copyright (C) 2015-2017, Gisselquist Technology, LLC
;;
;; This program is free software (firmware): you can redistribute it and/or
;; modify it under the terms of  the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or (at
;; your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; License:	GPL, v3, as defined and found on www.gnu.org,
;;		http://www.gnu.org/licenses/gpl.html
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;
	.section .start,"ax",@progbits
	.global	_start
_start:
	; The initial test is both a test of the assembler, as well as a test
	; of the BREAK/cache.  If done properly, the BRAnch will keep the
	; break from executing.
	noop	; This is both a test of the 
	bra	continue_test_with_testable_instructions
	break
	wait
	break	25
	busy
	rtu
continue_test_with_testable_instructions:
	; Now, let's place the assembler into a known state, by clearing
	; all of our (supervisor) registers.
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
	ldi	_top_of_stack,sp
	; Don't clear the user PC register
	; Now, let's try loading some constants into registers
	; Specifically, we're testing the LDI, LDIHI, and LDILO instructions
	ldi	0xdead,R5
	ldi	0x0beef,r6
	ldi	0xdeadbeef,r7
	brev	0xb57b, r8
	ldilo	0xbeef, r8

#define	PUSH_TEST
#define	PIPELINE_STACK_TEST
#define	MEM_PIPELINE_TEST
#define	CONDITIONAL_EXECUTION_TEST
#define	NOWAIT_PIPELINE_TEST	// Were wait states btwn regs removed properly?
#define	BCMEM_TEST	// Do memory and conditions work well together?
#define	PIPELINE_MEMORY_RACE_CONDITIONS
	cmp	0xdead,R5
	bnz	test_failure
	cmp	0xbeef,r6
	bnz	test_failure
	lsl	16,r5
	or	r6,r5
	cmp	r5,r7
	bnz	test_failure
	cmp	r7,r8
	bnz	test_failure
	bra	skip_dead_beef
dead_beef_sym:
	.int	0
	.fill	5,4,0xdeadbeef
	.int	0
skip_dead_beef:
	lw	dead_beef_sym(pc),r10	; Should load a zero here
	cmp	r10,r11			; r11 should still be zero from init abv
	bnz	test_failure
	mov	dead_beef_sym(pc),r10	; Now, let's get the address
	lw	4(r10),r10	; r10 now equals 0xdeadbeef
	cmp	r10,r8		; R8 = deadbeef from before
	bnz	test_failure

junk_address:
	xor	r0,r0
	bnz	test_failure
	ldi	5,r1
	cmp	0+r0,r1
	not.lt	r0
	not.ge	r1
	cmp	0,R0
	bnz	test_failure
	cmp	0xfffffffa,R1
	bnz	test_failure

	mov	junk_address(pc),r2	; Test pc-relative addressing
	mov	junk_address(pc),r3
	cmp	r2,r3
	bnz	test_failure
	lw	junk_address(pc),r5	; Test loads with pc-relative addressing
	lw	junk_address(pc),r6
	cmp	r5,r6
	bnz	test_failure
;
;#ifdef	NOONE // Testing comments after ifdef
;#else	; After else
;#endif /* and after endif */
;
	CLR	R0
	CLR	R1
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	ADD	1,R0
	CMP	6,R0
	BNZ	test_failure
	ADD	1,R1
	ADD	1,R1
	ADD	1,R1
	CMP	3,R1
	BNZ	test_failure
;	// Unlike the previous test, this test is going to see whether or not
;	// early branching messes with the pipeline.
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
	; Only problem is, I don't expect it to mess with the pipeline unless
	; the pipeline is full.  Therefore we are interested in something which
	; is not an early branch, conflicting with early branches.  So let's
	; try loading our pipeline in all kinds of different configurations,
	; just to see which if the conditional branch always annihilates the
	; early branch as desired.
	;
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
	; Let's repeat that last test, just in case the cache reloaded itself
	; in the middle and we didn't get our proper test.
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
;
;
;
;#ifdef	TRAP_TEST
traptest:
	bra	traptest_supervisor
	NEXIT	-1
traptest_user:
	trap	0
	busy
traptest_supervisor:
	mov	traptest_user(pc),upc
	rtu
	mov	ucc,r0
	tst	0x0200,r0	; Check for the trap bit
	tst.nz	0x020,r0	; Check for the GIE bit
	bz	test_failure
;
testbench:
	; Let's build a software test bench.
	ldi	0xff000000,r12	; Set R12 to point to our peripheral address
	mov	r12,ur12
	mov	test_start(pc),upc
	mov	_top_of_stack,r1
	MOV	R1,uSP
	rtu
	mov	ucc,r0
	and	0x0ffff,r0
	CMP	0x220,r0
	bnz	test_failure
test_success:
	NOUT 'S'
	NOUT 'i'
	NOUT 'm'
	NOUT ' '
	NOUT 'd'
	NOUT 'o'
	NOUT 'n'
	NOUT 'e'
	NOUT '\r'
	NOUT '\n'
	NOUT 'S'
	NOUT 'U'
	NOUT 'C'
	NOUT 'C'
	NOUT 'E'
	NOUT 'S'
	NOUT 'S'
	NOUT '!'
	NOUT '\r'
	NOUT '\n'
	NEXIT 0
	halt
;// Go into an infinite loop if the trap fails
;// Permanent loop instruction -- a busy halt if you will
test_failure:
	NDUMP
	NEXIT -1
	busy
;
;; Now for a series of tests.  If the test fails, call the trap
;; interrupt with the test number that failed.  Upon completion,
;; call the trap with #0.
;
;; Test LDI to PC
;; Some data registers
test_start:
	ldi	$0x01000,r11
	ldi	-1,r10
	ljmp	quickskip
	clr	r10
quickskip:
	noop
	cmp	$0,r10
	trap.z	0
	add	$1,r0
	add	$1,r0

; Let's test whether overflow works
	ldi	$0x02000,r11
	ldi	$-1,r0
	lsr	$1,r0
	add	$1,r0
	bv	first_overflow_passes
	trap	0
first_overflow_passes:
; Overflow set from subtraction
	ldi	$0x03000,r11
	BREV	$1,r0
	sub	$1,r0
	bv	subtraction_overflow_passes
	trap	0
subtraction_overflow_passes:
; Overflow set from LSR
	ldi	$0x04000,r11
	BREV	1,r0
	lsr	$1,r0
	bv	lsr_overflow_passes
	trap	0
lsr_overflow_passes:
; Overflow set from LSL
	ldi	$0x05000,r11
	BREV	2,R0
	lsl	$1,r0
	bv	lsl_overflow_passes
	trap	0
lsl_overflow_passes:
; Overflow set from LSL, negative to positive
	ldi	$0x06000,r11
	BREV	1,r0
	lsl	$1,r0
	bv	second_lsl_overflow_passes
	trap	0
second_lsl_overflow_passes:
; Test carry
	ldi	$0x07000,r11
	ldi	$-1,r0
	add	$1,r0
	tst	2,cc
	mov.z	cc,r2
	trap.z	0
; and carry from subtraction
	ldi	$0x08000,r11
	clr	r0
	sub	$1,r0
	tst	2,cc
	mov.z	cc,r2
	trap.z	0
; Carry from right shift
	clr	r0		; r0 = 0
	lsr	1,r0		; r0 = 0, c = 0
	add.c	1,r0		; r0 = 0
	cmp	1,r0		; r0 ?= 1
	trap.z	0
	LDI	1,r0		; r0 = 1
	lsr	1,r0		; r0 = 0, c = 1
	add.c	1,r0		; r0 = 1
	cmp	1,r0
	trap.nz	0
;
	ldi	0x070eca6,r0
	ldi	0x0408b85,r1
	ldi	0x0387653,r2
	lsr	1,r0
	xor.c	r1,r0
	cmp	r2,r0
	trap.nz	0
;
; Let's try a loop: for i=0; i<5; i++)
;	We'll use R0=i, Immediates for 5
	ldi	$0x09000,r11
	clr	r0
	clr	r1
for_loop:
	add	1,r1
	add	$1,r0
	cmp	$5,r0
	blt	for_loop

	cmp	r0,r1
	trap.nz	0
;
; Let's try a reverse loop.  Such loops are usually cheaper to
; implement, and this one is no different: 2 loop instructions 
; (minus setup instructions) vs 3 from before.
; R0 = 5; (from before)
; do {
; } while (R0 > 0);
	ldi	$0x0a000,r11
	clr	r1
	sub	1,r0
bgt_loop:
	add	1,r1
	sub	$1,r0
	bge	bgt_loop
	cmp	5,r1
	trap.nz	0

; How about the same thing with a >= comparison?
; R1 = 5; // Need to do this explicitly
; do {
; } while(R1 >= 0);
	ldi	$20,r0
	ldi	$5,r1
	clr	r2
bge_loop:
	add	1,r2
	sub	$1,r1
	bge	bge_loop

	cmp	6,r2
	trap.nz	0

; Let's try the reverse loop again, only this time we'll store our
; loop variable in memory.
; R0 = 5; (from before)
; do {
; } while (R0 > 0);
	ldi	$0x0b000,r11
	sub	4,sp
	clr	r0
	sw	r0,(sp)
mem_loop_test:
	mov	sp,r1
	ldi	$4,r0
	clr	r2
	sw	r0,(r1)
mem_loop:
	add	$1,r2
	add	$14,r0
	lw	(r1),r0
	sub	$1,r0
	sw	r0,(r1)
	bge	mem_loop
	cmp	$5,r2
	trap.ne	0
;
;; Now, let's test whether or not our LSR and carry flags work
	ldi	$0x0c000,r11
	ldi	-1,r0	; First test: shifting all the way should yield zero
	lsr	32,r0
	cmp	0,r0
	bnz	test_failure
	ldi	-1,r0	; Second test: anything greater than zero should set
	lsr	0,r0	; the carry flag
	trap.c	0
	lsr	1,r0
	trap.nc	0
;
	tst	2,cc	; C bit to be set
	mov.z	cc,r2
	trap.z	0
;
	lsr	31,r0
	trap.nz	0
	lsr	1,r0
	trap.c	0
;; Now repeat the above tests, looking to see whether or not ASR works
	ldi	-1,r0
	asr	32,r0
	cmp	-1,r0
	trap.nz	0
	ldi	-1,r0
	asr	0,r0
	trap.c	0
	cmp	-1,r0
	trap.nz	0
	asr	1,r0
	tst	2,r14
	trap.z	0
	asr	30,r0
	tst	2,r14
	trap.z	0
	ldi	-1,r0
	asr	1,r0
	cmp	-1,r0
	trap.nz	0
;
; Let's test whether LSL works
	ldi	0x035,r2
	lsl	8,r2
	ldi	0x03500,r1
	cmp	r2,r1
	trap.ne	0
	ldi	0x074,r0
	and	0x0ff,r0
	or	r0,r2
	cmp	0x03574,r2
	trap.ne	0
;
; A push test
	ldi	$0x0e000,r11	; Mark our test
	ldi	0x01248cab,r1
	ldi	0xd5312480,r2	; Let's see if we can preserve this as well
	mov	r1,r4
	mov	r2,r5
	JSR	reverse_bit_order
	cmp	r1,r4
	trap.ne	0
	cmp	r2,r5
	trap.ne	0
;
; A more thorough pipeline stack test
	ldi	$0x0f000,r11	; Mark our test
	LDI	1,R0
	MOV	1(R0),R1
	MOV	1(R1),R2
	MOV	1(R2),R3
	MOV	1(R3),R4
	MOV	1(R4),R5
	MOV	1(R5),R6
	JSR	pipeline_stack_test
	CMP	1,R0
	trap.ne	0
	CMP	2,R1
	trap.ne	0
	CMP	3,R2
	trap.ne	0
	CMP	4,R3
	trap.ne	0
	CMP	5,R4
	trap.ne	0
	CMP	6,R5
	trap.ne	0
	CMP	7,R6
	trap.ne	0

;
; Memory pipeline test
	LDI	0x10000,R11
	JSR	mem_pipeline_test
;
; Conditional execution test
	LDI	0x11000,R11
	JSR	conditional_execution_test
;
; The no-wait pipeline test
	LDI	0x12000,R11
	JSR	nowait_pipeline_test
;
;#ifdef	BCMEM_TEST
	LDI	0x13000,R11
	CLR	R0
	LDI	-1,R1
	SUB	4,SP
	SW	R0,(SP)
	LW	(SP),R1
	CMP	R0,R1
	TRAP.NZ	-1
	CMP	0x13000,R11
	BZ	bcmemtest_cmploc_1
	SW	R11,(SP)
bcmemtest_cmploc_1:
	LW	(SP),R0
	CMP	R0,R11
	TRAP.Z	-1
	CLR	R0
	CMP	R0,R11
	BZ	bcmemtest_cmploc_2
	SW.NZ	R11,(SP)
bcmemtest_cmploc_2:
	NOOP
	LW	(SP),R0
	CMP	R0,R11
	TRAP.NZ	-1

; The byte test --- have our 8-bit byte changes worked?
	ldi	0x14000, r11
	jsr	bytetest

;
;#ifdef	PIPELINE_MEMORY_RACE_CONDITIONS
;	LDI	0x14000,R11
;	FJSR(pipeline_memory_race_test,R0)
;#endif // PIPELINE_MEMORY_RACE_CONDITIONS
;
; Return success / Test the trap interrupt
	clr	r11
	trap
	noop
	noop

	NEXIT	-1
	BUSY
;
;// And, in case we miss a halt ...
	halt
;
;// Now, let's test whether or not we can handle a subroutine
reverse_bit_order:
	SUB	12,SP
	SW	R2,(SP)		; R1 will be our loop counter
	SW	R3,4(SP)	; R2 will be our accumulator and eventual result
	SW	R4,8(SP)
	LDI	32,R2
	CLR	R3
reverse_bit_order_loop:
	LSL	1,R3
	LSR	1,R1
	OR.C	1,R3
	SUB	1,R2
	BZ	reverse_bit_order_loop_over
	BRA	reverse_bit_order_loop
reverse_bit_order_loop_over:
	MOV	R3,R1
	LW	(SP),R2
	LW	4(SP),R3
	LW	8(SP),R4
	ADD	12,SP
	RETN
;
;; The pipeline stack test examines whether or not a series of memory commands
;; can be evaluated right after the other without problems.  This depends upon
;; the calling routine to properly set up registers to be tested.
;;
;; This is also an incomplete test, as nothing is done to test how these
;; pipeline reads/writes are affected by condition codes.
;;
pipeline_stack_test:
	SUB	52,SP
	SW	R0,(SP)
	SW	R1,4(SP)
	SW	R2,8(SP)
	SW	R3,12(SP)
	SW	R4,16(SP)
	SW	R5,20(SP)
	SW	R6,24(SP)
	SW	R7,28(SP)
	SW	R8,32(SP)
	SW	R9,36(SP)
	SW	R10,40(SP)
	SW	R11,44(SP)
	SW	R12,48(SP)
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
	LW	(SP),R0
	LW	4(SP),R1
	LW	8(SP),R2
	LW	12(SP),R3
	LW	16(SP),R4
	LW	20(SP),R5
	LW	24(SP),R6
	LW	28(SP),R7
	LW	32(SP),R8
	LW	36(SP),R9
	LW	40(SP),R10
	LW	44(SP),R11
	LW	48(SP),R12
	ADD	52,SP
	RETN
;
;#ifdef	MEM_PIPELINE_TEST
mem_pipeline_test:
	SUB	16,SP
	SW	R0,(SP)
	SW	R1,4(SP)
	LDI	0x10000,R11
	;
	; Test #1 ... Let's start by writing a value to memory
	LDI	-1,R0
	CLR	R1
	SW	R0,8(SP)
	LW	8(SP),R1
	CMP	R1,R0
	MOV.NZ	R11,CC
;
;	; Test #2, reading and then writing a value from memory
	NOP
	NOP
	CLR	R0
	CLR	R1
	LW	8(SP),R0	; This should load back up our -1 value
	SW	R0,12(SP)
	; Insist that the pipeline clear
	LW	2(SP),R0
	; Now let's try loading into R1
	NOP
	NOP
	NOP
	NOP
	LW	12(SP),R1
	CMP	R1,R0
	MOV.NZ	R11,CC
	
	LW	(SP),R0
	LW	4(SP),R1
	ADD	16,SP
	RETN
;#endif
;
conditional_execution_test:
	SUB	4,SP
	SW	R0,(SP)
	;
	XOR	R0,R0
	ADD.Z	1,R0
	TRAP.NZ	-1
	CMP.Z	0,R0
	TRAP.Z	-1
;
	LW	(SP),R0
	ADD	4,SP
	RETN
;
;;
;; Pipeline stalls have been hideous problems for me.  The CPU has been modified
;; with special logic to keep stages from stalling.  For the most part, this
;; means that ALU and memory results may be accessed either before or as they
;; are written to the register file.  This set of code is designed to test
;; whether this bypass logic works.
nowait_pipeline_test:
	; Allocate for us some number of registers
	;
	SUB	24,SP
	; Leave a spot open on the stack for a local variable,
	; kept in memory.
	SW	R0,(SP)
	SW	R1,4(SP)
	SW	R2,8(SP)
	SW	R3,12(SP)
	SW	R4,16(SP)
;	;
;	; Let's start with ALU-ALU testing
;	;	AA: result->input A
	CLR	R0
	ADD	1,R0
	CMP	1,R0
	TRAP.NZ	-1
;
	;	AA: result->input B
	CLR	R0
	CLR	R1
	ADD	1,R0
	CMP	R0,R1
	TRAP.Z	-1
;
	;	AA: result->input A on condition
	XOR	R0,R0
	ADD.Z	5,R0
	CMP	5,R0
	TRAP.NZ	-1
;
	;	AA: result->input B on condition
	CLR	R0
	XOR	R1,R1
	ADD.Z	5,R0
	CMP	R0,R1
	TRAP.Z	-1
;
	;	AA: result->input B plus offset
	CLR	R0
	XOR	R1,R1
	ADD	5,R0
	CMP	-5(R0),R1
	TRAP.NZ	-1
;
;	;	AA: result->input B plus offset on condition
	CLR	R0
	XOR	R1,R1
	ADD.Z	5,R0
	CMP	-5(R0),R1
	TRAP.NZ	-1
;
	;
	; Then we need to do ALU-Mem input testing
	;
	CLR	R0
	SW	R0,5(SP)
	LDI	8352,R0
	LW	5(SP),R0
	TST	-1,R0
	TRAP.NZ	-1
;
	LDI	937,R0		; Let's try again, this time something that's
	SW	R0,20(SP)	; not zero
	NOOP
	LW	20(SP),R0
	CMP	938,R0		; Let's not compare with self, let's that
	TRAP.GE	-1		; masks a problem--compare with a different
	CMP	936,R0		; number instead.
	TRAP.LT	-1
;
	; Mem output->ALU input testing
	;	We just did that as partof our last test
	; Mem output->MEM input testing
	;
	LDI	5328,R2
	LW	20(SP),R2
	SW	R2,20(SP)
	LW	20(SP),R1
	CMP	937,R1
	TRAP.NZ
	;
	LW	(SP),R0
	LW	4(SP),R1
	LW	8(SP),R2
	LW	12(SP),R3
	LW	16(SP),R4
	ADD	24,SP
	RETN

; Lets test whether or not we can read/write bytes like we are supposed to be
; able to.  Do we properly get 8-bit access?
bytetest:
	sub	4,sp
	;
	ldi	-1,r1
	sw	r1,(sp)
	lb	(sp),r1
	cmp	255,r1
	trap.nz	0
	lb	1(sp),r1
	cmp	255,r1
	trap.nz	0
	lb	2(sp),r1
	cmp	255,r1
	trap.nz	0
	lb	3(sp),r1
	cmp	255,r1
	trap.nz	0
	;
	lh	0(sp),r1
	cmp	65535,r1
	trap.nz	0
	lh	2(sp),r1
	cmp	65535,r1
	trap.nz	0
	;
	ldi	0xdeadbeef,r1
	sw	r1,(sp)
	;
	lb	(sp),r1
	cmp	0x0de,r1
	trap.nz	0
	lb	1(sp),r1
	cmp	0x0ad,r1
	trap.nz	0
	lb	2(sp),r1
	cmp	0x0be,r1
	trap.nz	0
	lb	3(sp),r1
	cmp	0x0ef,r1
	trap.nz	0
	;
	lh	0(sp),r1
	cmp	0x0dead,r1
	trap.nz	0
	lh	2(sp),r1
	cmp	0x0beef,r1
	trap.nz	0
	;
	; Now, let's try partial stores
	ldi	0xdeadbeef,r1
	brev	r1
	sb	r1,(sp)
	lw	(sp),r2
	ldi	0x7badbeef,r3
	cmp	r2,r3
	trap.nz
	;
	add	4,sp
	retn


;
;#ifdef	PIPELINE_MEMORY_RACE_CONDITIONS
;
;	THIS IS BROKEN, just needs to be rewritten somewhat
;
;pipeline_memory_race_test:
;	SUB	16,SP
;	SW	R0,(SP)
;	SW	R1,4(SP)
;	SW	R2,8(SP)
;
;	MOV	16(SP),R0	
;	LW	(R0),R0
;	LW	(R0),R0
;	CMP	275,R0
;	MOV.NZ	R11,CC
;
;	MOV	16(SP),R0	
;	; Here's the test sequence
;	LW	(R0),R1
;	LW	4(R0),R2
;	SW	R2,4(R1)
;	; Make sure we clear the load pipeline
;	LW	(R0),R1
;	; Load our written value
;	LW	4(R0),R2
;	CMP	275,R2
;	MOV.NZ	R11,CC
;
;	;
;	; Next failing sequence:
;	;	LW -x(R12),R0
;	;	LW y(R0),R0
;	MOV	pipeline_memory_test_data(PC),R0
;	MOV	1(R0),R1
;	SW	R1,4(R0)
;	LDI	3588,R2		; Just some random value
;	SW	R2,8(R0)
;	MOV	R0,R1
;	; Here's the test sequence
;	LW	(R0),R1
;	LW	4(R1),R1
;	CMP	R2,R1	
;	MOV.NZ	R11,CC
;
;	LW	(SP),R0
;	LW	4(SP),R1
;	LW	8(SP),R2
;	ADD	16,SP
;	RETN
;pipeline_memory_test_data:
;	.dat	__here__+0x0100000+1
;	.dat	275
;	.dat	0
;#endif
;	
