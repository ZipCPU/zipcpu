;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Filename:	cmptest.s
;;
;; Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
;;
;; Purpose:	To test how the CPU handles comparisons near the CPUs limits.
;;
;;
;; Creator:	Dan Gisselquist, Ph.D.
;;		Gisselquist Technology, LLC
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
;; You should have received a copy of the GNU General Public License along
;; with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
;; target there if the PDF file isn't present.)  If not, see
;; <http://www.gnu.org/licenses/> for a copy.
;;
;; License:	GPL, v3, as defined and found on www.gnu.org,
;;		http://www.gnu.org/licenses/gpl.html
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;
	.section .start,"ax"
	.global	_start
_start:
	NOUT	'E'
	NOUT	'n'
	NOUT	't'
	NOUT	'r'
	NOUT	'y'
	NOUT	'\r'
	NOUT	'\n'
	LDI	_top_of_stack,R0
	MOV	R0,uSP
	LDI	user_task,R0
	MOV	R0,uPC
	RTU
	CMP	0,R0
	BNZ	_test_failure
	NOUT	'P'
	NOUT	'A'
	NOUT	'S'
	NOUT	'S'
	NOUT	'!'
	NOUT	'\r'
	NOUT	'\n'
	NEXIT	0
	HALT
_test_failure:
	NOUT	'F'
	NOUT	'A'
	NOUT	'I'
	NOUT	'L'
	NOUT	'\r'
	NOUT	'\n'
	NEXIT	-1
	HALT

user_task:
	NOUT	'U'
	NOUT	's'
	NOUT	'e'
	NOUT	'r'
	NOUT	'\r'
	NOUT	'\n'
	; Clear our registers, so we start out with a clean slate
	LDI	0x0fff,R0
	LDI	0x0fff,R1
	LDI	0x0fff,R2
	LDI	0x0fff,R3
	LDI	0x0fff,R4
	LDI	0x0fff,R5
	LDI	0x0fff,R6
	LDI	0x0fff,R7
	LDI	0x0fff,R8
	LDI	0x0fff,R9
	LDI	0x0fff,R10
	LDI	0x0fff,R11
	LDI	0x0fff,R12
	CLR	R0
	CLR	R1
	CLR	R2
	CLR	R3
	CLR	R4
	CLR	R5
	CLR	R6
	CLR	R7
	CLR	R8
	CLR	R9
	CLR	R10
	CLR	R11
	CLR	R12
	JSR	test_function
	; On return, return back to user mode
	TRAP

test_function:
	NOUT	'T'
	NOUT	'e'
	NOUT	's'
	NOUT	't'
	NOUT	'\r'
	NOUT	'\n'
	LDI	0x7fffffff,R1
	LDI	0x80000000,R2
	CMP	R2,R1	
	MOV	CC,R3
	AND	0x0f,R3
	NDUMP	R3
	RETN
