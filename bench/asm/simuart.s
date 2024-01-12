;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Filename:	simuart.s
;; {{{
;; Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
;;
;; Purpose:	
;;
;;
;; Creator:	Dan Gisselquist, Ph.D.
;;		Gisselquist Technology, LLC
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; }}}
;; Copyright (C) 2015-2024, Gisselquist Technology, LLC
;; {{{
;; This program is free software (firmware): you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or (at
;; your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;; }}}
;; License:	GPL, v3, as defined and found on www.gnu.org,
;; {{{
;;		http://www.gnu.org/licenses/gpl.html
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; }}}
	.section .start,"ax",@progbits
	.global	_start
	.equ	uart, 0x150
_start:
	ldi	string,r2
	ldi	uart,r3

next_char:
	LB	(r2),R4
	TST	R4
	BZ	all_done
keep_waiting:
	LW	12(r3),R5
	TST	1,R5
	BNZ	keep_waiting
	SW	r4,12(r3)
	ADD	1,r2
	BRA	next_char
	
all_done:
	SEXIT	0
	HALT
string:
	.string	"Hello, World!\r\n"
