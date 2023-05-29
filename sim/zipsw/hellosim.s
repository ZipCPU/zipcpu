;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Filename:	sim/zipsw/hellosim.s
;; {{{
;; Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
;;
;; Purpose:	Hello World, only using the SIM instructions, as an initial
;;		test of whether or not the special SIM instructions even work.
;;
;;
;; Creator:	Dan Gisselquist, Ph.D.
;;		Gisselquist Technology, LLC
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; }}}
;; Copyright (C) 2017-2022, Gisselquist Technology, LLC
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
;;
;; You should have received a copy of the GNU General Public License along
;; with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
;; target there if the PDF file isn't present.)  If not, see
;; <http://www.gnu.org/licenses/> for a copy.
;; }}}
;; License:	GPL, v3, as defined and found on www.gnu.org,
;; {{{
;;		http://www.gnu.org/licenses/gpl.html
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; }}}
	.section .start, "ax"
	.global	_start
_start:
	NOUT	'H'
	NOUT	'e'
	NOUT	'l'
	NOUT	'l'
	NOUT	'o'
	NOUT	' '
	NOUT	'W'
	NOUT	'o'
	NOUT	'r'
	NOUT	'l'
	NOUT	'd'
	NOUT	'!'
	NOUT	'\r'
	NOUT	'\n'
	NEXIT	0
	HALT
	BUSY
