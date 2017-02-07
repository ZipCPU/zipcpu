;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Filename:	hellosim.s
;;
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
;;
;; Copyright (C) 2017, Gisselquist Technology, LLC
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
	.section .start, "ax"
	.global	_start
_start:
	SOUT	'H'
	SOUT	'e'
	SOUT	'l'
	SOUT	'l'
	SOUT	'o'
	SOUT	' '
	SOUT	'W'
	SOUT	'o'
	SOUT	'r'
	SOUT	'l'
	SOUT	'd'
	SOUT	'!'
	SOUT	'\r'
	SOUT	'\n'
	SEXIT	0
	;; And in case someone tries to run this on a *real* ZipCPU, as
	;; opposed to just the simulator, we'll just halt here.
	HALT
