/*******************************************************************************
*
* Filename:	simscript.ld
* {{{
* Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
*
* Purpose:	This script provides a description of the memory found within
*		the ZipCPU simulator, zippy_tb, for the purposes of where to
*	place text and data sections when linking.
*
* Creator:	Dan Gisselquist, Ph.D.
*		Gisselquist Technology, LLC
*
********************************************************************************
* }}}
* Copyright (C) 2016-2024, Gisselquist Technology, LLC
* {{{
* This program is free software (firmware): you can redistribute it and/or
* modify it under the terms of the GNU General Public License as published
* by the Free Software Foundation, either version 3 of the License, or (at
* your option) any later version.
*
* This program is distributed in the hope that it will be useful, but WITHOUT
* ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
* FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
* for more details.
* }}}
* License:	GPL, v3, as defined and found on www.gnu.org,
* {{{
*		http://www.gnu.org/licenses/gpl.html
*
* }}}
*******************************************************************************/

ENTRY(_start)

MEMORY
{
	ram (wx) : ORIGIN = 0x10000000, LENGTH = 0x10000000
}

_top_of_stack = ORIGIN(ram) + LENGTH(ram);

SECTIONS
{
  .everything ORIGIN(ram) : ALIGN(4) {
	*(.start) *(.text) *(.rodata) *(.strings) 
  	*(.fixdata) *(.data) *(COMMON) *(.bss)
	} > ram
  _top_of_heap = .;
}
