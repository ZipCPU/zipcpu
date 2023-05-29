/*******************************************************************************
*
* Filename:	bkram.ld
* {{{
* Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
*
* Creator:	Dan Gisselquist, Ph.D.
*		Gisselquist Technology, LLC
*
/*******************************************************************************
* }}}
* Copyright (C) 2017-2022, Gisselquist Technology, LLC
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
*
* You should have received a copy of the GNU General Public License along
* with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
* target there if the PDF file isn't present.)  If not, see
* <http://www.gnu.org/licenses/> for a copy.
* }}}
* License:	GPL, v3, as defined and found on www.gnu.org,
* {{{
*		http://www.gnu.org/licenses/gpl.html
*
/*******************************************************************************
*
* }}}
*/
ENTRY(_start)

MEMORY
{
	/* To be listed here, a slave must be of type MEMORY.  If the slave
	* has a defined name in its @LD.NAME tag, it will be listed here
	* under that name, otherwise it will be listed under it's
	* @$(PREFIX) tag with an underscore prepended to it.  The permissions
	* are given by the @LD.PERM tag.  Allowable permissions include
	* 'r' (read only), 'rx' (read and execute, but no writes),
	* 'wx' (read, write, and execute).  If no permission tag exists, a
	* permission of 'r' will be assumed.
	*/
	   bkram(wx) : ORIGIN = 0x04000000, LENGTH = 0x04000000
}

/* For each defined memory peripheral, we also define a pointer to that
* memory.  The name of this pointer is given by the @LD.NAME tag within
* the memory peripheral's configuration
*/
_bkram    = ORIGIN(bkram);
/* LD.DEFNS from mem_bkram_only */
_kram  = 0; /* No high-speed kernel RAM */
_ram   = ORIGIN(bkram);
_rom   = 0;
_top_of_stack = ORIGIN(bkram) + LENGTH(bkram);


/* LD.SCRIPT from mem_bkram_only */
SECTIONS
{
       .ramcode ORIGIN(bkram) : ALIGN(4) {
               _boot_address = .;
               _kram_start = .;
               _kram_end = .;
       		_ram_image_start = . ;
               *(.start) *(.boot)
               *(.kernel)
               *(.text.startup)
               *(.text*)
               *(.rodata*) *(.strings)
               *(.data) *(COMMON)
               }> bkram
       _ram_image_end = . ;
       .bss : ALIGN_WITH_INPUT {
               *(.bss)
               _bss_image_end = . ;
               } > bkram
       _top_of_heap = .;
}

