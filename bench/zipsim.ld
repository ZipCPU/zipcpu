/*******************************************************************************
*
* Filename:	zipsim.ld
*
* Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
*
* Purpose:	This script provides a description of the memory on the Arty,
*		for the purposes of where to place programs in memory during
*		linking.
*
* Creator:	Dan Gisselquist, Ph.D.
*		Gisselquist Technology, LLC
*
********************************************************************************
*
* Copyright (C) 2017, Gisselquist Technology, LLC
*
* This program is free software (firmware): you can redistribute it and/or
* modify it under the terms of  the GNU General Public License as published
* by the Free Software Foundation, either version 3 of the License, or (at
* your option) any later version.
*
* This program is distributed in the hope that it will be useful, but WITHOUT
* ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
* FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
* for more details.
* You should have received a copy of the GNU General Public License along
* with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
* target there if the PDF file isn't present.)  If not, see
* <http://www.gnu.org/licenses/> for a copy.
*
* License:	GPL, v3, as defined and found on www.gnu.org,
*		http://www.gnu.org/licenses/gpl.html
*
*
*******************************************************************************/

ENTRY(_start)

MEMORY
{
	flash  (rx) : ORIGIN = 0x1000000, LENGTH = 0x1000000 /* 2^24 = 16MB */
	sdram  (wx) : ORIGIN = 0x4000000, LENGTH = 0x4000000 /* 2^26 = 64MB */
}

_flash	= ORIGIN(flash);
_blkram	= 0;
_sdram	= ORIGIN(sdram);
_top_of_stack = ORIGIN(sdram) + LENGTH(sdram) - 4;

SECTIONS
{
	.rocode ORIGIN(flash) : {
		_boot_address = .;
		*(.start) *(.boot)
		} > flash
	_kernel_image_start = . ;
	_kernel_image_end = . ;
	_sdram_image_start = . ;
	.ramcode : {
		*(.kernel)
		*(.text.startup)
		*(.text)
		*(.rodata*) *(.strings)
		*(.data) *(COMMON)
		}> sdram AT> flash
	_sdram_image_end = . ;
	.bss : {
		*(.bss)
		_bss_image_end = . ;
		} > sdram
	_top_of_heap = .;
}
