////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/zipsw/zlib/crt0.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To start a program from flash, loading its various components
//		into on-chip block RAM, or off-chip DDR3 SDRAM, as indicated
//	by the symbols/pointers within the program itself.  As you will notice
//	by the names of the symbols, it is assumed that a kernel will be placed
//	into block RAM.
//
//	This particular implementation depends upon the following symbols
//	being defined:
//
//	int main(int argc, char **argv)
//		The location where your program will start from, once fully
//		loaded.  argc will always be set to zero, and ARGV to a pointer
//		to zero.
//
//	_top_of_stack:
//		A pointer to a location in memory which we can use for a stack.
//		The bootloader doesn't use much of this memory, although it does
//		use it.  It then resets the stack to this location and calls
//		your program.
//
//	_top_of_heap:
//		While not used by this program, this is assumed to be defined
//		by the linker as the lowest memory address in a space that can
//		be used by a malloc/free restore capability.
//
//	_rom:
//		The address of the beginning of a physical ROM device--often
//		a SPI flash device.  This is not the necessariliy the first
//		usable address on that device, as that is often reserved for
//		the first two FPGA configurations.
//
//		If no ROM device is present, set _rom=0 and the bootloader
//		will quietly and silently return.
//
//	_kram:
//		The first address of a fast RAM device (if present).  I'm
//		calling this device "Kernel-RAM", because (if present) it is
//		a great place to put kernel code.
//
//		if _kram == 0, no memory will be mapped to kernel RAM.
//
//	_ram:
//		The main RAM device of the system.  This is often the address
//		of the beginning of physical SDRAM, if SDRAM is present.
//
//	_kram_start:
//		The address of that location within _rom where the sections
//		needing to be moved begin at.
//
//	_kram_end:
//		The last address within the _kram device that needs to be
//		filled in.
//
//	_ram_image_start:
//		This address is more confusing.  This is equal to one past the
//		last used block RAM address, or the last used flash address if
//		no block RAM is used.  It is used for determining whether or not
//		block RAM was used at all.
//
//	_ram_image_end:
//		This is one past the last address in SDRAM that needs to be
//		set with valid data.
//
//		This pointer is made even more confusing by the fact that,
//		if there is nothing allocated in SDRAM, this pointer will
//		still point to block RAM.  To make matters worse, the MAP
//		file won't match the pointer in memory.  (I spent three days
//		trying to chase this down, and came up empty.  Basically,
//		the BFD structures may set this to point to block RAM, whereas
//		the MAP--which uses different data and different methods of
//		computation--may leave this pointing to SDRAM.  Go figure.)
//
//	_bss_image_end:
//		This is the last address of memory that must be cleared upon
//		startup, for which the program is assuming that it is zero.
//		While it may not be necessary to clear the BSS memory, since
//		BSS memory is always zero on power up, this bootloader does so
//		anyway--since we might be starting from a reset instead of power
//		up.
//
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2023, Gisselquist Technology, LLC
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
#include "zipcpu.h"
#include "board.h"		// Our current board support file
#include "bootloader.h"
#include "zipsys.h"

// USE_DMA
// {{{
// A bootloader is about nothing more than copying memory from a couple
// particular locations (Flash/ROM) to other locations in memory (BLKRAM
// and SDRAM).  Our DMA is a hardware accelerator that does nothing but
// copy memory from one location to another.  Why not use the DMA for this
// purpose then?
//
// Here, we have a USE_DMA #define.  When this is defined, the memory copy
// will be done using the DMA hardware accelerator.  This is a good thing,
// and this should be defined.  There are two problems with defining this
// however: 1) It obscures for any readers of this code what is actually
// happening, and 2) it makes the code dependent upon yet another piece of the
// hardware design working.  For these reasons, we allow you to turn it off.
// }}}
#ifdef _HAVE_ZIPSYS_DMA
#define	USE_DMA
#endif

//
// _start: (Assembly routine)
// {{{
// Notes:
// {{{
// Every computer needs to start processing from somewhere on reboot, and every
// program needs some entry point.  For the ZipCPU, that starting place is the
// routine with the _start symbol.  It is important that this start symbol be
// placed at the boot address for the CPU.  This is the very first address of
// program memory, and (currently) on the Arty board it is placed in Flash at
// _start = 0x4e0000.  To make certain this routine goes into the very first
// address in flash, we place it into it's own special section, the .start
// section, and then tell the linker that the .start section is the first
// section where it needs to start placing code.
//
// If you read through this short assembly routine below, you'll find that it
// does only a small number of tasks.  It sets the stack pointer to point to
// the top of the stack (a symbol defined in the linker file), calls the 
// bootloader, resets the stack pointer, clears any data cache, and then calls
// the kernel entry function.  It also sets up a return address for the kernel
// entry function so that, should the kernel ever exit, it wouldn't exit on 
// any error but rather it would exit by halting the CPU.
// }}}
asm("\t.section\t.start,\"ax\",@progbits\n"
	"\t.global\t_start\n"
"_start:"	"\t; Here's the global ZipCPU entry point upon reset/reboot\n"
	"\t; First step, clear all registers.  This is primarily to deal with\n"
	"\t; potential x values within these registers when running under a\n"
	"\t; simulator, and isn't truly necessary in other cases.\n"
	"\tLDI\t0,R0\n"
	"\tLDI\t0,R1\n"
	"\tLDI\t0,R2\n"
	"\tLDI\t0,R3\n"
	"\tLDI\t0,R4\n"
	"\tLDI\t0,R5\n"
	"\tLDI\t0,R6\n"
	"\tLDI\t0,R7\n"
	"\tLDI\t0,R8\n"
	"\tLDI\t0,R9\n"
	"\tLDI\t0,R10\n"
	"\tLDI\t0,R11\n"
	"\tLDI\t0,R12\n"
	"\tLDI\t_top_of_stack,SP"	"\t; Set up our supervisor stack ptr\n"
	"\tLDI\t0,CC\n"
	"\tMOV\t_kernel_is_dead(PC),uPC" "\t; Set user PC pointer to somewhere valid\n"
	"\tMOV\tR0,uR0\n"
	"\tMOV\tR0,uR1\n"
	"\tMOV\tR0,uR2\n"
	"\tMOV\tR0,uR3\n"
	"\tMOV\tR0,uR4\n"
	"\tMOV\tR0,uR5\n"
	"\tMOV\tR0,uR6\n"
	"\tMOV\tR0,uR7\n"
	"\tMOV\tR0,uR8\n"
	"\tMOV\tR0,uR9\n"
	"\tMOV\tR0,uR10\n"
	"\tMOV\tR0,uR11\n"
	"\tMOV\tR0,uR12\n"
	"\tMOV\tR0,uSP\n"
	"\tMOV\tR0,uCC\n"
#ifndef	SKIP_BOOTLOADER
	"\tMOV\t_after_bootloader(PC),R0" " ; JSR to the bootloader routine\n"
	"\tBRA\t_bootloader\n"
"_after_bootloader:\n"
	"\tLDI\t_top_of_stack,SP"	"\t; Set up our supervisor stack ptr\n"
	"\tOR\t0xc000,CC"		"\t; Clear the cache\n"
#endif
#ifdef	__USE_INIT_FINIT
	"\tJSR\tinit"		"\t; Initialize any constructor code\n"
	//
	"\tLDI\tfini,R1"	"\t; \n"
	"\tJSR\t_atexit"	"\t; Initialize any constructor code\n"
#endif
	//
	"\tCLR\tR1"			"\t; argc = 0\n"
	"\tMOV\t_argv(PC),R2"		"\t; argv = &0\n"
	"\tLDI\t__env,R3"		"\t; env = NULL\n"
	"\tJSR\tmain"		"\t; Call the user main() function\n"
	//
"_graceful_kernel_exit:"	"\t; Halt on any return from main--gracefully\n"
	"\tJSR\texit\n"	"\t; Call the _exit as part of exiting\n"
"\t.global\t_hw_shutdown\n"
"_hw_shutdown:\n"
	"\tNEXIT\tR1\n"		"\t; If in simulation, call an exit function\n"
"_kernel_is_dead:"		"\t; Halt the CPU\n"
	"\tHALT\n"		"\t; We should *never* continue following a\n"
	"\tBRA\t_kernel_is_dead" "\t; halt, do something useful if so ??\n"
"_argv:\n"
	"\t.WORD\t0,0\n"
	"\t.section\t.text");
// }}}

// extern _bootloader
// {{{
// We need to insist that the bootloader be kept in Flash, else it would depend
// upon running a routine from memory that ... wasn't in memory yet.  For this
// purpose, we place the bootloader in a special .boot section.  We'll also tell
// the linker, via the linker script, that this .boot section needs to be placed
// into flash.
// }}}
extern	void	_bootloader(void) __attribute__ ((section (".boot")));

//
// bootloader()
// {{{
// Here's the actual boot loader itself.  It copies three areas from flash:
//	1. An area from flash to block RAM
//	2. A second area from flash to SDRAM
//	3. The third area isn't copied from flash, but rather it is just set to
//		zero.  This is sometimes called the BSS segment.
//
#ifndef	SKIP_BOOTLOADER
// NOTNULL(A)
// {{{
// Several comparisons below look like: if (_ram != NULL) or even
// if (_ram == NULL).  The problem is that, in order to optimize linking, we've
// defined _ram as something like: unsigned _ram[1];  This means that GCC
// believes space is actually allocated for _ram somewhere (by the linker), but
// just doesn't know where.  Hence, GCC will optimize these comparisons away,
// since it knows they cannot be NULL.  The macro below helps to return the
// comparison back to what it should be--getting GCC out of the way in the
// process.  It's an ugly hack, but it works.
#define	NOTNULL(A)	(4 != (unsigned)&A[1])
// }}}
void	_bootloader(void) {
	// NSTR("BOOTLOADER");
	int *ramend = _ram_image_end, *bsend = _bss_image_end;

	if (!NOTNULL(_rom)) {
		// No ROM present
		// {{{
		// In this case, we have the least to do: an external loader
		// has already been responsible for loading us into memory.
		// All that's then required is simply to zero out the BSS
		// segment and start.  This can be done either with (or without)
		// the DMA.  If you want to understand how this routine
		// works, check out the non-DMA section
#ifdef	USE_DMA
		// NSTR("No-ROM");
		//
		// Clear the DMA from anything it might've been doing prior
		// to the CPU reset that brought us here.
		//
		_zip->z_dma.d_ctrl= DMACLEAR;
		if (bsend != ramend) {
			volatile int	zero = 0;

			// NSTR("BSS");
			_zip->z_pic = SYSINT_DMAC;
			_zip->z_dma.d_len = bsend - ramend;
			_zip->z_dma.d_rd  = (char *)&zero;
			_zip->z_dma.d_wr  = (char *)ramend;
			_zip->z_dma.d_ctrl = DMACCOPY|DMA_CONSTSRC;

// _zipscope->s_ctrl = 0x88000040;
			while((_zip->z_pic & SYSINT_DMAC)==0)
				;
		} CLEAR_CACHE;
#else	// USE_DMA
		int	*wrp = _ram_image_end;
		while(wrp < _bss_image_end)
			*wrp++ = 0;
#endif	// USE_DMA
		return;
		// }}}
	}

	int *kramdev = (_kram) ? _kram : _ram;

	// Okay, we have ROM present.  We need to copy our instructions and
	// data from the ROM to a designated RAM area.  Indeed, we allow two
	// designated RAM areas: kernel (fast) and normal RAM.  Once done,
	// we zero out the BSS segment.  This can be done with or without the
	// DMA
#ifdef	USE_DMA
	// {{{
	// Disable and clear all interrupts
	_zip->z_pic = CLEARPIC;
	// NSTR("DMA");
	_zip->z_dma.d_ctrl= DMACLEAR;

	// Copy to Kernel RAM
	// {{{
	if (NOTNULL(_kram)) {
		_zip->z_dma.d_rd  = (char *)_kram_start; // Flash memory ptr
		_zip->z_dma.d_wr  = (char *)((_kram) ? _kram : _ram);
		if (_kram_start != _kram_end) {
			// NSTR("KRAM");
			_zip->z_pic = SYSINT_DMAC;
			_zip->z_dma.d_len = 4*(_kram_end - _kram);
			_zip->z_dma.d_wr  = (char *)_kram;
			_zip->z_dma.d_ctrl= DMACCOPY;

			while((_zip->z_pic & SYSINT_DMAC)==0)
				;
		}
	} else {
		// NSTR("No-KRAM");
		// Continue writing to the RAM device from where we left off
		_zip->z_dma.d_rd = (char *)_ram_image_start; // ROM (flash) memory
	}
	// }}}

	// Copy to external or regular RAM
	// {{{
	_zip->z_dma.d_wr = (char *)_ram;
	_zip->z_dma.d_len = 4*(ramend - _ram);
	if (_zip->z_dma.d_len>0) {
		// NSTR("RAM");
		_zip->z_pic = SYSINT_DMAC;
		_zip->z_dma.d_ctrl= DMACCOPY;

		while((_zip->z_pic & SYSINT_DMAC)==0)
			;
	}
	// }}}

	// Zero out the BSS segment
	// {{{
	if (bsend != ramend) {
		volatile int	zero = 0;

		// NSTR("BSS");
		_zip->z_pic = SYSINT_DMAC;
		_zip->z_dma.d_len = 4*(bsend - ramend);
		_zip->z_dma.d_rd  = (char *)&zero;
		// _zip->z_dma.wr // Keeps the same value
		_zip->z_dma.d_ctrl = DMACCOPY|DMA_CONSTSRC|DMA_SRCWORD;

		while((_zip->z_pic & SYSINT_DMAC)==0)
			;
	}
	// }}}

	CLEAR_CACHE;
	// Disable and clear all interrupts
	_zip->z_pic = CLEARPIC;
	// }}}
#else
	// {{{
	int	*rdp = _kram_start, *wrp;
	// NSTR("Not using DMA");

	// Copy to Kernel RAM
	// {{{
	if (NOTNULL(_kram))
		wrp = _kram;
	else
		wrp = _ram;
	// Load any part of the image into kernel RAM (i.e. fast or block RAM),
	// but *only* if there's a block RAM section in the image.  Based upon
	// our LD script, the block RAM should be filled from _blkram to
	// _kernel_image_end.  It starts at _kram_start --- our last valid
	// address within the flash address region.
	//
	if (_kram_end != _kram_start) {	// The memory copy
		// NSTR("KRAM");
		while(wrp < _kram_end)
			*wrp++ = *rdp++;
	}
	// }}}

	// If there's a separate RAM section, then we'll switch to writing into
	// it next.  If not, we'll continue writing from where we left off in
	// kernel RAM.
	if (NOTNULL(_ram))
		wrp  = _ram;

	// Copy to external or regular RAM
	// {{{
	// Now, we move on to the SDRAM image.  We'll here load into SDRAM
	// memory up to the end of the SDRAM image, _sdram_image_end.
	// As with the last pointer, this one is also created for us by the
	// linker.
	// 
	// while(wrp < sdend)	// Could also be done this way ...
	// NSTR("RAM");
	for(int i=0; i< ramend - _ram; i++)
		*wrp++ = *rdp++;
	// }}}

	// Zero out the BSS segment
	// {{{
	// Finally, we load BSS.  This is the segment that only needs to be
	// cleared to zero.  It is available for global variables, but some
	// initialization is expected within it.  We start writing where
	// the valid SDRAM context, i.e. the non-zero contents, end.
	//
	// NSTR("BSS");
	for(int i=0; i<bsend - ramend; i++)
		*wrp++ = 0;
	// }}}
	// }}}
#endif	// USE_DMA
	// NSTR("Bootloader complete");
}
#endif	// SKIP_BOOTLOADER
// }}}

