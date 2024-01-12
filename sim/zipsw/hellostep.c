////////////////////////////////////////////////////////////////////////////////
//
// Filename:	hellostep.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a modified version of the original hello world.  As
//		with the original, if all goes well this program will print
//	Hello World to the UART, and then halt the CPU.  Behind the scenes,
//	what makes this program special is that the supervisor is stepping
//	through the Hello World program, one instruction at a time.  Thus, this
//	program is a test of the ZipCPU's stepping capabilities.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
#include <stdio.h>
#include "zipcpu.h"
#include "txfns.h"

void user_main(void) {
	printf("Hello, World!\n");
	zip_syscall();
}

int main(int argc, char **argv) {
	int		done = 0, success = 1;
	unsigned	user_regs[16];
	unsigned	user_stack[512];

	for(unsigned k=0; k<16; k++)
		user_regs[k] = 0;
	user_regs[15] = (unsigned)user_main;
	user_regs[14] = CC_STEP;
	user_regs[13] = (unsigned)&user_stack[512];
	zip_restore_context(user_regs);

	while(!done) {
		unsigned	ucc;

		zip_rtu();

		ucc = zip_ucc();
		if (ucc & CC_EXCEPTION) {
			txstr("\r\nEXCEPTION: CC = ");txhex(ucc); txstr("\r\n");
			txstr("\r\n");
			while((_uart->u_fifo & 0x010000) == 0)
				;
			done = 1;
			success = 0;
		} if (ucc & CC_TRAP)
			done = 1;
		else if ((ucc & CC_STEP) == 0) {
			success = 0;
			txstr("\r\nCC & STEP == 0 ?? CC = "); txhex(ucc);
			txstr("\r\n");
			while((_uart->u_fifo & 0x010000) == 0)
				;
		}
	}

	if (success)
		txstr("\r\n\r\nSUCCESS!\r\n");
}
