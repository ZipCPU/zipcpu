////////////////////////////////////////////////////////////////////////////////
//
// Filename:	helloworld.c
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	The original Helllo World program.  If everything works, this
//		will print Hello World to the UART, and then halt the CPU--if
//	run with no O/S.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <stdio.h>

int main(int argc, char **argv) {
	printf("Hello, World!\r\n");
	return 0;
}

