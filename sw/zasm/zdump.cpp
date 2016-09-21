////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zdump.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	Disassemble machine code files onto the stdout file.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015, Gisselquist Technology, LLC
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
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
#include <stdio.h>
#include <unistd.h>
#include <ctype.h>

#include "zopcodes.h"

void	dump_file(const bool bigend, const char *fn) {
	const	int	NZIP = 4096;
	char	ln[NZIP], lb[NZIP];
	ZIPI	ibuf[NZIP];
	FILE	*fp;
	int	nr;
	int	addr=0x08000;

	fp = fopen(fn, "r");
	if (!fp)
		return;
	printf("%s:\n", fn);
	while((nr=fread(ibuf, sizeof(ZIPI), NZIP, fp))>0) {
		for(int i=0; i<nr; i++) {
			if (bigend) {
				ZIPI bei, lei = ibuf[i];
				bei  = lei&0x0ff; bei<<=8; lei>>= 8;
				bei |= lei&0x0ff; bei<<=8; lei>>= 8;
				bei |= lei&0x0ff; bei<<=8; lei>>= 8;
				bei |= lei&0x0ff;
				ibuf[i] = bei;
			}
			zipi_to_string(ibuf[i], ln, lb);
			// printf("%s\n", ln);
			printf("%08x: (0x%08x %c%c%c%c) %s\n", addr++,
				ibuf[i],
				isgraph((ibuf[i]>>24)&0x0ff)?((ibuf[i]>>24)&0x0ff) : '.',
				isgraph((ibuf[i]>>16)&0x0ff)?((ibuf[i]>>16)&0x0ff) : '.',
				isgraph((ibuf[i]>> 8)&0x0ff)?((ibuf[i]>> 8)&0x0ff) : '.',
				isgraph((ibuf[i]    )&0x0ff)?((ibuf[i]    )&0x0ff) : '.',
				ln);
			if (lb[0])
				printf("%28s%s\n", "", lb);
		}
	} fclose(fp);
}

int main(int argc, char **argv) {
	bool	bigend = false;
	for(int argn=1; argn<argc; argn++) {
		if (argv[argn][0] == '-') {
			if (argv[argn][1] == 'B')
				bigend = true;
			else if (argv[argn][1] == 'L')
				bigend = false;
		} else if(access(argv[argn], R_OK)==0)
			dump_file(bigend, argv[argn]);
	}

	return 0;
}

