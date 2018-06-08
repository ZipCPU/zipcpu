////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pdump.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Disassemble machine code files onto the stdout file.  Unlike
//		the zip-objdump program that is part of the binutils suite, this
//	program takes the pfile.bin output of the bench test suite and adds
//	profiling information to the output.  It's useful for finding out where,
//	at least in simulation, your time is being spent.  It can also be used,
//	after the fact, to get a trace of what instructions the CPU executed.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include <algorithm>
#include <map>
#include <stdio.h>
#include <unistd.h>
#include <ctype.h>

#include "zipelf.h"
#include "zopcodes.h"
#include "byteswap.h"

typedef	uint32_t	ZIPI;	// A ZipCPU instruction word

typedef	struct	{ unsigned clks, addr; } ALT;
bool	altcmp(const ALT &a, const ALT &b) {
	return a.clks < b.clks;
}

typedef	struct { unsigned clks, hits, addr; } insn_stat;

typedef	std::map<unsigned, insn_stat *> vcd_profile;

void	dump_file(const char *fn) {
	const	int	NZIP = 4096;
	char	lna[NZIP], lnb[NZIP];
	FILE	*pf;
	unsigned	addr=0x0100000;
	vcd_profile	vp;

	pf = fopen("pfile.bin","rb");
	if (pf) {
		unsigned	buf[2];
		while(2 == fread(buf, sizeof(unsigned), 2, pf)) {
			addr = buf[0];
			if (vp.count(addr)>0) {
				vp[addr]->hits++;
				vp[addr]->clks += buf[1];
			} else {
				insn_stat	*is;

				is = new insn_stat;
				is->hits = 1;
				is->clks = buf[1];
				is->addr = addr;
				vp[addr] = is;
			}
		}
	}

	printf("%s:\n", fn);
	if (iself(fn)) {
		ELFSECTION **secpp=NULL, *secp;
		double		cpi;
		unsigned	entry;

		elfread(fn, entry, secpp);
		for(int i=0; secpp[i]->m_len; i++) {
			secp = secpp[i];
			for(unsigned j=0; j<secp->m_len; j+=4) {
				uint32_t	w, a;

				a = secp->m_vaddr+j;
				w = buildword((const unsigned char *)&secp->m_data[j]);
				zipi_to_double_string(a, w, lna, lnb);
				// printf("%s\n", ln);
				printf("%08x: (0x%08x %c%c%c%c) ", a, w,
					isgraph((w>>24)&0x0ff)?((w>>24)&0x0ff) : '.',
					isgraph((w>>16)&0x0ff)?((w>>16)&0x0ff) : '.',
					isgraph((w>> 8)&0x0ff)?((w>> 8)&0x0ff) : '.',
					isgraph((w    )&0x0ff)?((w    )&0x0ff) : '.'
					);
				if (vp.count(a)>0) {
					insn_stat *is = vp[a];
					cpi = is->clks / (double)is->hits;

					printf("%8d %8d %4.1f ", is->hits, is->clks, cpi);
				} else
					printf("%23s", "");

				printf("%s\n", lna);
				if (lnb[0])
					printf("-%50s%s\n", "", lnb);
			}
		}
	}
}

int main(int argc, char **argv) {
	if (argc <= 1)
		printf("USAGE: pdump <dump-file> | less\n");
	for(int argn=1; argn<argc; argn++) {
		if(access(argv[argn], R_OK)==0)
			dump_file(argv[argn]);
	}

	return 0;
}

