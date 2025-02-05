////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/verilator/mkhex.cpp
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Take a file mapped to SDRAM, and create a hexfile that can
//		be automatically loaded into the memory.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2025, Gisselquist Technology, LLC
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
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "zipelf.h"
#include "byteswap.h"

#define	MEMBASE	0x04000000
#define	MEMLEN	0x04000000

int	nextlg(unsigned vl) {
	// {{{
	int		nb = 0;
	unsigned	r;

	for(r=1; r<vl && nb < 32; r<<=1)
		nb++;
	return nb;
}
// }}}

void	usage(void) {
	// {{{
	printf("USAGE: mkfile [-hv] <zip-program-file>\n");
	printf("\n"
"\t-h\tDisplay this usage statement\n"
"\t-v\tDisplays some verbose messaging on stderr\n"
"\nThis program will produce a hex file suitable for using with memdev\n"
"as a boot ROM\n");
}
// }}}

int main(int argc, char **argv) {
	// {{{
	int		skp=0;
	bool		verbose = false;
	unsigned	entry = 0, buswidth=32;
	const char	*execfile = NULL;
	char		*hexname = NULL;
	ELFSECTION	**secpp = NULL, *secp;
	unsigned	wraddr = MEMBASE, endaddr = MEMBASE;
	FILE		*fpimg;

	if (argc < 2) {
		usage();
		exit(EXIT_SUCCESS);
	}

	skp=1;
	for(int argn=0; argn<argc-skp; argn++) {
		if (argv[argn+skp][0] == '-') {
			switch(argv[argn+skp][1]) {
			case 'h':
				usage();
				exit(EXIT_SUCCESS);
				break;
			case 'o':
				hexname = strdup(argv[argn+skp+1]);
				skp++;
				break;
			case 'v':
				verbose = true;
				break;
			case 'w':
				buswidth = atoi(argv[argn+skp+1]);
				skp++;
				break;
			default:
				fprintf(stderr, "Unknown option, -%c\n\n",
					argv[argn+skp][0]);
				usage();
				exit(EXIT_FAILURE);
				break;
			} skp++; argn--;
		} else {
			// Anything here must be either the program to load,
			// or a bit file to load
			argv[argn] = argv[argn+skp];
		}
	} argc -= skp;


	for(int argn=0; argn<argc; argn++) {
		if (iself(argv[argn])) {
			if (execfile) {
				printf("Too many executable files given, %s and %s\n", execfile, argv[argn]);
				usage();
				exit(EXIT_FAILURE);
			} execfile = argv[argn];
		} else { // if (isbitfile(argv[argn]))
			printf("Unknown file name or too many files, %s\n", argv[argn]);
			usage();
			exit(EXIT_FAILURE);
		}
	}

	if (execfile == NULL) {
		printf("No executable file given!\n\n");
		usage();
		exit(EXIT_FAILURE);
	}

	if ((execfile)&&(access(execfile,R_OK)!=0)) {
		// If there's no code file, or the code file cannot be opened
		fprintf(stderr, "Cannot open executable, %s\n", execfile);
		exit(EXIT_FAILURE);
	}

	const char *codef = (argc>0)?argv[0]:NULL;

	if (verbose)
		fprintf(stderr, "MkHex: Verbose mode on\n");


	if(iself(execfile)) {
		// zip-readelf will help with both of these ...
		elfread(codef, entry, secpp);
	} else {
		fprintf(stderr, "ERR: %s is not in ELF format\n", codef);
		exit(EXIT_FAILURE);
	}

	if (hexname == NULL || hexname[0] == '\0') {
		hexname = new char[strlen(execfile)+5];
		strcpy(hexname, execfile);
		strcat(hexname, ".hex");
	}

	// printf("Reading: %s\n", codef);
	// assert(secpp[1]->m_len = 0);
	for(int i=0; secpp[i]->m_len; i++) {
		bool	valid = false;
		secp=  secpp[i];

		if ((secp->m_start >= MEMBASE)
			&&(secp->m_start+secp->m_len <= MEMBASE+MEMLEN))
			valid = true;

		if (valid && secp->m_start+secp->m_len > endaddr)
			endaddr = secp->m_start+secp->m_len;

		if (!valid) {
			fprintf(stderr, "WARNING: No such memory will be loaded: 0x%08x - %08x\n",
				secp->m_start, secp->m_start+secp->m_len);
			exit(EXIT_FAILURE);
		}
	}

	unsigned	memsz = endaddr - wraddr;
	char		*memimg;

	// Round up to the nearest bus word
	if (memsz & (buswidth/8 - 1))
		memsz += (buswidth/8);
	memsz &= ~(buswidth/8 - 1);

	// Allocate some memory to work with
	memimg = new char[memsz];

	for(int i=0; secpp[i]->m_len; i++) {
		secp = secpp[i];

		if ((secp->m_start < MEMBASE)
				||(secp->m_start+secp->m_len > MEMBASE+MEMLEN))
			continue;

		memcpy(&memimg[secp->m_start-MEMBASE],
			secp->m_data, secp->m_len);
	}

	fpimg = fopen(hexname, "wb");
	unsigned	lineln = 0;
	for(unsigned pos=0; pos<memsz; pos+=buswidth/8) {
		for(unsigned sub=0; sub<buswidth/8; sub++) {
			fprintf(fpimg, "%02x", memimg[pos+sub] & 0x0ff);
			lineln += 2;
		}

		if (lineln + (buswidth/8) > 64) {
			fprintf(fpimg, "\n");
			lineln = 0;
		} else {
			fprintf(fpimg, " ");
			lineln ++;
		}
	}


	fclose(fpimg);
	return EXIT_SUCCESS;
}
// }}}

