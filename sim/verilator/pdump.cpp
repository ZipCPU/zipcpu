////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pdump.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	Disassemble machine code files onto the stdout file.  Unlike
//		the zdump program that is part of the assembler suite, this
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
#include <algorithm>
#include <stdio.h>
#include <unistd.h>
#include <ctype.h>

#include "zopcodes.h"

typedef	struct	{ unsigned clks, addr; } ALT;
bool	altcmp(const ALT &a, const ALT &b) {
	return a.clks < b.clks;
}

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <libelf.h>
#include <gelf.h>


bool	iself(const char *fname) {
	FILE	*fp;
	bool	ret = true;
	fp = fopen(fname, "rb");

	if (!fp)	return false;
	if (0x7f != fgetc(fp))	ret = false;
	if ('E'  != fgetc(fp))	ret = false;
	if ('L'  != fgetc(fp))	ret = false;
	if ('F'  != fgetc(fp))	ret = false;
	fclose(fp);
	return 	ret;

}


long	fgetwords(FILE *fp) {
	// Return the number of words in the current file, and return the 
	// file as though it had never been adjusted
	long	fpos, flen;
	fpos = ftell(fp);
	if (0 != fseek(fp, 0l, SEEK_END)) {
		fprintf(stderr, "ERR: Could not determine file size\n");
		perror("O/S Err:");
		exit(-2);
	} flen = ftell(fp);
	if (0 != fseek(fp, fpos, SEEK_SET)) {
		fprintf(stderr, "ERR: Could not seek on file\n");
		perror("O/S Err:");
		exit(-2);
	} flen /= sizeof(ZIPI);
	return flen;
}

class	SECTION {
public:
	unsigned	m_start, m_len;
	ZIPI		m_data[1];
};

SECTION	**singlesection(int nwords) {
	fprintf(stderr, "NWORDS = %d\n", nwords);
	size_t	sz = (2*(sizeof(SECTION)+sizeof(SECTION *))
		+(nwords-1)*(sizeof(ZIPI)));
	char	*d = (char *)malloc(sz);
	SECTION **r = (SECTION **)d;
	memset(r, 0, sz);
	r[0] = (SECTION *)(&d[2*sizeof(SECTION *)]);
	r[0]->m_len   = nwords;
	r[1] = (SECTION *)(&r[0]->m_data[r[0]->m_len]);
	r[0]->m_start = 0;
	r[1]->m_start = 0;
	r[1]->m_len   = 0;

	return r;
}

/*
SECTION **rawsection(const char *fname) {
	SECTION		**secpp, *secp;
	unsigned	num_words;
	FILE		*fp;
	int		nr;

	fp = fopen(fname, "r");
	if (fp == NULL) {
		fprintf(stderr, "Could not open: %s\n", fname);
		exit(-1);
	}

	if ((num_words=fgetwords(fp)) > MEMWORDS) {
		fprintf(stderr, "File overruns Block RAM\n");
		exit(-1);
	}
	secpp = singlesection(num_words);
	secp = secpp[0];
	secp->m_start = RAMBASE;
	secp->m_len = num_words;
	nr= fread(secp->m_data, sizeof(ZIPI), num_words, fp);
	if (nr != (int)num_words) {
		fprintf(stderr, "Could not read entire file\n");
		perror("O/S Err:");
		exit(-2);
	} assert(secpp[1]->m_len == 0);

	return secpp;
}*/

unsigned	byteswap(unsigned n) {
	unsigned	r;

	r = (n&0x0ff); n>>= 8;
	r = (r<<8) | (n&0x0ff); n>>= 8;
	r = (r<<8) | (n&0x0ff); n>>= 8;
	r = (r<<8) | (n&0x0ff); n>>= 8;

	return r;
}

void	elfread(const char *fname, unsigned &entry, SECTION **&sections) {
	Elf	*e;
	int	fd, i;
	size_t	n;
	char	*id;
	Elf_Kind	ek;
	GElf_Ehdr	ehdr;
	GElf_Phdr	phdr;
	const	bool	dbg = false;

	if (elf_version(EV_CURRENT) == EV_NONE) {
		fprintf(stderr, "ELF library initialization err, %s\n", elf_errmsg(-1));
		perror("O/S Err:");
		exit(EXIT_FAILURE);
	} if ((fd = open(fname, O_RDONLY, 0)) < 0) {
		fprintf(stderr, "Could not open %s\n", fname);
		perror("O/S Err:");
		exit(EXIT_FAILURE);
	} if ((e = elf_begin(fd, ELF_C_READ, NULL))==NULL) {
		fprintf(stderr, "Could not run elf_begin, %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	}

	ek = elf_kind(e);
	if (ek == ELF_K_ELF) {
		; // This is the kind of file we should expect
	} else if (ek == ELF_K_AR) {
		fprintf(stderr, "Cannot run an archive!\n");
		exit(EXIT_FAILURE);
	} else if (ek == ELF_K_NONE) {
		;
	} else {
		fprintf(stderr, "Unexpected ELF file kind!\n");
		exit(EXIT_FAILURE);
	}

	if (gelf_getehdr(e, &ehdr) == NULL) {
		fprintf(stderr, "getehdr() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if ((i=gelf_getclass(e)) == ELFCLASSNONE) {
		fprintf(stderr, "getclass() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if ((id = elf_getident(e, NULL)) == NULL) {
		fprintf(stderr, "getident() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	} if (i != ELFCLASS32) {
		fprintf(stderr, "This is a 64-bit ELF file, ZipCPU ELF files are all 32-bit\n");
		exit(EXIT_FAILURE);
	}

	if (dbg) {
	printf("    %-20s 0x%jx\n", "e_type", (uintmax_t)ehdr.e_type);
	printf("    %-20s 0x%jx\n", "e_machine", (uintmax_t)ehdr.e_machine);
	printf("    %-20s 0x%jx\n", "e_version", (uintmax_t)ehdr.e_version);
	printf("    %-20s 0x%jx\n", "e_entry", (uintmax_t)ehdr.e_entry);
	printf("    %-20s 0x%jx\n", "e_phoff", (uintmax_t)ehdr.e_phoff);
	printf("    %-20s 0x%jx\n", "e_shoff", (uintmax_t)ehdr.e_shoff);
	printf("    %-20s 0x%jx\n", "e_flags", (uintmax_t)ehdr.e_flags);
	printf("    %-20s 0x%jx\n", "e_ehsize", (uintmax_t)ehdr.e_ehsize);
	printf("    %-20s 0x%jx\n", "e_phentsize", (uintmax_t)ehdr.e_phentsize);
	printf("    %-20s 0x%jx\n", "e_shentsize", (uintmax_t)ehdr.e_shentsize);
	printf("\n");
	}


	// Check whether or not this is an ELF file for the ZipCPU ...
	if (ehdr.e_machine != 0x0dadd) {
		fprintf(stderr, "This is not a ZipCPU ELF file\n");
		exit(EXIT_FAILURE);
	}

	// Get our entry address
	entry = ehdr.e_entry;


	// Now, let's go look at the program header
	if (elf_getphdrnum(e, &n) != 0) {
		fprintf(stderr, "elf_getphdrnum() failed: %s\n", elf_errmsg(-1));
		exit(EXIT_FAILURE);
	}

	unsigned total_octets = 0, current_offset=0, current_section=0;
	for(i=0; i<(int)n; i++) {
		total_octets += sizeof(SECTION *)+sizeof(SECTION);

		if (gelf_getphdr(e, i, &phdr) != &phdr) {
			fprintf(stderr, "getphdr() failed: %s\n", elf_errmsg(-1));
			exit(EXIT_FAILURE);
		}

		if (dbg) {
		printf("    %-20s 0x%x\n", "p_type",   phdr.p_type);
		printf("    %-20s 0x%jx\n", "p_offset", phdr.p_offset);
		printf("    %-20s 0x%jx\n", "p_vaddr",  phdr.p_vaddr);
		printf("    %-20s 0x%jx\n", "p_paddr",  phdr.p_paddr);
		printf("    %-20s 0x%jx\n", "p_filesz", phdr.p_filesz);
		printf("    %-20s 0x%jx\n", "p_memsz",  phdr.p_memsz);
		printf("    %-20s 0x%x [", "p_flags",  phdr.p_flags);

		if (phdr.p_flags & PF_X)	printf(" Execute");
		if (phdr.p_flags & PF_R)	printf(" Read");
		if (phdr.p_flags & PF_W)	printf(" Write");
		printf("]\n");
		printf("    %-20s 0x%jx\n", "p_align", phdr.p_align);
		}

		total_octets += phdr.p_memsz;
	}

	char	*d = (char *)malloc(total_octets + sizeof(SECTION)+sizeof(SECTION *));
	memset(d, 0, total_octets);

	SECTION **r = sections = (SECTION **)d;
	current_offset = (n+1)*sizeof(SECTION *);
	current_section = 0;

	for(i=0; i<(int)n; i++) {
		r[i] = (SECTION *)(&d[current_offset]);

		if (gelf_getphdr(e, i, &phdr) != &phdr) {
			fprintf(stderr, "getphdr() failed: %s\n", elf_errmsg(-1));
			exit(EXIT_FAILURE);
		}

		if (dbg) {
		printf("    %-20s 0x%jx\n", "p_offset", phdr.p_offset);
		printf("    %-20s 0x%jx\n", "p_vaddr",  phdr.p_vaddr);
		printf("    %-20s 0x%jx\n", "p_paddr",  phdr.p_paddr);
		printf("    %-20s 0x%jx\n", "p_filesz", phdr.p_filesz);
		printf("    %-20s 0x%jx\n", "p_memsz",  phdr.p_memsz);
		printf("    %-20s 0x%x [", "p_flags",  phdr.p_flags);

		if (phdr.p_flags & PF_X)	printf(" Execute");
		if (phdr.p_flags & PF_R)	printf(" Read");
		if (phdr.p_flags & PF_W)	printf(" Write");
		printf("]\n");

		printf("    %-20s 0x%jx\n", "p_align", phdr.p_align);
		}

		current_section++;

		r[i]->m_start = phdr.p_vaddr;
		r[i]->m_len   = phdr.p_filesz/ sizeof(ZIPI);

		current_offset += phdr.p_memsz + sizeof(SECTION);

		// Now, let's read in our section ...
		if (lseek(fd, phdr.p_offset, SEEK_SET) < 0) {
			fprintf(stderr, "Could not seek to file position %08lx\n", phdr.p_offset);
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		} if (phdr.p_filesz > phdr.p_memsz)
			phdr.p_filesz = 0;
		if (read(fd, r[i]->m_data, phdr.p_filesz) != (int)phdr.p_filesz) {
			fprintf(stderr, "Didnt read entire section\n");
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}

		// Next, we need to byte swap it from big to little endian
		for(unsigned j=0; j<r[i]->m_len; j++)
			r[i]->m_data[j] = byteswap(r[i]->m_data[j]);

		if (dbg) for(unsigned j=0; j<r[i]->m_len; j++)
			fprintf(stderr, "ADR[%04x] = %08x\n", r[i]->m_start+j,
			r[i]->m_data[j]);
	}

	r[i] = (SECTION *)(&d[current_offset]);
	r[current_section]->m_start = 0;
	r[current_section]->m_len   = 0;

	elf_end(e);
	close(fd);
}

void	dump_file(const char *fn) {
	const	int	NZIP = 4096;
	char	lna[NZIP], lnb[NZIP];
	ZIPI	ibuf[NZIP];
	FILE	*fp, *pf;
	int	nr;
	unsigned	addr=0x0100000, mina = -1, maxa = 0,
			*pfcnt = NULL, *pfclk = NULL;

	pf = fopen("pfile.bin","rb");
	if (pf) {
		ALT	*pfalt;
		unsigned	buf[2], total_clks = 0;
		while(2 == fread(buf, sizeof(unsigned), 2, pf)) {
			if (mina > buf[0])
				mina = buf[0];
			if (maxa < buf[0])
				maxa = buf[0];
		}

		addr = mina;
		pfcnt = new unsigned[(maxa+2-mina)];
		pfclk = new unsigned[(maxa+2-mina)];
		pfalt = new ALT[(maxa+2-mina)];
		unsigned ncnt = maxa+2-mina;
		for(int i=0; i<(int)ncnt; i++)
			pfcnt[i] = pfclk[i] = 0;
		for(int i=0; i<(int)ncnt; i++)
			pfalt[i].addr = pfalt[i].clks = 0;

		rewind(pf);
		while(2 == fread(buf, sizeof(unsigned), 2, pf)) {
			pfcnt[buf[0]-addr]++;
			pfclk[buf[0]-addr] += buf[1];
			pfalt[buf[0]-addr].clks += buf[1];
			pfalt[buf[0]-addr].addr = buf[0];
			total_clks += buf[1];

			printf("%08x\n", buf[0]);
		} fclose(pf);

		printf("%08x (%8d) total clocks\n", total_clks, total_clks);

		std::sort(&pfalt[0], &pfalt[ncnt], altcmp);

		for(int i=0; i<(int)ncnt; i++)
			printf("%08x: %8d\n", pfalt[i].addr, pfalt[i].clks);
	}

	printf("%s:\n", fn);
	if (iself(fn)) {
		SECTION **secpp=NULL, *secp;
		unsigned entry;
		elfread(fn, entry, secpp);
		for(int i=0; secpp[i]->m_len; i++) {
			secp = secpp[i];
			for(unsigned j=0; j<secp->m_len; j++) {
				ZIPI	w = secp->m_data[j],a = secp->m_start+j;
				zipi_to_string(secp->m_data[j], lna, lnb);
				// printf("%s\n", ln);
				printf("%08x[%08x-%08x]: (0x%08x %c%c%c%c) ",
					secp->m_start+j, maxa, mina, w,
					isgraph((w>>24)&0x0ff)?((w>>24)&0x0ff) : '.',
					isgraph((w>>16)&0x0ff)?((w>>16)&0x0ff) : '.',
					isgraph((w>> 8)&0x0ff)?((w>> 8)&0x0ff) : '.',
					isgraph((w    )&0x0ff)?((w    )&0x0ff) : '.'
					);
				if ((a>=mina)&&(a<maxa)&&(pfcnt))
					printf("%8d %8d ", pfcnt[a-mina], pfclk[a-mina]);
				printf("%s\n", lna);
				if (lnb[0])
					printf("%26s%s\n", "", lnb);
			}
		}
	} else {
		fp = fopen(fn, "r");
		if (!fp)
			return;

		while((nr=fread(ibuf, sizeof(ZIPI), NZIP, fp))>0) {
			for(int i=0; i<nr; i++) {
				zipi_to_string(ibuf[i], lna, lnb);
				// printf("%s\n", ln);
				printf("%08x[%08x-%08x]: (0x%08x %c%c%c%c) ", addr,
					maxa, mina,
					ibuf[i],
					isgraph((ibuf[i]>>24)&0x0ff)?((ibuf[i]>>24)&0x0ff) : '.',
					isgraph((ibuf[i]>>16)&0x0ff)?((ibuf[i]>>16)&0x0ff) : '.',
					isgraph((ibuf[i]>> 8)&0x0ff)?((ibuf[i]>> 8)&0x0ff) : '.',
					isgraph((ibuf[i]    )&0x0ff)?((ibuf[i]    )&0x0ff) : '.'
					);
				if ((addr>=mina)&&(addr<maxa)&&(pfcnt))
					printf("%8d %8d ", pfcnt[addr-mina], pfclk[addr-mina]);
				printf("%s\n", lna);
				if (lnb[0])
					printf("%26s%s\n", "", lnb);

				addr++;
			} if (nr < NZIP)
				break;
		} fclose(fp);
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

