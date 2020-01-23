////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zsim.cpp
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	The main portion of a Simulator, not based upon any RTL or
//		Verilog code.  Why?  To get something up and running and testing
//	faster (even though the Verilog should be working/running?).
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <vector>
#include <ctype.h>
#include "twoc.h"
#include "zipelf.h"

#define	CC_CLRCACHE	(1<<14)
#define	CC_PHASE_BIT	(1<<13)
#define	CC_PHASE	(1<<13)
#define	CC_FPUERR	(1<<12)
#define	CC_DIVERR	(1<<11)
#define	CC_BUSERR	(1<<10)
#define	CC_TRAP		(1<<9)
#define	CC_ILL		(1<<8)
#define	CC_BREAK	(1<<7)
#define	CC_STEP		(1<<6)
#define	CC_GIE		(1<<5)
#define	CC_SLEEP	(1<<4)
#define	CC_V		(1<<3)
#define	CC_N		(1<<2)
#define	CC_C		(1<<1)
#define	CC_Z		(1   )

class	SIMDEV {
public:
	virtual	uint32_t	lw(uint32_t addr) = 0;
	virtual void	sw(uint32_t addr, uint32_t vl) = 0;

	virtual	uint32_t	lb(uint32_t addr) {
		uint32_t v = lw(addr&-4);

		// fprintf(stderr, "\tLH(%08x) -> %08x", addr, v);
		v >>= (8*(3-(addr&3)));
		// fprintf(stderr, " -> %08x", v);
		v &= 0x0ff;
		// fprintf(stderr, " -> %02x\n", v);
		return v;
	}
	virtual	uint32_t	lh(uint32_t addr) {
		uint32_t v = lw(addr&-4);

		// fprintf(stderr, "\tLH(%08x) -> %08x", addr, v);
		if ((addr&2)==0)
			v >>= 16;
		// fprintf(stderr, " -> %08x", v);
		v &= 0x0ffff;
		// fprintf(stderr, " -> %04x\n", v);
		return v;
	}

	virtual void sh(uint32_t addr, uint32_t vl) {
		uint32_t v = (vl & 0x0ffff);
		v = v | (v<<16);
		sw(addr, v);
	}

	virtual void sb(uint32_t addr, uint32_t vl) {
		uint32_t v = (vl & 0x0ff);
		v = v | (v<<16);
		v = v | (v<<8);
		sw(addr, v);
	}

	virtual	bool	interrupt(void) { return false; };
	virtual	void	tick(void) {};

	virtual	void	load(uint32_t addr, const char *buf, size_t ln) {}
};

class	UARTDEV : public SIMDEV {
	uint32_t	m_setup;
	bool		m_debug;
public:
	UARTDEV(void) { m_setup = 868; m_debug = false; }

	virtual	uint32_t	lw(uint32_t addr) {
		switch(addr&0x0c) {
		case  0: return m_setup;
		case  4: return 0;
		case  8: return 0x100;
		case 12: return 0;
		} return 0;
	}
		
	virtual void sw(uint32_t addr, uint32_t vl) {
		if (m_debug) fprintf(stderr,
			"UART->SW(%08x, %08x)\n", addr, vl);
		switch(addr&0x0c) {
		case  0: m_setup = vl & 0x3fffffff; break;
		case  4: break;
		case  8: break;
		case 12: putchar(vl & 0x0ff);
		}
	}
};


class	MEMDEV : public SIMDEV {
protected:
	char	*m_mem;
	bool	m_dbg;
public:
	MEMDEV(int nbits) {
		m_mem = new char[(1<<nbits)];
		m_dbg = false;
	}

	virtual	uint32_t	lw(uint32_t addr) {
		unsigned char	a, b, c, d;
		uint32_t	v;

		a = m_mem[addr];
		b = m_mem[addr+1];
		c = m_mem[addr+2];
		d = m_mem[addr+3];
		v = (a<<24)|(b<<16)|(c<<8)|d;

		if (m_dbg) fprintf(stderr,
			"\tReading %08x -> %02x:%02x:%02x:%02x -> v=%08x\n", addr,
			a, b, c, d, v);

		return v;
	}

	virtual void sw(uint32_t addr, uint32_t vl) {
		uint32_t maddr = addr & -4;
		m_mem[(maddr)  ] = (vl >>24)&0x0ff;
		m_mem[(maddr)+1] = (vl >>16)&0x0ff;
		m_mem[(maddr)+2] = (vl >> 8)&0x0ff;
		m_mem[(maddr)+3] = (vl     )&0x0ff;

		if (m_dbg)
			fprintf(stderr,
				"\tSW %08x <- %08x - %02x:%02x:%02x:%02x\n",
				addr, vl, m_mem[(maddr)  ] & 0x0ff,
				m_mem[(maddr)+1] & 0x0ff,
				m_mem[(maddr)+2] & 0x0ff,
				m_mem[(maddr)+3] & 0x0ff);
	}

	virtual void sh(uint32_t addr, uint32_t vl) {
		uint32_t maddr = addr & -2;
		m_mem[(maddr)  ] = (vl >> 8)&0x0ff;
		m_mem[(maddr)+1] = (vl     )&0x0ff;
		if (m_dbg)
			fprintf(stderr, "\tSH %08x <- %04x - %02x:%02x\n",
				addr, vl & 0x0ffff, m_mem[(maddr)  ] & 0x0ff,
				m_mem[(maddr)+1] & 0x0ff);
	}

	virtual void sb(uint32_t addr, uint32_t vl) {
		m_mem[addr] = vl;
		if (m_dbg)
			fprintf(stderr, "\tSB %08x <- %02x\n",
				addr, vl & 0x0ff);
	}

	void	load(uint32_t addr, const char *src, size_t n) {
		memcpy(&m_mem[addr], src, n);
	}
};

class	ROMDEV : public MEMDEV {
public:
	ROMDEV(int nbits) : MEMDEV(nbits) {}

	// virtual	uint32_t	lw(uint32_t addr);
	virtual	void	sw(uint32_t addr, uint32_t vl) {}
	virtual	void	sh(uint32_t addr, uint32_t vl) {}
	virtual	void	sb(uint32_t addr, uint32_t vl) {}
	void	load(uint32_t addr, const char *src, size_t n) {
		memcpy(&m_mem[addr], src, n);
	}
};

#ifndef	L_OK
#define	L_OK	8	// Okay for loads
#endif

class	SIMENTRY {
public:
	SIMDEV	*m_dev;
	uint32_t m_addr, m_mask;
	int	m_flags;
	char	*m_name;
};

class	SIMBUS {
	bool	m_buserr;
	std::vector<SIMENTRY *>	m_devlist;
	int	getdev(uint32_t addr) {
		for(size_t i=0; i<m_devlist.size(); i++)
			if ((addr&m_devlist[i]->m_mask)==m_devlist[i]->m_addr){
				return i;
		}

		/*
		fprintf(stderr, "GETDEV(0x%08x) - not found\n", addr);
		for(size_t i=0; i<m_devlist.size(); i++) {
			fprintf(stderr, "ADDR(0x%08x) & 0x%08x = %08x != %08x\n",
				addr, m_devlist[i]->m_mask,
				addr & m_devlist[i]->m_mask,
				m_devlist[i]->m_addr);
		} */

		return -1;
	}
	int	getwrdev(uint32_t addr) {
		int	devid = getdev(addr);
		if (0 <= devid) {
			if (m_devlist[devid]->m_flags & W_OK)
				return devid;
fprintf(stderr, "ADDRESS %08x in %s is not writable!!\n", addr, m_devlist[devid]->m_name);
		}
else fprintf(stderr, "ADDRESS %08x not found\n", addr);
		return -1;
	}
	int	getexdev(uint32_t addr) {
		int	devid = getdev(addr);
		if (0 <= devid) {
			if (m_devlist[devid]->m_flags & X_OK)
				return devid;
			fprintf(stderr, "Address in %s is not executable\n", m_devlist[devid]->m_name);
		}
		fprintf(stderr, "ExDEV not found (0x%08x), devid = %d\n", addr, devid);
		return -1;
	}
public:
	SIMBUS(void) { m_buserr = false; }
	void	add(SIMDEV *dev, uint32_t addr, uint32_t mask, const char *p, const char *name = "") {
		SIMENTRY	*s = new SIMENTRY;

		s->m_dev = dev;
		s->m_addr= addr;
		s->m_mask= mask;
		s->m_name= strdup(name);
		s->m_flags= 0;

		if ((strchr(p, 'w'))||(strchr(p, 'W')))
			s->m_flags |= W_OK;
		if ((strchr(p, 'r'))||(strchr(p, 'R')))
			s->m_flags |= R_OK;
		if ((strchr(p, 'x'))||(strchr(p, 'X')))
			s->m_flags |= X_OK;
		if ((strchr(p, 'l'))||(strchr(p, 'L')))
			s->m_flags |= L_OK;
		m_devlist.push_back(s);
	}

	uint32_t	lb(uint32_t addr) {
		int	devid;
		if (0 <= (devid = getdev(addr)))
			return m_devlist[devid]->m_dev->lb(addr & (~m_devlist[devid]->m_mask));
		m_buserr = true;
		return 0;
	}
	uint32_t	lh(uint32_t addr) {
		int	devid;
		if (0 <= (devid = getdev(addr)))
			return m_devlist[devid]->m_dev->lh(addr & ((~m_devlist[devid]->m_mask)&-2));
		m_buserr = true;
		return 0;
	}
	uint32_t	lw(uint32_t addr) {
		int	devid;
		if (0 <= (devid = getdev(addr)))
			return m_devlist[devid]->m_dev->lw(addr & ((~m_devlist[devid]->m_mask)&-4));
		m_buserr = true;
		return 0;
	}
	uint32_t	lx(uint32_t addr) {
		int	devid;
		if (0 <= (devid = getexdev(addr)))
			return m_devlist[devid]->m_dev->lw(addr & ((~m_devlist[devid]->m_mask)&-4));
		m_buserr = true;
		return 0;
	}
	void	sb(uint32_t addr, uint32_t vl) {
		int	devid;
		if (0 <= (devid = getwrdev(addr))) {
			return m_devlist[devid]->m_dev->sb(addr & (~m_devlist[devid]->m_mask), vl & 0x0ff);
		} else {
			fprintf(stderr, "No such address, %08x\n", addr);
		}
		m_buserr = true;
		return;
	}
	void	sh(uint32_t addr, uint32_t vl) {
		int	devid;
		if (0 <= (devid = getwrdev(addr)))
			return m_devlist[devid]->m_dev->sh(addr & -2 & (~m_devlist[devid]->m_mask), vl & 0x0ffff);
		m_buserr = true;
		return;
	}
	void	sw(uint32_t addr, uint32_t vl) {
		int	devid;
		if (0 <= (devid = getwrdev(addr)))
			return m_devlist[devid]->m_dev->sw(addr & -4 & (~m_devlist[devid]->m_mask), vl);
		m_buserr = true;
		return;
	}
	bool	interrupt(void) { return false; };

	bool	error(void) {
		bool tmp = m_buserr;
		m_buserr = false;
		return tmp;
	}

	void	tick(void) {
		for(size_t i=0; i<m_devlist.size(); i++)
			m_devlist[i]->m_dev->tick();
	}

	void	load(uint32_t addr, const char *data, size_t len) {
		int	devid;
		if ((0 <= (devid = getdev(addr)))
				&&(m_devlist[devid]->m_flags & L_OK))
			m_devlist[devid]->m_dev->load(
				addr & (~m_devlist[devid]->m_mask), data, len);
		else {
			fprintf(stderr, "DEVID = %d\n", devid);
			m_buserr = true;
		} return;
	}
};

class	ZIPMACHINE {
	bool		m_gie, m_jumped, m_advance_pc, m_locked;
	int		m_lockcount;
	unsigned long	m_icount;
public:
	uint32_t	m_r[32];
	SIMBUS		*m_bus;
	FILE		*m_mapf;

	ZIPMACHINE(void) {
		m_locked = false; m_lockcount = 0;
		m_mapf = NULL;
		m_bus = NULL;
		m_gie = false;
		m_jumped= m_advance_pc = false;
		m_icount = 0;
	}

	void dump() {
		fflush(stderr);
		fflush(stdout);
		printf("ZIPM--DUMP: ");
		if (gie())
			printf("Interrupts-enabled\n");
		else
			printf("Supervisor mode\n");
		printf("\n");

		printf("sR0 : %08x ", m_r[0]);
		printf("sR1 : %08x ", m_r[1]);
		printf("sR2 : %08x ", m_r[2]);
		printf("sR3 : %08x\n",m_r[3]);
		printf("sR4 : %08x ", m_r[4]);
		printf("sR5 : %08x ", m_r[5]);
		printf("sR6 : %08x ", m_r[6]);
		printf("sR7 : %08x\n",m_r[7]);
		printf("sR8 : %08x ", m_r[8]);
		printf("sR9 : %08x ", m_r[9]);
		printf("sR10: %08x ", m_r[10]);
		printf("sR11: %08x\n",m_r[11]);
		printf("sR12: %08x ", m_r[12]);
		printf("sSP : %08x ", m_r[13]);
		printf("sCC : %08x ",(m_r[14] & (~CC_GIE)));
		printf("sPC : %08x\n",m_r[15]);

		printf("\n");

		printf("uR0 : %08x ", m_r[16]);
		printf("uR1 : %08x ", m_r[17]);
		printf("uR2 : %08x ", m_r[18]);
		printf("uR3 : %08x\n",m_r[19]);
		printf("uR4 : %08x ", m_r[20]);
		printf("uR5 : %08x ", m_r[21]);
		printf("uR6 : %08x ", m_r[22]);
		printf("uR7 : %08x\n",m_r[23]);
		printf("uR8 : %08x ", m_r[24]);
		printf("uR9 : %08x ", m_r[25]);
		printf("uR10: %08x ", m_r[26]);
		printf("uR11: %08x\n",m_r[27]);
		printf("uR12: %08x ", m_r[28]);
		printf("uSP : %08x ", m_r[29]);
		printf("uCC : %08x ",(m_r[30]|CC_GIE));
		printf("uPC : %08x\n",m_r[31]);
		printf("\n");
		fflush(stderr);
		fflush(stdout);
	}

	void	ccodes(uint32_t newflags) {
		m_r[14+rbase()] = (cc() & -16)|(newflags&0x0f);
	}

	int	rbase(void) { return m_gie?16:0; }
	bool	gie()		{ return m_gie; };
	bool	locked()	{ return m_locked; };
	bool	sleeping()	{
		return (gie())&&(m_r[14+16]&CC_SLEEP)?true:false;
	};
	bool	sleep(bool nv)	{
		if (nv) {
			m_r[14   ] |= CC_SLEEP;
			m_r[14+16] |= CC_SLEEP;
		} else {
			m_r[14   ] &= (~CC_SLEEP);
			m_r[14+16] &= (~CC_SLEEP);
		} return sleeping();
	};
	bool	halted()	{
		return (!gie()) && (m_r[14]&CC_SLEEP);
	};
	uint32_t	cc()	{ return m_r[14+rbase()]|((m_gie)?CC_GIE:0); };
	bool	fault()		{
		if (cc() & (CC_PHASE|CC_ILL|CC_BREAK|CC_BUSERR|CC_DIVERR))
			return true;
		return false;
	}
	bool	gie(bool v)	{
		m_jumped = (m_gie != v);
		m_gie = v;
		return v;
	}
	bool	jumped(void)	{ return m_jumped; };
	void	pc_advance(bool pcgie) {
		m_r[15+((pcgie)?16:0)] += 4;
		m_r[15+((pcgie)?16:0)] &= -4;
	} void	pc_advance(void) { pc_advance(gie()); }
	uint32_t	pc(void)	{
		return m_r[15+rbase()];
	}

	static uint32_t bitreverse(uint32_t bv) {
		uint32_t b, r=0;
		for(b=0; b<32; b++, bv>>=1)
			r = (r<<1)|(bv&1);
		return r;
	}

	void	init(SIMBUS *bus) {
		m_bus = bus;
		for(int i=0; i<32; i++)
			m_r[i] = 0;
		m_gie = false;
	}

	void	siminsn(uint32_t insn) {
		// fprintf(stderr, "SIM-INSN(0x%08x)\n", insn);
		if ((insn & 0x0fffff)==0x00100) {
			// SIM Exit(0)
			exit(0);
		} else if ((insn & 0x0ffff0)==0x00310) {
			// SIM Exit(User-Reg)
			int	rcode;
			rcode = m_r[(insn&0x0f)+16] & 0x0ff;
			exit(rcode);
		} else if ((insn & 0x0ffff0)==0x00300) {
			// SIM Exit(Reg)
			int	rcode;
			rcode = m_r[(insn&0x0f)+rbase()] & 0x0ff;
			exit(rcode);
		} else if ((insn & 0x0fff00)==0x00100) {
			// SIM Exit(Imm)
			int	rcode;
			rcode = insn & 0x0ff;
			exit(rcode);
		} else if ((insn & 0x0fffff)==0x002ff) {
			// Full/unconditional dump
			fprintf(stderr, "SIM-DUMP\n");
			dump();
		} else if ((insn & 0x0ffff0)==0x00200) {
			// Dump a register
			int rid = (insn&0x0f)+rbase();
			fprintf(stderr, "R[%2d] = 0x%08x\n", rid, m_r[rid]);
		} else if ((insn & 0x0ffff0)==0x00210) {
			// Dump a user register
			int rid = (insn&0x0f);
			fprintf(stderr, "uR[%2d] = 0x%08x\n", rid, m_r[rid+16]);
		} else if ((insn & 0x0ffff0)==0x00230) {
			// SOUT[User Reg]
			int rid = (insn&0x0f)+16;
			fprintf(stderr, "%c", m_r[rid]&0x0ff);
		} else if ((insn & 0x0fffe0)==0x00220) {
			// SOUT[User Reg]
			int rid = (insn&0x0f)+rbase();
			fprintf(stderr, "%c", m_r[rid]&0x0ff);
		} else if ((insn & 0x0fff00)==0x00400) {
			// SOUT[Imm]
			fprintf(stderr, "%c", insn&0x0ff);
		} else { // if ((insn & 0x0f7c00000)==0x77800000)
			uint32_t	imm = insn & 0x03fffff;
			// Simm instruction that we dont recognize
			// if (imm)
			fprintf(stderr, "SIM 0x%08x\n", imm);
		}
	}

	void	fullinsn(uint32_t insn) {
		bool	wf, wb, fpu, noop, lock, wbreak, cmptst, mem,
			sto, ldi, mov, div, execinsn;
		bool	diverr, illegal;
		uint32_t	av, bv, result, f, arg, brg, opc;
		int32_t		imm;
		int		rb, cnd;
		const bool	dbg = false;

		m_icount ++ ;

		if (dbg) {
			fprintf(stderr, "%8ld INSN(@0x%08x, %08x)", m_icount, pc(), insn);
			if (m_mapf) {
				// bool	dbg = pc() == 0x040003cc;
				char	line[512], needle[512], *ptr = NULL,*lp;
				sprintf(needle, "%08x", pc());
				rewind(m_mapf);
				while(NULL != (lp = fgets(line, sizeof(line), m_mapf))) {
					while((*lp)&&(isspace(*lp)))
						lp++;
					if ((*lp != '0')||(tolower(*lp) == 'x'))
						continue;
					// if (dbg)fprintf(stderr, "\tMAP (%s?) %s\n", needle, lp);
					if (NULL != (ptr = strstr(lp, needle))){
						break;
					}
				} if (ptr) {
					if (strlen(ptr) > 8)
						ptr += 8;
					while((*ptr)&&(isspace(*ptr)))
						ptr++;
					int ln = strlen(ptr);
					while((ln > 0)&&(isspace(ptr[ln-1])))
						ptr[--ln] = '\0';
					fprintf(stderr, "\t%s", ptr);
				} else if (0x7b400000 == (insn&0x7fffffff))
					fprintf(stderr, "\treturn");
			} else fprintf(stderr, "\tNO-MAPF");
			fprintf(stderr, "\n");
		}
		m_jumped     = false;
		m_advance_pc = true;
		illegal      = false;
		noop         = false;
		lock         = false;
		wbreak       = false;

		if (m_locked) {
			m_lockcount--;
			if (m_lockcount <= 0)
				m_locked = false;
		}

		m_r[14+rbase()]
			&= ~(CC_ILL|CC_BREAK|CC_BUSERR|CC_DIVERR);

		opc = (insn >> 22) & 0x01f;
		arg = (insn >> 27) & 0x0f;
		brg = (insn >> 14) & 0x0f;

		cmptst=((opc&0x1e)==0x010);
		mem = ((opc&0x1c) == 0x014)||((opc&0x1e) == 0x012);
		sto = (mem)&&(opc&1);
		fpu =(((opc&0x1c)==0x1c)		// Top four FPU ops
				||((opc&0x1e)==0x1a));	// Bottom two FPU ops
		div =((opc&0x1e)==0x0e);
		ldi =((opc&0x1e)==0x18);
		mov =((opc&0x1f)==0x0d);

		if (ldi)	imm = sbits(insn, 23);
		else if (mov)	imm = sbits(insn, 13);
		else if (insn & 0x040000)
				imm = sbits(insn, 14);
		else		imm = sbits(insn, 18);

		// Do we read the B register?
		rb = (mov)||(((insn>>18)&1)&&(!ldi));

		// WriteBack
		wb = (!cmptst)&&(!sto);

		// Do we write flags back?
		wf = true;
		if (ldi)	wf = false;
		if (mov)	wf = false;
		if (mem)	wf = false;
		if (opc==0x08)	wf = false;	// BREV
		if (opc==0x09)	wf = false;	// LDILO
		if ((!cmptst)&&((arg & 0x0e)==0x0e)) // Writes to CC or PC
			wf = false;		// dont set the flags.

		cnd = (ldi) ? 0 : ((insn >> 19) & 7);

		if (fpu & ((arg&0x0e)==0x0e)) {
			fpu = false;
			noop  = ((opc&0x1e) == 0x1e);
			lock  = ((opc&0x1f) == 0x1d);
			wbreak = ((opc&0x1f) == 0x1c);
			illegal = !(noop|lock|wbreak);
			wb     = false;
			wf     = false;
			cnd    = 0;
		} else if (div & ((arg&0x0e)==0x0e)) {
			illegal = true;
		}

		if (cnd != 0) {
			if (!cmptst)
				wf = false;
			int	ccodes = cc() & 0x0f;
			switch(cnd) {
			case 1: execinsn =  (ccodes & CC_Z); break;
			case 2: execinsn =  (ccodes & CC_N); break;
			case 3: execinsn =  (ccodes & CC_C); break;
			case 4: execinsn =  (ccodes & CC_V); break;
			case 5: execinsn = ((ccodes & CC_Z)==0); break;	// NZ
			case 6: execinsn = ((ccodes & CC_N)==0); break;	// GE
			case 7: execinsn = ((ccodes & CC_C)==0); break;	// NC
			default:	execinsn = true;	break;
			}
		} else
			execinsn = true;

		if ((mov)&&(!gie())) {
			// Supervisor can read all registers
			arg |= (insn&0x40000)?0x10:0;
			brg |= (insn&0x02000)?0x10:0;
		} else {
			arg |= (gie())?0x10:0;
			brg |= (gie())?0x10:0;
		}
		result = 0;

		bv = imm;
		if (rb) {
			if ((brg&0x0f)==15) { // PC 
				bv = (imm << 2) + m_r[brg];
				if (gie()) {
					if (brg & 0x010)
						bv += 4;
				} else if ((brg & 0x10)==0)
					bv += 4;
			} else
				bv += m_r[brg];
		}
		av = m_r[arg];
		if ((int)arg == 15 + rbase())
			av += 4;

		if (execinsn) {
			f = 0;	// Resulting flags
			if (fpu) {
				float	fva, fvb, fvr;
				fva = *(float *)&av;
				fvb = *(float *)&bv;

				switch(opc) {
				case 26: fvr = fva + fvb;	break;
				case 27: fvr = fva - fvb;	break;
				case 28: fvr = fva * fvb;	break;
				case 29: fvr = fva / fvb;	break;
				case 30: fvr = (float)bv;	break;
				case 31: result = (int)fvb;	break;
				default: illegal = true;
				} if (opc != 31)
					result = *(uint32_t *)&fvr;
				if (result == 0)
					f = CC_Z;
				if (opc == 31) {
					if (result & 0x80000000)
						f |= CC_N;
				} else if (fvr < 0.0)
					f |= CC_N;
			} else if (noop) {
				if (insn != 0x7fc00000)
					siminsn(insn);
			} else if (wbreak) {
				wf = wb = false;
				m_advance_pc = false;
				if (gie()) {
					m_r[16+14] &= CC_BREAK;
					gie(false);
				} else {
					fprintf(stderr, "BREAK!\n");
					dump();
					exit(EXIT_FAILURE);
				}
			} else if (lock) {
				m_locked = true;
				m_lockcount = 3;
			} else {
				uint32_t	presign = (av>>31)&1, nsgn;
				switch(opc) {
				case  0: case 16: { // SUB, or CMP
					result = av - bv;
					if (av < bv)
						f |= CC_C;
					nsgn = (result >> 31)&1;
					if (presign != nsgn)
						f |= CC_V;
					} break;
				case  1: case 17: result = bv & av; break;//AND or TST
				case  2: { // ADD
					result = bv + av;
					if (result<(uint64_t)bv+(uint64_t)av)
						f |= CC_C;
					nsgn = (result >> 31)&1;
					if (presign != nsgn)
						f |= CC_V;
					} break;
				case  3: result = bv | av; break; // OR
				case  4: result = bv ^ av; break; // XOR
				case  5: { // LSR
					uint32_t nsgn;
					if (bv >= 32)
						result = 0;
					else
						result = ((uint32_t)av >> bv);
					nsgn = (result >> 31)&1;
					if (presign != nsgn)
						f |= CC_V;

					if ((bv !=0)&&(bv<33)&&(av&(1<<(bv-1))))
						f |= CC_C;
					} break;
				case  6: { // LSL
					uint32_t nsgn;
					if (bv >= 32)
						result = 0;
					else
						result = av << bv;
					nsgn = (result >> 31)&1;
					if (presign != nsgn)
						f |= CC_V;
					if((bv !=0)&&(bv<33)&&(av&(1<<(33-bv))))
						f |= CC_C;
					} break;
				case  7: { // ASR
					if ((bv >= 32)&&(av & 0x80000000))
						result = -1;
					else if (bv >= 32)
						result = 0;
					else
						result = ((int)av >> bv);

					if (av & 0x80000000) {
						// Signed carry
						if (bv >= 31)
							f |= CC_C;
						else if((bv != 0)
							&&(av&(1<<(33-bv))))
							f |= CC_C;
					} else {
						// Unsigned carry
						if((bv !=0)&&(bv<32)
							&&(av&(1<<(33-bv))))
							f |= CC_C;
					}
					} break;
				case  8: result = bitreverse(bv);	break; // BREV
				case  9: result = (av&0xffff0000)|(bv&0x0ffff);	break; // LDILO
				case 10: { // MPYUHI
					uint64_t ulv = av * bv;
					result = (ulv >> 32);
					} break;
				case 11: { // MPYSHI
					int64_t	lv = av * bv;
					result = (lv >> 32);
					} break;
				case 12: { // MPY
					int64_t ulv = av * bv;
					// bool	sn = (av<0)^(bv<0);
					result = (int32_t)(ulv & 0x0ffffffff);
					//if (((result&0x80000000)?1:0)
					//		^ ((sn)?1:0))
					//	f |= CC_V;
					} break;
				case 13: result = bv;		break; // MOV
				case 14: { // DIVU
					if (bv == 0)
						diverr = true;
					else
						result = (uint32_t)av
							/ (uint32_t)bv;
					} break;
				case 15: { // DIVS
					if (bv == 0)
						diverr = true;
					else
						result =(int32_t)av/(int32_t)bv;
					} break;
				// case 16: result = av - bv;	break;
				// case 17: result = av & bv;	break;
				case 18: result = m_bus->lw(bv);
					break;// LW
				case 19:
					m_bus->sw(bv, av);	break;// SW
				case 20: result = m_bus->lh(bv);break;// LH
				case 21: m_bus->sh(bv, av);	break;// SH
				case 22: result = m_bus->lb(bv);break;// LB
				case 23: m_bus->sb(bv, av);	break;// SB
				case 24: result = bv;		break;// LDI
				case 25: result = bv;		break;// LDI
				default: illegal = true;
				}
				if (result == 0)
					f |= CC_Z;
				if (result & 0x80000000)
					f |= CC_N;
			}

			if (illegal) {
				if (gie()) {
					m_r[16+14] |= CC_ILL;
					gie(false);
					m_jumped = true;
					m_advance_pc = false;
				} else {
					m_r[14] |= CC_ILL;
					fprintf(stderr, "ILLegal Instruction Exception\n");
					dump();
					exit(EXIT_FAILURE);
				}
			} else if ((mem)&&(m_bus->error())) {
				if (gie()) {
					m_r[16+14] |= CC_BUSERR;
					gie(false);
					m_jumped = true;
					m_advance_pc = false;
				} else {
					m_r[14] |= CC_BUSERR;
					fprintf(stderr, "BUS ERR\n");
					dump();
					exit(EXIT_FAILURE);
				}
			} else if ((div)&&(diverr)) {
				if (gie()) {
					m_r[16+14] |= CC_DIVERR;
					gie(false);
					m_jumped = true;
					m_advance_pc = false;
				} else {
					m_r[14] |= CC_DIVERR;
					fprintf(stderr, "DIV ERR: division by zero\n");
					dump();
					exit(EXIT_FAILURE);
				}
			} if (wf)
				ccodes(f);
			if (wb) {
				if (arg == (uint32_t)(15+rbase()))
					m_jumped = true;
				else if (arg == (uint32_t)(14+rbase())) {
					if (gie()) {
						if ((result & CC_GIE)==0) {
							result |= CC_TRAP;
							result &= (~(CC_SLEEP
							|CC_ILL
							|CC_BREAK
							|CC_BUSERR
							|CC_DIVERR
							|CC_FPUERR
							|CC_STEP
							|CC_SLEEP));
						}
					} else if (result & CC_GIE) {
						// Returning to userspace
						m_r[16+14] &= (~(CC_ILL
							|CC_BREAK
							|CC_BUSERR
							|CC_DIVERR
							|CC_FPUERR));
					}
				}
				if (dbg) fprintf(stderr,
					"\tREG[%02x] = %08x\n", arg, result);
				m_r[arg] = result;
				if ((int)arg == 15+rbase())
					m_advance_pc = false;
				if (((int)arg==14+rbase())&&(((m_gie)?1:0)^((result&CC_GIE)?1:0))) {
					gie((result&CC_GIE)?true:false);
					// Prevent us from advancing the PC
					m_jumped = true;
					// m_advance_pc = true;
				}
				// Some CC bits are constant.  Keep them that
				// way.
				m_r[14   ] &= (~CC_GIE);
				m_r[14+16] |= ( CC_GIE);
				m_r[15   ] &= -4;
				m_r[15+16] &= -4;
			}
		}
	}

	void	cisinsn(uint16_t insn) {
		uint32_t	imm;
		int		dr, br, cisop, fullop;

		cisop = (insn >> 8) & 0x07;
		switch(cisop) {
		case 0: fullop =  0; break; // SUB
		case 1: fullop =  1; break; // AND
		case 2: fullop =  2; break; // ADD
		case 3: fullop = 16; break; // CMP
		case 4: fullop = 18; break; // LW
		case 5: fullop = 19; break; // SW
		case 6: fullop = 24; break; // LDI
		case 7: fullop = 13; break; // MOV
		}

		dr = (insn>>11) & 0x0f;

		if (fullop == 24) {
			// LDI
			imm = sbits(insn, 8) & 0x07fffff;
			fullinsn(0x80000000 | (dr<<27) | (fullop<<22) | imm);
		} else if (fullop == 13) {
			// MOV
			br = (insn >> 3) & 0x0f;
			imm = sbits(insn, 3) & 0x01fff;
			fullinsn(0x80000000 | (dr << 27) | (fullop<<22) | (br<<14) | imm);
		} else if (insn & 0x80) {
			// Uses a breg
			br = (insn >> 3) & 0x0f;
			imm = sbits(insn, 3) & 0x3fff;
			fullinsn(0x80040000 | (dr << 27) | (fullop<<22) | (br<<14) | imm);
		} else if ((fullop == 18)||(fullop == 19)) {
			// Load or store, breg is assumed to be SP
// 0x04844000
			br = 13;
			imm = sbits(insn, 7) & 0x3fff;
			fullinsn(0x80040000 | (dr << 27) | (fullop<<22) | (br<<14) | imm);
		} else {
			imm = sbits(insn, 7) & 0x03ffff;
			fullinsn(0x80000000 | (dr << 27) | (fullop<<22) | imm);
		}
	}

	void	execute(uint32_t insn) {
		/// fprintf(stderr, "EXEC-INSN(@0x%08x - %08x)\n", pc(), insn);
		bool	igie = gie();
		if (insn & 0x80000000) {
			int		ibase = rbase();
			cisinsn((insn>>16) & 0x0ffff);
			if (m_advance_pc)
				m_r[14+ibase] |= (CC_PHASE);
			if ((!m_jumped)&&(igie == gie())) {
				cisinsn(insn & 0x0ffff);
				m_r[14+ibase] &= ~(CC_PHASE);
			} if (m_advance_pc)
				pc_advance(igie);
			m_jumped = false;
		} else {
			m_r[14+rbase()] &= ~(CC_PHASE);
			fullinsn(insn);

			if (m_advance_pc)
				pc_advance(igie);

			if ((gie())&&(cc() & CC_STEP))
				gie(false);
		}
	}
};

int main(int argc, char **argv) {
	const char *executable = "a.out";
	SIMBUS *bus;
	bool	done;
	ZIPMACHINE	*zipm;
	ELFSECTION	**secpp, *secp;
	uint32_t	entry;

	if (argc > 1)
		executable = argv[1];
	if (access(executable, R_OK)!=0) {
		fprintf(stderr, "Cannot read %s\n", executable);
		exit(EXIT_FAILURE);
	} elfread(executable, entry, secpp);
	if (0 == secpp[0]->m_len) {
		fprintf(stderr, "Executable file has no contents!\n");
		exit(EXIT_FAILURE);
	}

	// Timer  at 0x0100?
	// Buserr at 0x0101?
	// Addresses are given in 32-bit glory, so they reference 8-bit bytes
	bus = new SIMBUS();
	// BUSITEM net = new NETDEV();

	bus->add(new UARTDEV(),  0x00000150, 0xfffffff0, "RW", "UART");// 4 words
	// bus->add(new SDCDEV(12), 0x00000420, 0xfffffff0, "RW");// 4 words
	// bus->add(net->ctrl,   0x00000440, 0xffffffe0, "RW");// 8 words
	// bus->add(net->data,   0x00002000, 0xffffe000, "R"); // 8 words
	// bus->add(net->data,   0x00003000, 0xffffe000, "R"); // 8 words
	bus->add(new MEMDEV(17), 0x0020000, 0x7fe0000, "RWX", "BlockRAM");// Block RAM
	bus->add(new ROMDEV(24),0x01000000,0xff000000, "RXL", "Flash"); // Flash
	bus->add(new MEMDEV(28),0x10000000,0xf0000000, "RWX", "SDRAM");// SDRAM

	for(int s=0; secpp[s]->m_len; s++) {
		secp = secpp[s];
		if (false) fprintf(stderr,
			"Attempting to LOAD->(%08x, ..., %d)\n",
			secp->m_start, secp->m_len);
		bus->load(secp->m_start, (const char *)&secp->m_data[0], secp->m_len);
		if (bus->error()) {
			fprintf(stderr, "LOAD: Error writing to mem @ 0x%08x\n", secp->m_start);
			// exit(EXIT_FAILURE);
		}
	}

	if(bus->error()) {
		fprintf(stderr, "ERR: Executable file doesn\'t fit in simulator\n");
		exit(EXIT_FAILURE);
	}

	done = false;
	zipm = new ZIPMACHINE;
	if (access("map.txt", R_OK)==0)
		zipm->m_mapf = fopen("map.txt","r");
	zipm->init(bus);
	zipm->m_r[15] = entry;
	while(!done) {
		uint32_t	insn;
		insn = bus->lx(zipm->pc());

		if (bus->error()) {
			if (zipm->gie()) {
				zipm->m_r[14+16] |= CC_BUSERR;
				zipm->gie(false);
				continue;
			} else {
				zipm->m_r[14] |= CC_BUSERR;
				fprintf(stderr, "IFetch BUSERR, %08x\n", zipm->pc());
				zipm->dump();
				exit(EXIT_FAILURE);
			}
		} else {
			if (!zipm->sleeping())
				zipm->execute(insn);
		}

		if (zipm->halted()) {
			fflush(stderr);
			fflush(stdout);
			printf("CPU HALT\n");
			done = true;
			break;
		}

		bus->tick();
		if ((bus->interrupt())&&(zipm->gie())&&(!zipm->locked())) {
			zipm->gie(false);
			zipm->sleep(false);
		}
	}
}

