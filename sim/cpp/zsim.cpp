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
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <vector>
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
#define	CC_C		(1<<2)
#define	CC_N		(1<<1)
#define	CC_Z		(1   )

class	SIMDEV {
public:
	virtual	uint32_t	lw(uint32_t addr) = 0;
	virtual void	sw(uint32_t addr, uint32_t vl) = 0;

	virtual	uint32_t	lb(uint32_t addr) {
		uint32_t v = lw(addr&-4);
		v >>= (8*(3-(addr&3)));
		v &= 0x0ff;
		return v;
	}
	virtual	uint32_t	lh(uint32_t addr) {
		uint32_t v = lw(addr&-4);
		if (addr&2)
			v >>= 16;
		v &= 0x0ffff;
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
};

class	UARTDEV : public SIMDEV {
	uint32_t	m_setup;
public:
	UARTDEV(void) { m_setup = 868; }

	virtual	uint32_t	lw(uint32_t addr) {
		switch(addr&3) {
		case 0:	return m_setup;
		case 1:	return 0;
		case 2:	return 0x100;
		case 3:	return 0;
		}
	}
		
	virtual void sw(uint32_t addr, uint32_t vl) {
		switch(addr&3) {
		case 0:	m_setup = vl & 0x3fffffff; break;
		case 1:	break;
		case 2:	break;
		case 3:	putchar(vl & 0x0ff);
		}
	}
};


class	MEMDEV : public SIMDEV {
protected:
	char	*m_mem;
public:
	MEMDEV(int nbits) {
		m_mem = new char[(1<<nbits)];
	}

	virtual	uint32_t	lw(uint32_t addr) {
		unsigned char	a, b, c, d;
		uint32_t	v;

		a = m_mem[addr];
		b = m_mem[addr+1];
		c = m_mem[addr+2];
		d = m_mem[addr+3];
		v = (a<<24)|(b<<16)|(c<<8)|d;

		return v;
	}

	virtual void sw(uint32_t addr, uint32_t vl) {
		m_mem[(addr&-4)  ] = (vl >>24)&0x0ff;
		m_mem[(addr&-4)+1] = (vl >>16)&0x0ff;
		m_mem[(addr&-4)+2] = (vl >> 8)&0x0ff;
		m_mem[(addr&-4)+3] = (vl     )&0x0ff;
	}

	virtual void sh(uint32_t addr, uint32_t vl) {
		m_mem[(addr&-2)  ] = (vl >> 8)&0x0ff;
		m_mem[(addr&-2)+1] = (vl     )&0x0ff;
	}

	virtual void sb(uint32_t addr, uint32_t vl) {
		m_mem[addr] = vl;
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

class	SIMENTRY {
public:
	SIMDEV	*m_dev;
	uint32_t m_addr, m_mask;
	int	m_flags;
};

class	SIMBUS {
	bool	m_buserr;
	std::vector<SIMENTRY *>	m_devlist;
	SIMDEV	*getdev(uint32_t addr) {
		for(int i=0; i<m_devlist.size(); i++) {
			if ((addr&m_devlist[i]->m_mask)==m_devlist[i]->m_addr)
				return m_devlist[i]->m_dev;
		}
		return NULL;
	}
	SIMDEV	*getwrdev(uint32_t addr) {
		for(int i=0; i<m_devlist.size(); i++) {
			if ((addr&m_devlist[i]->m_mask)==m_devlist[i]->m_addr) {
				if (m_devlist[i]->m_flags & W_OK)
					return m_devlist[i]->m_dev;
				break;
			}
		}
		return NULL;
	}
	SIMDEV	*getexdev(uint32_t addr) {
		for(int i=0; i<m_devlist.size(); i++) {
			if ((addr&m_devlist[i]->m_mask)==m_devlist[i]->m_addr) {
				if (m_devlist[i]->m_flags & X_OK)
					return m_devlist[i]->m_dev;
				break;
			}
		}
		return NULL;
	}
public:
	SIMBUS(void) { m_buserr = false; }
	void	add(SIMDEV *dev, uint32_t addr, uint32_t mask, const char *p) {
		SIMENTRY	*s = new SIMENTRY;
		s->m_dev = dev;
		s->m_addr= addr;
		s->m_mask= mask;
		s->m_flags= 0;

		if (strchr(p, 'w'))
			s->m_flags |= W_OK;
		else if (strchr(p, 'r'))
			s->m_flags |= R_OK;
		else if (strchr(p, 'x'))
			s->m_flags |= X_OK;
		m_devlist.push_back(s);
	}

	uint32_t	lb(uint32_t addr) {
		SIMDEV	*dev;
		if (dev = getdev(addr))
			return dev->lb(addr);
		m_buserr = true;
		return 0;
	}
	uint32_t	lh(uint32_t addr) {
		SIMDEV	*dev;
		if (dev = getdev(addr))
			return dev->lh(addr & -2);
		m_buserr = true;
		return 0;
	}
	uint32_t	lw(uint32_t addr) {
		SIMDEV	*dev;
		if (dev = getdev(addr))
			return dev->lw(addr & -4);
		m_buserr = true;
		return 0;
	}
	uint32_t	lx(uint32_t addr) {
		SIMDEV	*dev;
		if (dev = getexdev(addr))
			return dev->lw(addr & -4);
		m_buserr = true;
		return 0;
	}
	void	sb(uint32_t addr, uint32_t vl) {
		SIMDEV	*dev;
		if (dev = getwrdev(addr))
			return dev->sb(addr, vl & 0x0ff);
		m_buserr = true;
		return;
	}
	void	sh(uint32_t addr, uint32_t vl) {
		SIMDEV	*dev;
		if (dev = getwrdev(addr))
			return dev->sh(addr & -2, vl & 0x0ffff);
		m_buserr = true;
		return;
	}
	void	sw(uint32_t addr, uint32_t vl) {
		SIMDEV	*dev;
		if (dev = getwrdev(addr))
			return dev->sw(addr & -4, vl);
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
		for(int i=0; i<m_devlist.size(); i++)
			tick();
	}
};

class	ZIPMACHINE {
public:
	uint32_t	m_r[32];
	bool		m_gie, m_jumped, m_advance_pc;
	SIMBUS		*m_bus;

	void dump() {
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
	}

	void	ccodes(uint32_t newflags) {
		m_r[14+rbase()] = (cc() & -16)|(newflags&0x0f);
	}

	int	rbase(void) { return m_gie?16:0; }
	bool	gie()		{ return m_gie; };
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
	void	pc_advance(void) {
		m_r[15+rbase()] += 4;
		m_r[15+rbase()] &= -4;
	} 
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
	
	void	fullinsn(uint32_t insn) {
		bool	wf, wb, fpu, noop, lock, wbreak, cmptst, mem,
			sto, ldi, mov, div, execinsn;
		bool	diverr, illegal, buserr;
		uint32_t	av, bv, result, f, arg, brg, opc;
		int32_t		iv, imm;
		int		rb, cnd;

		m_jumped     = false;
		m_advance_pc = true;

		m_r[14+rbase()]
			&= ~(CC_ILL|CC_BREAK|CC_BUSERR|CC_DIVERR);

		opc = (insn >> 23) & 0x01f;
		arg = (insn >> 28) & 0x0f;
		brg = (insn >> 14) & 0x0f;

		cmptst=((opc&0x1e)==0x010);
		mem = ((opc&0x1c) == 0x014)||((opc&0x1e) == 0x012);
		sto = (mem)&&(opc&1);
		fpu =(((opc&0x1c)==0x1c)	// Top four FPU ops
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
		wb = (cmptst)&&(!sto);

		// Do we write flags back?
		wf  = ((opc&0x0e)!=0x08)&&((opc&0x1e)!= 0x0e)
			&&((opc&0x01c)!=0x014)
			&&((opc&0x01c)!=0x014);
		if ((arg & 0x0e)==0x0e)
			wf = false;

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
			case 1: execinsn =  (ccodes & CC_Z);
			case 2: execinsn =  (ccodes & CC_N);
			case 3: execinsn =  (ccodes & CC_C);
			case 4: execinsn =  (ccodes & CC_V);
			case 5: execinsn = ((ccodes & CC_Z)==0);	// NZ
			case 6: execinsn = ((ccodes & CC_N)==0);	// GE
			case 7: execinsn = ((ccodes & CC_C)==0);	// NC
			default:	execinsn = true;	break;
			}
		}

		if ((mov)&&(!gie())) {
			// Supervisor can read all registers
			arg |= (insn&0x40000)?0x10:0;
			brg |= (insn&0x04000)?0x10:0;
		} else {
			arg |= (gie())?0x10:0;
			brg |= (gie())?0x10:0;
		}
		result = 0;

		bv = imm;
		if (rb) {
			if (((brg&0x0f)==15)&&(gie())) // PC
				bv = (imm << 2) + m_r[brg] + 4;
			else
				bv += m_r[brg];
		}
		av = m_r[arg];

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
				if ((insn & 0x0f7ffff00)==0x77800100) {
					// SIM Exit
					exit(sbits(insn, 8));
				} else if ((insn & 0xf7c00000)== 0x77800000) {
					dump();
				} // Otherwise it's a simple NOOP
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
				// Do nothing to lock the bus in a simulation
				assert((0)&&("No lock function implemented"));
			} else {
				switch(opc) {
				case  0: {
					result = av - bv;
					if (av < bv)
						f |= CC_C;
					if (((int)av<0)&&((int)bv>0)&&((int)result>0))
						f |= CC_V;
					else if (((int)av>0)&&((int)bv<0)&&((int)result<0))
						f |= CC_V;
					} break;
				case  1: result = bv & av; break;
				case  2: {
					result = bv + av;
						if (result<(uint64_t)bv+(uint64_t)av)
						f |= CC_C;
					if (((int)av>0)&&((int)bv>0)&&((int)result < 0))
						f |= CC_V;
					else if (((int)av<0)&&((int)bv<0)&&((int)result > 0))
						f |= CC_V;
					} break;
				case  3: result = bv | av; break;
				case  4: result = bv ^ av; break;
				case  5: {
					if (bv >= 32)
						result = 0;
					else
						result = ((uint32_t)av >> bv);
					if ((bv !=0)&&(bv<33)&&(av&(1<<(bv-1))))
						f |= CC_C;
					} break;
				case  6: {
					if (bv >= 32)
						result = 0;
					else
						result = av << bv;
					if((bv !=0)&&(bv<33)&&(av&(1<<(33-bv))))
						f |= CC_C;
					} break;
				case  7: {
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
				case  8: result = bitreverse(bv);	break;
				case  9: result = (av&0xffff0000)|(bv&0x0ffff);	break;
				case 10: {
					uint64_t ulv = av * bv;
					result = (ulv >> 32);
					} break;
				case 11: {
					int64_t	lv = av * bv;
					result = (lv >> 32);
					} break;
				case 12: {
					int64_t ulv = av * bv;
					bool	sn = (av<0)^(bv<0);
					result = (int32_t)(ulv & 0x0ffffffff);
					if (((result&0x80000000)?1:0)
							^ ((sn)?1:0))
						f |= CC_V;
					} break;
				case 13: result = bv;		break;
				case 14: {
					if (bv == 0)
						diverr = true;
					else
						result = (uint32_t)av
							/ (uint32_t)bv;
					} break;
				case 15: {
					if (bv == 0)
						diverr = true;
					else
						result =(int32_t)av/(int32_t)bv;
					} break;
				case 16: result = av - bv;	break;
				case 17: result = av & bv;	break;
				case 18: result = m_bus->lw(bv);break;
				case 19: m_bus->sw(bv, av);	break;
				case 20: result = m_bus->lh(bv);break;
				case 21: m_bus->sh(bv, av);	break;
				case 22: result = m_bus->lb(bv);break;
				case 23: m_bus->sb(bv, av);	break;
				case 24: result = bv;		break;
				case 25: result = bv;		break;
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
				if (arg == 15+rbase())
					m_jumped = true;
				else if (arg == 14+rbase()) {
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
				m_r[arg] = result;
				if (((m_gie)?1:0)^((result&CC_GIE)?1:0)) {
					gie((result&CC_GIE)?true:false);
					// Prevent us from advancing the PC
					m_jumped = true;
					// m_advance_pc = true;
				}
			}
		}
	}

	void	cisinsn(uint16_t insn) {
		uint32_t	imm;
		int		dr, br, cisop, fullop;

		cisop = (insn >> 8) & 0x07;
		switch(cisop) {
		case 0: fullop =  0; break;
		case 1: fullop =  1; break;
		case 2: fullop =  2; break;
		case 3: fullop = 16; break;
		case 4: fullop = 18; break;
		case 5: fullop = 19; break;
		case 6: fullop = 24; break;
		case 7: fullop = 13; break;
		}

		dr = (insn>>11) & 0x0f;

		if (fullop == 24) {
			// LDI
			imm = sbits(insn, 8) & 0x07fffff;
			fullinsn(0x80000000 | (dr<<27) | (fullop<<22) | imm);
		} else if (fullop == 13) {
			// MOV
			br = (insn >> 3);
			imm = sbits(insn, 3) & 0x01fff;
			fullinsn(0x80000000 | (dr << 27) | (fullop<<22) | (br<<14) | imm);
		} else if (insn & 0x80) {
			// Uses a breg
			br = (insn >> 3);
			imm = sbits(insn, 3) & 0x3fff;
			fullinsn(0x80004000 | (dr << 27) | (fullop<<22) | (br<<14) | imm);
		} else if ((fullop == 18)||(fullop == 19)) {
			// Load or store, breg is assumed to be SP
			br = 13;
			imm = sbits(insn, 7) & 0x3fff;
			fullinsn(0x80004000 | (dr << 27) | (fullop<<22) | (br<<14) | imm);
		} else {
			imm = sbits(insn, 7) & 0x03ffff;
			fullinsn(0x80000000 | (dr << 27) | (fullop<<22) | imm);
		}
	}

	void	execute(uint32_t insn) {
		bool	igie = gie();
		if (insn & 0x80000000) {
			int		ibase = rbase();
			uint32_t	pcv = pc();
			cisinsn((insn>>16) & 0x0ffff);
			if (m_advance_pc)
				m_r[14+ibase] |= (CC_PHASE);
			if ((!m_jumped)&&(igie == gie())) {
				cisinsn(insn & 0x0ffff);
				m_r[14+ibase] &= ~(CC_PHASE);
			} if (m_advance_pc)
				pc_advance();
			m_jumped = false;
		} else {
			m_r[14+rbase()] &= ~(CC_PHASE);
			fullinsn(insn);

			if (m_advance_pc)
				pc_advance();

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
	ELFSECTION	**sections, **secpp, *secp;
	uint32_t	entry;

	if (argc > 1)
		executable = argv[1];
	if (access(executable, R_OK)!=0) {
		fprintf(stderr, "Cannot read %s\n", executable);
		exit(EXIT_FAILURE);
	} elfread(executable, entry, sections);

	// Timer  at 0x0100?
	// Buserr at 0x0101?
	// Addresses are given in 32-bit glory, so they reference 8-bit bytes
	bus = new SIMBUS();
	// BUSITEM net = new NETDEV();

	bus->add(new UARTDEV(),  0x00000410, 0xfffffff0, "RW");// 4 words
	// bus->add(new SDCDEV(12), 0x00000420, 0xfffffff0, "RW");// 4 words
	// bus->add(net->ctrl,   0x00000440, 0xffffffe0, "RW");// 8 words
	// bus->add(net->data,   0x00002000, 0xffffe000, "R"); // 8 words
	// bus->add(net->data,   0x00003000, 0xffffe000, "R"); // 8 words
	bus->add(new MEMDEV(17), 0x0020000, 0x7fe0000, "RWX");// Block RAM
	bus->add(new ROMDEV(24), 0x1000000, 0x7000000, "RX"); // Flash
	bus->add(new MEMDEV(26), 0x4000000, 0x4000000, "RWX");// SDRAM

	for(int s=0; secpp[s]->m_len; s++) {
		secp = secpp[s];
		for(int i=0; i<secp->m_len; i++)
			bus->sb(secp->m_start+i, secp->m_data[i]);
	}

	if(bus->error()) {
		fprintf(stderr, "ERR: Executable file doesn\'t fit in simulator");
		exit(EXIT_FAILURE);
	}

	done = false;
	zipm = new ZIPMACHINE;
	zipm->init(bus);
	zipm->m_r[15] = entry;
	while(!done) {
		uint32_t	insn = bus->lx(zipm->pc());
		bool	vliw;

		if (bus->error()) {
			if (zipm->gie()) {
				zipm->m_r[14+16] |= CC_BUSERR;
				zipm->gie(false);
				continue;
			} else {
				zipm->m_r[14] |= CC_BUSERR;
				zipm->dump();
				exit(EXIT_FAILURE);
			}
		} else {
			if (!zipm->sleeping())
				zipm->execute(insn);
		}

		if (zipm->halted()) {
			printf("CPU HALT\n");
			done = true;
			break;
		}

		bus->tick();
		if (bus->interrupt()) {
			zipm->gie(false);
			zipm->sleep(false);
		}
	}
}

