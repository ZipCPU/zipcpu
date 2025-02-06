////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/zasm/asmdata.cpp
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Like asmdata.h, this contains necessary data structures for the
//		assembler.  Specifically, in C/C++ fashion, this contains most
//	of the code for actually building such structures.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2025, Gisselquist Technology, LLC
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
// }}}
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "asmdata.h"
#include "twoc.h"

extern	void	yyerror(const char *str);

unsigned int	ILINE::eval(const int lno) {
	return (lno==0)?m_in:DEFAULT_LINE;
}

unsigned int	VLINE::eval(const int lno) {
	return DEFAULT_LINE;
}

unsigned int	DLINE::eval(const int lno) {
	return (lno==0)?m_data:DEFAULT_LINE;
}

void LLINE::addline(ASMLINE *line) {
	if (m_lines != NULL) {
		ASMLINE **nwlines = new ASMLINE *[m_nlines+1];
		for(int i=0; i<m_nlines; i++)
			nwlines[i] = m_lines[i];
		delete[] m_lines;
		nwlines[m_nlines++] = line;

		m_lines = nwlines;
	} else {
		m_lines = new ASMLINE *[1];
		m_lines[m_nlines++] = line;
	}

	if (m_lineno > line->m_lineno)
		m_lineno = line->m_lineno;
};

bool	LLINE::isdefined(void) {
	for(int i=0; i<m_nlines; i++)
		if (!m_lines[i]->isdefined())
		return false;
	return true;
};

LLINE::~LLINE(void) {
	for(int i=0; i<m_nlines; i++)
		delete m_lines[i];
	delete m_lines;
}

unsigned int	LLINE::eval(const int lno) {
	return (lno < m_nlines)?m_lines[lno]->eval(0) : DEFAULT_LINE;
}

// int	m_op; // An operator
// AST	*m_left, *m_right;

int	AST_BRANCH::eval(void) {
	int	lft = m_left->eval(), rht = m_right->eval();

	switch(m_op) {
		case '+':	return lft + rht;
		case '-':	return lft - rht;
		case '*':	return lft * rht;
		case '/':	return lft / rht;
		case '%':	return lft % rht;
		case '^':	return lft ^ rht;
		case '|':	return lft | rht;
		case '&':	return lft & rht;
		case '~':	return ~lft;
		default:	yyerror("Unknown operation"); return lft;
	}
} void	AST_BRANCH::reduce(void) {
	if ((m_left)&&(m_left->m_node_type != 'N')&&(m_left->isdefined())) {
		int	val = m_left->eval();
		delete	m_left;
		m_left = new AST_NUMBER(val);
	} else
		m_left->reduce();
	if ((m_right)&&(m_right->m_node_type != 'N')&&(m_right->isdefined())) {
		int	val = m_right->eval();
		delete	m_right;
		m_right = new AST_NUMBER(val);
	} else
		m_right->reduce();
}

AST_IDENTIFIER::AST_IDENTIFIER(AST *ida, const char *idb) {
	m_node_type = 'I';
	m_id = ((AST_IDENTIFIER*)ida)->m_id + "." + std::string(idb);
	delete ida;
}

bool	AST_IDENTIFIER::isdefined(void) {
	bool	answer = stb_isdefined(m_id);
	return answer;
} int	AST_IDENTIFIER::eval(void) {
	return stb_value(m_id);
} void	AST_IDENTIFIER::reduce(void) {}

bool	AST_LABEL::isdefined(void) {
	bool	answer = stb_isdefined(m_label);
	return answer;
} int	AST_LABEL::eval(void) {
	return stb_value(m_label);
} void	AST_LABEL::reduce(void) {}


int	AST_NUMBER::eval(void) {
	return m_val;
} void	AST_NUMBER::reduce(void) {}

void	OBJFILE::open(const char *fname) {
	if ((m_fp != NULL)||(m_pc != 0l)) {
		fprintf(stderr, "Error: Can only change file names at startup\n");
		exit(-2);
	}
	m_fp = fopen(fname, "w");
	if (m_fp == NULL) {
		fprintf(stderr, "Cannot open %s for writing\n", fname);
		perror("O/S Err:");
		m_fp = fopen("/dev/null","w");
	}
}

void	OBJFILE::operator+=(ASMLINE *ln) {
	unsigned int	buf[1];
	int		nlines = ln->nlines();

	if (!ln->isdefined()) {
		// fprintf(stderr, "%08x: Adding undefined line:\n", m_pc);
		// ((TLINE *)ln)->dump(stderr);
		m_tbl.insert(m_tbl.end(), SAVED_ASMLINE(m_pc,ln));
	/*
	} else {
		fprintf(stderr, "%08x: Adding to file:\n", m_pc);
		((TLINE *)ln)->dump(stderr);
	*/
	}
	for(int i=0; i<nlines; i++) {
		buf[0] = ln->eval(i);
		if (m_fp) fwrite(buf, sizeof(ZIPI), 1, m_fp);
		m_pc++;
	}
}

bool	OBJFILE::reduce(void) {
	SVDTBL::iterator	i;
	bool	all_reduced = true;

	// printf("Checking for reductions\n");
	unsigned int tmp = m_pc;
	for(i=m_tbl.begin(); i != m_tbl.end(); i++) {
		// printf("LINE %08x\n", i->m_pc);
		ASMLINE	*ln = i->m_ln;
		m_pc = i->m_pc;
		if (ln->isdefined()) {
			// printf("PC = 0x%08x reduces\n", i->m_pc);
			fseek(m_fp, sizeof(ZIPI)*i->m_pc, SEEK_SET);
			for(int k=0; k< ln->nlines(); k++) {
				ZIPI	buf[1];
				m_pc = i->m_pc+k;
				buf[0] = ln->eval(k);
				// printf("\t0x%08x -> %08x\n", i->m_pc+k,
					// buf[0]);
				fwrite(buf, sizeof(ZIPI), 1, m_fp);
			}
		} else {
			fprintf(stderr, "Line %d contains an undefined symbol: ", ln->m_lineno);
			fprintf(stderr, "PC = 0x%08x isn\'t ready yet\n", i->m_pc);
			i->m_ln->dump(stderr);
			all_reduced = false;
		}
	} m_pc = tmp; 
	return all_reduced;
}

bool	fitsin(const int v, const int b) {
	if (v>0)
		return (v < (1<<(b-1)));
	else
		return (-v <= (1<<b));
}

#define	BLD_DUALOP(OP)							\
	if (m_opa == zp.ZIP_Rnone)					\
		yyerror("Err: Dual Ops need a result register");	\
	if (m_opb != zp.ZIP_Rnone) {					\
		if(!fitsin(imm, 14))					\
			yyerror("14-bit: Immediate out of range");	\
		in = zp.OP(m_cond,imm,m_opb,m_opa);			\
	} else {							\
		if(!fitsin(imm, 18))					\
			yyerror("18-bit: Immediate out of range");	\
		in = zp.OP(m_cond,imm,m_opa);				\
	}

#define	BLD_BRANCH(OP,CND)						\
	if (fitsin(offset, 13))						\
		in = zp.OP(offset);					\
	else if (fitsin(offset, 18))					\
		in = zp.op_add(zp.CND, offset, zp.ZIP_PC);		\
	else { in = zp.OP(offset); yyerror("LONG JUMP NOT SUPPORTED"); }

ASMLINE	*TLINE::eval(void) {
	ZIPI	in;
	ZPARSER	zp;
	int	offset = 0, imm = 0;

	if (m_opcode != OP_MOV) {
		if ( ((m_opa!=zp.ZIP_Rnone)&&(m_opa > zp.ZIP_PC))
			|| ((m_opb!=zp.ZIP_Rnone)&&(m_opb > zp.ZIP_PC))  )
			yyerror("Only move instructions can reference user regs");
	}

	// Offset used in jumps
	if (m_imm) {
		imm = m_imm->eval();
		offset = imm-objcode.pc()-1;

		if (m_opb == zp.ZIP_PC)
			imm = offset;
	}

	switch(m_opcode) {
		case OP_CMP:
			BLD_DUALOP(op_cmp)
			break;
		case OP_TST:
			BLD_DUALOP(op_tst)
			break;
		case OP_MOV:
			if ((m_opa == zp.ZIP_Rnone)||(m_opb == zp.ZIP_Rnone)) {
				yyerror("Moves can only occurr between registers");
				fprintf(stderr, "m_opa = %d, m_opb = %d\n", m_opa, m_opb);
				fprintf(stderr, "m_imm = %d\n", imm);
			} else if (!fitsin(imm, 13))
				yyerror("Immediate overflow on move");
			in = zp.op_mov(m_cond, imm, m_opb, m_opa);
			break;
#ifdef	LONG_MPY
		case OP_MPY:
			BLD_DUALOP(op_mpy);
			break;
#else
		case OP_LDIHI:
			if ((imm & (-1<<16))!=0)
				yyerror("16-bit Immediate out of range");
			if (m_opb != zp.ZIP_Rnone)
				yyerror("LDIHI cannot accept OP-B registers");
			if (m_opa == zp.ZIP_Rnone)
				yyerror("LDIHI needs a register result");
			in = zp.op_ldihi(m_cond, imm, m_opa);
			break;
#endif
		case OP_LDILO:
			if ((imm & (-1<<16))!=0)
				yyerror("16-bit Immediate out of range");
			if (m_opb != zp.ZIP_Rnone)
				yyerror("LDIHI cannot accept OP-B registers");
			if (m_opa == zp.ZIP_Rnone)
				yyerror("LDIHI needs a register result");
			if ((imm & (-1<<16))!=0)
				yyerror("16-bit Immediate out of range");
			in = zp.op_ldilo(m_cond, imm, m_opa);
			break;
#ifdef	LONG_MPY
		case OP_MPYUHI:
			BLD_DUALOP(op_mpyuhi);
			break;
		case OP_MPYSHI:
			BLD_DUALOP(op_mpyshi);
			break;
#else
		case OP_MPYU:
			if ((m_opb == zp.ZIP_PC)||(m_opb == zp.ZIP_CC)
				||(m_opa == zp.ZIP_PC)||(m_opa == zp.ZIP_CC))
				yyerror("MPYU does not support PC or CC register operands or results");
			else if (m_opb == zp.ZIP_Rnone)
				in = zp.op_mpyu(m_cond, imm, m_opa);
			else
				in = zp.op_mpyu(m_cond, imm, m_opb, m_opa);
			break;
		case OP_MPYS:
			if ((m_opb == zp.ZIP_PC)||(m_opb == zp.ZIP_CC)
				||(m_opa == zp.ZIP_PC)||(m_opa == zp.ZIP_CC))
				yyerror("MPYS does not support PC or CC register operands or results");
			else if (m_opb == zp.ZIP_Rnone)
				in = zp.op_mpys(m_cond, imm, m_opa);
			else
				in = zp.op_mpys(m_cond, imm, m_opb, m_opa);
			break;
#endif
		case OP_ROL:
			if (m_opa == zp.ZIP_Rnone)
				yyerror("ROL needs a register result");
			if (m_opb != zp.ZIP_Rnone)
				in = zp.op_rol(m_cond, imm, m_opb, m_opa);
			else
				in = zp.op_rol(m_cond, imm, m_opa);
			break;
		case OP_SUB:
			BLD_DUALOP(op_sub)
			break;
		case OP_AND:
			BLD_DUALOP(op_and)
			break;
		case OP_ADD:
			BLD_DUALOP(op_add)
			break;
		case OP_OR:
			BLD_DUALOP(op_or)
			break;
		case OP_XOR:
			BLD_DUALOP(op_xor)
			break;
		case OP_LSL:
			BLD_DUALOP(op_lsl)
			break;
		case OP_ASR:
			BLD_DUALOP(op_asr)
			break;
		case OP_LSR:
			BLD_DUALOP(op_lsr)
			break;
		case OP_LOD:
			if (m_opb != zp.ZIP_Rnone)
				in = zp.op_lod(m_cond, imm, m_opb, m_opa);
			else
				in = zp.op_lod(m_cond, imm, m_opa);
			break;
		case OP_STO:
			if (m_opb != zp.ZIP_Rnone)
				in = zp.op_sto(m_cond, m_opa, imm, m_opb);
			else
				in = zp.op_sto(m_cond, m_opa, imm);
			break;
		case OP_BREV:
			BLD_DUALOP(op_brev);
			break;
		case OP_POPC:
			BLD_DUALOP(op_popc);
			break;
		case OP_LDI:
			if (fitsin(zp.brev(imm),18)) {
				imm = zp.brev(imm);
				BLD_DUALOP(op_brev);
			} else if ((!fitsin(imm, 23))||(m_cond != zp.ZIPC_ALWAYS)) {
				if (m_opa == zp.ZIP_PC)
					yyerror("Cannot LDI 32-bit addresses into PC register!");
				LLINE *lln = new LLINE;
#ifdef	LONG_MPY
				lln->addline(new ILINE(zp.op_brev(m_cond, sbits(zp.brev(imm),18), m_opa)));
#else
				lln->addline(new ILINE(zp.op_ldihi(m_cond, (imm>>16)&0x0ffff, m_opa)));
#endif
				lln->addline(new ILINE(zp.op_ldilo(m_cond, imm&0x0ffff, m_opa)));
				lln->m_lineno = m_lineno;
				return lln;
			} else
				in = zp.op_ldi(imm, m_opa);
			break;
		case OP_DIVU:
			BLD_DUALOP(op_divu);
			break;
		case OP_DIVS:
			BLD_DUALOP(op_divs);
			break;
		case OP_CLRF:
			in = zp.op_clrf(m_cond, m_opb);
			break;
		case OP_NOT:
			in = zp.op_not(m_cond, m_opb);
			break;
		case OP_NEG:
			if (m_cond != zp.ZIPC_ALWAYS) {
				LLINE *lln = new LLINE;
				lln->addline(new ILINE(zp.op_mov(m_cond,-1,m_opb,m_opb)));
				lln->addline(new ILINE(zp.op_not(m_cond,m_opb)));
				return lln;
			} else {
				LLINE *lln = new LLINE;
				lln->addline(new ILINE(zp.op_not(m_opb)));
				lln->addline(new ILINE(zp.op_add(1,m_opb)));
				return lln;
			}break;
		case OP_JMP:
			if (m_opb == zp.ZIP_Rnone) {
				if (m_cond != zp.ZIPC_ALWAYS)
					yyerror("JMP: Conditions are not allowed for absolute jumps.");
				imm &= (1<<23)-1;
				if (!fitsin(imm, 23))
					yyerror("JMP: Absolute jump address out of range");
				in = zp.op_ldi(imm, zp.ZIP_PC);
			} else if (fitsin(imm,13)) {
				in = zp.op_mov(m_cond, imm, m_opb, zp.ZIP_PC);
			} else if (fitsin(imm,18))
				in = zp.op_add(m_cond, imm, m_opb, zp.ZIP_PC);
			else
				yyerror("JMP: Immediate out of range");
			break;
		case OP_BRA:
			BLD_BRANCH(op_bra,ZIPC_ALWAYS)
			break;
		case OP_BZ:
			BLD_BRANCH(op_brz,ZIPC_Z)
			break;
		case OP_BNZ:
			BLD_BRANCH(op_bnz,ZIPC_NZ)
			break;
		case OP_BGE:
			BLD_BRANCH(op_bge,ZIPC_GE)
			break;
		case OP_BGT:
			BLD_BRANCH(op_bgt,ZIPC_GT)
			break;
		case OP_BLT:
			BLD_BRANCH(op_blt,ZIPC_LT)
			break;
		case OP_BRC:
			BLD_BRANCH(op_brc,ZIPC_C)
			break;
		case OP_BRV:
			BLD_BRANCH(op_brv,ZIPC_V)
			break;
		case OP_CLR:	
			if((m_cond == zp.ZIPC_ALWAYS))
				in = zp.op_clr(m_opb);
			else
				in = zp.op_clrf(m_cond, m_opb);
			break;
		case OP_TRAP:
			if((m_opb == zp.ZIP_Rnone)&&(m_cond == zp.ZIPC_ALWAYS))
				in = zp.op_ldi(imm, zp.ZIP_CC);
			else if((m_opb == zp.ZIP_Rnone)&&((imm&0x0ffdf)==imm))
				in = zp.op_ldilo(m_cond, imm & 0x0ffdf, zp.ZIP_CC);
			else if((m_opb != zp.ZIP_Rnone)&&(fitsin(imm, 13)))
				in = zp.op_mov(m_cond, imm, m_opb, zp.ZIP_CC);
			else {
				yyerror("Illegal trap!");
				in = zp.op_trap(m_cond, 0);
			}
			break;
		case OP_RETN:	// yywarn("RETN opcode is deprecated");
				in = zp.op_lod(m_cond, imm, m_opb, m_opa);
				in = zp.op_lod(m_cond, -1, zp.ZIP_SP, zp.ZIP_PC);
			break;
		case OP_HALT:	in = zp.op_halt(m_cond); break;
		case OP_RTU:	in = zp.op_rtu(m_cond); break;
		case OP_BUSY:	in = zp.op_busy(m_cond); break;
		case OP_NOOP:	in = zp.op_noop(); break;
		case OP_BREAK:	in = zp.op_break(); break;
		case OP_LOCK:	in = zp.op_lock(); break;
		case OP_LJMP:	in = zp.op_ljmp(); break;
		case OP_NONE:
		default:	{ char ebuf[256]; sprintf(ebuf, "Unrecognized OP-Code, %d, NONE = %d, CLR=%d", m_opcode, OP_NONE, OP_CLR); 
				yyerror(ebuf);
				in = zp.op_noop(); break;
				}
	}
	ILINE	*rs = new ILINE(in);
	rs->m_lineno = m_lineno;
}

int	TLINE::nlines(void)  {
	if ((m_opcode == OP_LDI)&&( (!(m_imm->isdefined()))
			|| (m_cond != ZPARSER::ZIPC_ALWAYS)
			|| (!fitsin(m_imm->eval(), 23)) )) {
		return 2;
	}
	return 1;
}

unsigned int	TLINE::eval(const int lno) {
	if (!isdefined())
		return DEFAULT_LINE;
	else {
		ASMLINE *ln = this->eval();
		unsigned int val = ln->eval(lno);
		delete ln;
		return val;
	}
}

void	TLINE::dump(FILE *fp) {
	if (m_state == 'V')
		fprintf(fp, "Void @%d\n", m_lineno);
	else if (m_state != 'T')
		fprintf(fp, "TLINE state != T (== %c)\n", m_state);
	else {
		fprintf(fp, "TLINE @%d\n", m_lineno);
		switch(m_opcode) {
		case OP_CMP: fprintf(fp, "\tTLINE OP   = CMP\n");
			break;
		case OP_TST: fprintf(fp, "\tTLINE OP   = TST\n");
			break;
		case OP_MOV: fprintf(fp, "\tTLINE OP   = MOV\n");
			break;
#ifdef	LONG_MPY
		case OP_MPY: fprintf(fp,"\tTLINE OP   = MPY\n");
			break;
#else
		case OP_LDIHI:fprintf(fp,"\tTLINE OP   = LDIHI\n");
			break;
#endif
		case OP_LDILO:fprintf(fp,"\tTLINE OP   = LDILO\n");
			break;
#ifdef	LONG_MPY
		case OP_MPYUHI: fprintf(fp,"\tTLINE OP   = MPYUHI\n");
			break;
		case OP_MPYSHI: fprintf(fp,"\tTLINE OP   = MPYSHI\n");
			break;
#else
		case OP_MPYU: fprintf(fp,"\tTLINE OP   = MPYU\n");
			break;
		case OP_MPYS: fprintf(fp,"\tTLINE OP   = MPYS\n");
			break;
#endif
		case OP_ROL: fprintf(fp, "\tTLINE OP   = ROL\n");
			break;
		case OP_SUB: fprintf(fp, "\tTLINE OP   = SUB\n");
			break;
		case OP_AND: fprintf(fp, "\tTLINE OP   = AND\n");
			break;
		case OP_ADD: fprintf(fp, "\tTLINE OP   = ADD\n");
			break;
		case OP_OR: fprintf(fp, "\tTLINE OP   = OR\n");
			break;
		case OP_XOR: fprintf(fp, "\tTLINE OP   = XOR\n");
			break;
		case OP_LSL: fprintf(fp, "\tTLINE OP   = LSL\n");
			break;
		case OP_ASR: fprintf(fp, "\tTLINE OP   = ASR\n");
			break;
		case OP_LSR: fprintf(fp, "\tTLINE OP   = LSR\n");
			break;
		case OP_LOD: fprintf(fp, "\tTLINE OP   = LOD\n");
			break;
		case OP_STO: fprintf(fp, "\tTLINE OP   = STO\n");
			break;
		case OP_LDI: fprintf(fp, "\tTLINE OP   = LDI\n");
			break;
		case OP_CLRF: fprintf(fp, "\tTLINE OP   = CLRF\n");
			break;
		case OP_NOT: fprintf(fp, "\tTLINE OP   = NOT\n");
			break;
		case OP_JMP: fprintf(fp, "\tTLINE OP   = JMP\n");
			break;
		case OP_BRA: fprintf(fp, "\tTLINE OP   = BRA\n");
			break;
		case OP_BZ:
		case OP_BNZ:
		case OP_BGE:
		case OP_BGT:
		case OP_BLT:
		case OP_BRC:
		case OP_BRV:
			fprintf(fp, "\tTLINE OP   = BRA.C\n");
			break;
		case OP_CLR: fprintf(fp, "\tTLINE OP   = CLR\n");
			break;
		case OP_NEG: fprintf(fp, "\tTLINE OP   = NEG\n");
			break;
		case OP_TRAP: fprintf(fp, "\tTLINE OP   = TRAP\n");
			break;
		case OP_HALT: fprintf(fp, "\tTLINE OP   = HALT\n");
			break;
		case OP_RTU: fprintf(fp, "\tTLINE OP   = RTU\n");
			break;
		case OP_BUSY: fprintf(fp, "\tTLINE OP   = BUSY\n");
			break;
		case OP_BREAK: fprintf(fp, "\tTLINE OP   = BREAK\n");
			break;
		case OP_NOOP: fprintf(fp, "\tTLINE OP   = NOOP\n");
		case OP_LOCK: fprintf(fp, "\tTLINE OP   = LOCK\n");
			break;
		case OP_NONE:
		default:
			fprintf(fp, "\tTLINE OP   = (Unrecognized, %d)\n", m_opcode);
				break;
		}
		if (m_cond == 0)
			fprintf(fp, "\tTLINE COND = (Always)\n");
		else
			fprintf(fp, "\tTLINE COND = %s\n", zop_ccstr[m_cond&0x07]);
		if (m_imm == NULL)
			fprintf(fp, "\tTLINE imm  = (NULL)\n");
		else if (!m_imm->isdefined()) {
			m_imm->reduce();
			fprintf(fp, "\tTLINE imm  = ");
			m_imm->dump(fp);
			fprintf(fp, "\n");
		} else
			fprintf(fp, "\tTLINE imm  = %d\n", m_imm->eval());
		if (m_opb != ZPARSER::ZIP_Rnone)
			fprintf(fp, "\tTLINE opb  = %d\n", m_opb);
		if (m_opa != ZPARSER::ZIP_Rnone)
			fprintf(fp, "\tTLINE opa  = %d\n", m_opa);
	}
}


// Now, for our symbol table
class	SYMTABLE_ENTRY {
private:
	int	m_recursion_check;

	std::string	&trim(std::string &s) {
		std::string::iterator	ptr = s.end()-1;

		while((ptr >= s.begin())&&(isspace(*ptr)))
			*ptr-- = '\0';
		if (*ptr == ':')
			*ptr-- = '\0';

		// printf("STORING: %s\n", s.c_str());

		return s;
	}

public:
	std::string	m_name;
	AST		*m_value;
	SYMTABLE_ENTRY(const char *str) : m_recursion_check(0), m_name(str), m_value(NULL) {
		trim(m_name);
	} SYMTABLE_ENTRY(const char *str, AST *v) : m_recursion_check(0), m_name(str), m_value(v) {
		trim(m_name);
	} ~SYMTABLE_ENTRY(void) {
		if (m_value)
			delete m_value;
	}

	SYMTABLE_ENTRY &operator=(AST *new_value) {
		if (m_value)
			delete	m_value;
		m_value = new_value;
	}

	bool	isdefined(void) {
		if (m_recursion_check > 0) {
			fprintf(stderr, "RECURSION DETECTED! Symbol: %s\n",
				m_name.c_str());
			return false;
		}
		m_recursion_check = 1;
		if (m_value->m_node_type != 'N')
			m_value->reduce();
		bool	answer = m_value->isdefined();
		m_recursion_check = 0;
		return answer;
	}
	int	val(void) {
		if ((m_value->isdefined())&&(m_value->m_node_type != 'N')) {
			int	v = m_value->eval();
			AST	*tmp;
			tmp = m_value;
			m_value = new AST_NUMBER(v);
			delete tmp;
		} return (m_value->eval());
	}
	void	dump(FILE *fp) { m_value->dump(fp); }
};

class	SYMBOL_TABLE	{
private:
	typedef	SYMTABLE_ENTRY	*TBLV;
	typedef	std::list<TBLV>	TBLT;

	TBLT	m_tbl;

	TBLT::iterator	lookup(const char *str) {
		TBLT::iterator	i = m_tbl.begin();
		for(; (i!=m_tbl.end())&&(strcmp(str, (*i)->m_name.c_str())>0);
				i++)
			;
		if ((i != m_tbl.end())&&(strcmp(str,(*i)->m_name.c_str())==0))
			return i;
		return	m_tbl.end();
	}

public:
	SYMBOL_TABLE(void) {}
	~SYMBOL_TABLE(void) {
		TBLT::iterator i = m_tbl.begin();
		while(i != m_tbl.end()) {
			delete (*i);
			i = m_tbl.erase(i);
		}
	}

	void	define(const char *key, AST *value) {
		SYMTABLE_ENTRY	*v = new SYMTABLE_ENTRY(key, value);
		TBLT::iterator	i = m_tbl.begin();
		for(; (i!=m_tbl.end())&&(strcmp(key, (*i)->m_name.c_str())>0);
				i++)
			;
		m_tbl.insert(i, v);

		/*
		fprintf(stderr, "Defining: %s = ", key);
		value->dump(stderr);
		fprintf(stderr, "\n");
		*/
	}

	bool	isdefined(const char *key) {
		TBLT::iterator	i = lookup(key);
		if (i == m_tbl.end()) {
			// fprintf(stderr, "%s is not in the symbol table\n", key);
			return false;
		} else {
			bool	defined = (*i)->isdefined();
			/*
			if (!defined) {
				fprintf(stderr, "KEY: %s = ", key);
				(*i)->dump(stderr);
				fprintf(stderr, " is not yet defined\n");
			} */
			return (*i)->isdefined();
		}
	}

	int	value(const char *key) {
		TBLT::iterator	i = lookup(key);
		if (i == m_tbl.end())
			return 0;
		else
			return (*i)->val();
	}
};

SYMBOL_TABLE	*global_context = NULL, *file_context = NULL;

bool	stb_isdefined(const char *key) {
	if ((file_context)&&(file_context->isdefined(key)))
		return true;
	else
		return global_context->isdefined(key);
} int	stb_value(const char *key) {
	if ((file_context)&&(file_context->isdefined(key)))
		return file_context->value(key);
	else
		return global_context->value(key);
} void	stb_define(const char *key, AST *value) {
	file_context->define(key, value);
} void	gbl_define(const char *key, AST *value) {
	global_context->define(key, value);
}

void	create_new_context(void) {
	if (global_context == NULL)
		global_context = new SYMBOL_TABLE;
	if (file_context != NULL)
		delete file_context;
	file_context = new SYMBOL_TABLE;
}


// Convenience functions for accessing the symbol table
bool	stb_isdefined(const std::string &key) {
	bool answer = stb_isdefined(key.c_str());
	return answer;
} int	stb_value(const std::string &key) {
	return stb_value(key.c_str());
} void	stb_define(const std::string &key, AST *value) {
	stb_define(key.c_str(), value);
} void	gbl_define(const std::string &key, AST *value) {
	gbl_define(key.c_str(), value);
}


