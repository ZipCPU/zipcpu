////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	asmdata.h
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	Data structures for the assembler.  In particular, this file
//		declares: Abstract Syntax Trees (ASTs) to store operations for
//		later calculation, ASMLINEs or assembled lines (which may or
//		may not be defined, depending upon symbol table status),
//		symbol table access and the final output object file together
//		with its necessary relocations.  Yes, linking is done, but as
//		part of the assembler and not part of a separate linker.
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
#ifndef	ASMDATA_H
#define	ASMDATA_H

#include <stdio.h>
#include <string>
#include <list>
#include "zopcodes.h"
#include "zparser.h"

extern	"C" char	*linecp;
extern	int	yylineno;

typedef enum {
//	TST	OPCND
	// Dual operand instructions that take conditions
	OP_CMP, OP_TST, OP_MOV, OP_LDIHI, OP_LDILO, OP_MPYU, OP_MPYS, OP_ROL,
		OP_SUB, OP_AND, OP_ADD, OP_OR, OP_XOR,
		OP_LSL, OP_ASR, OP_LSR,
	// New multiplies
	OP_MPY, OP_MPYSHI, OP_MPYUHI,
	// New bit-wise operations
	OP_BREV, OP_POPC,
	// New divide instruction
	OP_DIVU, OP_DIVS,
	// New floating point instructions
	OP_FPADD, OP_FPSUB, OP_FPMUL, OP_FPDIV, OP_FPCVT, OP_FPINT,
	// Memory operands/operators
	OP_LOD, OP_STO,
	// Dual operand instructions that do not take conditions
	OP_LDI,
	// Single operand instructions that can take conditions
	OP_CLRF, OP_JMP, OP_NOT,
	// Branch operands
	OP_BRA, OP_BLT, OP_BZ, OP_BNZ, OP_BGT, OP_BGE, OP_BRC, OP_BRV,
	// Single operand instructions that have no explicit conditions
	OP_CLR, OP_TRAP, OP_NEG,
	// BAREOPs that can have conditions
	OP_HALT,  OP_RTU, OP_BUSY, OP_RETN,
	// BAREOPs without conditions
	OP_BREAK, OP_NOOP, OP_LOCK, OP_LJMP,
	// Error condition--undefined operand
	OP_NONE
} LEXOPCODE;

#define	DEFAULT_LINE	0x76000000

class	ASMLINE	{
public:
	char	m_state;
	int	m_lineno;
	virtual	bool	isdefined(void) { return true; };
	virtual	~ASMLINE(void) {};
	virtual	int	nlines(void) { return 0; }
	virtual	unsigned int	eval(const int lno) { return DEFAULT_LINE; }
	virtual	void	dump(FILE *fp) = 0;
};

class	AST { // The actual expression tree
public:
	// node type is one of:
	// 'B' a branch with two sides
	// 'N' a number
	// 'I' an identifier
	// 'A' ?? an address ?? would we need this?
	virtual	~AST(void) {}
	char	m_node_type;
	virtual	bool	isdefined(void) = 0;
	virtual	int	eval(void) = 0;
	virtual	void	reduce(void) = 0;
	virtual void	dump(FILE *fp) = 0;
};

/*
class	ULINE : public ASMLINE	{ // Unprocessed line of assembly
public:
	std::string	m_file, m_text;
	int		m_lineno;
	ULINE(const int line, const std::string file,
		const std::string text) : m_file(file), m_text(text),
					m_lineno(line) { m_state = 'U'; }
	class TLINE	*eval(void);
	int		nlines(void) { return 0; };
	virtual	bool	isdefined(void) { return false; };
};
*/

class	ILINE : public ASMLINE { // Instruction line
public:
	ZIPI	m_in;
	ILINE(const ZIPI in) : m_in(in) { m_state = 'I'; m_lineno = yylineno; };
	virtual	bool	isdefined(void) { return true; };
	virtual	int	nlines(void) { return 1; }
	virtual	unsigned int	eval(const int lno);
	void	dump(FILE *fp) { fprintf(fp, "IN: %08x\n", m_in); }
};

class	VLINE : public ASMLINE { // Void line
public:
	VLINE(void) { m_state = 'V'; m_lineno = yylineno; };
	virtual	bool	isdefined(void) { return true; };
	virtual	int	nlines(void) { return 0; }
	virtual	unsigned int	eval(const int lno);
	void	dump(FILE *fp) { fprintf(fp, "void\n"); }
};

class	DLINE : public ASMLINE { // Data line
public:
	ZIPI	m_data;
	DLINE(const ZIPI dat) : m_data(dat) { m_state = 'D'; m_lineno = yylineno; };
	virtual	bool	isdefined(void) { return true; };
	virtual	int	nlines(void) { return 1; }
	virtual	unsigned int	eval(const int lno);
	void	dump(FILE *fp) { fprintf(fp, "\tWORD\t%08d\n", m_data); }
};

class	LLINE : public ASMLINE { // List line -- one line that has turned into
		// many
public:
	int	m_nlines;
	ASMLINE	**m_lines;
	LLINE(void) : m_nlines(0), m_lines(NULL) { m_state = 'L'; m_lineno = yylineno; };
	void addline(ASMLINE *line) ;
	virtual	bool	isdefined(void);
	~LLINE(void);
	virtual	int	nlines(void) { return m_nlines; }
	virtual	unsigned int	eval(const int lno);
	void	dump(FILE *fp) { 
		for(int i=0; i<m_nlines; i++)
			m_lines[i]->dump(fp);
	}
};

class	TLINE : public ASMLINE { // Expression tree
public:
	LEXOPCODE		m_opcode;
	ZPARSER::ZIPCOND	m_cond;
	AST			*m_imm;
	ZPARSER::ZIPREG		m_opb, m_opa;

	TLINE(void) : m_opcode(OP_NONE), m_cond(ZPARSER::ZIPC_ALWAYS),
			m_imm(NULL), m_opa(ZPARSER::ZIP_Rnone), m_opb(ZPARSER::ZIP_Rnone)
			{ m_state = 'T'; m_lineno = yylineno; };
	virtual	bool	isdefined(void) {
		if (m_imm != NULL) {
			bool answer = m_imm->isdefined();
			return answer;
		} else return true;
	}
	ASMLINE *eval(void);
	~TLINE(void) { if (m_imm) delete m_imm; }
	virtual	int	nlines(void); //  { return 1; }
	virtual	unsigned int	eval(const int lno);
	void	dump(FILE *fp);
};

class	AST_BRANCH : public AST { // The actual expression tree
public:
	int	m_op; // An operator
	AST	*m_left, *m_right;

	AST_BRANCH(int op, AST *l, AST *r)
		: m_op(op), m_left(l), m_right(r) { m_node_type = 'B';
		}
	~AST_BRANCH(void) {
		if (m_left)
			delete	m_left;
		if (m_right)
			delete	m_right;
	}

	bool	isdefined(void) {
		return ((m_left)&&(m_right)
				&&(m_left->isdefined())
				&&(m_right->isdefined()));
	}

	int	eval(void);
	void	reduce(void);
	void	dump(FILE *fp) {
		fprintf(fp, "(");
		m_left->dump(fp);
		fprintf(fp, ") %c (", m_node_type);
		m_right->dump(fp);
		fprintf(fp, ")");
	}
};

class	AST_NUMBER : public AST { // A number at the base of the tree
public:
	int	m_val;
	AST_NUMBER(int val) : m_val(val) { m_node_type = 'N'; }
	bool	isdefined(void) { return true; }
	int	eval(void);
	void	reduce(void);
	void	dump(FILE *fp) { fprintf(fp, "%d", m_val); }
};

class	AST_IDENTIFIER : public AST { // An identifier within the expression tree
public:
	std::string	m_id;
	AST_IDENTIFIER(const char *id) : m_id(id) { m_node_type = 'I'; }
	AST_IDENTIFIER(AST *ida, const char *idb);
	bool	isdefined(void);
	int	eval(void);
	void	reduce(void);
	void	dump(FILE *fp) { fprintf(fp, "%s", m_id.c_str()); }
};

class	AST_LABEL : public AST { // An address label within the expression tree
	// This is special, because it cannot be evaluated without knowing
	// the PC value at this address
public:
	std::string	m_label;
	AST_LABEL(const char *id) : m_label(id) { m_node_type = 'L'; }
	bool	isdefined(void);
	int	eval(void);
	void	reduce(void);
	void	dump(FILE *fp) { fprintf(fp, "%s", m_label.c_str()); }
};

class	SAVED_ASMLINE {
public:
	unsigned int	m_pc;
	ASMLINE		*m_ln;
	SAVED_ASMLINE(const unsigned int pc, ASMLINE *ln) : m_pc(pc), m_ln(ln)
		{}
};

class	OBJFILE {
	typedef	std::list<SAVED_ASMLINE> SVDTBL;

	SVDTBL		m_tbl;
	unsigned int	m_pc;
	FILE		*m_fp;

public:
	OBJFILE(void) { m_fp = NULL; m_pc = 0; }
	void open(const char *fname);
	void close(void) { fclose(m_fp); };
	unsigned int pc(void) { return m_pc; }
	void	operator+=(ASMLINE *ln);
	bool	reduce(void);
};

// The file we are building
extern	OBJFILE	objcode;

// Functions for accessing and defining elements in our symbol table
extern	bool	stb_isdefined(const char *key);
extern	int	stb_value(const char *key);
extern	void	stb_define(const char *key, AST *value);
extern	void	gbl_define(const char *key, AST *value);
extern	bool	stb_isdefined(const std::string &key); //  { return stb_isdefined(key.c_str()); }
extern	int	stb_value(const std::string &key); //  { return stb_value(key.c_str()); }
extern	void	stb_define(const std::string &key, AST *value); //  { return stb_define(key.c_str(), value); }
extern	void	gbl_define(const std::string &key, AST *value); //  { return stb_define(key.c_str(), value); }
extern	void	create_new_context(void); // Create a new symbol table context


#endif // ASMDATA_H
