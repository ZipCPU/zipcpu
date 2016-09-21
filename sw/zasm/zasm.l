/*******************************************************************************
**
** Filename: 	zasm.l
**
** Project:	Zip CPU -- a small, lightweight, RISC CPU core
**
** Purpose:	The lexical analyzer for the assembler.  This converts assembler
**		input into tokens, to feed the parser.
**
**
** Creator:	Dan Gisselquist, Ph.D.
**		Gisselquist Technology, LLC
**
********************************************************************************
**
** Copyright (C) 2015, Gisselquist Technology, LLC
**
** This program is free software (firmware): you can redistribute it and/or
** modify it under the terms of  the GNU General Public License as published
** by the Free Software Foundation, either version 3 of the License, or (at
** your option) any later version.
**
** This program is distributed in the hope that it will be useful, but WITHOUT
** ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
** for more details.
**
** You should have received a copy of the GNU General Public License along
** with this program.  (It's in the $(ROOT)/doc directory, run make with no
** target there if the PDF file isn't present.)  If not, see
** <http://www.gnu.org/licenses/> for a copy.
**
** License:	GPL, v3, as defined and found on www.gnu.org,
**		http://www.gnu.org/licenses/gpl.html
**
**
*******************************************************************************/

%{
#include <stdio.h>
#include "asmdata.h"
#include "zasm.tab.h"

extern "C" int yylex();
extern "C" int	yywrap() { return 1;}
extern	char *master_input_filename;
extern	int	decode_char_int(const char *str);
%}

%option yylineno
%option warn

%%

"#line"[ \t]+[0-9]+[ \t]+[\"][^"]*[\"][ \t]*$ {
	/* This should really be true *only* at the beginning of a line,
	* however such line beginnings aren't matching.  My guess is that
	* the reason is my line copying code at the bottom that sucks up the
	* newline for LEX.  Hence, this is what we have.
	*/
		yylineno = atoi(&yytext[6]);
		char	*bg, *en;
		bg = strchr(yytext, '\"')+1;
		en = strchr(bg, '\"'); *en = '\0';
		if ((master_input_filename == NULL)||(strcmp(master_input_filename, bg)!=0)) {
			if (!master_input_filename) delete[] master_input_filename;
			master_input_filename = new char[en-bg+2];
			strcpy(master_input_filename, bg);
		}
		return '\n';
		}
"#line"[ \t]+[0-9]+[ \t]*$	{ yylineno = atoi(&yytext[6]); return '\n';}
^"#line".*$		{ printf("WARNING: Unmatched #line: %s\n", yytext); return '\n'; }
"#line".*$		{ printf("WARNING: Unmatched #line, not at beginnning: %s\n", yytext); return '\n'; }
(?i:ur)1[0-5]	{ yylval.u_reg=(ZPARSER::ZIPREG)(26+yytext[3]-'0');return REG; }
(?i:sr)1[0-5]	{ yylval.u_reg=(ZPARSER::ZIPREG)(10+yytext[3]-'0');return REG; }
[rR]1[0-5]	{ yylval.u_reg=(ZPARSER::ZIPREG)(10+yytext[2]-'0');return REG; }
(?i:ur)[0-9]	{ yylval.u_reg=(ZPARSER::ZIPREG)(16+yytext[2]-'0');return REG; }
(?i:sr)[0-9]	{ yylval.u_reg=(ZPARSER::ZIPREG)(   yytext[2]-'0');return REG; }
[rR][0-9]	{ yylval.u_reg=(ZPARSER::ZIPREG)(   yytext[1]-'0');return REG; }
(?i:upc)	{ yylval.u_reg = ZPARSER::ZIP_uPC; return REG; }
(?i:spc)	{ yylval.u_reg = ZPARSER::ZIP_PC; return REG; }
(?i:pc)		{ yylval.u_reg = ZPARSER::ZIP_PC; return REG; }
(?i:ucc)	{ yylval.u_reg = ZPARSER::ZIP_uCC; return REG; }
(?i:scc)	{ yylval.u_reg = ZPARSER::ZIP_CC; return REG; }
(?i:cc)		{ yylval.u_reg = ZPARSER::ZIP_CC; return REG; }
(?i:usp)	{ yylval.u_reg = ZPARSER::ZIP_uSP; return REG; }
(?i:ssp)	{ yylval.u_reg = ZPARSER::ZIP_SP; return REG; }
(?i:sp)		{ yylval.u_reg = ZPARSER::ZIP_SP; return REG; }
(?i:gbl)	{ yylval.u_reg = ZPARSER::ZIP_R12; return REG; }
(?i:bra)	{ yylval.u_op  = OP_BRA; return BRANCHOP; }
(?i:brz)	{ yylval.u_op  = OP_BZ;  return BRANCHOP; }
(?i:bz)		{ yylval.u_op  = OP_BZ;  return BRANCHOP; }
(?i:bnz)	{ yylval.u_op  = OP_BNZ; return BRANCHOP; }
(?i:bne)	{ yylval.u_op  = OP_BNZ; return BRANCHOP; }
(?i:bge)	{ yylval.u_op  = OP_BGE; return BRANCHOP; }
(?i:bgt)	{ yylval.u_op  = OP_BGT; return BRANCHOP; }
(?i:bg)		{ yylval.u_op  = OP_BGT; return BRANCHOP; }
(?i:blt)	{ yylval.u_op  = OP_BLT; return BRANCHOP; }
(?i:bn)		{ yylval.u_op  = OP_BLT; return BRANCHOP; }
(?i:brc)	{ yylval.u_op  = OP_BRC; return BRANCHOP; }
(?i:bc)		{ yylval.u_op  = OP_BRC; return BRANCHOP; }
(?i:brv)	{ yylval.u_op  = OP_BRV; return BRANCHOP; }
(?i:bv)		{ yylval.u_op  = OP_BRV; return BRANCHOP; }
(?i:clr)	{ yylval.u_op  = OP_CLR; return SINGLOP; }
(?i:clrf)	{ yylval.u_op  = OP_CLRF;return SINGLOP; }
(?i:int)	{ yylval.u_op  = OP_TRAP;return SINGLOP; }
(?i:trap)	{ yylval.u_op  = OP_TRAP;return SINGLOP; }
(?i:jmp)	{ yylval.u_op  = OP_JMP; return SINGLOP; }
(?i:neg)	{ yylval.u_op  = OP_NEG; return SINGLOP; }
(?i:not)	{ yylval.u_op  = OP_NOT; return SINGLOP; }
(?i:cmp)	{ yylval.u_op  = OP_CMP; return DUALOP; }
(?i:tst)	{ yylval.u_op  = OP_TST; return DUALOP; }
(?i:mov)	{ yylval.u_op  = OP_MOV; return DUALOP; }
(?i:ldi)	{ yylval.u_op  = OP_LDI; return LDIOP; }
(?i:ldihi)	{ yylval.u_op =OP_LDIHI; return LDHLOP; }
(?i:lhi)	{ yylval.u_op =OP_LDIHI; return LDHLOP; }
(?i:ldilo)	{ yylval.u_op =OP_LDILO; return LDHLOP; }
(?i:llo)	{ yylval.u_op =OP_LDILO; return LDHLOP; }
(?i:mpyu)	{ yylval.u_op = OP_MPYU; return DUALOP; }
(?i:mpys)	{ yylval.u_op = OP_MPYS; return DUALOP; }
(?i:rol)	{ yylval.u_op  = OP_ROL; return DUALOP; }
(?i:sub)	{ yylval.u_op  = OP_SUB; return DUALOP; }
(?i:and)	{ yylval.u_op  = OP_AND; return DUALOP; }
(?i:add)	{ yylval.u_op  = OP_ADD; return DUALOP; }
(?i:or)		{ yylval.u_op  = OP_OR; return DUALOP;; }
(?i:xor)	{ yylval.u_op  = OP_XOR; return DUALOP; }
(?i:lsl)	{ yylval.u_op  = OP_LSL; return DUALOP; }
(?i:asr)	{ yylval.u_op  = OP_ASR; return DUALOP; }
(?i:lsr)	{ yylval.u_op  = OP_LSR; return DUALOP; }
(?i:ljmp)	{ yylval.u_op = OP_LJMP;  return BAREOP; }
(?i:lod)	{ yylval.u_op = OP_LOD;   return LOADOP; }
(?i:sto)	{ yylval.u_op = OP_STO;   return STOROP; }
(?i:halt)	{ yylval.u_op = OP_HALT;  return BAREOP;  }
(?i:wait)	{ yylval.u_op = OP_HALT;  return BAREOP;  }
(?i:rtu)	{ yylval.u_op = OP_RTU;   return BAREOP;  }
(?i:retn)	{ yylval.u_op = OP_RETN;   return BAREOP;  }
(?i:ret)	{ yylval.u_op = OP_RETN;   return BAREOP;  }
(?i:nop)	{ yylval.u_op = OP_NOOP;  return BAREOP; }
(?i:noop)	{ yylval.u_op = OP_NOOP;  return BAREOP; }
(?i:break)	{ yylval.u_op = OP_BREAK; return BAREOP; }
(?i:brk)	{ yylval.u_op = OP_BREAK; return BAREOP; }
(?i:busy) 	{ yylval.u_op = OP_BUSY;  return BAREOP; }
(?i:brev) 	{ yylval.u_op = OP_BREV;  return DUALOP; }
(?i:popc) 	{ yylval.u_op = OP_POPC;  return DUALOP; }
(?i:divu) 	{ yylval.u_op = OP_DIVU;  return DUALOP; }
(?i:divs) 	{ yylval.u_op = OP_DIVS;  return DUALOP; }
(?i:fpadd) 	{ yylval.u_op = OP_FPADD;  return DUALOP; }
(?i:fpsub) 	{ yylval.u_op = OP_FPSUB;  return DUALOP; }
(?i:fpmul) 	{ yylval.u_op = OP_FPMUL;  return DUALOP; }
(?i:fpdiv) 	{ yylval.u_op = OP_FPDIV;  return DUALOP; }
(?i:fpcvt) 	{ yylval.u_op = OP_FPCVT;  return DUALOP; }
(?i:fpint) 	{ yylval.u_op = OP_FPINT;  return DUALOP; }
(?i:mpyshi) 	{ yylval.u_op = OP_MPYSHI;  return DUALOP; }
(?i:mpyuhu) 	{ yylval.u_op = OP_MPYUHI;  return DUALOP; }
(?i:mpy) 	{ yylval.u_op = OP_MPY;  return DUALOP; }
(?i:equ)	{ return EQU; }
(?i:fill)	{ return FILL; }
(?i:word)	{ return WORD; }
"__"[hH][eE][rR][eE]"__" { return HERE; }
[\.][dD][aA][tT] { return WORD; }
[\.](?i:z)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_Z;  return COND; }
[\.](?i:ne)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_NZ; return COND; }
[\.](?i:nz)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_NZ; return COND; }
[\.](?i:ge)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_GE; return COND; }
[\.](?i:gt)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_GT; return COND; }
[\.](?i:lt)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_LT; return COND; }
[\.](?i:n)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_LT; return COND; }
[\.](?i:c)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_C;  return COND; }
[\.](?i:v)/[ \t\n]	{ yylval.u_cond = ZPARSER::ZIPC_V;  return COND; }
[_A-Za-z][_a-zA-Z0-9]*  { yylval.u_id  = strdup(yytext);    return IDENTIFIER; }
"$"?[-]?0[xX][0-9A-Fa-f]+ { yylval.u_ival = strtoul(yytext+(((*yytext)=='$')?1:0),NULL,16);return INT;}
"$"?[-]?0[0-7]+		  { yylval.u_ival = strtoul(yytext+(((*yytext)=='$')?1:0),NULL, 8);return INT;}
"$"?[-]?[1-9][0-9]*	  { yylval.u_ival = strtoul(yytext+(((*yytext)=='$')?1:0),NULL,10);return INT;}
"$"?[-]?[1-9A-Fa-f][0-9A-Fa-f]*h {yylval.u_ival=strtoul(yytext+(((*yytext)=='$')?1:0),NULL,16); return INT;}
"$"?[-]?[0-7]+o		{ yylval.u_ival = strtoul(yytext+(((*yytext)=='$')?1:0),NULL, 8);return INT;}
"\'"(("\\\'")|([^'\\])|("\\"[0abfnrtv])|("\\\\")|("\\\"")){1,4}"\'" {
		yylval.u_ival = decode_char_int(&yytext[1]); return INT; }
"$"?"0"		  { yylval.u_ival = 0;return INT;}
"$"		{ return DOLLAR; }
","		{ return COMMA; }
"+"		{ return PLUS; }
"-"		{ return MINUS; }
"*"		{ return TIMES; }
"||"		{ return BOOLEANOR; }
"|"		{ return BITWISEOR; }
"&&"		{ return BOOLEANAND; }
"&"		{ return BITWISEAND; }
"^"		{ return BITWISEXOR; }
":"		{ return COLON; }
"."		{ return DOT; }
"%"		{ return '%'; }
[ \t]+		{ }
[(]		{ return '('; }
[)]		{ return ')'; }
\n.*		{ if (linecp) free(linecp); linecp = strdup(&yytext[1]); yyless(1); return '\n'; }

%%

int	decode_char_int(const char *str) {
	unsigned r = 0;
	// fprintf(stderr, "Decoding character string: \'%s\n", str);
	while((*str)&&('\'' != (*str))) {
		if ('\\' == (*str)) {
			// Process escape characters
			str++;
			if ('\0' != (*str)) {
				r<<=8;
				switch(*str) {
				case '0': break;
				case  'a': r |= '\a'; break;
				case  'b': r |= '\b'; break;
				case  'n': r |= '\n'; break;
				case  'f': r |= '\f'; break;
				case  'r': r |= '\r'; break;
				case  't': r |= '\t'; break;
				case  'v': r |= '\v'; break;
				case '\'': r |= '\''; break;
				case '\"': r |= '\"'; break;
				case '\\': r |= '\\'; break;
				} str++;
			}
		} else {
			r = (r<<8)|(*str);
			str++;
		} 
	} return r;
}
