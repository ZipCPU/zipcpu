/*******************************************************************************
**
** Filename: 	zasm.y
**
** Project:	Zip CPU -- a small, lightweight, RISC CPU core
**
** Purpose:	The parser for the Zip Assembler.  This is actually not just
**		the parser, but the main program as well.
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
 #include <stdlib.h>
 #include <string.h>
 #include "asmdata.h"

#define	DEFAULT_OUTPUT_FNAME	"z.out"
#define YYDEBUG 1

  extern "C" int yylex(void);
  extern "C" int yyparse(void);
  // extern "C" FILE *yyin;
  void yyerror(const char *);
  unsigned int global_parser_pc;
  char *master_input_filename = NULL;
  extern int yylineno;
  char	*linecp = NULL;	// A copy of the input line
%}

%token COMMA EQU PLUS MINUS TIMES HERE DOLLAR COLON
%token BOOLEANOR BITWISEOR BOOLEANAND BITWISEAND BITWISEXOR DOT
%token WORD FILL
%token LOADOP STOROP LDIOP
%token BAREOP BRANCHOP COND DUALOP IDENTIFIER INT LDHLOP REG SINGLOP

%union {
	ZPARSER::ZIPREG		u_reg;
	ZPARSER::ZIPCOND	u_cond;
	int			u_ival;
	LEXOPCODE		u_op;
	char			*u_id;
	ASMLINE			*u_ln;
	AST			*u_ast;
}

%type	<u_reg>		REG
%type	<u_cond>	COND opcond
%type	<u_ival>	INT
%type	<u_id>		IDENTIFIER
%type	<u_op>		BAREOP SINGLOP DUALOP BRANCHOP LDHLOP
%type	<u_ln>		unlabeledline instruction wordlist fillist opb
%type	<u_ln>		bareop singlop dualop loadop storop line
%type	<u_ast>		expr value multident

%left BOOLEANOR
%left BOOLEANAND
%left BITWISEOR BITWISEXOR
%left BITWISEAND
%left '%'
%left PLUS MINUS
%left TIMES '/'

%% /* The grammar follows */

input:
  %empty
| input line { if ($2) {objcode += $2; global_parser_pc += $2->nlines(); if ($2->isdefined()) delete $2; } }
;

line:
   '\n' { $$ = NULL; }
| unlabeledline '\n' { $$ = $1; }
| multident COLON unlabeledline '\n' {
	if ($1->m_node_type == 'I') {
		if (((AST_IDENTIFIER*)$1)->m_id[0] == 'L')
			stb_define(((AST_IDENTIFIER *)$1)->m_id, new AST_NUMBER(global_parser_pc));
		else
			gbl_define(((AST_IDENTIFIER *)$1)->m_id, new AST_NUMBER(global_parser_pc));
		delete $1;
		}
	$$ = $3;
	}
| multident COLON '\n' {
	if ($1->m_node_type == 'I') {
		if (((AST_IDENTIFIER*)$1)->m_id[0] == 'L')
			stb_define(((AST_IDENTIFIER *)$1)->m_id, new AST_NUMBER(global_parser_pc));
		else
			gbl_define(((AST_IDENTIFIER *)$1)->m_id, new AST_NUMBER(global_parser_pc));
		delete $1;
	}
	$$ = new VLINE();
	}
| multident EQU expr '\n' {
	if ($1->m_node_type == 'I') {
		stb_define(((AST_IDENTIFIER *)$1)->m_id, $3);
		delete $1;
	}
	$$ = new VLINE();
	}
;

unlabeledline:
  instruction	{ $$ = $1; }
| WORD wordlist { $$ = $2; }
| FILL fillist { $$ = $2; }
;

wordlist:
  expr	{
	if ($1->isdefined())
		$$ = new DLINE($1->eval());
	else {
		$$ = new VLINE();
		yyerror("ERROR: word list undefined");
	}}
| wordlist COMMA expr {
	if ($3->isdefined()) {
		LLINE	*ln;
		if ($1->m_state == 'L') {
			ln = ((LLINE *)$1);
		} else {
			ln = new LLINE();
			ln->addline($1);
		} ln->addline(new DLINE($3->eval()));
		$$ = ln;
	} else {
		$$ = new VLINE();
		yyerror("ERROR: word list undefined\n");
	}}
;

fillist:
  expr COMMA expr { 
		if (($1->isdefined())&&($3->isdefined())) {
			int	ntimes = $1->eval(),
				val = $3->eval();
			LLINE	*ln = new LLINE();
			for(int i=0; i<ntimes; i++)
				ln->addline(new DLINE(val));
			$$ = ln;
		} else {
			yyerror("Fill list undefined\n");
			$$ = new VLINE();
		}
	}
;

instruction:
  dualop  opb COMMA REG {
		$$ = $1;
		((TLINE*)$1)->m_imm = ((TLINE*)$2)->m_imm; ((TLINE*)$2)->m_imm = NULL;
		((TLINE*)$1)->m_opb = ((TLINE*)$2)->m_opb;
		((TLINE*)$1)->m_opa = $4;
		if ($1->isdefined()) {
			$$ = ((TLINE*)$1)->eval();
			delete $1;
			delete $2;
		}
	}
| dualop  opb COMMA multident {
		char	buf[256];
		sprintf(buf, "%s is not a register", ((AST_IDENTIFIER *)$4)->m_id.c_str());
		yyerror(buf);
		$$ = new VLINE();
		delete $1;
		delete $2;
		delete $4;
	}
| singlop opb	{
		$$ = $1;
		((TLINE*)$1)->m_imm = ((TLINE*)$2)->m_imm; ((TLINE*)$2)->m_imm = NULL;
		((TLINE*)$1)->m_opb = ((TLINE*)$2)->m_opb;
		if ($1->isdefined()) {
			$$ = ((TLINE *)$1)->eval();
			delete $1;
		}
	}
| bareop	{ $$ = $1; }
| LDHLOP  opcond expr COMMA REG {
		TLINE *tln = new TLINE;
		tln->m_opcode = $1;
		tln->m_cond   = $2;
		tln->m_imm    = $3;
		tln->m_opa    = $5;

		if (tln->isdefined()) {
			$$ = tln->eval();
			delete tln;
		} else
			$$ = tln;
	}
| LDHLOP  opcond expr COMMA multident {
		char	buf[256];
		sprintf(buf, "%s is not a register", ((AST_IDENTIFIER *)$5)->m_id.c_str());
		yyerror(buf);
		$$ = new VLINE();
		delete $3;
		delete $5;
	}
| LDIOP          expr COMMA REG {
		TLINE *tln = new TLINE;
		tln->m_opcode = OP_LDI;
		tln->m_cond   = ZPARSER::ZIPC_ALWAYS;
		tln->m_imm    = $2;
		tln->m_opa    = $4;

		if (tln->isdefined()) {
			$$ = tln->eval();
			delete tln;
		} else
			$$ = tln;
	}
| LDIOP  expr COMMA multident {
		char	buf[256];
		sprintf(buf, "%s is not a register", ((AST_IDENTIFIER *)$4)->m_id.c_str());
		yyerror(buf);
		$$ = new VLINE();
		delete $2;
		delete $4;
	}
| BRANCHOP  expr	{
		TLINE *tln = new TLINE;
		tln->m_opcode = $1;
		tln->m_imm    = $2;

		if (tln->isdefined()) {
			$$ = tln->eval();
			delete tln;
		} else
			$$ = tln;
	}
| loadop opb COMMA REG {
		TLINE *tln = new TLINE;
		((TLINE*)$2)->m_opcode = OP_LOD;
		((TLINE*)$2)->m_cond   = ((TLINE*)$1)->m_cond;
		((TLINE*)$2)->m_opa    = $4;

		delete $1;

		if (((TLINE *)$2)->isdefined()) {
			$$ = ((TLINE *)$2)->eval();
			delete $2;
		} else
			$$ = $2;
	}
| loadop opb COMMA multident {
		char	buf[256];
		sprintf(buf, "%s is not a register", ((AST_IDENTIFIER *)$4)->m_id.c_str());
		yyerror(buf);
		$$ = new VLINE();
		delete $1;
		delete $2;
		delete $4;
	}
| storop REG COMMA opb {
		TLINE *tln = new TLINE;
		tln->m_opcode = OP_STO;
		tln->m_cond   = ((TLINE*)$1)->m_cond;
		tln->m_imm    = ((TLINE*)$4)->m_imm;
		tln->m_opb    = ((TLINE*)$4)->m_opb;
		tln->m_opa    = $2;

		delete $1;

		if (tln->isdefined()) {
			$$ = tln->eval();
			delete tln;
		} else
			$$ = tln;
	}
| storop multident COMMA opb {
		char	buf[256];
		sprintf(buf, "%s is not a register", ((AST_IDENTIFIER *)$2)->m_id.c_str());
		yyerror(buf);
		$$ = new VLINE();
		delete $1;
		delete $2;
		delete $4;
	}
;

dualop: DUALOP	opcond {
	TLINE *tln = new TLINE();
	tln->m_opcode = $1;
	tln->m_cond   = $2;
	$$ = tln;
	}
;

singlop: SINGLOP opcond {
	TLINE *tln = new TLINE();
	tln->m_opcode = $1;
	tln->m_cond   = $2;
	$$ = tln;
	}
;

storop: STOROP opcond {
	TLINE *tln = new TLINE();
	tln->m_opcode = OP_STO;
	tln->m_cond   = $2;
	$$ = tln;
	}
;

loadop: LOADOP opcond {
	TLINE *tln = new TLINE();
	tln->m_opcode = OP_LOD;
	tln->m_cond   = $2;
	$$ = tln;
	}
;

bareop: BAREOP	opcond {
	TLINE *tln = new TLINE();
	tln->m_opcode = $1;
	tln->m_cond   = $2;
	$$ = tln;
	}
;

opcond:
	COND	{ $$ = $1; }
|	%empty	{ $$ = ZPARSER::ZIPC_ALWAYS; }
;

opb:
	expr	{
		TLINE *tln = new TLINE();
		tln->m_imm = $1;
		$$ = tln;
	}
|	expr PLUS REG {
		TLINE *tln = new TLINE();
		tln->m_imm = $1;
		tln->m_opb = $3;
		$$ = tln;
	}
|	expr '(' REG ')' {
		TLINE *tln = new TLINE();
		tln->m_imm = $1;
		tln->m_opb = $3;
		$$ = tln;
	}
|	'(' REG ')' {
		TLINE *tln = new TLINE();
		tln->m_imm = new AST_NUMBER(0);
		tln->m_opb = $2;
		$$ = tln;
	}
|	REG {
		TLINE *tln = new TLINE();
		tln->m_imm = new AST_NUMBER(0);
		tln->m_opb = $1;
		$$ = tln;
	}
;

expr:
	value			{ $$ = $1; }
|	MINUS value %prec TIMES	 { $$ = new AST_BRANCH('-',new AST_NUMBER(0), $2); }
|	expr PLUS expr		{ $$ = new AST_BRANCH('+',$1,$3); }
|	expr MINUS expr		{ $$ = new AST_BRANCH('-',$1,$3); }
|	expr TIMES expr		{ $$ = new AST_BRANCH('*',$1,$3); }
|	expr '/' expr		{ $$ = new AST_BRANCH('/',$1,$3); }
|	expr '%' expr		{ $$ = new AST_BRANCH('%',$1,$3); }
|	expr BOOLEANOR expr	{ $$ = new AST_BRANCH('o',$1,$3); }
|	expr BITWISEOR expr	{ $$ = new AST_BRANCH('|',$1,$3); }
|	expr BOOLEANAND expr	{ $$ = new AST_BRANCH('a',$1,$3); }
|	expr BITWISEAND expr	{ $$ = new AST_BRANCH('&',$1,$3); }
|	expr BITWISEXOR expr	{ $$ = new AST_BRANCH('^',$1,$3); }
|	'(' expr ')'		{ $$ = $2; }
;
	/* expr OR  (|) value */
	/* expr XOR (^) value */
	/* expr AND (&) value */

value:
	INT	{ $$ = new AST_NUMBER($1); }
| multident	{ $$ = $1; }
| HERE		{ $$ = new AST_NUMBER(global_parser_pc); }
;

multident:
	IDENTIFIER		{ $$ = new AST_IDENTIFIER($1); delete $1; }
| multident DOT IDENTIFIER	{ $$ = new AST_IDENTIFIER($1,$3); delete $3; }
;
%%

#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/fcntl.h>
#include <assert.h>
#include <string>

OBJFILE	objcode;

void	yyerror(const char *str) {
	fprintf(stderr, "%s:%d: ERROR: %s\n", master_input_filename, yylineno, str);
	if (linecp) fprintf(stderr, "Offending line was: %s\n", linecp);
}

FILE	*run_preprocessor(pid_t &pid, const char *path = NULL, const char *zname = NULL) {
	int	pipefd[2];

	if (pipe(pipefd)!=0) {
		fprintf(stderr, "PIPE FAILED!\n");
		perror("O/S Err:");
		exit(-2);
	} if ((zname)&&(access(zname, R_OK)!=0)) { // if !zname, then use stdin
		fprintf(stderr, "Cannot open %s\n", zname);
		perror("O/S Err:");
		exit(-2);
	}


	if (0 == (pid = fork())) {
		int	fdin, fdout;

		// Child process -- run the preprocessor

		// Close the reader: we write only
		close(pipefd[0]);

		// Adjust stdout to write to our pipe instead of anywhere else
		fdout = pipefd[1];
		close(STDOUT_FILENO);
		dup2(fdout, STDOUT_FILENO);

		char	*zpp_path;
		if (path != NULL) {
			zpp_path = new char[strlen(path+1+strlen("/zpp"))];
			strcpy(zpp_path, path);
			strcat(zpp_path, "/zpp");
		} else zpp_path = strdup("zpp");

		// This call should never return
		//	We have to pass the name here, rather than an open file,
		// since zpp needs to mark for us what file it is in at all
		// times.
		if (zname)
			execlp(zpp_path, "zpp", zname, NULL);
		else
			execlp(zpp_path, "zpp", NULL);

		fprintf(stderr, "Could not start pre-processor!\n");
		perror("O/S Err:");

		exit(-5);
	}

	close(pipefd[1]);
	return fdopen(pipefd[0], "r");
}

void	usage(void) {
	printf("USAGE: zasm [-h] [-d] [-E] [-o <out-fname>] <asm-file> [<asm-file> ]* ...\n");
	printf("\t-d\tTurns on debugging in the parser\n");
	printf("\t-E\tProduces preprocessor output only\n");
	printf("\t-h\tDisplays this message\n");
	printf("\t-o <out-fname>\tWrites the output to <out-fname>.  The\n"
		"\t\tdefault output file is \"" DEFAULT_OUTPUT_FNAME "\".\n");

	printf("\t-I <dir>\tSearch <dir> for include files.\n");
}

int	main(int argc, char **argv) {
	int	skp = 0;
	const char	*zout_fname = NULL;
	char		*path_to_zasm = NULL;
	bool	preprocess_only = false;
	FILE		*ppout;
	pid_t		zpp_pid;
	int		zpp_status;
	std::string	inclist;
	if (NULL != getenv("ZIPINC"))
		inclist = getenv("ZIPINC");

	master_input_filename = NULL;

	// Find what directory zasm is in, so that we can find zpp when
	// necessary.
	path_to_zasm = NULL;
	if (strchr(argv[0], '/')) {
		path_to_zasm = strdup(argv[0]);
		char *ptr = strrchr(path_to_zasm,'/');
		*ptr = '\0';
	}

	skp=1;
	for(int argn=0; argn+skp<argc; argn++) {
		if (argv[argn+skp][0] == '-') {
			if (argv[argn+skp][1] == 'o') {
				if (zout_fname)
					free((void *)zout_fname);
				zout_fname = strdup(argv[argn+skp+1]);
				skp++;
			} else if (argv[argn+skp][1] == 'E')
				preprocess_only = true;
			else if (argv[argn+skp][1] == 'I') {
				if (argv[argn+skp][2]) {
					if (inclist.size() != 0) {
						inclist += std::string(":");
						inclist += &argv[argn+skp][2];
					} else
						inclist = &argv[argn+skp][2];
				} else if (argn+skp+1<argc) {
					if (inclist.size() != 0) {
						inclist += std::string(":");
						inclist += argv[argn+skp+1];
					} else
						inclist = argv[argn+skp+1];
					skp++;
				}
			} else if (argv[argn+skp][1] == 'd')
				yydebug = 1;
			else if (argv[argn+skp][1] == 'h') {
				usage();
				exit(0);
			}

			skp++;
			argn--;
		} else {
			argv[argn] = argv[argn+skp];
		}
	} argc -= skp;

	if (zout_fname) {
		for(int argn=0; argn<argc; argn++) {
			if (strcmp(zout_fname, argv[argn])==0) {
				fprintf(stderr, "ERR: Cowardly refusing to overwrite \'%s\'\n", zout_fname);
				exit(-2);
			}
		}
	}

	if (preprocess_only) {
		objcode.open("/dev/null");
		if (zout_fname)
			ppout = fopen(zout_fname, "w");
		else
			ppout = stdout;
	} else {
		if (!zout_fname)
			zout_fname = DEFAULT_OUTPUT_FNAME;

		objcode.open(zout_fname);
	}

	setenv("ZIPINC",inclist.c_str(), 1);
	master_input_filename = NULL;

	if (argc > 0) {
		for(int argn=0; argn<argc; argn++) {
			extern	FILE	*yyin;
			extern	void	yyrestart(FILE *);
			FILE	*tst;

			create_new_context();
			if (master_input_filename)
				free(master_input_filename);
			master_input_filename = strdup(argv[argn]);
			if (preprocess_only) {
				FILE	*fp = run_preprocessor(zpp_pid, path_to_zasm, master_input_filename);
				int	ch;
				while(EOF != (ch = fgetc(fp)))
					fputc(ch, ppout);
				waitpid(zpp_pid, &zpp_status, WNOHANG);
			} else {
				yyrestart(run_preprocessor(zpp_pid, path_to_zasm, master_input_filename));
				yylineno = 1;
				yyparse();
				waitpid(zpp_pid, &zpp_status, WNOHANG);
			}
		}
	} else { // Run from Stdin
		extern	FILE	*yyin;
		extern	void	yyrestart(FILE *);

		create_new_context();
		master_input_filename = strdup("(stdin)");
		if (preprocess_only) {
			int	ch;
				FILE	*fp = run_preprocessor(zpp_pid, path_to_zasm, master_input_filename);
			while(EOF != (ch = fgetc(fp)))
				fputc(ch, ppout);
			waitpid(zpp_pid, &zpp_status, WNOHANG);
		} else {
			yyin = run_preprocessor(zpp_pid, NULL);
			yyrestart(yyin);
			yyparse();
			waitpid(zpp_pid, &zpp_status, WNOHANG);
		}
	}

	if (0 != WEXITSTATUS(zpp_status)) {
		if (!preprocess_only) {
			objcode.close();
			unlink(zout_fname);
		}
	} if (!objcode.reduce())
		fprintf(stderr, "Not all symbols defined!\n");
}


