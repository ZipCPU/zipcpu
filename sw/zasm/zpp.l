/*******************************************************************************
**
** Filename: 	zpp.l
**
** Project:	Zip CPU -- a small, lightweight, RISC CPU core
**
** Purpose:	The preprocessor for the Zip Assembler.
**
**	This routine strips comments, handles #define's, #ifdef's, and
**	#include statements in a C fashion.
**
**	#define macro's are also defined in the language and therefore
**	supposed to be supported, but the support isn't there yet.
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
// #include <FlexLexer.h>
#include <string>
#include <ctype.h>
#include <stdio.h>
#include <list>
#include <vector>
#include <assert.h>

using namespace std;

int yylex();
void	mark_line(void);
int	end_of_file(void);
void	pushf(const char *fname);

// #include "zprepr.tab.h"
int	ndef = 0, structno = 0;
char	*structid = NULL;
void	stb_define(const char *str);
bool	stb_current(const char *str);
bool	stb_hasargs(const char *str);
void	stb_expand(FILE *fout, const char *str);
std::string	stb_expand(const char *str);
void	stb_args(const char *str);
void	stb_macro(const char *value);
void	stb_addmacro(const char *value);
bool	stb_isdefined(const char *str);
const char	*stb_getdefn(const char *str);
%}
%x DEF DFA DFV DFV_EOL INDEF IFDEFV INNOTDEF NODEF NVRDEF COMMENT INSTRUCT
%x INDEF_EOL INNOTDEF_EOL GETSTRUCTID NVRDEF_EOL DONTDEF
%option noyywrap
%option stack
ID [_:A-Za-z][_:A-Za-z0-9]*
IDDOT {ID}("."{ID})*

%%
<COMMENT>"*/"		{ yy_pop_state(); }
<COMMENT>[^*\n]+	{ /* Ignore comments */ }
<COMMENT>"*"+[^/]	{ /* Ignore comments */ }
<INITIAL,INDEF>^"#include"[ \t]+\"[^\n\"]+\"	{
		char *ptr = &yytext[9], *start, *end, *str;
		while(isspace(*ptr))
			ptr++;
		start = ++ptr;
		ptr++;
		while((*ptr)&&(*ptr != '\"'))
			ptr++;
		*ptr = '\0';
		pushf(start);
		// push_file_state(yylineno); // and filename ...
		mark_line();
	}
<INITIAL,INDEF>^"#define"[ \t]+	{ yy_push_state(DEF); }
 /* <*>^"#line"[ \t]+(0-9)+[ \t]+["][^"]*["][ \t]*\n	{ } */
<DEF>{IDDOT}/[^(]	{
		// fprintf(stderr, "Defining \'%s\'\n", yytext);
		stb_define(yytext);
		BEGIN DFV;
	}
<DEF>{IDDOT}/[(]	{ stb_define(yytext); BEGIN DFA; }
<DFA>"("[^)\n]+")"				{
		/* Process macro arguments */
		stb_args(yytext);
		BEGIN DFV;
	}
<DFV>^[ \t]+	{ stb_macro(yytext); /* Replicate initial spaces */ }
<DFV>[ \t]+	{ stb_macro(" "); /* Ignore all  but one internal space */ }
<DFV>{ID}	{/* Parse to end of line, get value for our define */
		// fprintf(stderr, "%s may be a macro, line %d\n", yytext, yylineno);
		if ((!stb_current(yytext))&&(stb_isdefined(yytext))) {
			// fprintf(stderr, "Recursive MACRO!\n");
			stb_macro(stb_getdefn(yytext));
		} else {
			// fprintf(stderr, "But it is not defined\n");
			stb_macro(yytext);
		}
	}
<DFV>{ID}[ \t]*[(][ \t]*{ID}[ \t]*(,[ \t]*{ID}[ \t]*)*[)]	{ 
		// fprintf(stderr, "%s may be a macro within a macro!\n", yytext);
		if ((!stb_current(yytext))&&(stb_isdefined(yytext))) {
			if (stb_hasargs(yytext)) {
				std::string str = stb_expand(yytext);
				stb_macro(str.c_str());
			} else {
				char *dup = strdup(yytext), *ptr;
				ptr = strchr(dup, '(');
				*ptr = '\0';
				stb_macro(stb_getdefn(dup));
				free(dup);
				yyless(strchr(yytext,'(')-yytext);
			}
		} else if (!stb_current(yytext)) {
			stb_macro(yytext);
		} else {
			char *dup = strdup(yytext), *ptr;
			ptr = strchr(dup, '(');
			*ptr = '\0';
			stb_macro(stb_getdefn(dup));
			free(dup);
			yyless(strchr(yytext,'(')-yytext);
		}
	}
<DFV>[^a-zA-Z_0-9 \t\n]+	{/* Parse to end of line, get value for our define */
		// fprintf(stderr, "A: Adding to macro %s\n", yytext);
		stb_macro(yytext);
	}
<DFV>0[xX][0-9A-Fa-f]+	{/* Get any hexadecimal constants */
		// fprintf(stderr, "B: Adding to macro %s\n", yytext);
		stb_macro(yytext);
	}
<DFV>[0-9A-Fa-f]+[hH]	{/* Get any hexadecimal constants */
		// fprintf(stderr, "C: Adding to macro %s\n", yytext);
		stb_macro(yytext);
	}
<DFV>[0-7]+[oO]	{/* Get any octal constants */
		// fprintf(stderr, "D: Adding to macro %s\n", yytext);
		stb_macro(yytext);
	}
<DFV>[0-9]+	{/* Get any decimal constants */
		// fprintf(stderr, "E: Adding to macro %s\n", yytext);
		stb_macro(yytext);
	}
<DFV>[ \t]*((;|"//").*)?$	{/* Parse to end of line, get value for our define */
		yy_pop_state();
	}
<DFV>[ \t]*"\\"[ \t]*((;|"//").*)?\n	{/* Continue onto next line */
		fprintf(yyout, "\n"); mark_line(); yylineno++;
		stb_macro("\n");
	}
<INNOTDEF,NODEF,NVRDEF>^"#define".*$	{ yy_push_state(DONTDEF); }
<DONTDEF>"\\"[ \t]*((;"//").*)?\n	{/* Continue onto next line */
		fprintf(yyout, "\n"); mark_line(); yylineno++; }
<DONTDEF>[a-zA-Z0-9_,.()]*	{ }
<DONTDEF>[ \t]*			{ }
<DONTDEF>((;|"//").*)?$		{ yy_pop_state(); }
<DONTDEF>"\\"[ \t]*((;|"//").*)?\n	{/* Continue onto next line */
		fprintf(yyout, "\n"); mark_line(); yylineno++; }
<INITIAL,INDEF>^[ \t]+.[dD][aA][tT][aA]?	{ fprintf(yyout, "\tWORD"); }
<INITIAL,INDEF>^"#defcont"[ \t]+	{
		yy_push_state(DFV); }
<INITIAL,INDEF>^"#ifdef"[ \t]*	{ ndef = 0;
		yy_push_state(IFDEFV); }
<INITIAL,INDEF>^"#ifndef"[ \t]*	{ ndef = 1;
		yy_push_state(IFDEFV); }
<INNOTDEF,NODEF,NVRDEF>^"#ifdef"[ \t]*	{ ndef = 2;
		yy_push_state(IFDEFV); }
<INNOTDEF,NODEF,NVRDEF>^"#ifndef"[ \t]*	{ ndef = 2;
		yy_push_state(IFDEFV); }
<IFDEFV>{IDDOT}	{
		bool	known = stb_isdefined(yytext);
		if (ndef == 2) {
			BEGIN NVRDEF_EOL;
		} else if ( ((known)&&(ndef==0)) || ((!known)&&(ndef!=0)) ) {
			BEGIN INDEF_EOL;
		} else {
			BEGIN INNOTDEF_EOL;
		}
	}
	/* Not yet: <INITIAL,INDEF>^"#if"[ \t]*		{ yy_push_state(IFDEFE); }
	/* Not yet: <INITIAL,INDEF>^"#if"[ \t]*		{ yy_push_state(IFDEFE); }
	/* Not yet: <IFDEFE><expr> { yy_push_state(IFDEFE); } */
	/* <INNOTDEF>^"#elsif"[ \t]*	{ yy_pop_state(); yy_push_state(IFDEFE); } */
<INDEF_EOL>[ \t]*$		{ BEGIN INDEF; }
<INDEF_EOL>(;|"//").*$		{ BEGIN INDEF; }
<INNOTDEF_EOL>[ \t]*$		{ BEGIN INNOTDEF; }
<INNOTDEF_EOL>(;|"//").*$	{ BEGIN INNOTDEF; }
<NVRDEF_EOL>[ \t]*$		{ BEGIN NVRDEF; }
<NVRDEF_EOL>(;|"//").*$		{ BEGIN NVRDEF; }
<NVRDEF_EOL>[^ \t\n].*$		{ BEGIN INDEF; mark_line(); }
<INNOTDEF_EOL>[^ \t\n].*$	{ BEGIN INNOTDEF; mark_line(); }
<INDEF,NVRDEF>^"#else"[ \t]*((;|"//").*)?$	{ BEGIN NODEF; }
<INNOTDEF>^"#else"[ \t]*((;|"//").*)?$		{ BEGIN INDEF; }
<INNOTDEF,NVRDEF,NODEF>^[^#\n]([^\n]*)$		{ /* Skip text */ }
<INDEF>^"#elsif"[ \t]*		{ BEGIN NVRDEF; }
<NVRDEF,NODEF,INDEF,INNOTDEF>^"#endif"[ \t]*((;|"//").*)?$	{
				yy_pop_state(); }
<NVRDEF,NODEF,INDEF,INNOTDEF>^"#endif"[ \t]*"/*"	{ BEGIN COMMENT; }
<NVRDEF,NODEF,INDEF,INNOTDEF>^"#endif"	{ yy_pop_state(); }
<*>^"#ifdef"[ \t]*		{ fprintf(stderr, "ERR: Line %d, Unknown ifdef!! (state = %d)\n", yylineno, YYSTATE);}
<*>^"#else"[ \t]*		{ fprintf(stderr, "ERR: Line %d, Unknown else!! (state = %d)\n", yylineno, YYSTATE);}
<*>^"#endif"[ \t]*		{ fprintf(stderr, "ERR: Line %d, Unknown endif!! (state = %d)\n", yylineno, YYSTATE);}
<INITIAL,INDEF>^"#struct"[ \t]*	{ yy_push_state(GETSTRUCTID); structno  = 0; }
<*>^"#"{ID}[ \t]*		{
	fprintf(stderr, "ERR: Line %d, unrecognized preprocessor instruction, \'%s\' (state = %d)\n",
			yylineno, yytext, YYSTATE);
	}
<GETSTRUCTID>{ID}/[ \t\n;/]	{ BEGIN INSTRUCT;
		structid = strdup(yytext);
		}
<INSTRUCT>{ID}("."{ID})*	{ 
		fprintf(yyout, "\t%s.%s\tequ\t%d", structid, yytext, structno++); }
<INSTRUCT>^"#endstruct".*$	{ yy_pop_state(); }
	/* Not yet: ^"#struct"[ \t]*	{}	*/
	/* Not yet: ^"#endstruct"[ \t]*	{}	*/
	/* Not yet: ^"#seg"[ \t]*	{}	*/
<INITIAL,INDEF>{ID}/[^(]	{ 
		if (stb_isdefined(yytext))
			fprintf(yyout, "%s", stb_getdefn(yytext));
		else
			fprintf(yyout, "%s", yytext);
	}
<INITIAL,INDEF>{ID}([ \t]*)	{ 
		if (stb_isdefined(yytext))
			fprintf(yyout, "%s", stb_getdefn(yytext));
		else
			fprintf(yyout, "%s", yytext);
	}
<INITIAL,INDEF>{ID}[ \t]*[(][ \t]*{ID}[ \t]*(,[ \t]*{ID}[ \t]*)*[)]	{ 
		// fprintf(stderr, "%s may be a macro!\n", yytext);
		if (stb_isdefined(yytext)) {
			if (stb_hasargs(yytext)) {
				stb_expand(yyout, yytext);
			} else {
				fprintf(yyout, "%s", stb_getdefn(yytext));
				yyless(strchr(yytext,'(')-yytext);
			}
		} else {
			// fprintf(stderr, "But it is not defined\n");
			fprintf(yyout, "%s", yytext);
		}
	}
<INITIAL,INDEF>"\'"(("\\\'")|([^'\\])|("\\"[0abfnrtv])|("\\\\")|("\\\"")){1,4}"\'" { ECHO; }
<*>[ \t]*"//".*$	{ /* Ignore (trailing) comment only lines */ }
<*>[ \t]*";".*$		{ /* Ignore (trailing) comment only lines */ }
<*>"#warning".*$	{ fprintf(stderr, "WARNING: %s\n", &yytext[8]); }
<*>"#error".*$		{ fprintf(stderr, "ERROR: %s\n", &yytext[8]); exit(-1); }
<*>"/*"			{ yy_push_state(COMMENT); }
<*>[ \t]+		{ ECHO; }
<*>\n			{ ECHO; yylineno++; mark_line(); }
	/* <*>.			{ printf("Unmatched \'%c\'\n", yytext[0]); } */
<NVRDEF,NODEF,INDEF,INNOTDEF><<EOF>>	{ fprintf(stderr, "Unexpected EOF!  Expecting #endif\n"); yyterminate(); }
<IFDEFV><<EOF>>		{ fprintf(stderr, "Unexpected EOF!  Expecting #endif\n"); yyterminate(); }
<COMMENT><<EOF>>	{ fprintf(stderr, "Unexpected EOF!  Expecting */\n"); yyterminate(); }
<INSTRUCT><<EOF>>	{ fprintf(stderr, "Unexpected EOF!  Expecting #endstruct\n"); yyterminate(); }
<GETSTRUCTID><<EOF>>	{ fprintf(stderr, "Unexpected EOF!  Expecting #struct ID, then #endstruct\n"); yyterminate(); }
<DFA,DFV,DFV_EOL><<EOF>> { fprintf(stderr, "Unexpected EOF!  Expecting end of line\n"); yyterminate(); }
<INDEF_EOL,INNOTDEF_EOL><<EOF>	{ fprintf(stderr, "Unexpected EOF  Expecting end of line, then #endif\n"); yyterminate(); }
<INITIAL><<EOF>>	{ if (end_of_file()) yyterminate(); }

%%

class	SYMTABLE_ACTION {
public:
	// Types: 0 (end of actions), 1-X, argument number, <0 raw string
	int		m_type;
	std::string	m_str;		// if m_type < 0, have m_str
};

class	SYMTABLE_ENTRY {
private:
	bool	m_reduced;
	std::string	&trim(std::string &s) {
		std::string::iterator	ptr = s.end();

		while((ptr >= s.begin())&&(isspace(*ptr)))
			*ptr-- = '\0';

		return s;
	}

public:
	std::string	m_name, m_value, m_args;
	std::vector<SYMTABLE_ACTION>	m_actions;
	SYMTABLE_ENTRY(const char *str) : m_name(str) {
		trim(m_name);
		m_reduced = false;
	}
	SYMTABLE_ENTRY &operator+=(const char *str) {
		const char	*start = str;

		while(isspace(*start))
			start++;
		if (m_value.length()!=0)
			m_value += " ";

		m_value += str;

		/*
		printf("ENTRY::SYMBOL \'%s\' NOW = \'%s\'\n",
			m_name.c_str(), m_value.c_str());
		*/
		return *this;
	}
	SYMTABLE_ENTRY &setargs(const char *str) {
		m_args += str;
		return *this;
	}

	const std::string &getdefn(void) {
		return m_value;
	}

	bool	hasargs(void) {
		return (m_args.size()>0);
	}

	void	reduce(void) {
		if (m_reduced)
			return;

		// fprintf(stderr, "Reducing %s ( %s ) \n", m_name.c_str(), m_args.c_str());
		std::vector<std::string>	alist;
		int i=0, bg, en;
		do {
			if ((m_args[i] == ',')||(m_args[i] == '('))
				i++;
			while((m_args[i])&&(isspace(m_args[i])))
				i++;
			bg = i;
			while((m_args[i])&&(
				(isalpha(m_args[i]))
				||(m_args[i]==':')
				||(m_args[i]=='_')
				||(isdigit(m_args[i]))))
				i++;
			en = i;
			while((m_args[i])&&(isspace(m_args[i])))
				i++;

			alist.push_back(m_args.substr(bg,en-bg));
			// printf("Found argument %2ld of %s: \'%s\'\n",
				// alist.size(),
				// m_name.c_str(),
				// m_args.substr(bg,en-bg).c_str());
		} while((m_args[i])&&(m_args[i] == ','));

		assert(m_args[i] == ')');

		// Now that we know our arguments, lets look for these
		// arguments in our macro definition
		std::string	building;
		i = 0;
		while(m_value[i]) {
			int	nxti = m_value.size(), nxtv;
			for(int a=0; a<alist.size(); a++) {
				const char *ptr;
				ptr = strstr(m_value.c_str()+i, alist[a].c_str());
				while((ptr)&&(ptr-m_value.c_str() < nxti)) {
					int loc = ptr-m_value.c_str();
					const char *pre = ptr-1;
					const char *pst = ptr+alist[a].size();
					if ((loc < nxti)&&(
						(loc == i)
						||((!isalpha(*pre)
							&&(*pre != '_')
							&&(*pre != ':')
							&&(!isdigit(*pre)))))
						&&((*pst=='\0')
					  	||(	(!isalpha(*pst))
							&&(*pst != '_')
							&&(*pst != ':')
							&&(!isdigit(*pst)))))
					{
					 		nxti = loc;
							nxtv = a;
							break;
					} else {
						ptr = strstr(m_value.c_str()+loc, alist[a].c_str());
						loc = ptr-m_value.c_str();
					}
				}
			}

			if (nxti < m_value.size()) {
				// Found an argument!!
				SYMTABLE_ACTION	act;
				if (nxti > i) {
					act.m_type = -1;
					act.m_str = m_value.substr(i,nxti-i);
					// printf("ACTION: \'%s\'\n", act.m_str.c_str());
					m_actions.push_back(act);
				}
				act.m_type = nxtv;
				act.m_str = "";
				m_actions.push_back(act);
				// printf("ACTION[%2d]: \'%s\'\n", nxtv, alist[nxtv].c_str());
				
				i = nxti+alist[nxtv].size();
			} else break; // No more arguments
		} if (i<m_value.size()) {
			SYMTABLE_ACTION act;
			act.m_type = -1;
			act.m_str = m_value.substr(i);
			// printf("ACTION: \'%s\'\n", act.m_str.c_str());
			m_actions.push_back(act);
		}
		m_reduced = true;
	}

	std::string expand(std::string args) {
		if (!m_reduced)
			reduce();
		std::vector<std::string>	alist;
		std::string	result;

		// printf("Expanding %s\n", args.c_str());
		int i=0, bg, en, nest=-1;
		do {
			if ((args[i] == '(')||(args[i] == ',')) {
				if (args[i] =='(')
					nest++;
				i++;
			}
			while((args[i])&&(isspace(args[i])))
				i++;
			bg = i;
			while((args[i])&&(args[i] != ',')&&((args[i] != ')')||(nest != 0))) {
				if (args[i] == '(')
					nest++;
				else if (args[i] == ')')
					nest--;
				i++;
			} en = i-1;
			while((en>0)&&(isspace(args[en])))
				en--;
			alist.push_back(args.substr(bg,en+1-bg));
			// printf("Argument %2ld of %s maps to \'%s\'\n",
				// alist.size(),
				// m_name.c_str(),
				// args.substr(bg,en+1-bg).c_str());
		} while((args[i])&&(args[i] == ','));

		// printf("At end, args[i] = \'%s\'\n", &args[i]);
		assert(args[i] == ')');

		// printf("Filling in %ld actions\n", m_actions.size());
		for(i=0; i<m_actions.size(); i++) {
			if((m_actions[i].m_type >= 0)&&(m_actions[i].m_type < alist.size()))
				result += alist[m_actions[i].m_type].c_str();
			else if (m_actions[i].m_type < 0)
				result += m_actions[i].m_str.c_str();
			// else {
				// fprintf(fout, "m_type = %d, size = %ld\n", m_actions[i].m_type, alist.size());
			// }
		}

		return result;
	}
};

class	SYMBOL_TABLE {
private:
	typedef	SYMTABLE_ENTRY 	*TBLV;
	typedef	std::list<TBLV>	TBLT;

	TBLT	m_tbl;
	TBLT::iterator	lookup(const char *str) {
		TBLT::iterator	i = m_tbl.begin();
		for(; (i!= m_tbl.end())&&(strcmp(str, (*i)->m_name.c_str())>0); i++)
			;
		if ((i != m_tbl.end())&&(strcmp(str, (*i)->m_name.c_str())==0))
			return i;
		return m_tbl.end();
	}

public:
	SYMBOL_TABLE(void) {}

	void define(const char *str) {
		SYMTABLE_ENTRY	*v = new SYMTABLE_ENTRY(str);
		TBLT::iterator	i = m_tbl.begin();
		for(; (i!= m_tbl.end())&&(strcmp(str, (*i)->m_name.c_str())>0); i++)
			;
		m_tbl.insert(i, v);

		// fprintf(stderr, "SYMS::Defining SYMBOL: \'%s\'\n", str);
	}

	bool defined(const char *str) {
		TBLT::iterator	i = lookup(str);
		if (i==m_tbl.end())
			return false;
		else
			return true;
	}


	void	undefine(const char *str) {
		TBLT::iterator	i = lookup(str);
		if (i == m_tbl.end())
			return;
		TBLV	v = (*i);
		m_tbl.erase(i);
		delete	v;
	}

	void	addmacro(const char *name, const char *str) {
		TBLT::iterator i = lookup(name);
		if (i == m_tbl.end()) {
			fprintf(stderr, "ADDMACRO::INTERNAL ERR, \'%s\' NOT DEFINED!\n", name);
		} *(*i) += str;
	}
				
	void	addargs(const char *name, const char *str) {
		TBLT::iterator i = lookup(name);
		if (i == m_tbl.end()) {
			fprintf(stderr, "INTERNAL ERR, %s NOT DEFINED!\n", name);
		} (*i)->setargs(str);
	}
	bool	hasargs(const char *name) {
		TBLT::iterator i = lookup(name);
		if (i == m_tbl.end()) {
			return false;
		} return (*i)->hasargs();
	}
	const	char *getdefn(const char *name) {
		TBLT::iterator i = lookup(name);
		if (i == m_tbl.end()) {
			fprintf(stderr, "GETDEFN::INTERNAL ERR, \'%s\' NOT DEFINED!\n", name);
			return NULL;
		} (*i)->getdefn().c_str();
	}

	std::string	expand(const char *name, const char *ptr) {
		TBLT::iterator  i = lookup(name);
		if (i==m_tbl.end())
			return std::string("");
		return (*i)->expand(std::string(ptr));
	}
				
};

SYMTABLE_ENTRY	*last = NULL;
SYMBOL_TABLE	syms;
std::string	last_define;

char	*stb_trim(const char *str) {
	// fprintf(stderr, "Checking whether %s needs to be expanded\n",str);
	char *dup = strdup(str), *chr;
	chr = strchr(dup, '(');
	if (chr != NULL)
		*chr = '\0';
	// fprintf(stderr, "\tLooking it up by the name \'%s\'\n", dup);

	// Now, let's trim our string
	char	*end = dup+strlen(dup)-1;
	while((*dup)&&(end>dup)&&(isspace(*end)))
		*end-- = '\0';
	return dup;
}

void	stb_define(const char *str) {
	/*
	if (last_define.size()>0) {
		fprintf(stderr, "LAST-DEFINE(%s): %s\n", last_define.c_str(),
			stb_getdefn(last_define.c_str()));
	} */
	char	*alt = stb_trim(str);
	if (syms.defined(alt)) {
		fprintf(stderr, "WARNING!  Symbol \'%s\' is already defined!\n", str);
		syms.undefine(str);
	}

	syms.define(alt);
	last_define = alt;
	free(alt);
}

void	stb_args(const char *args) {
	syms.addargs(last_define.c_str(), args);
}

void	stb_macro(const char *value) {
	syms.addmacro(last_define.c_str(), value);
}

void	stb_addmacro(const char *value) {
	syms.addmacro(last_define.c_str(),value);
}

bool	stb_isdefined(const char *str) {
	char	*dup = stb_trim(str);
	bool r = (syms.defined(dup));
	free(dup);
	return r;
}

const char *stb_getdefn(const char *str) {
	char	*dup = stb_trim(str);
	const char	*r;
	r = syms.getdefn(dup);
	free(dup);
	return r;
}

bool	stb_current(const char *str) {
	return (strcmp(str, last_define.c_str())==0);
}

bool	stb_hasargs(const char *str) {
	char	*dup = stb_trim(str);
	bool r = (syms.hasargs(dup));
	// fprintf(stderr, "\t%s has %sarguments\n", dup, (r)?"":"no ");
	free(dup);
	return r;
}

std::string	stb_expand(const char *macro) {
	const	char	*ptr;
	std::string	str;
	ptr = strchr(macro, '(');
	assert(ptr);
	ptr--;
	while((ptr>macro)&&(isspace(*ptr)))
		ptr--;
	char *nam = strndup(macro, ptr+1-macro);
	ptr = strchr(ptr, '(');
	// fprintf(stderr, "Requesting an expansion of %s -- %s\n", nam, ptr);
	str = syms.expand(nam, ptr);
	free(nam);

	return str;
}

void	stb_expand(FILE *fout, const char *macro) {
	std::string	str = stb_expand(macro);
	fprintf(fout, "%s", str.c_str());
}

class	BUFSTACK {
public:
	FILE		*m_fp;
	char		*m_fname;
	int		m_lineno;
	BUFSTACK	*m_prev;
	YY_BUFFER_STATE	m_bs;

	static	BUFSTACK	*curbs;
	static	const char	*curfilename;

	BUFSTACK(void) {
		m_fp = stdin;

		if (curbs)
			curbs->m_lineno = yylineno;
		m_prev = curbs;
		// m_bs = yy_create_buffer(fp, YY_BUF_SIZE);
		m_fname = strdup("(stdin)");
		// yy_switch_to_buffer(m_bs);
		m_bs = NULL;
		curbs = this;
		m_lineno = 1;
		curfilename = m_fname;

		yyrestart(m_fp);
		yylineno = 1;
	}

	BUFSTACK(const char *fname) {
		m_fp = fopen(fname, "r");
		if (!m_fp) {
			char *pathptr = getenv("ZIPINC");
			if (!pathptr) {
				fprintf(stderr, "Cannot open %s\n", fname);
				perror("O/S Err:");
				exit(-1);
			} else {
				char	*dptr, *colonp;
				char *pathcpy = new char[strlen(pathptr)+8192];
				strcpy(pathcpy, pathptr);

				// fprintf(stderr, "ZIPINC := %s\n", pathptr);
				dptr = pathptr;
				while((!m_fp)&&(NULL != (colonp = strchr(dptr, ':')))) {
					strncpy(pathcpy, dptr, colonp-pathptr);
					strcat(pathcpy, "/");
					strcat(pathcpy, fname);
					// fprintf(stderr, "Looking for include file, %s\n", pathcpy);
					if (access(fname, R_OK)==0)
						m_fp = fopen(pathcpy, "r");
					dptr = colonp+1;
				} if ((!m_fp)&&(*dptr)) {
					strcpy(pathcpy, dptr);
					strcat(pathcpy, "/");
					strcat(pathcpy, fname);
					// fprintf(stderr, "Looking for include file, %s\n", pathcpy);
					m_fp = fopen(pathcpy, "r");
				} if (!m_fp) {
					fprintf(stderr, "Cannot open %s\n", fname);
					perror("O/S Err:");
					exit(-1);
				}

				delete[] pathcpy;
			}
		}

		if (curbs)
			curbs->m_lineno = yylineno;
		m_prev = curbs;
		m_bs = yy_create_buffer(m_fp, YY_BUF_SIZE);
		m_fname = strdup(fname);
		yy_switch_to_buffer(m_bs);
		curbs = this;
		m_lineno = 1;
		curfilename = m_fname;

		yyrestart(m_fp);
		yylineno = 1;
	}

	~BUFSTACK(void) {
		// fprintf(stderr, "DELETING(%s)\n", m_fname);
		fclose(m_fp);
		free(m_fname);
		if (m_bs)
			yy_delete_buffer(m_bs);
		curbs = m_prev;

		if (curbs) {
			yy_switch_to_buffer(curbs->m_bs);
			yylineno = curbs->m_lineno;
			curfilename = curbs->m_fname;
		}
	}

	void	mark(void) {
		FILE	*fp = yyout;
		if (!fp) fp = stdout;
		fprintf(fp, "#line %d \"%s\"\n", yylineno, m_fname);
	}

	void	markline(void) {
		FILE	*fp = yyout;
		if (!fp) fp = stdout;
		fprintf(fp, "#line %d\n", yylineno);
	}

	static	void pop(void) {
		// fprintf(stderr, "POP! (%s)\n", curbs->m_fname);
		if (curbs)
			delete curbs;
	}
};

BUFSTACK *BUFSTACK::curbs = NULL;
const char *BUFSTACK::curfilename = NULL;

int		last_marked_line = -1;
const char	*last_marked_file = NULL;
void	mark_line(void) {
	if ((yylineno != last_marked_line+1)||(BUFSTACK::curfilename != last_marked_file))
		if (BUFSTACK::curfilename == last_marked_file)
			BUFSTACK::curbs->markline();
		else BUFSTACK::curbs->mark();
	last_marked_line = yylineno;
	last_marked_file = BUFSTACK::curfilename;
}

int	end_of_file(void) {
	BUFSTACK::pop();
	return (BUFSTACK::curbs == NULL);
}

void	pushf(const char *fname) {
	BUFSTACK	*bs = new BUFSTACK(fname);
}

int main(int argc, char **argv) {
	yylineno = 1;
	if (argc < 2) { // Stdin only
		BUFSTACK::curbs = new BUFSTACK();
		yylex();
	} else {
		for(int argn=1; argn<argc; argn++) {
			BUFSTACK	*bs = new BUFSTACK(argv[argn]);
			mark_line();
			yylex();
			// delete	bs;
		}
	}

	return 0;
}
// <NODEF,NVRDEF>.*		{ fprintf(stderr, "Ignoring everything, line %d, \'%s\'\n", yylineno, yytext); /* Ignore everything in these states*/ }

