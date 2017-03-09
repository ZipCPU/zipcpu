" Vim syntax file
" Language:     Zip CPU Assembly Language
" Maintainer:   Dan Gisselquist
" Last Change:  2016 Sep 24
"
"/////////////////////////////////////////////////////////////////////////////
"/
"/ Filename:	zip.vim
"/
"/ Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
"/
"/ Purpose:	A VIM syntax file for hilighting Zip Assembly files within
"/		vim.
"/
"/
"/ Creator:	Dan Gisselquist, Ph.D.
"/		Gisselquist Technology, LLC
"/
"///////////////////////////////////////////////////////////////////////////////
"/
"/ Copyright (C) 2015-2016, Gisselquist Technology, LLC
"/
"/ This program is free software (firmware): you can redistribute it and/or
"/ modify it under the terms of  the GNU General Public License as published
"/ by the Free Software Foundation, either version 3 of the License, or (at
"/ your option) any later version.
"/
"/ This program is distributed in the hope that it will be useful, but WITHOUT
"/ ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
"/ FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
"/ for more details.
"/
"/ License:	GPL, v3, as defined and found on www.gnu.org,
"/		http://www.gnu.org/licenses/gpl.html
"/
"/
"///////////////////////////////////////////////////////////////////////////////
"/
"/
" This is a ZipCPU syntax highlight definition file for use with VIM.

" Run this wih :set syntax=zip
" 	Look up new-filetype for autodetection

if exists("b:current_syntax")
  finish
endif

"ignore case for assembly
syn case ignore

"  Identifier Keyword characters (defines \k)
if version >= 600
	setlocal iskeyword=@,48-57,#,$,:,?,@-@,_,~
endif

syn sync minlines=5

syn region zipComment start=";" end="$" contains=zipTodo,@Spell
syn region zipComment start="//" end="$" contains=zipTodo,@Spell
syn region zipComment start="/\*" end="\*/" contains=zipTodo,@Spell
" syn match zipComment ";.*" contains=zipTodo

syn match zipIdentifier	"[a-zA-Z_$][a-zA-Z0-9_$]*"
" syn match zipDirective		"\.[a-zA-Z_$][a-zA-Z_$.]\+"
syn match zipLabel		"[a-zA-Z_$.][a-zA-Z0-9_$.]*\s\=:\>"he=e-1
syn region zipstring		start=+"+ skip=+\\\\\|\\"+ end=+"+
syn region zipcharstr		start=+'+ skip=+\\\\\|\\'+ end=+'+
syn match zipOctal		"\$\=0[0-7_]*\>"
syn match zipBinary		"\$\=0[bB][01_]*\>"
syn match zipHex		"\$\=0[xX][0-9a-fA-F_]*\>"
syn match zipDecimal		"\$\=[1-9_][0-9_]*\>"
" syn match zipFloat		"\$\=[0-9_]*\.[0-9_]*\([eE][+-]\=[0-9_]*\)\=\>"

"simple instructions
syn keyword zipopcode sub and add or xor lsr lsl asr
syn keyword zipopcode brev ldilo mpyuhi mpyshi mpy mov divu divs
syn keyword zipopcode cmp tst test lw sw lh sh lb sb ldi
syn keyword zipopcode fpadd fpsub fpmul fpdiv fpi2f fpf2i
syn keyword zipopcode noop break brk lock
syn keyword zipopcode bz beq bnz bne bc bnc bv bra blt bge ljmp jsr ljsr
syn keyword zipopcode clr halt wait jmp ljmp not trap busy neg rtu retn
syn keyword zipopcode sim sexit nexit sdump ndump snoop sdump sstr nstr

"delimiters

"operators
syn match zipoperators "[()#,]"
" syn match zipoperators "\(+\|\*\|-\|/\|\\\|^\|&\|\|=\)"

"TODO
syn match zipTodo      "\(TODO\|XXX\|FIXME\|NOTE\)"

syn keyword zipCondition z ne nz ge lt n nc c v

"The regex for different zip registers are given below
syn match zipregisters "[us]\=R\([0-9]\|1[0-5]\)\>"
syn keyword zipregisters gbl sp cc pc lr fp ulr ufp usp ucc upc
"floating point classes

"Data allocation syntax
syn match zipdata "\.ascii\s*\>"
syn match zipdata "\.asciz\s*\>"
syn match zipdata "\.byte\s*\>"
syn match zipdata "\.short\s*\>"
syn match zipdata "\.word\s*\>"
syn match zipdata "\.int\s*\>"
syn match zipdata "\.long\s*\>"
syn match zipdata "\.single\s*\>"
syn match zipdata "\.float\s*\>"
syn match zipdata "\.skip\s*\>"
syn match zipdata "\.fill\s*\>"
syn match zipdata "\.set\s*\>"
syn match zipdata "string8\=\(\(\(\.ua\)\=\(\.msb\|\.lsb\)\=\)\|\(\(\.msb\|\.lsb\)\=\(\.ua\)\=\)\)\=\>"
syn match zipdata "string16\=\(\(\(\.ua\)\=\(\.msb\|\.lsb\)\=\)\|\(\(\.msb\|\.lsb\)\=\(\.ua\)\=\)\)\=\>"
syn match zipdata "string32\=\(\(\(\.ua\)\=\(\.msb\|\.lsb\)\=\)\|\(\(\.msb\|\.lsb\)\=\(\.ua\)\=\)\)\=\>"
syn match zipdata "string64\=\(\(\(\.ua\)\=\(\.msb\|\.lsb\)\=\)\|\(\(\.msb\|\.lsb\)\=\(\.ua\)\=\)\)\=\>"

" Define the default highlighting.
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_zip_syn_inits")
	command -nargs=+ HiLink hi def link <args>

	"zip specific stuff
	HiLink zipLabel		Define
	HiLink zipComment	Comment
	HiLink zipDirective	Type
	HiLink zipopcode	Statement
	HiLink zipCondition	Statement
	HiLink zipregisters	Operator
	HiLink zipstring	String
	HiLink zipcharstr	Character
	HiLink zipDecimal	Number
	HiLink zipHex		Number
	HiLink zipBinary	Number
	HiLink zipOctal	Number
	HiLink zipIdentifier	Identifier
	HiLink zipdata		Type
	HiLink zipdelimiter	Delimiter
	HiLink zipoperator	Operator
	HiLink zipTodo		Todo

	" HiLink ia64Float	Float
	delcommand HiLink
endif

let b:current_syntax = "zip"

" vim: ts=8 sw=2
