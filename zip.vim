" Vim syntax file
" Language:     Zip CPU Assembly Language
" Maintainer:   Dan Gisselquist
" Last Change:  2015 Dec 20
"
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
syn keyword zipopcode sub and add or xor lsr lsl asr lhi llo ldihi ldilo
syn keyword zipopcode mpyu mpys divu divs
syn keyword zipopcode brev popc rol mov cmp tst lod sto ldi
syn keyword zipopcode noop break brk lock
syn keyword zipopcode fpadd fpsub fpmul fpdiv dpcvt fpint
syn keyword zipopcode bz beq bnz bc brc brv bv bra blt bgt bge
syn keyword zipopcode clr halt wait clrf jmp ljmp not trap busy neg rtu

"delimiters

"operators
syn match zipoperators "[()#,]"
" syn match zipoperators "\(+\|\*\|-\|/\|\\\|^\|&\|\|=\)"

"TODO
syn match zipTodo      "\(TODO\|XXX\|FIXME\|NOTE\)"

syn keyword zipCondition z ne nz ge gt lt n c v

"The regex for different zip registers are given below
syn match zipregisters "[us]\=R\([0-9]\|1[0-5]\)\>"
syn keyword zipregisters gbl sp cc pc usp ucc upc
"floating point classes

"Data allocation syntax
syn match zipdata "word\s*\>"
syn match zipdata "fill\s*\>"
syn match zipdata "stringz\=\(\(\(\.ua\)\=\(\.msb\|\.lsb\)\=\)\|\(\(\.msb\|\.lsb\)\=\(\.ua\)\=\)\)\=\>"

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
