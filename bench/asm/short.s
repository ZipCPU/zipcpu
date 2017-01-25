;;
	.section .start, "ax"
	.global	_start
_start:
	SOUT	'H'
	SOUT	'e'
	SOUT	'l'
	SOUT	'l'
	SOUT	'o'
	SOUT	' '
	SOUT	'W'
	SOUT	'o'
	SOUT	'r'
	SOUT	'l'
	SOUT	'd'
	SOUT	'!'
	SOUT	'\r'
	SOUT	'\n'
	LW	_start(PC),R0
	CMP	R3,R4
	SDUMP	R0
	SEXIT	0

