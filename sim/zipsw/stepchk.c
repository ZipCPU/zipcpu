#include <stdint.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"
#include "txfns.h"

const	uint32_t	SMPCMD_GO = 0,
			SMPCMD_HALT  = (1<<0),
			SMPCMD_STEP  = (1<<2),
			SMPCMD_CATCH = (1<<5);

#define	UARTTX	_uart->u_tx
#define	TXBUSY	(UARTTX & 0x0100)

void	testprg(void);
// {{{
asm(
"testprg:\n"
	"\tCLR\tR1\n"
".Ltestprg:\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tADD\t257,R1\n"
	"\tBRA\t.Ltestprg\n"
);
// }}}

int     smp_count(void);
// {{{
asm("\t.text\n\t.global\tsmp_count\n"
	"\t.type\tsmp_count,@function\n"
	"\t.text\n\t.global\tusmp_count\n"
	"\t.type\tsmp_count,@function\n"
"smp_count:\n"
	"CLR\tR2\n"
	"MOV\tR2,uR0\n"
	"MOV\tR2,uR1\n"
	"MOV\tR2,uR2\n"
	"MOV\tR2,uSP\n"
	"MOV\tR2,uCC\n"
	"LDI\tusmp_count,R2\n"
	"MOV\tR2,uPC\n"
	"RTU\n"
	"MOV\tuR1,R1\n"
	"RTN\n"
"usmp_count:\n"
	"\tCLR  R1\n"
	// "\tLDI       _smp,R2\n"
	"\tLDI  50332160,R2\n"
".Lsmp_count_loop:\n"
	"\tLW   (R2),R3\n"
	"\tADD  1,R1\n"
	"\tADD  512,R2\n"
	"\tJMP  .Lsmp_count_loop\n"
);
// }}}

void	wait_for_uart_idle(void) {
	// {{{
	while(TXBUSY)
		;
}
// }}}

int	main(int argc, char **argv) {
	const	int	ITERATIONS = 5000;
	int	failed = 0, code = 0;
	int	num_smp = smp_count()+1;

	txstr("NUM_SMP : "); txhex(num_smp); txstr("\r\n");

	if (num_smp > 1) {
		// {{{
		volatile SMP * const cpu = &_smp[1];
	txstr("OPT_SMP\r\n");

		cpu->c_control  = SMPCMD_GO | SMPCMD_HALT | SMPCMD_CATCH;
		cpu->c_sreg[ 0] = 0;
		cpu->c_sreg[13] = 0;
		cpu->c_sreg[14] = 0;
		cpu->c_sreg[15] = (uint32_t)testprg;

		// Must never double step, and must always step some amount
		// {{{
		for(int k=0; k<ITERATIONS; k++) {
			register	uint32_t	a, b, c, d;

			c = cpu->c_sreg[0];
			a = cpu->c_sreg[1];
			b = cpu->c_sreg[2];
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;

			b = cpu->c_sreg[1];
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			c = cpu->c_sreg[1];
			d = cpu->c_sreg[1];

			if (c != d) {
				failed = 1;
				txstr("SMP FAIL #1 [Reg-Consistency]:\n Before =   "); txhex(a),
				txstr("\n Mid +1 =   "); txhex(b);
				txstr("\n Mid +3 =   "); txhex(c);
				txstr("\n Mid +3 =   "); txhex(d);
				txstr(" [2nd Read]\n");
				break;
			}

			d = b-a;
			if (d != 0 && d != 257) {
				failed = 2;
				txstr("SMP FAIL #2 [Single-Step]:\n Before =   "); txhex(a),
				txstr("\n Mid +1 =   "); txhex(b);
				txstr("\n Mid +3 =   "); txhex(c);
				txstr("\n Diff   =   "); txhex(d);
				txstr(" [X-1]\n");
				break;
			}

			// Given four step commands, the CPU must only step
			// one, two, three, or four times, never more.
			d = c-b;
			if (0 != d && d != 257 && d != 257*2
						&& d != 257*3 && d != 257*4) {
				failed = 3;
				code   = d;
				txstr("SMP FAIL #3 [Multi-step]\n Before =   "); txhex(a),
				txstr("\n Mid +1 =   "); txhex(b);
				txstr("\n Mid +3 =   "); txhex(c);
				txstr("\n L Diff =   "); txhex(d);
				txstr(" [X-3]\n");
				break;
			}
		}
		// }}}

		// Final result checking
		// {{{
		if (0 == failed) {
			register	uint32_t	a, b, c, d;

			c = cpu->c_sreg[1];
			if (0 == c) {
				failed = 4;
				code = c;
				txstr("SMP FAIL #4 [DEAD CPU]\n"
					" uR1: 0x"); txhex(c);
				txstr("\n");
			} else if ((0x101 * ITERATIONS * 5) < c) {
				failed = 5;
				code = c;
				txstr("SMP FAIL #5 [Over-Active CPU]\n"
					" uR1: 0x"); txhex(c);
				txstr("\n");
			}
		}
		// }}}
		// }}}
	} else {
		// {{{
		uint32_t	uregs[16];
		uint32_t	preuinsn, postuinsn, ucc, a, b, c, d;

		failed= 0;

		for(int k=0; k<16; k++)
			uregs[k] = 0;
		uregs[15] = (uint32_t)testprg;
		zip_restore_context(uregs);

		// Must never double step, and must always step some amount
		ucc |= CC_STEP | CC_GIE;
#define	STEP	SETUREG(ucc, "uCC"); zip_rtu();
		for(int k=0; k<ITERATIONS; k++) {
			// Step once
			// {{{
			GETUREG(b, "uR0");
			GETUREG(a, "uR1");
			GETUREG(c, "uR2");
			// preuinsn = _axilp->z_u.ac_icnt;
			// preticks = _axilp->z_jiffies;
			STEP;
			// postticks = _axilp->z_jiffies;
			// postuinsn = _axilp->z_u.ac_icnt;
			GETUREG(b, "uR1");
			GETUREG(d, "uR1");

			if (d != b) {
				failed = 1;
				txstr("FAIL #1 [Reg-Consistency]\r\nA = "); txhex(a),
				txstr("\r\nB = "); txhex(b);
				txstr("\r\nC = "); txhex(c);
				txstr("\r\nD = "); txhex(d);
				txstr("\r\n");
				break;
			}

			d = b-a;
			if (d != 0 && d != 257) {
				failed = 2;
				txstr("FAIL #2 [Single-Step]\r\nA = "); txhex(a),
				txstr("\r\nB = "); txhex(b);
				txstr("\r\nC = "); txhex(c);
				txstr("\r\nD = "); txhex(d);
				txstr("\r\n");
				break;
			}

			// }}}

			// Step four times in a row
			// {{{
			// preuinsn = postuinsn;
			STEP;
			STEP;
			STEP;
			STEP;
			GETUREG(c,   "uR1");
			// postuinsn = _axilp->z_u.ac_icnt;

			d = c-b;
			if (d != 257 && d != 514 && d != 771 && d != 1028) {
				failed = 3;
				code   = b;
				txstr("FAIL #3 [Multi-step]\r\nA = "); txhex(a),
				txstr("\r\nB = "); txhex(b);
				txstr("\r\nC = "); txhex(c);
				txstr("\r\nD = "); txhex(d);
				txstr("\r\n");
				// code   = c;	// == 2
				// code   = d;	// == 2?
				break;
			}

			/*
			// Must have stepped four instructions worth
			d = postuinsn - preuinsn;
			if (d != 4) {
				failed = 2;
			}
			*/

			// Keep us from the watchdog timeout, by doing
			// *something* on the bus
			uregs[0]++;
			// }}}
		}

		// Final result checking
		// {{{
		if (0 == failed) {
			GETUREG(c,   "uR1");

			if (0 == c) {
				failed = 4;
				code = c;
				txstr("SMP FAIL #4 [DEAD CPU]\n"
					"\n uR1    =   0x"); txhex(c);
				txstr("\n");
			} else if (0x101 * ITERATIONS * 4 > c) {
				failed = 5;
				code = c;
				txstr("SMP FAIL #5 [Over-Active CPU]\n"
					"\n uR1    =   0x"); txhex(c);
				txstr("\n");
			}
		}
		// }}}
		// }}}
	}

	// Report on the result
	// {{{
	if (failed) {
		txstr("CODE: "); txhex(failed); txstr("\r\n");
		txstr(" D  : "); txhex(code); txstr("\r\n");
		txstr("FAIL!\r\n\r\n");
        	// asm("NDUMP");

		if (num_smp > 1) {
			volatile SMP * const cpu = &_smp[1];
			unsigned	r;

			r = cpu->c_sreg[0]; txstr(  "sR0 : "); txhex(r);
			r = cpu->c_sreg[1]; txstr( " sR1 : "); txhex(r);
			r = cpu->c_sreg[2]; txstr( " sR2 : "); txhex(r);
			r = cpu->c_sreg[3]; txstr( " sR3 : "); txhex(r);

			r = cpu->c_sreg[4]; txstr("\nsR4 : "); txhex(r);
			r = cpu->c_sreg[5]; txstr( " sR5 : "); txhex(r);
			r = cpu->c_sreg[6]; txstr( " sR6 : "); txhex(r);
			r = cpu->c_sreg[7]; txstr( " sR7 : "); txhex(r);

			r = cpu->c_sreg[8]; txstr("\nsR8 : "); txhex(r);
			r = cpu->c_sreg[9]; txstr( " sR9 : "); txhex(r);
			r = cpu->c_sreg[10];txstr( " sR10: "); txhex(r);
			r = cpu->c_sreg[11];txstr( " sR11: "); txhex(r);

			r = cpu->c_sreg[12];txstr("\nsR12: "); txhex(r);
			r = cpu->c_sreg[13]; txstr( " sSP : "); txhex(r);
			r = cpu->c_sreg[14]; txstr( " sCC : "); txhex(r);
			r = cpu->c_sreg[15]; txstr( " sPC : "); txhex(r);
			txstr("\n\n");
		} else {
			unsigned	r;

			GETUREG(r, "uR0"); txstr(  "uR0 : "); txhex(r);
			GETUREG(r, "uR1"); txstr( " uR1 : "); txhex(r);
			GETUREG(r, "uR2"); txstr( " uR2 : "); txhex(r);
			GETUREG(r, "uR3"); txstr( " uR3 : "); txhex(r);

			GETUREG(r, "uR4"); txstr("\nuR4 : "); txhex(r);
			GETUREG(r, "uR5"); txstr( " uR5 : "); txhex(r);
			GETUREG(r, "uR6"); txstr( " uR6 : "); txhex(r);
			GETUREG(r, "uR7"); txstr( " uR7 : "); txhex(r);

			GETUREG(r, "uR8"); txstr("\nuR8 : "); txhex(r);
			GETUREG(r, "uR9"); txstr( " uR9 : "); txhex(r);
			GETUREG(r, "uR10");txstr( " uR10: "); txhex(r);
			GETUREG(r, "uR11");txstr( " uR11: "); txhex(r);

			GETUREG(r, "uR12");txstr("\nuR12: "); txhex(r);
			GETUREG(r, "uSP"); txstr( " uSP : "); txhex(r);
			GETUREG(r, "uCC"); txstr( " uCC : "); txhex(r);
			GETUREG(r, "uPC"); txstr( " uPC : "); txhex(r);
			txstr("\n\n");
		}
	} else {
        	txstr("\r\n");
        	txstr("-----------------------------------\r\n");
        	txstr("All tests passed.  Halting CPU.\r\n");
	}
        wait_for_uart_idle();
        txstr("\r\n");
        wait_for_uart_idle();
        asm("NEXIT 0");
        zip_halt();
	// }}}
}
