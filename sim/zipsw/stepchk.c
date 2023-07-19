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

			a = cpu->c_sreg[1];
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;

			b = cpu->c_sreg[1];
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			cpu->c_control = SMPCMD_CATCH | SMPCMD_STEP;
			c = cpu->c_sreg[1];

			d = b-a;
			if (d != 0 && d != 257) {
				failed = 1;
				txstr("FAIL #1\r\nA = "); txhex(a),
				txstr("\r\nB = "); txhex(b);
				txstr("\r\nC = "); txhex(c);
				txstr("\r\nD = "); txhex(d);
				txstr("\r\n");
				break;
			}

			d = c-b;
			if (d != 0 && d != 257 && d != 514
						&& d != 771 && d != 1028) {
				failed = 2;
				txstr("FAIL #2\r\nA = "); txhex(a),
				txstr("\r\nB = "); txhex(b);
				txstr("\r\nC = "); txhex(c);
				txstr("\r\nD = "); txhex(d);
				txstr("\r\n");
				break;
			}

			// Must always step by some amount
			/*
			if (a == d) {
				failed = 3;
				txstr("FAIL #3\r\nA = "); txhex(a),
				txstr("\r\nB = "); txhex(b);
				txstr("\r\nC = "); txhex(c);
				txstr("\r\nD = "); txhex(d);
				txstr("\r\n");

				break;
			}
			*/
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
			GETUREG(a, "uR1");
			// preuinsn = _axilp->z_u.ac_icnt;
			// preticks = _axilp->z_jiffies;
			STEP;
			// postticks = _axilp->z_jiffies;
			// postuinsn = _axilp->z_u.ac_icnt;
			GETUREG(b, "uR1");

			/*
			d = postuinsn-preuinsn;
			if (d != 1) {
				failed = 1; break;
			}
			*/

			d = b-a;
			if (d != 0 && d != 257) {
				failed = 1;
				txstr("FAIL #1\r\nA = "); txhex(a),
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
				failed = 2;
				code   = b;
				txstr("FAIL #2\r\nA = "); txhex(a),
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
		// }}}
	}

	// Report on the result
	// {{{
	if (failed) {
		txstr("CODE: "); txhex(failed); txstr("\r\n");
		txstr(" D  : "); txhex(code); txstr("\r\n");
		txstr("FAIL!\r\n\r\n");
        	asm("NDUMP");
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
