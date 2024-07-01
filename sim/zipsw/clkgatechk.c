////////////////////////////////////////////////////////////////////////////////
//
// Filename:	clkgatechk.c
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
//
// }}}
#include <zipcpu.h>
#include <zipsys.h>
#include "txfns.h"

char	psalm[] = 
	"+==============================================================================+\n"
	"|                                                                              |\n"
	"| The LORD is my light and my salvation; whom shall I fear? the LORD is the    |\n"
	"|   strength of my life; of whom shall I be afraid?                            |\n"
	"| When the wicked, even mine enemies and my foes, came upon me to eat up my    |\n"
	"|   flesh, they stumbled and fell.                                             |\n"
	"| Though an host should encamp against me, my heart shall not fear: though war |\n"
	"|   should rise against me, in this will I be confident.                       |\n"
	"| One thing have I desired of the LORD, that will I seek after; that I may     |\n"
	"|   dwell in the house of the LORD all the days of my life, to behold the      |\n"
	"|   beauty of the LORD, and to enquire in his temple.                          |\n"
	"| For in the time of trouble he shall hide me in his pavilion: in the secret   |\n"
	"|   of his tabernacle shall he hide me; he shall set me up upon a rock.        |\n"
	"| And now shall mine head be lifted up above mine enemies round about me:      |\n"
	"|   therefore will I offer in his tabernacle sacrifices of joy; I will sing,   |\n"
	"|   yea, I will sing praises unto the LORD.                                    |\n"
	"| Hear, O LORD, when I cry with my voice: have mercy also upon me, and answer  |\n"
	"|   me.                                                                        |\n"
	"| When thou saidst, Seek ye my face; my heart said unto thee, Thy face, LORD,  |\n"
	"|   will I seek.                                                               |\n"
	"| Hide not thy face far from me; put not thy servant away in anger: thou hast  |\n"
	"|   been my help; leave me not, neither forsake me, O God of my salvation.     |\n"
	"| When my father and my mother forsake me, then the LORD will take me up.      |\n"
	"| Teach me thy way, O LORD, and lead me in a plain path, because of mine       |\n"
	"|   enemies.                                                                   |\n"
	"| Deliver me not over unto the will of mine enemies: for false witnesses are   |\n"
	"|   risen up against me, and such as breathe out cruelty.                      |\n"
	"| I had fainted, unless I had believed to see the goodness of the LORD in the  |\n"
	"|   land of the living.                                                        |\n"
	"| Wait on the LORD: be of good courage, and he shall strengthen thine heart:   |\n"
	"|   wait, I say, on the LORD.                                                  |\n"
	"|                                                                              |\n"
	"+==============================================================================+\n";

#define	PIC		_zip->z_pic
#define	TIMER		_zip->z_tma
#define	TIMINT_A	0x10
#define	INTERVAL	750
#define	AUTORELOAD	0x80000000

int	main(int argc, char **argv) {
	const char *ptr = psalm;

	// Start the timer
	TIMER = AUTORELOAD | INTERVAL;	// Auto-reload, every INTERVAL clock cycles

	// Acknowledge and disable all interrupts
	PIC = CLEARPIC;

	while(*ptr) {
		PIC = TIMINT_A | EINT(TIMINT_A);	// Enable and clear Timer A
		txchr(*ptr++);

		// Wait for the next interrupt
		zip_idle();
	}

	asm("NEXIT 0");
	zip_halt();
}

