////////////////////////////////////////////////////////////////////////////////
//
// Filename:	abs_div.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	The original divide module provides an Integer divide
//		capability to the Zip CPU.  This module is an abstract
//	divide module.  It *might* produce a valid integer divide, either signed
//	or unsigned, result.  It might instead do somethin else.  It is designed
//	to be easier for the formal tools to work with.
//
// Steps:
//	i_reset	The DIVide unit starts in idle.  It can also be placed into an
//	idle by asserting the reset input.
//
//	i_wr	When i_reset is asserted, a divide begins.  On the next clock:
//
//	  o_busy is set high so everyone else knows we are at work and they can
//		wait for us to complete.
//
//	  pre_sign is set to true if we need to do a signed divide.  In this
//		case, we take a clock cycle to turn the divide into an unsigned
//		divide.
//
//	  o_quotient, a place to store our result, is initialized to all zeros.
//
//	  r_dividend is set to the numerator
//
//	  r_divisor is set to 2^31 * the denominator (shift left by 31, or add
//		31 zeros to the right of the number.
//
//	pre_sign When true (clock cycle after i_wr), a clock cycle is used
//		to take the absolute value of the various arguments (r_dividend
//		and r_divisor), and to calculate what sign the output result
//		should be.
//
//
//	At this point, the divide is has started.  The divide works by walking
//	through every shift of the
//
//		    DIVIDEND	over the
//		DIVISOR
//
//	If the DIVISOR is bigger than the dividend, the divisor is shifted
//	right, and nothing is done to the output quotient.
//
//		    DIVIDEND
//		 DIVISOR
//
//	This repeats, until DIVISOR is less than or equal to the divident, as in
//
//		DIVIDEND
//		DIVISOR
//
//	At this point, if the DIVISOR is less than the dividend, the
//	divisor is subtracted from the dividend, and the DIVISOR is again
//	shifted to the right.  Further, a '1' bit gets set in the output
//	quotient.
//
//	Once we've done this for 32 clocks, we've accumulated our answer into
//	the output quotient, and we can proceed to the next step.  If the
//	result will be signed, the next step negates the quotient, otherwise
//	it returns the result.
//
//	On the clock when we are done, o_busy is set to false, and o_valid set
//	to true.  (It is a violation of the ZipCPU internal protocol for both
//	busy and valid to ever be true on the same clock.  It is also a
//	violation for busy to be false with valid true thereafter.)
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
// {{{
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
//
`default_nettype	none
// }}}
module	abs_div #(
		// {{{
		parameter		BW=32, LGBW = 5,
		// Verilator lint_off UNUSED
		parameter	[0:0]	OPT_LOWPOWER = 1'b0,
		// Verilator lint_on  UNUSED
		parameter	[4:0]	MAXDELAY = 3
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Input parameters
		input	wire		i_wr, i_signed,
		input	wire [(BW-1):0]	i_numerator, i_denominator,
		// Output parameters
		output	wire		o_busy,
		output	reg		o_valid, o_err,
		output	reg [(BW-1):0]	o_quotient,
		output	wire	[3:0]	o_flags
		// }}}
	);

	// Declarations
	// {{{
	// Verilator lint_off UNDRIVEN
	(* anyseq *)	reg			any_err;
	(* anyseq *)	reg	[(BW-1):0]	any_quotient;
	(* anyseq *)	reg	[5:0]		wait_time;
	(* anyseq *)	reg	[3:0]		any_flags;
	// Verilator lint_on  UNDRIVEN
	reg	[5:0]	r_busy_counter;
	// }}}

	always @(*)
		o_err      = any_err;
	always @(*)
		o_quotient = any_quotient;

	always @(*)
		assume(wait_time > 5'h1);

	always @(*)
		assume((MAXDELAY == 0)||(wait_time < MAXDELAY));

	// r_busy_counter
	// {{{
	initial	r_busy_counter = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_busy_counter <= 0;
	else if ((i_wr)&&(!o_busy))
		r_busy_counter <= wait_time;
	else if (r_busy_counter > 0)
		r_busy_counter <= r_busy_counter - 1'b1;
	// }}}

	always @(*)
		assert((MAXDELAY == 0)||(r_busy_counter < MAXDELAY));

	assign	o_busy = (r_busy_counter != 0);

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_valid <= 1'b0;
	else
		o_valid <= (r_busy_counter == 1);
	// }}}

	assign o_flags    = (o_valid) ? 
			{ 1'b0, o_quotient[31], any_flags[1],
					(o_quotient == 0) } : any_flags;
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	always @(posedge i_clk)
	if (!f_past_valid)
		assert((!o_busy)&&(!o_valid));

`define	ASSUME	assert

	initial	`ASSUME(i_reset);
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		`ASSUME(!i_wr);

	always @(*)
	if (o_busy)
		`ASSUME(!i_wr);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(o_busy))&&(!o_busy))
		assume(o_valid);

	always @(*)
	if (o_err)
		assume(o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wr)))
		assert(o_busy);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid)))
		assume(!o_valid);

	always @(*)
	if ((o_valid)&&(!o_err))
		assume(o_flags[3] == ((o_quotient == 0)? 1'b1:1'b0));

	always @(*)
	if ((o_valid)&&(!o_err))
		assume(o_flags[1] == o_quotient[BW-1]);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_busy))&&(!$past(i_wr)))
		assume(!o_busy);

	always @(posedge i_clk)
		assume((!o_busy)||(!o_valid));

`endif
// }}}
endmodule
