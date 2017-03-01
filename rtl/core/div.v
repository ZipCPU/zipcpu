////////////////////////////////////////////////////////////////////////////////
//
// Filename:	div.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Provide an Integer divide capability to the Zip CPU.  Provides
//		for both signed and unsigned divide.
//
// Steps:
//	i_rst	The DIVide unit starts in idle.  It can also be placed into an
//	idle by asserting the reset input.
//
//	i_wr	When i_rst is asserted, a divide begins.  On the next clock:
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
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
//
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
// `include "cpudefs.v"
//
module	div(i_clk, i_rst, i_wr, i_signed, i_numerator, i_denominator,
		o_busy, o_valid, o_err, o_quotient, o_flags);
	parameter		BW=32, LGBW = 5;
	input			i_clk, i_rst;
	// Input parameters
	input			i_wr, i_signed;
	input	[(BW-1):0]	i_numerator, i_denominator;
	// Output parameters
	output	reg		o_busy, o_valid, o_err;
	output	reg [(BW-1):0]	o_quotient;
	output	wire	[3:0]	o_flags;

	// r_busy is an internal busy register.  It will clear one clock
	// before we are valid, so it can't be o_busy ...
	//
	reg			r_busy;
	reg	[(2*BW-2):0]	r_divisor;
	reg	[(BW-1):0]	r_dividend;
	wire	[(BW):0]	diff; // , xdiff[(BW-1):0];
	assign	diff = r_dividend - r_divisor[(BW-1):0];
	// assign	xdiff= r_dividend - { 1'b0, r_divisor[(BW-1):1] };

	reg		r_sign, pre_sign, r_z, r_c, last_bit;
	reg	[(LGBW-1):0]	r_bit;

	reg	zero_divisor;
	initial	zero_divisor = 1'b0;
	always @(posedge i_clk)
		zero_divisor <= (r_divisor == 0)&&(r_busy);

	initial	r_busy = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			r_busy <= 1'b0;
		else if (i_wr)
			r_busy <= 1'b1;
		else if ((last_bit)||(zero_divisor))
			r_busy <= 1'b0;

	initial	o_busy = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			o_busy <= 1'b0;
		else if (i_wr)
			o_busy <= 1'b1;
		else if (((last_bit)&&(~r_sign))||(zero_divisor))
			o_busy <= 1'b0;
		else if (~r_busy)
			o_busy <= 1'b0;

	always @(posedge i_clk)
		if ((i_rst)||(i_wr))
			o_valid <= 1'b0;
		else if (r_busy)
		begin
			if ((last_bit)||(zero_divisor))
				o_valid <= (zero_divisor)||(~r_sign);
		end else if (r_sign)
		begin
			o_valid <= (~zero_divisor); // 1'b1;
		end else
			o_valid <= 1'b0;

	initial	o_err = 1'b0;
	always @(posedge i_clk)
		if((i_rst)||(o_valid))
			o_err <= 1'b0;
		else if (((r_busy)||(r_sign))&&(zero_divisor))
			o_err <= 1'b1;
		else
			o_err <= 1'b0;

	initial	last_bit = 1'b0;
	always @(posedge i_clk)
		if ((i_wr)||(pre_sign)||(i_rst))
			last_bit <= 1'b0;
		else if (r_busy)
			last_bit <= (r_bit == {{(LGBW-1){1'b0}},1'b1});

	always @(posedge i_clk)
		// if (i_rst) r_busy <= 1'b0;
		// else
		if (i_wr)
		begin
			//
			// Set our values upon an initial command.  Here's
			// where we come in and start.
			//
			// r_busy <= 1'b1;
			//
			o_quotient <= 0;
			r_bit <= {(LGBW){1'b1}};
			r_divisor <= {  i_denominator, {(BW-1){1'b0}} };
			r_dividend <=  i_numerator;
			r_sign <= 1'b0;
			pre_sign <= i_signed;
			r_z <= 1'b1;
		end else if (pre_sign)
		begin
			//
			// Note that we only come in here, for one clock, if
			// our initial value may have been signed.  If we are
			// doing an unsigned divide, we then skip this step.
			//
			r_sign <= ((r_divisor[(2*BW-2)])^(r_dividend[(BW-1)]));
			// Negate our dividend if necessary so that it becomes
			// a magnitude only value
			if (r_dividend[BW-1])
				r_dividend <= -r_dividend;
			// Do the same with the divisor--rendering it into
			// a magnitude only.
			if (r_divisor[(2*BW-2)])
				r_divisor[(2*BW-2):(BW-1)] <= -r_divisor[(2*BW-2):(BW-1)];
			//
			// We only do this stage for a single clock, so go on
			// with the rest of the divide otherwise.
			pre_sign <= 1'b0;
		end else if (r_busy)
		begin
			// While the divide is taking place, we examine each bit
			// in turn here.
			//
			r_bit <= r_bit + {(LGBW){1'b1}}; // r_bit = r_bit - 1;
			r_divisor <= { 1'b0, r_divisor[(2*BW-2):1] };
			if (|r_divisor[(2*BW-2):(BW)])
			begin
			end else if (diff[BW])
			begin
				// 
				// diff = r_dividend - r_divisor[(BW-1):0];
				//
				// If this value was negative, there wasn't
				// enough value in the dividend to support
				// pulling off a bit.  We'll move down a bit
				// therefore and try again.
				//
			end else begin
				//
				// Put a '1' into our output accumulator.
				// Subtract the divisor from the dividend,
				// and then move on to the next bit
				//
				r_dividend <= diff[(BW-1):0];
				o_quotient[r_bit[(LGBW-1):0]] <= 1'b1;
				r_z <= 1'b0;
			end
			r_sign <= (r_sign)&&(~zero_divisor);
		end else if (r_sign)
		begin
			r_sign <= 1'b0;
			o_quotient <= -o_quotient;
		end

	// Set Carry on an exact divide
	wire	w_n;
	always @(posedge i_clk)
		r_c <= (r_busy)&&((diff == 0)||(r_dividend == 0));
	assign w_n = o_quotient[(BW-1)];

	assign o_flags = { 1'b0, w_n, r_c, r_z };
endmodule
