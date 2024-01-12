////////////////////////////////////////////////////////////////////////////////
//
// Filename:	div.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Provide an Integer divide capability to the Zip CPU.  Provides
//		for both signed and unsigned divide.
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
`default_nettype	none
// }}}
module	div #(
		parameter		BW=32, LGBW = 5,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Input parameters
		input	wire		i_wr, i_signed,
		input	wire [(BW-1):0]	i_numerator, i_denominator,
		// Output parameters
		output	reg		o_busy, o_valid, o_err,
		output	reg [(BW-1):0]	o_quotient,
		output	wire	[3:0]	o_flags
		// }}}
	);

	// Local declarations
	// {{{
	// r_busy is an internal busy register.  It will clear one clock
	// before we are valid, so it can't be o_busy ...
	//
	reg			r_busy;
	reg	[BW-1:0]	r_divisor;
	reg	[(2*BW-2):0]	r_dividend;
	wire	[(BW):0]	diff; // , xdiff[(BW-1):0];
	assign	diff = r_dividend[2*BW-2:BW-1] - r_divisor;

	reg			r_sign, pre_sign, r_z, r_c, last_bit;
	reg	[(LGBW-1):0]	r_bit;
	reg			zero_divisor;
	wire	w_n;
	// }}}

	// r_busy
	// {{{
	// The Divide logic begins with r_busy.  We use r_busy to determine
	// whether or not the divide is in progress, vs being complete.
	// Here, we clear r_busy on any reset and set it on i_wr (the request
	// to do a divide).  The divide ends when we are on the last bit,
	// or equivalently when we discover we are dividing by zero.
	initial	r_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_busy <= 1'b0;
	else if (i_wr)
		r_busy <= 1'b1;
	else if ((last_bit)||(zero_divisor))
		r_busy <= 1'b0;
	// }}}

	// o_busy
	// {{{
	// o_busy is very similar to r_busy, save for some key differences.
	// Primary among them is that o_busy needs to (possibly) be true
	// for an extra clock after r_busy clears.  This would be that extra
	// clock where we negate the result (assuming a signed divide, and that
	// the result is supposed to be negative.)  Otherwise, the two are
	// identical.
	initial	o_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_busy <= 1'b0;
	else if (i_wr)
		o_busy <= 1'b1;
	else if (((last_bit)&&(!r_sign))||(zero_divisor))
		o_busy <= 1'b0;
	else if (!r_busy)
		o_busy <= 1'b0;
	// }}}

	// zero_divisor
	// {{{
	always @(posedge i_clk)
	if (i_wr)
		zero_divisor <= (i_denominator == 0);
	// }}}

	// o_valid
	// {{{
	// o_valid is part of the ZipCPU protocol.  It will be set to true
	// anytime our answer is valid and may be used by the calling module.
	// Indeed, the ZipCPU will halt (and ignore us) once the i_wr has been
	// set until o_valid gets set.
	//
	// Here, we clear o_valid on a reset, and any time we are on the last
	// bit while busy (provided the sign is zero, or we are dividing by
	// zero).  Since o_valid is self-clearing, we don't need to clear
	// it on an i_wr signal.
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(o_valid))
		o_valid <= 1'b0;
	else if ((r_busy)&&(zero_divisor))
		o_valid <= 1'b1;
	else if (r_busy)
	begin
		if (last_bit)
			o_valid <= (!r_sign);
	end else if (r_sign)
	begin
		o_valid <= 1'b1;
	end else
		o_valid <= 1'b0;
	// }}}

	// o_err
	// {{{
	// Division by zero error reporting.  Anytime we detect a zero divisor,
	// we set our output error, and then hold it until we are valid and
	// everything clears.
	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_err <= 1'b0;
	else if ((r_busy)&&(zero_divisor))
		o_err <= 1'b1;
	else
		o_err <= 1'b0;
	// }}}

	// r_bit
	// {{{
	// Keep track of which "bit" of our divide we are on.  This number
	// ranges from 31 down to zero.  On any write, we set ourselves to
	// 5'h1f.  Otherwise, while we are busy (but not within the pre-sign
	// adjustment stage), we subtract one from our value on every clock.
	initial	r_bit = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_bit <= 0;
	else if ((r_busy)&&(!pre_sign))
		r_bit <= r_bit + 1'b1;
	else
		r_bit <= 0;
	// }}}

	// last_bit
	// {{{
	// This logic replaces a lot of logic that was inside our giant state
	// machine with ... something simpler.  In particular, we'll use this
	// logic to determine if we are processing our last bit.  The only trick
	// is, this bit needs to be set whenever (r_busy) and (r_bit == -1),
	// hence we need to set on (r_busy) and (r_bit == -2) so as to be set
	// when (r_bit == 0).
	initial	last_bit = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_bit <= 1'b0;
	else if (r_busy)
		last_bit <= (r_bit == {(LGBW){1'b1}}-1'b1);
	else
		last_bit <= 1'b0;
	// }}}

	// pre_sign
	// {{{
	// This is part of the state machine.  pre_sign indicates that we need
	// a extra clock to take the absolute value of our inputs.  It need only
	// be true for the one clock, and then it must clear itself.
	initial	pre_sign = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		pre_sign <= 1'b0;
	else
		pre_sign <= (i_wr)&&(i_signed)&&((i_numerator[BW-1])||(i_denominator[BW-1]));
	// }}}

	// r_z
	// {{{
	// As a result of our operation, we need to set the flags.  The most
	// difficult of these is the "Z" flag indicating that the result is
	// zero.  Here, we'll use the same logic that sets the low-order
	// bit to clear our zero flag, and leave the zero flag set in all
	// other cases.
	always @(posedge i_clk)
	if (i_wr)
		r_z <= 1'b1;
	else if ((r_busy)&&(!pre_sign)&&(!diff[BW]))
		r_z <= 1'b0;
	// }}}

	// r_dividend
	// {{{
	// This is initially the numerator.  On a signed divide, it then becomes
	// the absolute value of the numerator.  We'll subtract from this value
	// the divisor for every output bit we are looking for--just as with
	// traditional long division.
	always @(posedge i_clk)
	if (pre_sign)
	begin
		// If we are doing a signed divide, then take the
		// absolute value of the dividend
		if (r_dividend[BW-1])
		begin
			r_dividend[2*BW-2:0] <= {(2*BW-1){1'b0}};
			r_dividend[BW:0] <= -{ 1'b1, r_dividend[BW-1:0] };
		end
	end else if (r_busy)
	begin
		r_dividend <= { r_dividend[2*BW-3:0], 1'b0 };
		if (!diff[BW])
			r_dividend[2*BW-2:BW] <= diff[(BW-2):0];
	end else if (!r_busy && (!OPT_LOWPOWER || i_wr))
		// Once we are done, and r_busy is no longer high, we'll
		// always accept new values into our dividend.  This
		// guarantees that, when i_wr is set, the new value
		// is already set as desired.
		r_dividend <=  { 31'h0, i_numerator };
	// }}}

	// r_divisor
	// {{{
	initial	r_divisor = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_divisor <= 0;
	else if ((pre_sign)&&(r_busy))
	begin
		if (r_divisor[BW-1])
			r_divisor <= -r_divisor;
	end else if (!r_busy && (!OPT_LOWPOWER || i_wr))
		r_divisor <= i_denominator;
	// }}}

	// r_sign
	// {{{
	// is a flag for our state machine control(s).  r_sign will be set to
	// true any time we are doing a signed divide and the result must be
	// negative.  In that case, we take a final logic stage at the end of
	// the divide to negate the output.  This flag is what tells us we need
	// to do that.  r_busy will be true during the divide, then when r_busy
	// goes low, r_sign will be checked, then the idle/reset stage will have
	// been reached.  For this reason, we cannot set r_sign unless we are
	// up to something.
	initial	r_sign = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_sign <= 1'b0;
	else if (pre_sign)
		r_sign <= ((r_divisor[(BW-1)])^(r_dividend[(BW-1)]));
	else if (r_busy)
		r_sign <= (r_sign)&&(!zero_divisor);
	else
		r_sign <= 1'b0;
	// }}}

	// o_quotient
	// {{{
	initial	o_quotient = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_quotient <= 0;
	else if (r_busy)
	begin
		o_quotient <= { o_quotient[(BW-2):0], 1'b0 };
		if (!diff[BW])
			o_quotient[0] <= 1'b1;
	end else if (r_sign)
		o_quotient <= -o_quotient;
	else
		o_quotient <= 0;
	// }}}

	// r_c
	// {{{
	// Set Carry on an exact divide
	// Perhaps nothing uses this, but ... well, I suppose we could remove
	// this logic eventually, just ... not yet.
	initial	r_c = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_c <= 1'b0;
	else
		r_c <= (r_busy)&&(diff == 0);
	// }}}

	// w_n
	// {{{
	// The last flag: Negative.  This flag is set assuming that the result
	// of the divide was negative (i.e., the high order bit is set).  This
	// will also be true of an unsigned divide--if the high order bit is
	// ever set upon completion.  Indeed, you might argue that there's no
	// logic involved.
	assign w_n = o_quotient[(BW-1)];
	// }}}

	assign o_flags = { 1'b0, w_n, r_c, r_z };
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

`ifdef	DIV
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	initial	`ASSUME(i_reset);
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_busy);
		assert(!o_valid);
		assert(!o_err);
		//
		assert(!r_busy);
		// assert(!zero_divisor);
		assert(r_bit==0);
		assert(!last_bit);
		assert(!pre_sign);
		// assert(!r_z);
		// assert(r_dividend==0);
		assert(o_quotient==0);
		assert(!r_c);
		assert(r_divisor==0);

		`ASSUME(!i_wr);
	end

	always @(*)
	if (o_busy)
		`ASSUME(!i_wr);

	always @(*)
	if (r_busy)
		assert(o_busy);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(o_busy))&&(!o_busy))
	begin
		assert(o_valid);
	end

	// A formal methods section
	//
	// This section isn't yet complete.  For now, it is just
	// a description of things I think should be in here ... not
	// yet a description of what it would take to prove
	// this divide (yet).
	always @(*)
	if (o_err)
		assert(o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_wr)))
		assert(!pre_sign);
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wr))&&($past(i_signed))
			&&(|$past({i_numerator[BW-1],i_denominator[BW-1]})))
		assert(pre_sign);

	// always @(posedge i_clk)
	// if ((f_past_valid)&&(!$past(pre_sign)))
		// assert(!r_sign);
	reg	[BW:0]	f_bits_set;

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wr)))
		assert(o_busy);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid)))
		assert(!o_valid);

	always @(*)
	if ((o_valid)&&(!o_err))
	begin
		assert(r_z == ((o_quotient == 0)? 1'b1:1'b0));
	end else if (o_busy)
		assert(r_z == (((o_quotient&f_bits_set[BW-1:0]) == 0)? 1'b1: 1'b0));

	always @(*)
	if ((o_valid)&&(!o_err))
		assert(w_n == o_quotient[BW-1]);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(r_busy))&&(!$past(i_wr)))
		assert(!o_busy);
	always @(posedge i_clk)
		assert((!o_busy)||(!o_valid));

	always @(*)
	if(r_busy)
		assert(o_busy);

	always @(posedge i_clk)
	if (i_reset)
		f_bits_set <= 0;
	else if (i_wr)
		f_bits_set <= 0;
	else if ((r_busy)&&(!pre_sign))
		f_bits_set <= { f_bits_set[BW-1:0], 1'b1 };

	always @(posedge i_clk)
	if (r_busy)
		assert(((1<<r_bit)-1) == f_bits_set);

	always @(*)
	if ((o_valid)&&(!o_err))
		assert((!f_bits_set[BW])&&(&f_bits_set[BW-1:0]));


	/*
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(r_busy))
		&&($past(r_divisor[2*BW-2:BW])==0))
	begin
		if ($past(r_divisor) == 0)
		begin
			assert(o_err);
		end else if ($past(pre_sign))
		begin
			if ($past(r_dividend[BW-1]))
				assert(r_dividend == -$past(r_dividend));
			if ($past(r_divisor[(2*BW-2)]))
			begin
				assert(r_divisor[(2*BW-2):(BW-1)]
					== -$past(r_divisor[(2*BW-2):(BW-1)]));
				assert(r_divisor[BW-2:0] == 0);
			end
		end else begin
			if (o_quotient[0])
			begin
				assert(r_dividend == $past(diff));
			end else
				assert(r_dividend == $past(r_dividend));

			// r_divisor should shift down on every step
			assert(r_divisor[2*BW-2]==0);
			assert(r_divisor[2*BW-3:0]==$past(r_divisor[2*BW-2:1]));
		end
		if ($past(r_dividend) >= $past(r_divisor[BW-1:0]))
		begin
			assert(o_quotient[0]);
		end else
			assert(!o_quotient[0]);
	end
	*/

       	always @(*)
	if (r_busy)
		assert((f_bits_set & r_dividend[BW-1:0])==0);

       	always @(*)
	if (r_busy)
		assert((r_divisor == 0) == zero_divisor);

`ifdef	VERIFIC
	// {{{
	// Verify unsigned division
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_wr)&&(i_denominator != 0)&&(!i_signed)
		|=> ((!o_err)&&(!o_valid)&&(o_busy)&&(!r_sign)&&(!pre_sign)
	       			throughout (r_bit == 0)
			##1 ((r_bit == $past(r_bit)+1)&&({1'b0,r_bit}< BW-1))
					[*0:$]
			##1 ({ 1'b0, r_bit } == BW-1))
			##1 (!o_err)&&(o_valid));

	// Verify division by zero
	assert property (@(posedge i_clk)
		disable iff (i_reset)
		(i_wr)&&(i_denominator == 0)
		|=> (zero_divisor throughout
			(!o_err)&&(!o_valid)&&(pre_sign) [*0:1]
			##1 ((r_busy)&&(!o_err)&&(!o_valid))
			##1 ((o_err)&&(o_valid))));

	// }}}
`endif	// VERIFIC
`endif
// }}}
endmodule
//
// How much logic will this divide use, now that it's been updated to
// a different (long division) algorithm?
//
// iCE40 stats			(Updated)	(Original)
//   Number of cells:                700	820
//     SB_CARRY                      125	125
//     SB_DFF                          1	  
//     SB_DFFE                        33	  1
//     SB_DFFESR                      37
//     SB_DFFESS                      31
//     SB_DFFSR                       40	 40
//     SB_LUT4                       433	553
// 
// Xilinx stats			(Updated)	(Original)
//   Number of cells:                758	831
//     FDRE                          142	142
//     LUT1                           97	 97
//     LUT2                           69	174
//     LUT3                            6	  5
//     LUT4                            1	  6
//     LUT5                           68	 35
//     LUT6                           94	 98
//     MUXCY                         129	129
//     MUXF7                          12	  8
//     MUXF8                           6	  3
//     XORCY                         134	134

