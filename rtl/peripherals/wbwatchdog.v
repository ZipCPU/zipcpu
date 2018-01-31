////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbwatchdog.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A Zip timer, redesigned to be a bus watchdog
//
//	This is basically a timer, but there are some unique features to it.
//
//	1. There is no way to "write" the timeout to this watchdog.  It is
//		fixed with an input (that is assumed to be constant)
//	2. The counter returns to i_timer and the interrupt is cleared on any
//		reset.
//	3. Between resets, the counter counts down to zero.  Once (and if) it
//		hits zero, it will remain at zero until reset.
//	4. Any time the counter is at zero, and until the reset that resets
//		the counter, the output interrupt will be set.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017-2018, Gisselquist Technology, LLC
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
`default_nettype	none
//
module	wbwatchdog(i_clk, i_reset, i_timeout, o_int);
	parameter	BW = 32;
	input	wire		i_clk, i_reset;
	// Inputs (these were at one time wishbone controlled ...)
	input	wire [(BW-1):0]	i_timeout;
	// Interrupt line
	output	reg		o_int;

	reg	[(BW-1):0]	r_value;
	initial	r_value = {(BW){1'b1}};
	always @(posedge i_clk)
		if (i_reset)
			r_value <= i_timeout[(BW-1):0];
		else if (!o_int)
			r_value <= r_value + {(BW){1'b1}}; // r_value - 1;

	// Set the interrupt on our last tick.
	initial	o_int   = 1'b0;
	always @(posedge i_clk)
		if (i_reset)
			o_int <= 1'b0;
		else if (!o_int)
			o_int <= (r_value == { {(BW-1){1'b0}}, 1'b1 });

`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge f_past_valid)
		f_past_valid <= 1'b1;

	///////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	///////////////////////////////////////////////
	always @(*)
		assume(i_timeout > 1);
	always @(posedge i_clk)
	if (f_past_valid)
		assume(i_timeout == $past(i_timeout));

	//
	//
	///////////////////////////////////////////////
	//
	//
	// Assertions about our internal state and our outputs
	//
	//
	///////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_int))&&(!$past(i_reset)))
		assert(o_int);

	always @(*)
		assert(o_int == (r_value == 0));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(o_int)))
	begin
		assert(r_value == $past(r_value)-1'b1);
	end

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		if (!f_past_valid)
			assert(r_value == {(BW){1'b1}});
		else // if ($past(i_reset))
			assert(r_value == $past(i_timeout));
		assert(!o_int);
	end
`endif
endmodule
