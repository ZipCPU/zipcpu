////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbwatchdog.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A Zip timer, redesigned to be a bus watchdog
//
//	This is a **really** stripped down Zip Timer.  All options for external
//	control have been removed.  This timer may be reset, and ... that's 
//	about it.  The goal is that this stripped down timer be used as a bus
//	watchdog element.  Even at that, it's not really fully featured.  The
//	rest of the important features can be found in the zipsystem module.
//
//	As a historical note, the wishbone watchdog timer began as a normal
//	timer, with some fixed inputs.  This makes sense, if you think about it:
//	if the goal is to interrupt a stalled wishbone transaction by inserting
//	a bus error, then you can't use the bus to set it up or configure it
//	simply because the bus in question is ... well, unreliable.  You're
//	trying to make it reliable.
//
//	The problem with using the ziptimer in a stripped down implementation
//	was that the fixed inputs caused the synthesis tool to complain about
//	the use of registers values would never change.  This solves that
//	problem by explicitly removing the cruft that would otherwise
//	just create synthesis warnings and errors.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017, Gisselquist Technology, LLC
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
module	wbwatchdog(i_clk, i_rst, i_ce, i_timeout, o_int);
	parameter	BW = 32;
	input			i_clk, i_rst, i_ce;
	// Inputs (these were at one time wishbone controlled ...)
	input	[(BW-1):0]	i_timeout;
	// Interrupt line
	output	reg		o_int;

	reg	[(BW-1):0]	r_value;
	initial	r_value = 0;
	always @(posedge i_clk)
		if (i_rst)
			r_value <= i_timeout[(BW-1):0];
		else if ((i_ce)&&(~o_int))
			r_value <= r_value + {(BW){1'b1}}; // r_value - 1;

	// Set the interrupt on our last tick.
	initial	o_int   = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(~i_ce))
			o_int <= 1'b0;
		else
			o_int <= (r_value == { {(BW-1){1'b0}}, 1'b1 });

endmodule
