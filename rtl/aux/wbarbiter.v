////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbarbiter.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	At some point in time, I might wish to have two masters connect
//		to the same wishbone bus.  As an example, I might wish to have
//		both the instruction fetch and the load/store operators
//		of my Zip CPU access the the same bus.  How shall they both
//		get access to the same resource?  This module allows the
//		wishbone interfaces from two sources to drive the bus, while
//		guaranteeing that only one drives the bus at a time.
//
//		The core logic works like this:
//
//		1. If 'A' or 'B' asserts the o_cyc line, a bus cycle will begin,
//			with acccess granted to whomever requested it.
//		2. If both 'A' and 'B' assert o_cyc at the same time, only 'A'
//			will be granted the bus.  (If the alternating parameter 
//			is set, A and B will alternate who gets the bus in
//			this case.)
//		3. The bus will remain owned by whomever the bus was granted to
//			until they deassert the o_cyc line.
//		4. At the end of a bus cycle, o_cyc is guaranteed to be
//			deasserted (low) for one clock.
//		5. On the next clock, bus arbitration takes place again.  If
//			'A' requests the bus, no matter how long 'B' was
//			waiting, 'A' will then be granted the bus.  (Unless
//			again the alternating parameter is set, then the
//			access is guaranteed to switch to B.)
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
`define	WBA_ALTERNATING
module	wbarbiter(i_clk, i_rst, 
	// Bus A
	i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	// Bus B
	i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	// Both buses
	o_cyc, o_stb, o_we, o_adr, o_dat, o_sel, i_ack, i_stall, i_err);
	// 18 bits will address one GB, 4 bytes at a time.
	// 19 bits will allow the ability to address things other than just
	// the 1GB of memory we are expecting.
	parameter			DW=32, AW=19;
	// Wishbone doesn't use an i_ce signal.  While it could, they dislike
	// what it would (might) do to the synchronous reset signal, i_rst.
	input	wire			i_clk, i_rst;
	// Bus A
	input	wire			i_a_cyc, i_a_stb, i_a_we;
	input	wire	[(AW-1):0]	i_a_adr;
	input	wire	[(DW-1):0]	i_a_dat;
	input	wire	[(DW/8-1):0]	i_a_sel;
	output	wire			o_a_ack, o_a_stall, o_a_err;
	// Bus B
	input	wire			i_b_cyc, i_b_stb, i_b_we;
	input	wire	[(AW-1):0]	i_b_adr;
	input	wire	[(DW-1):0]	i_b_dat;
	input	wire	[(DW/8-1):0]	i_b_sel;
	output	wire			o_b_ack, o_b_stall, o_b_err;
	//
	output	wire			o_cyc, o_stb, o_we;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	input	wire			i_ack, i_stall, i_err;

	// All the fancy stuff here is done with the three primary signals:
	//	o_cyc
	//	w_a_owner
	//	w_b_owner
	// These signals are helped by r_cyc, r_a_owner, and r_b_owner.
	// If you understand these signals, all else will fall into place.

	// r_cyc just keeps track of the last o_cyc value.  That way, on
	// the next clock we can tell if we've had one non-cycle before
	// starting another cycle.  Specifically, no new cycles will be
	// allowed to begin unless r_cyc=0.
	reg	r_cyc;
	always @(posedge i_clk)
		if (i_rst)
			r_cyc <= 1'b0;
		else
			r_cyc <= o_cyc;

	// Go high immediately (new cycle) if ...
	//	Previous cycle was low and *someone* is requesting a bus cycle
	// Go low immadiately if ...
	//	We were just high and the owner no longer wants the bus
	// WISHBONE Spec recommends no logic between a FF and the o_cyc
	//	This violates that spec.  (Rec 3.15, p35)
	assign o_cyc = ((~r_cyc)&&((i_a_cyc)||(i_b_cyc))) || ((r_cyc)&&((w_a_owner)||(w_b_owner)));


	// Register keeping track of the last owner, wire keeping track of the
	// current owner allowing us to not lose a clock in arbitrating the
	// first clock of the bus cycle
	reg	r_a_owner, r_b_owner;
	wire	w_a_owner, w_b_owner;
`ifdef	WBA_ALTERNATING
	reg	r_a_last_owner;

`endif
	always @(posedge i_clk)
		if (i_rst)
		begin
			r_a_owner <= 1'b0;
			r_b_owner <= 1'b0;
		end else begin
			r_a_owner <= w_a_owner;
			r_b_owner <= w_b_owner;
`ifdef	WBA_ALTERNATING
			if (w_a_owner)
				r_a_last_owner <= 1'b1;
			else if (w_b_owner)
				r_a_last_owner <= 1'b0;
`endif
		end
	//
	// If you are the owner, retain ownership until i_x_cyc is no
	// longer asserted.  Likewise, you cannot become owner until o_cyc
	// is de-asserted for one cycle.
	//
	// 'A' is given arbitrary priority over 'B'
	// 'A' may own the bus only if he wants it.  When 'A' drops i_a_cyc,
	// o_cyc must drop and so must w_a_owner on the same cycle.
	// However, when 'A' asserts i_a_cyc, he can only capture the bus if
	// it's had an idle cycle.
	// The same is true for 'B' with one exception: if both contend for the
	// bus on the same cycle, 'A' arbitrarily wins.
`ifdef	WBA_ALTERNATING
	assign w_a_owner = (i_a_cyc)	// if A requests ownership, and either
			&& ((r_a_owner) // A has already been recognized or
			|| ((~r_cyc) // the bus is free and
				&&((~i_b_cyc) // B has not requested, or if he 
				||(~r_a_last_owner)) )); // has, it's A's turn
	assign w_b_owner = (i_b_cyc)&& ((r_b_owner) || ((~r_cyc)&&((~i_a_cyc)||(r_a_last_owner)) ));
`else
	assign w_a_owner = (i_a_cyc)&& ((r_a_owner) ||  (~r_cyc) );
	assign w_b_owner = (i_b_cyc)&& ((r_b_owner) || ((~r_cyc)&&(~i_a_cyc)) );
`endif

	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if 
	// neither owns the bus than the values on the various lines are
	// irrelevant.  (This allows us to get two outputs per Xilinx 6-LUT)
	assign o_stb = (o_cyc) && ((w_a_owner) ? i_a_stb : i_b_stb);
	assign o_we  = (w_a_owner) ? i_a_we  : i_b_we;
	assign o_adr = (w_a_owner) ? i_a_adr : i_b_adr;
	assign o_dat = (w_a_owner) ? i_a_dat : i_b_dat;
	assign o_sel = (w_a_owner) ? i_a_sel : i_b_sel;

	// We cannot allow the return acknowledgement to ever go high if
	// the master in question does not own the bus.  Hence we force it
	// low if the particular master doesn't own the bus.
	assign	o_a_ack   = (w_a_owner) ? i_ack   : 1'b0;
	assign	o_b_ack   = (w_b_owner) ? i_ack   : 1'b0;

	// Stall must be asserted on the same cycle the input master asserts
	// the bus, if the bus isn't granted to him.
	assign	o_a_stall = (w_a_owner) ? i_stall : 1'b1;
	assign	o_b_stall = (w_b_owner) ? i_stall : 1'b1;

	//
	//
	assign	o_a_err = (w_a_owner) ? i_err : 1'b0;
	assign	o_b_err = (w_b_owner) ? i_err : 1'b0;

endmodule

