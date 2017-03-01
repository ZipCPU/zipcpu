////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbpriarbiter.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a priority bus arbiter.  It allows two separate wishbone
//		masters to connect to the same bus, while also guaranteeing
//		that one master can have the bus with no delay any time the
//		other master is not using the bus.  The goal is to eliminate
//		the combinatorial logic required in the other wishbone
//		arbiter, while still guarateeing access time for the priority
//		channel.
//
//		The core logic works like this:
//
//		1. When no one requests the bus, 'A' is granted the bus and
//			guaranteed that any access will go right through.
//		2. If 'B' requests the bus (asserts cyc), and the bus is idle,
//			then 'B' will be granted the bus.
//		3. Bus grants last as long as the 'cyc' line is high.
//		4. Once 'cyc' is dropped, the bus returns to 'A' as the owner.
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
module	wbpriarbiter(i_clk,
	// Bus A
	i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	// Bus B
	i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	// Both buses
	o_cyc, o_stb, o_we, o_adr, o_dat, o_sel, i_ack, i_stall, i_err);
	parameter			DW=32, AW=32;
	//
	input				i_clk;
	// Bus A
	input				i_a_cyc, i_a_stb, i_a_we;
	input		[(AW-1):0]	i_a_adr;
	input		[(DW-1):0]	i_a_dat;
	input		[(DW/8-1):0]	i_a_sel;
	output	wire			o_a_ack, o_a_stall, o_a_err;
	// Bus B
	input				i_b_cyc, i_b_stb, i_b_we;
	input		[(AW-1):0]	i_b_adr;
	input		[(DW-1):0]	i_b_dat;
	input		[(DW/8-1):0]	i_b_sel;
	output	wire			o_b_ack, o_b_stall, o_b_err;
	//
	output	wire			o_cyc, o_stb, o_we;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	input				i_ack, i_stall, i_err;

	// Go high immediately (new cycle) if ...
	//	Previous cycle was low and *someone* is requesting a bus cycle
	// Go low immadiately if ...
	//	We were just high and the owner no longer wants the bus
	// WISHBONE Spec recommends no logic between a FF and the o_cyc
	//	This violates that spec.  (Rec 3.15, p35)
	assign o_cyc = (r_a_owner) ? i_a_cyc : i_b_cyc;
	reg	r_a_owner;
	initial	r_a_owner = 1'b1;
	always @(posedge i_clk)
		if (~i_b_cyc)
			r_a_owner <= 1'b1;
		else if ((i_b_cyc)&&(~i_a_cyc))
			r_a_owner <= 1'b0;


	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if
	// neither owns the bus than the values on the various lines are
	// irrelevant.
	assign o_we  = (r_a_owner) ? i_a_we  : i_b_we;
`ifdef	ZERO_ON_IDLE
	//
	// ZERO_ON_IDLE will use up more logic and may even slow down the master
	// clock if set.  However, it may also reduce the power used by the
	// FPGA by preventing things from toggling when the bus isn't in use.
	// The option is here because it also makes it a lot easier to look
	// for when things happen on the bus via VERILATOR when timing and
	// logic counts don't matter.
	//
	assign o_stb = (o_cyc)?((r_a_owner) ? i_a_stb : i_b_stb):0;
	assign o_adr = (o_stb)?((r_a_owner) ? i_a_adr : i_b_adr):0;
	assign o_dat = (o_stb)?((r_a_owner) ? i_a_dat : i_b_dat):0;
	assign o_sel = (o_stb)?((r_a_owner) ? i_a_sel : i_b_sel):0;
	assign o_a_ack   = (o_cyc)&&( r_a_owner) ? i_ack   : 1'b0;
	assign o_b_ack   = (o_cyc)&&(~r_a_owner) ? i_ack   : 1'b0;
	assign o_a_stall = (o_cyc)&&( r_a_owner) ? i_stall : 1'b1;
	assign o_b_stall = (o_cyc)&&(~r_a_owner) ? i_stall : 1'b1;
	assign o_a_err = (o_cyc)&&( r_a_owner) ? i_err : 1'b0;
	assign o_b_err = (o_cyc)&&(~r_a_owner) ? i_err : 1'b0;
`else
	assign o_stb = (r_a_owner) ? i_a_stb : i_b_stb;
	assign o_adr = (r_a_owner) ? i_a_adr : i_b_adr;
	assign o_dat = (r_a_owner) ? i_a_dat : i_b_dat;
	assign o_sel = (r_a_owner) ? i_a_sel : i_b_sel;

	// We cannot allow the return acknowledgement to ever go high if
	// the master in question does not own the bus.  Hence we force it
	// low if the particular master doesn't own the bus.
	assign	o_a_ack   = ( r_a_owner) ? i_ack   : 1'b0;
	assign	o_b_ack   = (~r_a_owner) ? i_ack   : 1'b0;

	// Stall must be asserted on the same cycle the input master asserts
	// the bus, if the bus isn't granted to him.
	assign	o_a_stall = ( r_a_owner) ? i_stall : 1'b1;
	assign	o_b_stall = (~r_a_owner) ? i_stall : 1'b1;

	//
	//
	assign	o_a_err = ( r_a_owner) ? i_err : 1'b0;
	assign	o_b_err = (~r_a_owner) ? i_err : 1'b0;
`endif

endmodule

