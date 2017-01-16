///////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbdblpriarb.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This should almost be identical to the priority arbiter, save
//		for a simple diffence: it allows the arbitration of two
//	separate wishbone buses.  The purpose of this is to push the address
//	resolution back one cycle, so that by the first clock visible to this
//	core, it is known which of two parts of the bus the desired address
//	will be on, save that we still use the arbiter since the underlying
//	device doesn't know that there are two wishbone buses.
//
//	So at this point we've deviated from the WB spec somewhat, by allowing
//	two CYC and two STB lines.  Everything else is the same.  This allows
//	(in this case the Zip CPU) to determine whether or not the access
//	will be to the local ZipSystem bus or the external WB bus on the clock
//	before the local bus access, otherwise peripherals were needing to do
//	multiple device selection comparisons/test within a clock: 1) is this
//	for the local or external bus, and 2) is this referencing me as a
//	peripheral.  This then caused the ZipCPU to fail all timing specs.
//	By creating the two pairs of lines, CYC_A/STB_A and CYC_B/STB_B, the
//	determination of local vs external can be made one clock earlier
//	where there's still time for the logic, and the second comparison
//	now has time to complete.
//
//	So let me try to explain this again.  To use this arbiter, one of the
//	two masters sets CYC and STB before, only the master determines which
//	of two address spaces the CYC and STB apply to before the clock and
//	only sets the appropriate CYC and STB lines.  Then, on the clock tick,
//	the arbiter determines who gets *both* busses, as they both share every
//	other WB line. Thus, only one of CYC_A and CYC_B going out will ever
//	be high at a given time.
//
//	Hopefully this makes more sense than it sounds. If not, check out the
//	code below for a better explanation.
//
//	20150919 -- Added supported for the WB error signal.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
///////////////////////////////////////////////////////////////////////////
//
module	wbdblpriarb(i_clk, i_rst, 
	// Bus A
	i_a_cyc_a,i_a_cyc_b,i_a_stb_a,i_a_stb_b,i_a_we,i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	// Bus B
	i_b_cyc_a,i_b_cyc_b,i_b_stb_a,i_b_stb_b,i_b_we,i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	// Both buses
	o_cyc_a, o_cyc_b, o_stb_a, o_stb_b, o_we, o_adr, o_dat, o_sel,
		i_ack, i_stall, i_err);
	parameter			DW=32, AW=32;
	// Wishbone doesn't use an i_ce signal.  While it could, they dislike
	// what it would (might) do to the synchronous reset signal, i_rst.
	input				i_clk, i_rst;
	// Bus A
	input				i_a_cyc_a, i_a_cyc_b, i_a_stb_a, i_a_stb_b, i_a_we;
	input		[(AW-1):0]	i_a_adr;
	input		[(DW-1):0]	i_a_dat;
	input		[(DW/8-1):0]	i_a_sel;
	output	wire			o_a_ack, o_a_stall, o_a_err;
	// Bus B
	input				i_b_cyc_a, i_b_cyc_b, i_b_stb_a, i_b_stb_b, i_b_we;
	input		[(AW-1):0]	i_b_adr;
	input		[(DW-1):0]	i_b_dat;
	input		[(DW/8-1):0]	i_b_sel;
	output	wire			o_b_ack, o_b_stall, o_b_err;
	// 
	output	wire			o_cyc_a,o_cyc_b, o_stb_a, o_stb_b, o_we;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	input				i_ack, i_stall, i_err;

	// All of our logic is really captured in the 'r_a_owner' register.
	// This register determines who owns the bus.  If no one is requesting
	// the bus, ownership goes to A on the next clock.  Otherwise, if B is 
	// requesting the bus and A is not, then ownership goes to not A on
	// the next clock.  (Sounds simple ...)
	//
	// The CYC logic is here to make certain that, by the time we determine
	// who the bus owner is, we can do so based upon determined criteria.
	assign o_cyc_a = (~i_rst)&&((r_a_owner) ? i_a_cyc_a : i_b_cyc_a);
	assign o_cyc_b = (~i_rst)&&((r_a_owner) ? i_a_cyc_b : i_b_cyc_b);
	reg	r_a_owner;
	initial	r_a_owner = 1'b1;
	always @(posedge i_clk)
		if (i_rst)
			r_a_owner <= 1'b1;
		else if ((~o_cyc_a)&&(~o_cyc_b))
			r_a_owner <= ((i_b_cyc_a)||(i_b_cyc_b))? 1'b0:1'b1;


	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if 
	// neither owns the bus than the values on these various lines are
	// irrelevant.
	assign o_stb_a = (r_a_owner) ? i_a_stb_a : i_b_stb_a;
	assign o_stb_b = (r_a_owner) ? i_a_stb_b : i_b_stb_b;
	assign o_we    = (r_a_owner) ? i_a_we    : i_b_we;
	assign o_adr   = (r_a_owner) ? i_a_adr   : i_b_adr;
	assign o_dat   = (r_a_owner) ? i_a_dat   : i_b_dat;
	assign o_sel   = (r_a_owner) ? i_a_sel   : i_b_sel;

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
	// These error lines will be implemented soon, as soon as the rest of
	// the Zip CPU is ready to support them.
	//
	assign	o_a_err = ( r_a_owner) ? i_err : 1'b0;
	assign	o_b_err = (~r_a_owner) ? i_err : 1'b0;

endmodule

