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
// Copyright (C) 2015,2018, Gisselquist Technology, LLC
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
module	wbpriarbiter(i_clk,
	// Bus A
	i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	// Bus B
	i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	// Both buses
	o_cyc, o_stb, o_we, o_adr, o_dat, o_sel, i_ack, i_stall, i_err);
	parameter			DW=32, AW=32;
	//
	// ZERO_ON_IDLE uses more logic than the alternative.  It should be
	// useful for reducing power, as these circuits tend to drive wires
	// all the way across the design, but it may also slow down the master
	// clock.  I've used it as an option when using VERILATOR, 'cause
	// zeroing things on idle can make them stand out all the more when
	// staring at wires and dumps and such.
	parameter	[0:0]		OPT_ZERO_ON_IDLE = 1'b0;
	parameter	[0:0]		F_OPT_CLK2FFLOGIC = 1'b0;
	//
	input	wire			i_clk;
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

	// Go high immediately (new cycle) if ...
	//	Previous cycle was low and *someone* is requesting a bus cycle
	// Go low immadiately if ...
	//	We were just high and the owner no longer wants the bus
	// WISHBONE Spec recommends no logic between a FF and the o_cyc
	//	This violates that spec.  (Rec 3.15, p35)
	reg	r_a_owner;

	initial	r_a_owner = 1'b1;
	always @(posedge i_clk)
		if (!i_b_cyc)
			r_a_owner <= 1'b1;
		// Allow B to set its CYC line w/o activating this interface
		else if ((i_b_cyc)&&(i_b_stb)&&(!i_a_cyc))
			r_a_owner <= 1'b0;

	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if
	// neither owns the bus than the values on these various lines are
	// irrelevant.

	assign o_cyc = (r_a_owner) ? i_a_cyc : i_b_cyc;
	assign o_we  = (r_a_owner) ? i_a_we  : i_b_we;
	assign o_stb   = (r_a_owner) ? i_a_stb   : i_b_stb;
	generate if (OPT_ZERO_ON_IDLE)
	begin
		assign	o_adr     = (o_stb)?((r_a_owner) ? i_a_adr  : i_b_adr):0;
		assign	o_dat     = (o_stb)?((r_a_owner) ? i_a_dat  : i_b_dat):0;
		assign	o_sel     = (o_stb)?((r_a_owner) ? i_a_sel  : i_b_sel):0;
		assign	o_a_ack   = (o_cyc)&&( r_a_owner) ? i_ack   : 1'b0;
		assign	o_b_ack   = (o_cyc)&&(!r_a_owner) ? i_ack   : 1'b0;
		assign	o_a_stall = (o_cyc)&&( r_a_owner) ? i_stall : 1'b1;
		assign	o_b_stall = (o_cyc)&&(!r_a_owner) ? i_stall : 1'b1;
		assign	o_a_err   = (o_cyc)&&( r_a_owner) ? i_err : 1'b0;
		assign	o_b_err   = (o_cyc)&&(!r_a_owner) ? i_err : 1'b0;
	end else begin
		assign o_adr   = (r_a_owner) ? i_a_adr   : i_b_adr;
		assign o_dat   = (r_a_owner) ? i_a_dat   : i_b_dat;
		assign o_sel   = (r_a_owner) ? i_a_sel   : i_b_sel;

		// We cannot allow the return acknowledgement to ever go high if
		// the master in question does not own the bus.  Hence we force it
		// low if the particular master doesn't own the bus.
		assign	o_a_ack   = ( r_a_owner) ? i_ack   : 1'b0;
		assign	o_b_ack   = (!r_a_owner) ? i_ack   : 1'b0;

		// Stall must be asserted on the same cycle the input master asserts
		// the bus, if the bus isn't granted to him.
		assign	o_a_stall = ( r_a_owner) ? i_stall : 1'b1;
		assign	o_b_stall = (!r_a_owner) ? i_stall : 1'b1;

		//
		//
		assign	o_a_err = ( r_a_owner) ? i_err : 1'b0;
		assign	o_b_err = (!r_a_owner) ? i_err : 1'b0;
	end endgenerate

`ifdef	FORMAL

`ifdef	WBPRIARBITER
	generate if (F_OPT_CLK2FFLOGIC)
	begin
		reg	f_last_clk;
		initial	assume(!i_clk);
		always @($global_clock)
		begin
			assume(i_clk != f_last_clk);
			f_last_clk <= i_clk;
		end
	end endgenerate
`define	`ASSUME	assume
`else
`define	`ASSUME	assert
`endif

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	assume(!i_a_cyc);
	initial	assume(!i_a_stb);

	initial	assume(!i_b_cyc);
	initial	assume(!i_b_stb);

	initial	assume(!i_ack);
	initial	assume(!i_err);

	always @(posedge i_clk)
	begin
		if (o_cyc)
			assert((i_a_cyc)||(i_b_cyc));
		if ((f_past_valid)&&($past(o_cyc))&&(o_cyc))
			assert($past(r_a_owner) == r_a_owner);
		if ((f_past_valid)&&($past(!o_cyc))&&($past(i_a_stb)))
			assert(r_a_owner);
		if ((f_past_valid)&&($past(!o_cyc))&&($past(i_b_stb)))
			assert(!r_a_owner);
	end

	reg	f_reset;
	initial	f_reset = 1'b1;
	always @(posedge i_clk)
		f_reset <= 1'b0;
	always @(*)
		if (!f_past_valid)
			assert(f_reset);

	parameter	F_LGDEPTH=3;

	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding,
			f_a_nreqs, f_a_nacks, f_a_outstanding,
			f_b_nreqs, f_b_nacks, f_b_outstanding;

	fwb_master #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbm(i_clk, f_reset,
			o_cyc, o_stb, o_we, o_adr, o_dat, o_sel,
			i_ack, i_stall, 32'h0, i_err,
			f_nreqs, f_nacks, f_outstanding);
	fwb_slave  #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wba(i_clk, f_reset,
			i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel, 
			o_a_ack, o_a_stall, 32'h0, o_a_err,
			f_a_nreqs, f_a_nacks, f_a_outstanding);
	fwb_slave  #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbb(i_clk, f_reset,
			i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel,
			o_b_ack, o_b_stall, 32'h0, o_b_err,
			f_b_nreqs, f_b_nacks, f_b_outstanding);

	always @(posedge i_clk)
		if (r_a_owner)
		begin
			assert(f_b_nreqs == 0);
			assert(f_b_nacks == 0);
			assert(f_a_outstanding == f_outstanding);
		end else begin
			assert(f_a_nreqs == 0);
			assert(f_a_nacks == 0);
			assert(f_b_outstanding == f_outstanding);
		end

	always @(posedge i_clk)
		if ((r_a_owner)&&(i_b_cyc))
			assume(i_b_stb);

	always @(posedge i_clk)
		if ((r_a_owner)&&(i_a_cyc))
			assume(i_a_stb);

`endif
endmodule

