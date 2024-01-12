////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbarbiter.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a priority bus arbiter.  It allows two separate wishbone
//		masters to connect to the same bus, while also guaranteeing
//	that the last master can have the bus with no delay any time it is
//	idle.  The goal is to minimize the combinatorial logic required in this
//	process, while still minimizing access time.
//
//	The core logic works like this:
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
//
`define	WBA_ALTERNATING
// }}}
module	wbarbiter #(
		// {{{
		parameter			DW=32, AW=32,
		parameter			SCHEME="ALTERNATING",
		parameter	[0:0]		OPT_ZERO_ON_IDLE = 1'b0
`ifdef	FORMAL
		, parameter			F_MAX_STALL = 3,
		parameter			F_MAX_ACK_DELAY = 3,
		parameter			F_LGDEPTH=3
`endif
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Bus A -- the priority bus
		// {{{
		input	wire			i_a_cyc, i_a_stb, i_a_we,
		input	wire	[(AW-1):0]	i_a_adr,
		input	wire	[(DW-1):0]	i_a_dat,
		input	wire	[(DW/8-1):0]	i_a_sel,
		output	wire			o_a_stall, o_a_ack, o_a_err,
		// }}}
		// Bus B
		// {{{
		input	wire			i_b_cyc, i_b_stb, i_b_we,
		input	wire	[(AW-1):0]	i_b_adr,
		input	wire	[(DW-1):0]	i_b_dat,
		input	wire	[(DW/8-1):0]	i_b_sel,
		output	wire			o_b_stall, o_b_ack, o_b_err,
		// }}}
		// Combined/arbitrated bus
		// {{{
		output	wire			o_cyc, o_stb, o_we,
		output	wire	[(AW-1):0]	o_adr,
		output	wire	[(DW-1):0]	o_dat,
		output	wire	[(DW/8-1):0]	o_sel,
		input	wire			i_stall, i_ack, i_err
		// }}}
`ifdef	FORMAL
		, output	wire	[(F_LGDEPTH-1):0]
			f_nreqs, f_nacks, f_outstanding,
			f_a_nreqs, f_a_nacks, f_a_outstanding,
			f_b_nreqs, f_b_nacks, f_b_outstanding
`endif
		// }}}
	);

	// {{{
	// Go high immediately (new cycle) if ...
	//	Previous cycle was low and *someone* is requesting a bus cycle
	// Go low immadiately if ...
	//	We were just high and the owner no longer wants the bus
	// WISHBONE Spec recommends no logic between a FF and the o_cyc
	//	This violates that spec.  (Rec 3.15, p35)
	// }}}

	// Local declarations
	// {{{
	reg	r_a_owner;
	// }}}

	assign o_cyc = (r_a_owner) ? i_a_cyc : i_b_cyc;
	initial	r_a_owner = 1'b1;

	// r_a_owner -- determined through arbitration
	// {{{
	generate if (SCHEME == "PRIORITY")
	begin : PRI
		// {{{
		always @(posedge i_clk)
		if (!i_b_cyc)
			r_a_owner <= 1'b1;
		// Allow B to set its CYC line w/o activating this
		// interface
		else if ((i_b_stb)&&(!i_a_cyc))
			r_a_owner <= 1'b0;
		// }}}
	end else if (SCHEME == "ALTERNATING")
	begin : ALT
		// {{{
		reg	last_owner;

		initial	last_owner = 1'b0;
		always @(posedge i_clk)
		if ((i_a_cyc)&&(r_a_owner))
			last_owner <= 1'b1;
		else if ((i_b_cyc)&&(!r_a_owner))
			last_owner <= 1'b0;

		always @(posedge i_clk)
		if ((!i_a_cyc)&&(!i_b_cyc))
			r_a_owner <= !last_owner;
		else if ((r_a_owner)&&(!i_a_cyc))
		begin

			if (i_b_stb)
				r_a_owner <= 1'b0;

		end else if ((!r_a_owner)&&(!i_b_cyc))
		begin

			if (i_a_stb)
				r_a_owner <= 1'b1;

		end
		// }}}
	end else // if (SCHEME == "LAST")
	begin : LST
		// {{{
		always @(posedge i_clk)
		if ((!i_a_cyc)&&(i_b_stb))
			r_a_owner <= 1'b0;
		else if ((!i_b_cyc)&&(i_a_stb))
			r_a_owner <= 1'b1;
		// ?}}}
	end endgenerate
	// }}}

	// o_we
	// {{{
	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if
	// neither owns the bus than the values on the various lines are
	// irrelevant.
	assign o_we  = (r_a_owner) ? i_a_we  : i_b_we;
	// }}}

	// Other bus outputs
	// {{{
	generate if (OPT_ZERO_ON_IDLE)
	begin : LOW_POWER
		// {{{
		// OPT_ZERO_ON_IDLE will use up more logic and may even slow
		// down the master clock if set.  However, it may also reduce
		// the power used by the FPGA by preventing things from toggling
		// when the bus isn't in use.  The option is here because it
		// also makes it a lot easier to look for when things happen
		// on the bus via VERILATOR when timing and logic counts
		// don't matter.
		//
		assign o_stb     = (o_cyc)? ((r_a_owner) ? i_a_stb : i_b_stb):0;
		assign o_adr     = (o_stb)? ((r_a_owner) ? i_a_adr : i_b_adr):0;
		assign o_dat     = (o_stb)? ((r_a_owner) ? i_a_dat : i_b_dat):0;
		assign o_sel     = (o_stb)? ((r_a_owner) ? i_a_sel : i_b_sel):0;
		assign o_a_ack   = (o_cyc)&&( r_a_owner) ? i_ack   : 1'b0;
		assign o_b_ack   = (o_cyc)&&(!r_a_owner) ? i_ack   : 1'b0;
		assign o_a_stall = (o_cyc)&&( r_a_owner) ? i_stall : 1'b1;
		assign o_b_stall = (o_cyc)&&(!r_a_owner) ? i_stall : 1'b1;
		assign o_a_err   = (o_cyc)&&( r_a_owner) ? i_err : 1'b0;
		assign o_b_err   = (o_cyc)&&(!r_a_owner) ? i_err : 1'b0;
		// }}}
	end else begin : LOW_LOGIC
		// {{{

		assign o_stb = (r_a_owner) ? i_a_stb : i_b_stb;
		assign o_adr = (r_a_owner) ? i_a_adr : i_b_adr;
		assign o_dat = (r_a_owner) ? i_a_dat : i_b_dat;
		assign o_sel = (r_a_owner) ? i_a_sel : i_b_sel;

		// We cannot allow the return acknowledgement to ever go high if
		// the master in question does not own the bus.  Hence we force
		// it low if the particular master doesn't own the bus.
		assign	o_a_ack   = ( r_a_owner) ? i_ack   : 1'b0;
		assign	o_b_ack   = (!r_a_owner) ? i_ack   : 1'b0;

		// Stall must be asserted on the same cycle the input master
		// asserts the bus, if the bus isn't granted to him.
		assign	o_a_stall = ( r_a_owner) ? i_stall : 1'b1;
		assign	o_b_stall = (!r_a_owner) ? i_stall : 1'b1;

		//
		//
		assign	o_a_err = ( r_a_owner) ? i_err : 1'b0;
		assign	o_b_err = (!r_a_owner) ? i_err : 1'b0;
		// }}}
	end endgenerate
	// }}}

	// Make Verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_reset };
	// verilator lint_on  UNUSED
	// verilator coverage_on
	// }}}
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

`ifdef	WBARBITER
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	`ASSUME(!i_a_cyc);
	initial	`ASSUME(!i_a_stb);

	initial	`ASSUME(!i_b_cyc);
	initial	`ASSUME(!i_b_stb);

	initial	`ASSUME(!i_ack);
	initial	`ASSUME(!i_err);

	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	begin
		if (o_cyc)
			assert((i_a_cyc)||(i_b_cyc));
		if ((f_past_valid)&&($past(o_cyc))&&(o_cyc))
			assert($past(r_a_owner) == r_a_owner);
	end

	fwb_master #(
		// {{{
		.DW(DW), .AW(AW),
		.F_MAX_STALL(F_MAX_STALL),
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_ACK_DELAY(F_MAX_ACK_DELAY),
		.F_OPT_RMW_BUS_OPTION(1),
		.F_OPT_DISCONTINUOUS(1),
		.F_OPT_CLK2FFLOGIC(1'b0)
		// }}}
	) f_wbm (
		// {{{
		i_clk, i_reset,
		o_cyc, o_stb, o_we, o_adr, o_dat, o_sel,
		i_ack, i_stall, 32'h0, i_err,
		f_nreqs, f_nacks, f_outstanding
		// }}}
	);

	fwb_slave  #(
		// {{{
		.DW(DW), .AW(AW),
		.F_MAX_STALL(0),
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_ACK_DELAY(0),
		.F_OPT_RMW_BUS_OPTION(1),
		.F_OPT_DISCONTINUOUS(1),
		.F_OPT_CLK2FFLOGIC(1'b0)
		// }}}
	) f_wba (
		// {{{
		i_clk, i_reset,
		i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel,
		o_a_ack, o_a_stall, 32'h0, o_a_err,
		f_a_nreqs, f_a_nacks, f_a_outstanding
		// }}}
	);

	fwb_slave  #(
		// {{{
		.DW(DW), .AW(AW),
		.F_MAX_STALL(0),
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_ACK_DELAY(0),
		.F_OPT_RMW_BUS_OPTION(1),
		.F_OPT_DISCONTINUOUS(1),
		.F_OPT_CLK2FFLOGIC(1'b0)
		// }}}
	) f_wbb (
		// {{{
		i_clk, i_reset,
		i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel,
		o_b_ack, o_b_stall, 32'h0, o_b_err,
		f_b_nreqs, f_b_nacks, f_b_outstanding
		// }}}
	);

	// Induction properties, relating nreqs and nacks to r_a_owner
	// {{{
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
	// }}}

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(i_a_stb))&&(!$past(i_b_cyc)))
		assert(r_a_owner);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_a_cyc))&&($past(i_b_stb)))
		assert(!r_a_owner);

	always @(posedge i_clk)
		if ((f_past_valid)&&(r_a_owner != $past(r_a_owner)))
			assert(!$past(o_cyc));

`endif
// }}}
endmodule

