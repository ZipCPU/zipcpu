////////////////////////////////////////////////////////////////////////////////
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
module	wbdblpriarb(i_clk, i_reset,
	// Bus A
	i_a_cyc_a,i_a_cyc_b,i_a_stb_a,i_a_stb_b,i_a_we,i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	// Bus B
	i_b_cyc_a,i_b_cyc_b,i_b_stb_a,i_b_stb_b,i_b_we,i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	// Both buses
	o_cyc_a, o_cyc_b, o_stb_a, o_stb_b, o_we, o_adr, o_dat, o_sel,
		i_ack, i_stall, i_err);
	parameter			DW=32, AW=32;
	//
	// ZERO_ON_IDLE uses more logic than the alternative.  It should be
	// useful for reducing power, as these circuits tend to drive wires
	// all the way across the design, but it may also slow down the master
	// clock.  I've used it as an option when using VERILATOR, 'cause
	// zeroing things on idle can make them stand out all the more when
	// staring at wires and dumps and such.
	parameter	[0:0]		OPT_ZERO_ON_IDLE = 1'b0;
	//
	//
	parameter			F_LGDEPTH = 3;
	//
	// F_OPT_CLK2FFLOGIC shouldn't be needed.  However, if this component
	// is being used as a component of a multi-clock formal design, then
	// it will be necessary.  Set this any-time the design is being built
	// with the yosys clk2fflogic command used as part of the yosys script.
	parameter	[0:0]		F_OPT_CLK2FFLOGIC = 1'b0;
	// Wishbone doesn't use an i_ce signal.  While it could, they dislike
	// what it would (might) do to the synchronous reset signal, i_reset.
	input	wire			i_clk, i_reset;
	// Bus A
	input	wire			i_a_cyc_a, i_a_cyc_b, i_a_stb_a, i_a_stb_b, i_a_we;
	input	wire	[(AW-1):0]	i_a_adr;
	input	wire	[(DW-1):0]	i_a_dat;
	input	wire	[(DW/8-1):0]	i_a_sel;
	output	wire			o_a_ack, o_a_stall, o_a_err;
	// Bus B
	input	wire			i_b_cyc_a, i_b_cyc_b, i_b_stb_a, i_b_stb_b, i_b_we;
	input	wire	[(AW-1):0]	i_b_adr;
	input	wire	[(DW-1):0]	i_b_dat;
	input	wire	[(DW/8-1):0]	i_b_sel;
	output	wire			o_b_ack, o_b_stall, o_b_err;
	//
	output	wire			o_cyc_a,o_cyc_b, o_stb_a, o_stb_b, o_we;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	input	wire			i_ack, i_stall, i_err;

	// All of our logic is really captured in the 'r_a_owner' register.
	// This register determines who owns the bus.  If no one is requesting
	// the bus, ownership goes to A on the next clock.  Otherwise, if B is
	// requesting the bus and A is not, then ownership goes to not A on
	// the next clock.  (Sounds simple ...)
	//
	// The CYC logic is here to make certain that, by the time we determine
	// who the bus owner is, we can do so based upon determined criteria.
	reg	r_a_owner;

	initial	r_a_owner = 1'b1;
	always @(posedge i_clk)
		if (i_reset)
			r_a_owner <= 1'b1;
		/*
		// Remain with the "last owner" until 1) the other bus requests
		// access, and 2) the last owner no longer wants it.  This
		// logic "idles" on the last owner.
		//
		// This is an alternating bus owner strategy
		//
		else if ((!o_cyc_a)&&(!o_cyc_b))
			r_a_owner <= ((i_b_stb_a)||(i_b_stb_b))? 1'b0:1'b1;
		//
		// Expanding this out
		//
		// else if ((r_a_owner)&&((i_a_cyc_a)||(i_a_cyc_b)))
		//		r_a_owner <= 1'b1;
		// else if ((!r_a_owner)&&((i_b_cyc_a)||(i_b_cyc_b)))
		//		r_a_owner <= 1'b0;
		// else if ((r_a_owner)&&((i_b_stb_a)||(i_b_stb_b)))
		//		r_a_owner <= 1'b0;
		// else if ((!r_a_owner)&&((i_a_stb_a)||(i_a_stb_b)))
		//		r_a_owner <= 1'b0;
		//
		// Logic required:
		//
		//	Reset line
		//	+ 9 inputs (data)
		//	+ 9 inputs (CE)
		//	Could be done with three LUTs
		//		First two evaluate o_cyc_a and o_cyc_b (above)
		*/
		// Option 2:
		//
		// "Idle" on A as the owner.
		// If a request is made from B, AND A is idle, THEN
		// switch.  Otherwise, if B is ever idle, revert back to A
		// regardless of whether A wants it or not.
		else if ((!i_b_cyc_a)&&(!i_b_cyc_b))
			r_a_owner <= 1'b1;
		else if ((!i_a_cyc_a)&&(!i_a_cyc_b)
				&&((i_b_stb_a)||(i_b_stb_b)))
			r_a_owner <= 1'b0;

	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if
	// neither owns the bus than the values on these various lines are
	// irrelevant.

	assign o_cyc_a = ((r_a_owner) ? i_a_cyc_a : i_b_cyc_a);
	assign o_cyc_b = ((r_a_owner) ? i_a_cyc_b : i_b_cyc_b);
	assign o_stb_a = (r_a_owner) ? i_a_stb_a : i_b_stb_a;
	assign o_stb_b = (r_a_owner) ? i_a_stb_b : i_b_stb_b;
	assign o_we    = (r_a_owner) ? i_a_we    : i_b_we;
	generate if (OPT_ZERO_ON_IDLE)
	begin
		wire	o_cyc, o_stb;
		assign	o_cyc     = ((o_cyc_a)||(o_cyc_b));
		assign	o_stb     = ((o_stb_a)||(o_stb_b));
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

`ifdef	WBDBLPRIARB
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
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	`ASSUME(i_reset);
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	initial	`ASSUME(!i_a_cyc_a);
	initial	`ASSUME(!i_a_stb_a);
	initial	`ASSUME(!i_a_cyc_b);
	initial	`ASSUME(!i_a_stb_b);

	initial	`ASSUME(!i_b_cyc_a);
	initial	`ASSUME(!i_b_stb_a);
	initial	`ASSUME(!i_b_cyc_b);
	initial	`ASSUME(!i_b_stb_b);

	initial	`ASSUME(!i_ack);
	initial	`ASSUME(!i_err);

	always @(*)
		`ASSUME((!i_a_cyc_a)||(!i_a_cyc_b));
	always @(*)
		`ASSUME((!i_b_cyc_a)||(!i_b_cyc_b));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_a_cyc_a)))
		`ASSUME(!i_a_cyc_b);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_a_cyc_b)))
		`ASSUME(!i_a_cyc_a);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_b_cyc_a)))
		`ASSUME(!i_b_cyc_b);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_b_cyc_b)))
		`ASSUME(!i_b_cyc_a);

	wire	f_cyc, f_stb;
	assign	f_cyc = (o_cyc_a)||(o_cyc_b);
	assign	f_stb = (o_stb_a)||(o_stb_b);
	always @(posedge i_clk)
	begin
		if (o_cyc_a)
			assert((i_a_cyc_a)||(i_b_cyc_a));
		if (o_cyc_b)
			assert((i_a_cyc_b)||(i_b_cyc_b));
		assert((!o_cyc_a)||(!o_cyc_b));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin
		if ($past(f_cyc))
		begin
			if (($past(o_cyc_a))&&(o_cyc_a))
				assert($past(r_a_owner) == r_a_owner);
			if (($past(o_cyc_b))&&(o_cyc_b))
				assert($past(r_a_owner) == r_a_owner);
		end else begin
			if (($past(i_a_stb_a))||($past(i_a_stb_b)))
				assert(r_a_owner);
			if (($past(i_b_stb_a))||($past(i_b_stb_b)))
				assert(!r_a_owner);
		end
	end


	wire	[(F_LGDEPTH-1):0]
			f_nreqs_a, f_nacks_a, f_outstanding_a,
			f_nreqs_b, f_nacks_b, f_outstanding_b,
			f_a_nreqs_a, f_a_nacks_a, f_a_outstanding_a,
			f_a_nreqs_b, f_a_nacks_b, f_a_outstanding_b,
			f_b_nreqs_a, f_b_nacks_a, f_b_outstanding_a,
			f_b_nreqs_b, f_b_nacks_b, f_b_outstanding_b;

	fwb_master #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbm_a(i_clk, i_reset,
			o_cyc_a, o_stb_a, o_we, o_adr, o_dat, o_sel,
			(o_cyc_a)&&(i_ack), i_stall, 32'h0, (o_cyc_a)&&(i_err),
			f_nreqs_a, f_nacks_a, f_outstanding_a);
	fwb_master #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbm_b(i_clk, i_reset,
			o_cyc_b, o_stb_b, o_we, o_adr, o_dat, o_sel,
			(o_cyc_b)&&(i_ack), i_stall, 32'h0, (o_cyc_b)&&(i_err),
			f_nreqs_b, f_nacks_b, f_outstanding_b);
	fwb_slave  #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wba_a(i_clk, i_reset,
			i_a_cyc_a, i_a_stb_a, i_a_we, i_a_adr, i_a_dat, i_a_sel, 
			(o_cyc_a)&&(o_a_ack), o_a_stall, 32'h0, (o_cyc_a)&&(o_a_err),
			f_a_nreqs_a, f_a_nacks_a, f_a_outstanding_a);
	fwb_slave  #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wba_b(i_clk, i_reset,
			i_a_cyc_b, i_a_stb_b, i_a_we, i_a_adr, i_a_dat, i_a_sel, 
			(o_cyc_b)&&(o_a_ack), o_a_stall, 32'h0, (o_cyc_b)&&(o_a_err),
			f_a_nreqs_b, f_a_nacks_b, f_a_outstanding_b);
	fwb_slave  #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbb_a(i_clk, i_reset,
			i_b_cyc_a, i_b_stb_a, i_b_we, i_b_adr, i_b_dat, i_b_sel,
			(o_cyc_a)&&(o_b_ack), o_b_stall, 32'h0, (o_cyc_a)&&(o_b_err),
			f_b_nreqs_a, f_b_nacks_a, f_b_outstanding_a);
	fwb_slave  #(.F_MAX_STALL(0),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_ACK_DELAY(0),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbb_b(i_clk, i_reset,
			i_b_cyc_b, i_b_stb_b, i_b_we, i_b_adr, i_b_dat, i_b_sel,
			(o_cyc_b)&&(o_b_ack), o_b_stall, 32'h0, (o_cyc_b)&&(o_b_err),
			f_b_nreqs_b, f_b_nacks_b, f_b_outstanding_b);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin
		if (r_a_owner)
		begin
			assert(f_b_nreqs_a == 0);
			assert(f_b_nreqs_b == 0);
			//
			assert(f_b_nacks_a == 0);
			assert(f_b_nacks_b == 0);
			//
			if (i_a_cyc_a)
			begin
				assert(f_a_outstanding_a == f_outstanding_a);
				assert(f_a_outstanding_b == 0);
				assert(f_outstanding_b == 0);
				assert(f_a_nreqs_b == 0);
				assert(f_a_nacks_b == 0);
			end else if (i_a_cyc_b)
			begin
				assert(f_a_outstanding_b == f_outstanding_b);
				assert(f_a_outstanding_a == 0);
				assert(f_outstanding_a == 0);
				assert(f_a_nreqs_a == 0);
				assert(f_a_nacks_a == 0);
			end
		end else begin
			assert(f_a_nreqs_a == 0);
			assert(f_a_nreqs_b == 0);
			//
			assert(f_a_nacks_a == 0);
			assert(f_a_nacks_b == 0);
			//
			if (i_b_cyc_a)
			begin
				assert(f_b_outstanding_a == f_outstanding_a);
				assert(f_b_outstanding_b == 0);
				assert(f_outstanding_b == 0);
				assert(f_b_nreqs_b == 0);
				assert(f_b_nacks_b == 0);
			end else if (i_b_cyc_b)
			begin
				assert(f_b_outstanding_b == f_outstanding_b);
				assert(f_b_outstanding_a == 0);
				assert(f_outstanding_a == 0);
				assert(f_b_nreqs_a == 0);
				assert(f_b_nacks_a == 0);
			end
		end
	end

	always @(posedge i_clk)
		if ((r_a_owner)&&(i_b_cyc_a))
			`ASSUME((i_b_stb_a)&&(!i_b_stb_b));
	always @(posedge i_clk)
		if ((r_a_owner)&&(i_b_cyc_b))
			`ASSUME((i_b_stb_b)&&(!i_b_stb_a));

	always @(posedge i_clk)
		if ((r_a_owner)&&(i_a_cyc_a))
			`ASSUME((i_a_stb_a)&&(!i_a_stb_b));
	always @(posedge i_clk)
		if ((r_a_owner)&&(i_a_cyc_b))
			`ASSUME((i_a_stb_b)&&(!i_a_stb_a));

`endif
endmodule

