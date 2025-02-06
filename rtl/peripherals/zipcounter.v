////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/peripherals/zipcounter.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:
//		A very, _very_ simple counter.  It's purpose doesn't really
//	include rollover, but it will interrupt on rollover.  It can be set,
//	although my design concept is that it can be reset.  It cannot be
//	halted.  It will always produce interrupts--whether or not they are
//	handled interrupts is another question--that's up to the interrupt
//	controller.
//
//	My intention is to use this counter for process accounting: I should
//	be able to use this to count clock ticks of processor time assigned to
//	each task by resetting the counter at the beginning of every task
//	interval, and reading the result at the end of the interval.  As long
//	as the interval is less than 2^32 clocks, there should be no problem.
//	Similarly, this can be used to measure CPU wishbone bus stalls,
//	prefetch stalls, or other CPU stalls (i.e. stalling as part of a JMP
//	instruction, or a read from the condition codes following a write).
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2025, Gisselquist Technology, LLC
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
module	zipcounter #(
		// {{{
		parameter	BW = 32
`ifdef	FORMAL
		, localparam	F_LGDEPTH = 2
`endif
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset, i_event,
		// Wishbone inputs
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(BW-1):0]	i_wb_data,
		// Wishbone outputs
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[(BW-1):0]	o_wb_data,
		// Interrupt line
		output	reg			o_int
		// }}}
	);

	// o_int, o_wb_data
	// {{{
	initial	o_int = 0;
	initial	o_wb_data = 32'h00;
	always @(posedge i_clk)
	if (i_reset)
		{ o_int, o_wb_data } <= 0;
	else if ((i_wb_stb)&&(i_wb_we))
		{ o_int, o_wb_data } <= { 1'b0, i_wb_data };
	else if (i_event)
		{ o_int, o_wb_data } <= o_wb_data+{{(BW-1){1'b0}},1'b1};
	else
		o_int <= 1'b0;
	// }}}

	// o_wb_ack
	// {{{
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb;
	// }}}
	assign	o_wb_stall = 1'b0;


	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc };
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
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We never stall the bus
	always @(*)
		assert(!o_wb_stall);

	// We always ack every transaction on the following clock
	always @(posedge i_clk)
		assert(o_wb_ack == ((f_past_valid)&&(!$past(i_reset))
						&&($past(i_wb_stb))));

	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;

	fwb_slave #(
		// {{{
		.AW(1), .F_MAX_STALL(0),
			.F_MAX_ACK_DELAY(1), .F_LGDEPTH(F_LGDEPTH)
		// }}}
	) fwbi(
		// {{{
		i_clk, i_reset,
		i_wb_cyc, i_wb_stb, i_wb_we, 1'b0, i_wb_data, 4'hf,
			o_wb_ack, o_wb_stall, o_wb_data, 1'b0,
		f_nreqs, f_nacks, f_outstanding
		// }}}
	);

	always @(*)
	if ((o_wb_ack)&&(i_wb_cyc))
	begin
		assert(f_outstanding==1);
	end else
		assert(f_outstanding == 0);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Drop the interrupt line and reset the counter on any reset
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert((!o_int)&&(o_wb_data == 0));
	// }}}

	// Clear the interrupt and set the counter on any write (other than
	// during a reset)
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
		&&($past(i_wb_stb))&&($past(i_wb_we)))
		assert((!o_int)&&(o_wb_data == $past(i_wb_data)));
	// }}}

	// Normal logic of the routine itself
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(i_wb_stb)))
	begin
		if (!$past(i_event))
		begin
			// If the CE line wasn't set on the last clock, then the
			// counter must not change, and the interrupt line must
			// be low.
			assert(o_wb_data == $past(o_wb_data));
			assert(!o_int);
		end else // if ($past(i_event))
		begin
			// Otherwise, if the CE line was high on the last clock,
			// then our counter should have incremented.
			assert(o_wb_data == $past(o_wb_data) + 1'b1);

			// Likewise, if the counter rolled over, then the
			// output interrupt, o_int, should be true.
			if ($past(o_wb_data)=={(BW){1'b1}})
			begin
				assert(o_int);
			end else
				// In all other circumstances it should be clear
				assert(!o_int);
		end
	end
	// ?}}}

	// The output interrupt should never be true two clocks in a row
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_int)))
		assert(!o_int);
	// }}}
	// }}}
`endif
// }}}
endmodule
