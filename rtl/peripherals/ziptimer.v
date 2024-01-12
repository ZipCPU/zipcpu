////////////////////////////////////////////////////////////////////////////////
//
// Filename:	ziptimer.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A lighter weight implementation of the Zip Timer.
//
// Interface:
//	Two options:
//	1. One combined register for both control and value, and ...
//		The reload value is set any time the timer data value is "set".
//		Reading the register returns the timer value.  Controls are
//		set so that writing a value to the timer automatically starts
//		it counting down.
//	2. Two registers, one for control one for value.
//		The control register would have the reload value in it.
//	On the clock when the interface is set to zero the interrupt is set.
//		Hence setting the timer to zero will disable the timer without
//		setting any interrupts.  Thus setting it to five will count
//		5 clocks: 5, 4, 3, 2, 1, Interrupt.
//
//
//	Control bits:
//		(Start_n/Stop.  This bit has been dropped.  Writing to this
//			timer any value but zero starts it.  Writing a zero
//			clears and stops it.)
//		AutoReload.  If set, then on reset the timer automatically
//			loads the last set value and starts over.  This is
//			useful for distinguishing between a one-time interrupt
//			timer, and a repetitive interval timer.
//		(INTEN.  Interrupt enable--reaching zero always creates an
//			interrupt, so this control bit isn't needed.  The
//			interrupt controller can be used to mask the interrupt.)
//		(COUNT-DOWN/UP: This timer is *only* a count-down timer.
//			There is no means of setting it to count up.)
//	WatchDog
//		This timer can be implemented as a watchdog timer simply by
//		connecting the interrupt line to the reset line of the CPU.
//		When the timer then expires, it will trigger a CPU reset.
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
module	ziptimer #(
		// {{{
		parameter	BW = 32, VW = (BW-1),
		parameter [0:0]	RELOADABLE = 1
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset, i_ce,
		// Wishbone inputs
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire [BW-1:0]	i_wb_data,
		input	wire [BW/8-1:0]	i_wb_sel,
		// Wishbone outputs
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	wire [BW-1:0]	o_wb_data,
		// Interrupt line
		output	reg		o_int
		// }}}
	);

	// Local declarations
	// {{{
	reg			r_running;
	reg			r_zero  = 1'b1;
	reg	[(VW-1):0]	r_value;

	wire	wb_write;

	wire			auto_reload;
	wire	[(VW-1):0]	interval_count;
	// }}}

	assign	wb_write = ((i_wb_stb)&&(i_wb_we));

	// r_running
	// {{{
	initial	r_running = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_running <= 1'b0;
	else if (wb_write)
		r_running <= (|i_wb_data[(VW-1):0]);
	else if ((r_zero)&&(!auto_reload))
		r_running <= 1'b0;
	// }}}

	// r_auto_reload, r_interval_count
	// {{{
	generate
	if (RELOADABLE != 0)
	begin : GEN_RELOAD
		// {{{
		reg			r_auto_reload;
		reg	[(VW-1):0]	r_interval_count;

		// r_auto_reload
		// {{{
		initial	r_auto_reload = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_auto_reload <= 1'b0;
		else if (wb_write)
			r_auto_reload <= (i_wb_data[(BW-1)])
					&&(|i_wb_data[(VW-1):0]);
		// }}}

		assign	auto_reload = r_auto_reload;

		// r_interval_count
		// {{{
		// If setting auto-reload mode, and the value to other
		// than zero, set the auto-reload value
		always @(posedge i_clk)
		if (i_reset)
			r_interval_count <= 0;
		else if (wb_write)
			r_interval_count <= i_wb_data[(VW-1):0];
		// }}}

		assign	interval_count = r_interval_count;
		// }}}
	end else begin : NO_AUTO_RELOAD
		// {{{
		assign	auto_reload = 1'b0;
		assign	interval_count = 0;
		// }}}
	end endgenerate
	// }}}

	// r_value
	// {{{
	initial	r_value = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_value <= 0;
	else if (wb_write)
		r_value <= i_wb_data[(VW-1):0];
	else if ((i_ce)&&(r_running))
	begin
		if (!r_zero)
			r_value <= r_value - 1'b1;
		else if (auto_reload)
			r_value <= interval_count;
	end
	// }}}

	// r_zero
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		r_zero <= 1'b1;
	else if (wb_write)
		r_zero <= (i_wb_data[(VW-1):0] == 0);
	else if ((r_running)&&(i_ce))
	begin
		if (r_value == { {(VW-1){1'b0}}, 1'b1 })
			r_zero <= 1'b1;
		else if ((r_zero)&&(auto_reload))
			r_zero <= 1'b0;
	end
	// }}}

	// o_int
	// {{{
	// Set the interrupt on our last tick, as we transition from one to
	// zero.
	initial	o_int   = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(wb_write)||(!i_ce))
		o_int <= 1'b0;
	else // if (i_ce)
		o_int <= (r_value == { {(VW-1){1'b0}}, 1'b1 });
	// }}}

	// o_wb_ack
	// {{{
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= (!i_reset)&&(i_wb_stb);
	// }}}
	assign	o_wb_stall = 1'b0;

	// o_wb_data
	// {{{
	generate if (VW < BW-1)
	begin : GEN_TRIM
		assign	o_wb_data = { auto_reload, {(BW-1-VW){1'b0}}, r_value };
	end else begin : NO_TRIM
		assign	o_wb_data = { auto_reload, r_value };
	end endgenerate
	// }}}

	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data, i_wb_sel };
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

	initial	assume(i_reset);
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(r_value     == 0);
		assert(r_running   == 0);
		assert(auto_reload == 0);
		assert(r_zero      == 1'b1);
	end


	always @(*)
	if (i_wb_stb)
		assume(i_wb_cyc);

	always @(*)
		assert(r_zero == (r_value == 0));

	always @(*)
	if (r_value != 0)
		assert(r_running);

	always @(*)
	if (auto_reload)
		assert(r_running);

	always @(*)
	if (!RELOADABLE)
		assert(auto_reload == 0);

	always @(*)
	if (auto_reload)
		assert(interval_count != 0);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(r_value)==0)
			&&(!$past(wb_write))&&(!$past(auto_reload)))
		assert(r_value == 0);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(wb_write))
			&&($past(r_value)==0)&&($past(auto_reload)))
	begin
		if ($past(i_ce))
		begin
			assert(r_value == interval_count);
		end else
			assert(r_value == $past(r_value));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(wb_write))&&($past(r_value)!=0))
	begin
		if ($past(i_ce))
		begin
			assert(r_value == $past(r_value)-1'b1);
		end else
			assert(r_value == $past(r_value));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(wb_write)))
		assert(r_value == $past(i_wb_data[(VW-1):0]));

	// Check auto_reload
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset) || !RELOADABLE)
	begin
		assert(!auto_reload);
	end else if ($past(wb_write))
	begin
		if (!$past(i_wb_data[BW-1]))
		begin
			assert(!auto_reload);
		end else
			assert(auto_reload == $past(|i_wb_data[VW-1:0]));
	end else
		assert($stable(auto_reload));
	// }}}

	always @(posedge i_clk)
	if (!(f_past_valid)||($past(i_reset)))
	begin
		assert(!o_int);
	end else if (($past(wb_write))||(!$past(i_ce)))
	begin
		assert(!o_int);
	end else
		assert(o_int == ((r_running)&&(r_value == 0)));

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_wb_ack);
	end else if ($past(i_wb_stb))
		assert(o_wb_ack);

	always @(*)
		assert(!o_wb_stall);
	always @(*)
		assert(o_wb_data[BW-1] == auto_reload);
	always @(*)
		assert(o_wb_data[VW-1:0] == r_value);
`endif
// }}}
endmodule
