////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	skidbuffer.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A basic SKID buffer.
//
//	Skid buffers are required for high throughput AXI code, since the AXI
//	specification requires that all outputs be registered.  This means
//	that, if there are any stall conditions calculated, it will take a clock
//	cycle before the stall can be propagated up stream.  This means that
//	the data will need to be buffered for a cycle until the stall signal
//	can make it to the output.
//
//	Handling that buffer is the purpose of this core.
//
//	On one end of this core, you have the i_valid and i_data inputs to
//	connect to your bus interface.  There's also a registered o_ready
//	signal to signal stalls for the bus interface.
//
//	The other end of the core has the same basic interface, but it isn't
//	registered.  This allows you to interact with the bus interfaces
//	as though they were combinatorial logic, by interacting with this half
//	of the core.
//
//	If at any time the incoming !stall signal, i_ready, signals a stall,
//	the incoming data is placed into a buffer.  Internally, that buffer
//	is held in r_data with the r_valid flag used to indicate that valid
//	data is within it.
//
// Parameters:
//	DW or data width
//		In order to make this core generic, the width of the data in the
//		skid buffer is parameterized
//
//	OPT_LOWPOWER
//		Forces both o_data and r_data to zero if the respective *VALID
//		signal is also low.  While this costs extra logic, it can also
//		be used to guarantee that any unused values aren't toggling and
//		therefore unnecessarily using power.
//
//		This excess toggling can be particularly problematic if the
//		bus signals have a high fanout rate, or a long signal path
//		across an FPGA.
//
//	OPT_OUTREG
//		Causes the outputs to be registered
//
//	OPT_PASSTHROUGH
//		Turns the skid buffer into a passthrough.  Used for formal
//		verification only.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2020, Gisselquist Technology, LLC
// {{{
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
// }}}
module skidbuffer #(
		// {{{
		parameter	[0:0]	OPT_LOWPOWER = 0,
		parameter	[0:0]	OPT_OUTREG = 1,
		//
		parameter	[0:0]	OPT_PASSTHROUGH = 0,
		parameter		DW = 8
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		input	wire			i_valid,
		output	reg			o_ready,
		input	wire	[DW-1:0]	i_data,
		output	reg			o_valid,
		input	wire			i_ready,
		output	reg	[DW-1:0]	o_data
		// }}}
	);

	reg	[DW-1:0]	r_data;

	generate if (OPT_PASSTHROUGH)
	begin : PASSTHROUGH
		// {{{
		always @(*)
			o_ready = i_ready;
		always @(*)
			o_valid = i_valid;
		always @(*)
		if (!i_valid && OPT_LOWPOWER)
			o_data = 0;
		else
			o_data = i_data;

		always @(*)
			r_data = 0;
		// }}}
	end else begin : LOGIC
		// We'll start with skid buffer itself
		// {{{
		reg			r_valid;

		// r_valid
		// {{{
		initial	r_valid = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_valid <= 0;
		else if ((i_valid && o_ready) && (o_valid && !i_ready))
			// We have incoming data, but the output is stalled
			r_valid <= 1;
		else if (i_ready)
			r_valid <= 0;
		// }}}

		// r_data
		// {{{
		initial	r_data = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && i_reset)
			r_data <= 0;
		else if (OPT_LOWPOWER && (!o_valid || i_ready))
			r_data <= 0;
		else if ((!OPT_LOWPOWER || !OPT_OUTREG || i_valid) && o_ready)
			r_data <= i_data;
		// }}}

		// o_ready
		// {{{
		always @(*)
			o_ready = !r_valid;
		// }}}

		//
		// And then move on to the output port
		//
		if (!OPT_OUTREG)
		begin : NET_OUTPUT
			// Outputs are combinatorially determined from inputs
			// {{{
			// o_valid
			// {{{
			always @(*)
				o_valid = !i_reset && (i_valid || r_valid);
			// }}}

			// o_data
			// {{{
			always @(*)
			if (r_valid)
				o_data = r_data;
			else if (!OPT_LOWPOWER || i_valid)
				o_data = i_data;
			else
				o_data = 0;
			// }}}
			// }}}
		end else begin : REG_OUTPUT
			// Register our outputs
			// {{{
			// o_valid
			// {{{
			initial	o_valid = 0;
			always @(posedge i_clk)
			if (i_reset)
				o_valid <= 0;
			else if (!o_valid || i_ready)
				o_valid <= (i_valid || r_valid);
			// }}}

			// o_data
			// {{{
			initial	o_data = 0;
			always @(posedge i_clk)
			if (OPT_LOWPOWER && i_reset)
				o_data <= 0;
			else if (!o_valid || i_ready)
			begin

				if (r_valid)
					o_data <= r_data;
				else if (!OPT_LOWPOWER || i_valid)
					o_data <= i_data;
				else
					o_data <= 0;
			end
			// }}}

			// }}}
		end
		// }}}
	end endgenerate

`ifdef	FORMAL
`ifdef	VERIFIC
`define	FORMAL_VERIFIC
`endif
`endif
//
`ifdef	FORMAL_VERIFIC
	// Reset properties
	property RESET_CLEARS_IVALID;
		@(posedge i_clk) i_reset |=> !i_valid;
	endproperty

	property IDATA_HELD_WHEN_NOT_READY;
		@(posedge i_clk) disable iff (i_reset)
		i_valid && !o_ready |=> i_valid && $stable(i_data);
	endproperty

`ifdef	SKIDBUFFER
	assume	property (IDATA_HELD_WHEN_NOT_READY);
`else
	assert	property (IDATA_HELD_WHEN_NOT_READY);
`endif

	generate if (!OPT_PASSTHROUGH)
	begin

		assert property (@(posedge i_clk)
			OPT_OUTREG && i_reset |=> o_ready && !o_valid);

		assert property (@(posedge i_clk)
			!OPT_OUTREG && i_reset |-> !o_valid);

		// Rule #1:
		//	Once o_valid goes high, the data cannot change until the
		//	clock after i_ready
		assert property (@(posedge i_clk)
			disable iff (i_reset)
			o_valid && !i_ready
			|=> (o_valid && $stable(o_data)));

		// Rule #2:
		//	All incoming data must either go directly to the
		//	output port, or into the skid buffer
		assert property (@(posedge i_clk)
			disable iff (i_reset)
			(i_valid && o_ready
				&& (!OPT_OUTREG || o_valid) && !i_ready)
				|=> (!o_ready && r_data == $past(i_data)));

		// Rule #3:
		//	After the last transaction, o_valid should become idle
		if (!OPT_OUTREG)
		begin

			assert property (@(posedge i_clk)
				disable iff (i_reset)
				i_ready |=> (o_valid == i_valid));

		end else begin

			assert property (@(posedge i_clk)
				disable iff (i_reset)
				i_valid && o_ready |=> o_valid);

			assert property (@(posedge i_clk)
				disable iff (i_reset)
				!i_valid && o_ready && i_ready |=> !o_valid);

		end

		// Rule #4
		//	Same thing, but this time for r_valid
		assert property (@(posedge i_clk)
			!o_ready && i_ready |=> o_ready);


		if (OPT_LOWPOWER)
		begin
			//
			// If OPT_LOWPOWER is set, o_data and r_data both need
			// to be zero any time !o_valid or !r_valid respectively
			assert property (@(posedge i_clk)
				(OPT_OUTREG || !i_reset) && !o_valid |-> o_data == 0);

			assert property (@(posedge i_clk)
				o_ready |-> r_data == 0);

			// else
			//	if OPT_LOWPOWER isn't set, we can lower our
			//	logic count by not forcing these values to zero.
		end

`ifdef	SKIDBUFFER
		reg	f_changed_data;

		// Cover test
		cover property (@(posedge i_clk)
			disable iff (i_reset)
			(!o_valid && !i_valid)
			##1 i_valid &&  i_ready [*3]
			##1 i_valid && !i_ready
			##1 i_valid &&  i_ready [*2]
			##1 i_valid && !i_ready [*2]
			##1 i_valid &&  i_ready [*3]
			// Wait for the design to clear
			##1 o_valid && i_ready [*0:5]
			##1 (!o_valid && !i_valid && f_changed_data));

		initial	f_changed_data = 0;
		always @(posedge i_clk)
		if (i_reset)
			f_changed_data <= 1;
		else if (i_valid && $past(!i_valid || o_ready))
		begin
			if (i_data != $past(i_data + 1))
				f_changed_data <= 0;
		end else if (!i_valid && i_data != 0)
			f_changed_data <= 0;

`endif	// SKIDCOVER
	end endgenerate

`endif	// FORMAL_VERIFIC
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
