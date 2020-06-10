////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fmem.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
`default_nettype none
//
module	fmem #(
		parameter [0:0]	IMPLEMENT_LOCK = 1'b0,
		parameter F_LGDEPTH = 4,
		parameter OPT_MAXDEPTH = 1
	) (
		input	wire			i_clk,
		input	wire			i_bus_reset,
		input	wire			i_cpu_reset,
		//
		// CPU interface
		input	wire			i_stb,
		input	wire			i_pipe_stalled,
		input	wire			i_clear_cache,
		input	wire			i_lock,
		input	wire	[2:0]		i_op,
		input	wire	[31:0]		i_addr,
		input	wire	[31:0]		i_data,
		input	wire	[4:0]		i_oreg,
		input	reg			i_busy,
		input	reg			i_rdbusy,
		input	reg			i_valid,
		input	reg			i_done,
		input	reg			i_err,
		input	reg	[4:0]		i_wreg,
		input	reg	[31:0]		i_result,
		//
		output	reg [F_LGDEPTH-1:0]	f_outstanding
	);

`ifdef	ZIPCPU
`define	CPU_ASSUME	assume
`define	CPU_ASSERT	assert
`else
`define	CPU_ASSUME	assert
`define	CPU_ASSERT	assume
`endif

	reg	f_past_valid;
	initial	f_past_valid <= 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Reset checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(i_bus_reset);

	always @(*)
	if (i_bus_reset)
		assume(i_cpu_reset);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_cpu_reset))
	begin
		`CPU_ASSUME(!i_valid);
		`CPU_ASSUME(!i_done);
		`CPU_ASSUME(!i_err);
	end

	//
	////////////////////////////////////////////////////////////////////////
	//
	always @(*)
	if (!i_busy)
		`CPU_ASSUME(!i_rdbusy);

	always @(*)
		`CPU_ASSUME(!i_valid || !i_err);

	initial	f_outstanding = 0;
	always @(posedge i_clk)
	if (i_cpu_reset)
		f_outstanding <= 0;
	else casez({ i_stb, i_done, i_err })
	3'b100: f_outstanding <= f_outstanding + 1;
	3'b010: f_outstanding <= f_outstanding - 1;
	3'b??1: f_outstanding <= 0;
	default: begin end
	endcase

	always @(*)
		assert(f_outstanding <= OPT_MAXDEPTH);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_cpu_reset))
	begin
		`CPU_ASSERT(!i_stb);
	
		// If we reset the CPU but not the bus, the bus might still
		// be busy for a while.  Same as if we are using AXI and we
		// get an error--we still have to flush the rest of what's
		// on the bus.  It's just that ... the CPU doesn't need to wait,
		// same as if it were writing something to the bus.
		//
		`CPU_ASSUME(!i_rdbusy);

		`CPU_ASSUME(!i_valid);
		`CPU_ASSUME(!i_err);
	end else if ($past(i_err))
	begin
		`CPU_ASSERT(!i_stb);
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(i_stb && i_pipe_stalled && !i_cpu_reset))
	begin
		`CPU_ASSERT(i_stb);
		`CPU_ASSERT($stable(i_addr));
		`CPU_ASSERT($stable(i_data));
		`CPU_ASSERT($stable(i_oreg));
		`CPU_ASSERT($stable(i_lock));
	end

	always @(*)
	if (!IMPLEMENT_LOCK)
		`CPU_ASSERT(!i_stb || !i_lock);

	always @(posedge i_clk)
	if (IMPLEMENT_LOCK && f_past_valid && !$past(i_cpu_reset))
	begin
		if ($past(!i_lock && (!i_stb || i_busy)))
			`CPU_ASSERT(!i_lock);
	end

	always @(*)
	if (!i_done)
		`CPU_ASSUME(!i_valid);

//	always @(*)
//	if (i_done)
//		`CPU_ASSUME(!i_busy);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_rdbusy))
		`CPU_ASSUME(!i_valid);
		
	always @(posedge i_clk)
	if (f_past_valid && $past(i_stb && !i_cpu_reset && !i_err))
	begin
		`CPU_ASSUME(i_busy || i_valid || i_err);

		if (i_busy)
			`CPU_ASSUME(i_rdbusy == $past(!i_op[0]));
	end
		
	always @(posedge i_clk)
	if (f_past_valid && !$past(i_cpu_reset))
	begin
		//
		// Will never happen, 'cause i_stb can't be true when i_busy
		//
		if ($past(i_stb && i_busy) && i_stb)
		begin
			`CPU_ASSERT($stable(i_op));
			`CPU_ASSERT($stable(i_addr));
			`CPU_ASSERT($stable(i_data));
			`CPU_ASSERT($stable(i_oreg));
			`CPU_ASSERT($stable(i_lock));
		end
	end

	always @(*)
	if (i_stb)
		`CPU_ASSERT(i_op[2:1] != 2'b00);

	//
	// This is guaranteed by the CPU: No new requests during busy.  It
	// isn't necessarily required by most handshaking interfaces, but the
	// CPU needs it in order to make certain that it doesn't accidentally
	// issue instructions.  It's part of the CPU pipeline logic.
	always @(*)
	if (i_pipe_stalled)
		`CPU_ASSERT(!i_stb);

	always @(*)
	if (i_stb && i_busy)
		`CPU_ASSERT(i_rdbusy == !i_op[0]);

	always @(posedge i_clk)
	if (f_past_valid && $past(i_busy && !i_pipe_stalled && !i_stb))
		`CPU_ASSERT(!i_stb || i_lock);

	//
	// This is also required of the CPU pipeline logic.  Following any
	// error the pipeline needs to be cleared.  That means that, on an
	// error, you can't have any new requests
	always @(*)
	if (i_err)
		`CPU_ASSERT(!i_stb);

	always @(posedge i_clk)
	if (f_past_valid && $past(i_cpu_reset || i_err))
		`CPU_ASSERT(!i_stb);

	always @(*)
	if (i_rdbusy)
		`CPU_ASSERT(!i_stb || !i_op[0]);

	always @(*)
	if (i_rdbusy)
		`CPU_ASSUME(i_busy);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[3:0]	cvr_returns, cvr_errors;

	initial	cvr_returns = 0;
	always @(posedge i_clk)
	if (i_cpu_reset)
		cvr_returns <= 0;
	else if (i_valid && !cvr_returns[3])
		cvr_returns <= cvr_returns + 1;

	always @(*)
		cover(cvr_returns > 4);

	initial	cvr_errors = 0;
	always @(posedge i_clk)
	if (i_cpu_reset)
		cvr_errors <= 0;
	else if (i_err && !cvr_errors[3])
		cvr_errors <= cvr_errors + 1;

	always @(*)
		cover(cvr_returns > 2);
endmodule
