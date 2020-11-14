////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fmem.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
// }}}
module	fmem #(
		// {{{
		parameter [0:0]	IMPLEMENT_LOCK = 1'b0,
		parameter F_LGDEPTH = 4,
		parameter OPT_MAXDEPTH = 1
		// }}}
	) (
		// {{{
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
		// input	wire	[4:0]		i_areg,
		input	wire			i_busy,
		input	wire			i_rdbusy,
		input	wire			i_valid,
		input	wire			i_done,
		input	wire			i_err,
		input	wire	[4:0]		i_wreg,
		input	wire	[31:0]		i_result,
		//
		output	reg [F_LGDEPTH-1:0]	f_outstanding,
		output	reg			f_pc,
		output	reg			f_gie,
		output	reg			f_read_cycle,
		output	reg	[4:0]		f_last_reg
		// , output	reg			f_endpipe,
		// output	reg	[4:0]		f_addr_reg,
		// }}}
	);

	// Declarations and setup
	// {{{
`ifdef	ZIPCPU
`define	CPU_ASSUME	assume
`define	CPU_ASSERT	assert
`else
`define	CPU_ASSUME	assert
`define	CPU_ASSERT	assume
`endif

	reg	f_past_valid;
	reg	past_stb, past_rd, past_busy;

	initial	f_past_valid <= 0;
	always @(posedge i_clk)
		f_past_valid <= 1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset checks
	// {{{
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

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	always @(*)
	if (!f_past_valid || !i_busy)
		`CPU_ASSUME(!i_rdbusy);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_bus_reset || i_cpu_reset))
		`CPU_ASSUME(!i_rdbusy);

	always @(*)
		`CPU_ASSUME(!i_valid || !i_err);

	initial	f_outstanding = 0;
	always @(posedge i_clk)
	if (i_cpu_reset || i_err)
		f_outstanding <= 0;
	else casez({ i_stb, i_done })
	2'b10: f_outstanding <= f_outstanding + 1;
	2'b01: f_outstanding <= f_outstanding - 1;
	default: begin end
	endcase

	always @(*)
	if (f_outstanding == 0)
		`CPU_ASSUME(!i_done && !i_err);

	always @(*)
		assert(f_outstanding <= OPT_MAXDEPTH);

	always @(*)
	if (f_outstanding == OPT_MAXDEPTH + ((i_done || i_err) ? 1:0))
		`CPU_ASSUME(i_pipe_stalled);

	always @(*)
	if (!i_err && f_outstanding > ((i_done || i_err) ? 1:0))
		`CPU_ASSUME(i_busy);

	// The CPU is not allowed to write to the CC register while a memory
	// read operation is ongoing, lest any resulting bus error get returned
	// to the wrong mode--i.e. user bus error halting the supervisor.  What
	// this means, though, is that the CPU will *never* attempt to clear
	// any cache while the cache is busy.
	always @(*)
	if (!i_cpu_reset && f_outstanding > 0 && i_rdbusy)
		`CPU_ASSERT(!i_clear_cache);

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
	else if (i_rdbusy)
		`CPU_ASSUME(i_valid);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_rdbusy))
		`CPU_ASSUME(!i_valid);
	else if (f_past_valid && !i_err && $past(i_rdbusy)
			&& (f_outstanding > (i_valid ? 1:0)))
		`CPU_ASSUME(i_rdbusy);

	initial	past_stb = 1'b0;
	always @(posedge i_clk)
		past_stb <= i_stb && !i_cpu_reset && !i_err;

	initial	past_rd = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || i_err)
		past_rd <= 1'b0;
	else if (i_stb && !i_op[0])
		past_rd <= 1'b1;
	else
		past_rd <= i_rdbusy && (f_outstanding > (i_valid ? 1:0));

	// Can only become busy on a CPU reset or a bus request
	initial	past_busy = 1'b1;
	always @(posedge i_clk)
	if (i_cpu_reset || i_stb)
		past_busy <= 1'b1;
	else if (!i_busy)
		past_busy <= 1'b0;

	always @(*)
	if (!past_busy)
		`CPU_ASSUME(!i_busy);

	always @(*)
		`CPU_ASSUME(!i_rdbusy || !i_err);

	always @(*)
	if (past_stb)
	begin
		`CPU_ASSUME(i_busy || i_valid || i_err);

		if (i_busy)
			`CPU_ASSUME(i_err || i_rdbusy == past_rd);
	end else if (!past_rd || !i_busy)
		`CPU_ASSUME(!i_rdbusy);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_cpu_reset))
	begin
		//
		// Will never happen, 'cause i_stb can't be true when i_busy
		//
		if ($past(i_stb && i_pipe_stalled) && i_stb)
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
	if (!i_cpu_reset && i_busy && f_outstanding > 0)
		`CPU_ASSERT(!i_clear_cache);

	always @(*)
	if (i_pipe_stalled)
		`CPU_ASSERT(!i_stb);

	always @(*)
	if (!i_busy)
		`CPU_ASSUME(!i_pipe_stalled);

	// Reads must always complete before writes, and vice versa
	always @(*)
	if (i_stb && i_busy)
		`CPU_ASSERT(f_read_cycle == !i_op[0]);

	// always @(posedge i_clk)
	// if (f_past_valid && $past(i_busy && !i_pipe_stalled && !i_stb))
	//	`CPU_ASSERT(!i_stb || i_lock);

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
	// f_last_reg, f_pc properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	f_pc = 0;
	always @(posedge i_clk)
	if (i_stb && !i_pipe_stalled)
		f_last_reg <= i_oreg;

	always @(*)
	if (f_outstanding == 1 && i_valid)
		`CPU_ASSUME(f_last_reg == i_wreg);

	initial	f_pc = 0;
	always @(posedge i_clk)
	if (i_cpu_reset || i_err)
		f_pc <= 0;
	else if (i_stb && !i_op[0] && i_oreg[3:1] == 3'h7)
		f_pc <= 1'b1;
	else if (i_valid && i_wreg[3:1] == 3'h7)
		f_pc <= 1'b0;

	//
	// Once the CPU issues a request to read into one of the special
	// registers (either CC, or PC), it will not issue another read request
	// until this request has completed.
	always @(*)
	if (f_pc)
		`CPU_ASSERT(!i_stb);

	always @(*)
	if (f_last_reg[3:1] != 3'h7)
		assert(!f_pc);
	else if (i_rdbusy)
		assert(f_pc);

	always @(*)
	if (f_pc)
	begin
		`CPU_ASSUME(f_read_cycle);
		if (f_outstanding > 1 && !i_err)
			`CPU_ASSUME(!i_valid || i_wreg[3:1] != 3'h7);
		else if (f_outstanding == 1 && i_valid)
			`CPU_ASSUME(i_wreg[3:1] == 3'h7);
		`CPU_ASSUME(f_outstanding > 0);
	end else if (i_valid)
		`CPU_ASSUME(!i_valid || i_wreg[3:1] != 3'h7);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// f_gie properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (i_stb)
		f_gie <= i_oreg[4];

	always @(*)
	if (i_stb && f_outstanding > 0)
		`CPU_ASSERT(f_gie == i_oreg[4]);

	always @(*)
	if (i_valid)
		`CPU_ASSUME(f_gie == i_wreg[4]);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// f_read_cycle properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	f_read_cycle = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || i_clear_cache)
		f_read_cycle <= 1'b0;
	else if (i_stb)
		f_read_cycle <= !i_op[0];
	else if (!i_busy)
		f_read_cycle <= 1'b0;

	always @(*)
	if (!f_read_cycle)
	begin
		`CPU_ASSERT(!i_rdbusy);
		`CPU_ASSERT(!i_valid);
	end else if (i_done)
	begin
		`CPU_ASSUME(i_valid || i_err);
		if (!i_err)
		`CPU_ASSUME((f_outstanding <= (i_valid ? 1:0)) || i_rdbusy);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Address register checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Here's the (to be written) rule: During a string of operations,
	// there is one address register.
/*
	always @(posedge i_clk)
	if (i_reset)
		f_endpipe <= 1'b1;
	else if (i_stb)
		f_endpipe <= i_op[0] || (i_oreg == i_areg);

	always @(posedge i_clk)
	if (i_stb)
		f_addr_reg <= i_areg;

	//
	// Mid cycle, the CPU can't add a new register to the end
	always @(*)
	if (f_read_cycle && (i_valid || f_outstanding > 0) && i_stb && !i_op[0])
	begin
		`CPU_ASSERT(!f_endpipe);
		`CPU_ASSERT(i_oreg != f_addr_reg);
	end


	//
	// Only the last item can write to the address register, and that only
	// if f_endpipe is true.
	always @(*)
	if (f_read_cycle && !i_err && i_valid)
	begin
		// If we aren't ever writing to the address register
		// ... or if we are, the address register must be the last
		// register to be returned, then don't allow a write response
		// to the address register
		if (!f_endpipe || f_outstanding > (i_valid ? 1:0))
			`CPU_ASSUME(!i_valid || i_wreg != f_addr_reg);
	end
*/
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
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
	// }}}
endmodule
