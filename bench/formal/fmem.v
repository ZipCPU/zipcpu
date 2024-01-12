////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fmem.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To formalize the interface between the CPU and the memory unit.
//		Memory units that meet these criteria may interact with the
//	ZipCPU without error.
//
// Portlist:
//	i_clk	This is a synchronous interface
//	i_sys_reset	A global reset signal.  This resets the entire bus.
//	i_cpu_reset	Must be true during a global reset signal.  This
//			resets the CPU.  The bus may (or may not) be reset at
//			the same time.
//	i_stb		The CPU is making a request of the memory unit
//	i_pipe_stalled	The memory unit cannot accept the CPU's request
//	i_clear_cache	The CPU would like to clear any cached memory
//	i_lock		The CPU would like to initiate a locked sequence.
//			(This will be true from the first read operation,
//			through one ALU operation, to the strobe associated with
//			a following write operation.)
//	i_op		The type of memory operation requested
//		3'b000: (Illegal/Unused)
//		3'b001:	(Illegal/Unused)
//		3'b010:	Load   a 32'b word (i.e. a read)
//		3'b011:	Store  a 32'b word (i.e. a write)
//		3'b100:	Load   a 16'b word
//		3'b101:	Store  a 16'b word
//		3'b110:	Load  an 8'b word
//		3'b111:	Store an 8'b word
//	i_addr		The address to read from or write to.  Only valid when
//			i_stb is also true.
//	i_data		The data to be written during a store operation.
//	i_areg		The register to write the return data back to
//	i_busy		Whether the memory unit is busy doing something or not.
//			If the memory unit is busy, it may still accept
//			further reads (during a read cycle), or further writes
//			(during a write cycle) if i_pipe_stalled is clear.
//
//			Note that just because the memory unit is busy doesn't
//			mean it's busy doing anything relevant for the CPU.
//			The CPU may have issued a command, and then been reset.
//			In that case, the memory unit may still need to complete
//			the last command.
//	i_rdbusy	Not only is the memory unit busy, but it's busy in a
//			way where it might write data back to the CPU when it
//			is done.
//	i_valid		A read has completed, the data for that read is now
//			available in i_result, to be written to i_wreg
//	i_done		An operation has completed--either read or write
//	i_err		A bus error has occurred.  It may or may not be clear
//			which instruction caused it.  The CPU should begin any
//			exception handling.
//	i_wreg		If i_valid is true, this is the register that the
//			result needs to be written to.
//	i_result	The result of the last read
//
// Other ports are useful for synchronizing these formal properties to the
// CPU.  These include:
//
//	f_outstanding	A counter of how many requests are outstanding.  This
//			is incremented on every i_stb, and decremented on every
//			i_done.
//	f_pc		True if the last read will be written to either the
//			flags register or the program counter.
//	f_gie		True if the registers to be read are user mode
//			registers (i.e. the "Global Interrupt Enable" for the
//			ZipCPU is set), requested by the CPU within user mode,
//			or clear if they are supervisor registers (the Global
//			Interrupt Enable, or gie bit, is clear).  The memory
//			unit will only do one or the other, never both.
//	f_read_cycle	True if we are in a read cycle (i.e. a load), false
//			during any store operations.  The memory must cease
//			to be busy before switching directions.
//	f_axi_write_cycle
//			True if we are in an AXI exclusive access write cycle.
//			If this cycle fails, the write will return and require
//			a write to the program counter.
//	f_last_reg	The last read register.  Once data is returned to this
//			register, the current string or reads will be complete.
//	f_addr_reg	The base address register.  On any string of reads,
//			the CPU will guarantee that the loads are not stored
//			into the base address register unless it is the last
//			register in any sequence.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
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
		// OPT_LOCK
		// {{{
		// If false, forces the i_lock parameter to be zero and
		// guarantees no bus locking.  Can be set to 1'b1 to test both
		// with and without bus locking.
		// }}}
		parameter [0:0]	OPT_LOCK = 1'b0,
		// F_LGDEPTH
		// {{{
		// This is the number of bits required to hold our internal
		// counters.  It should have a sufficient number of bits to
		// hold the OPT_MAXDEPTH.
		// }}}
		parameter F_LGDEPTH = 4,
		// OPT_MAXDEPTH
		// {{{
		// OPT_MAXDEPTH is the maximum number of requests which may be
		// outstanding at any given time
		// }}}
		parameter [F_LGDEPTH-1:0]	OPT_MAXDEPTH = 1,
		// OPT_AXI_LOCK
		// {{{
		// AXI locks have special semantics.  When a lock takes place
		// with AXI semantics, there must be a locked read followed by
		// a locked write.  The locked write is treated as a read that
		// might write back to the program counter of the CPU, and so
		// rdbusy will be true during the locked write.  If you want to
		// check both the AXI and non-AXI lock semantics, feel free to
		// set this to one.
		parameter OPT_AXI_LOCK = 0
		// }}}
		// }}}
	) (
		// {{{
		//
		// See above comments for a description of these signals
		//
		input	wire			i_clk,
		input	wire			i_sys_reset,
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
		input	wire	[4:0]		i_areg, // Base address register
		//
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
		output	reg			f_axi_write_cycle,
		output	reg	[4:0]		f_last_reg,
		output	reg	[4:0]		f_addr_reg
		// , output	reg			f_endpipe,
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
	// Verilator lint_off UNDRIVEN
	(* anyconst *) reg f_check_axi_lock;
	// Verilator lint_on  UNDRIVEN

	initial	f_past_valid = 0;
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
		assume(i_sys_reset);

	always @(*)
	if (i_sys_reset)
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
	if (!f_past_valid || $past(i_sys_reset || i_cpu_reset))
		`CPU_ASSUME(!i_rdbusy);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_busy || i_stb))
		`CPU_ASSUME(!i_busy);

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

	// Stability while stalled
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && $past(i_stb && i_pipe_stalled && !i_cpu_reset))
	begin
		`CPU_ASSERT(i_stb);
		`CPU_ASSERT($stable(i_addr));
		`CPU_ASSERT($stable(i_data));
		`CPU_ASSERT($stable(i_oreg));
		// `CPU_ASSERT($stable(i_lock));
	end
	// }}}

	always @(*)
	if (!OPT_LOCK)
		`CPU_ASSERT(!i_stb || !i_lock);

	always @(posedge i_clk)
	if (OPT_LOCK && f_past_valid && !$past(i_cpu_reset))
	begin
	//	if ($past(!i_lock && (!i_stb || i_busy)))
	//		`CPU_ASSERT(!i_lock);
	end

	always @(*)
	if (!i_done)
	begin
		`CPU_ASSUME(!i_valid);
	end else if (i_rdbusy)
		`CPU_ASSUME(i_valid);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_rdbusy))
	begin
		`CPU_ASSUME(!i_valid);
	end else if (f_past_valid && $past(i_rdbusy) && f_axi_write_cycle)
	begin
		`CPU_ASSUME(f_outstanding == 1);
		if (i_valid)
		begin
			`CPU_ASSUME(i_wreg[3:0] == 4'hf && i_done);
		end else
			`CPU_ASSUME(i_rdbusy || i_done || i_err);
	end else if (f_past_valid && !i_err && $past(i_rdbusy)
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
			`CPU_ASSUME(i_err || i_rdbusy == past_rd || f_axi_write_cycle);
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
	if (i_clear_cache)
		`CPU_ASSERT(!i_stb);

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
	// f_addr_reg, f_last_reg, f_pc properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The last register
	// {{{
	// For pipeline hazard purposes, it's important to be able to know and
	// track the last register that will be returned to the CPU.
	always @(posedge i_clk)
	if (i_stb && !i_pipe_stalled)
	begin
		f_last_reg <= i_oreg;
		if (OPT_LOCK && f_check_axi_lock && i_op[0] && i_lock)
			f_last_reg[3:0] <= 4'hf;
	end

	always @(*)
	if (f_outstanding == 1 && i_valid && !f_axi_write_cycle)
		`CPU_ASSUME(f_last_reg == i_wreg);

	always @(*)
	if (f_axi_write_cycle)
	begin
		`CPU_ASSUME(f_last_reg[3:0] == 4'hf);
		assert(f_outstanding == 1);
	end
	// }}}

	//
	// The base address register
	// {{{
	// In any string of reads, the ZipCPU will only ever use a single
	// base address.  The ZipCPU will *not* read into the base address
	// register unless that read is the last in the string of reads.
	always @(posedge i_clk)
	if (i_stb)
		f_addr_reg <= i_areg;

	always @(*)
	if (i_stb && i_rdbusy)
		`CPU_ASSERT(i_areg == f_addr_reg);

	always @(*)
	if (i_rdbusy)
		`CPU_ASSERT(!i_stb || f_last_reg != i_areg);

	always @(*)
	if (i_rdbusy && i_valid)
	begin
		if (f_outstanding > 1)
			`CPU_ASSUME(i_wreg != f_addr_reg);
	end
	// }}}

	// f_pc
	// {{{
	// True if any register will return a write to either the program
	// counter or the CC register.  If such a read exists, it must be the
	// last in a sequence.
	initial	f_pc = 0;
	always @(posedge i_clk)
	if (i_cpu_reset || i_err)
		f_pc <= 0;
	else if (i_stb && !i_op[0] && i_oreg[3:1] == 3'h7)
		f_pc <= 1'b1;
	else if (f_check_axi_lock && i_stb && i_op[0] && i_lock)
		f_pc <= 1'b1;
	else if (i_valid && i_wreg[3:1] == 3'h7)
		f_pc <= 1'b0;
	else if (f_axi_write_cycle && i_done)
		f_pc <= 1'b0;

	//
	// Once the CPU issues a request to read into one of the special
	// registers (either CC, or PC), it will not issue another read request
	// until this request has completed.
	always @(*)
	if (f_pc && f_read_cycle)
		`CPU_ASSERT(!i_stb);

	always @(*)
	if (f_pc && !f_read_cycle && f_axi_write_cycle
			&& f_outstanding > ((i_done || i_err) ? 1:0))
		`CPU_ASSUME(i_pipe_stalled);

	always @(*)
	if (f_last_reg[3:1] != 3'h7)
	begin
		assert(!f_pc || f_axi_write_cycle);
	end else if (i_rdbusy)
		assert(f_pc);

	always @(*)
	if (f_pc)
	begin
		`CPU_ASSUME(f_read_cycle || f_axi_write_cycle);
		if (f_axi_write_cycle)
		begin
			assert(f_check_axi_lock);
			`CPU_ASSUME(f_outstanding == 1);
		end else begin
			if (f_outstanding > 1 && !i_err)
			begin
				`CPU_ASSUME(!i_valid || i_wreg[3:1] != 3'h7);
			end else if (f_outstanding == 1 && i_valid)
				`CPU_ASSUME(i_wreg[3:1] == 3'h7);
			`CPU_ASSUME(f_outstanding > 0);
		end
	end else if (i_valid)
		`CPU_ASSUME(!i_valid || i_wreg[3:1] != 3'h7);
	// }}}
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
	// f_axi_write_cycle properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (OPT_AXI_LOCK == 0 || !OPT_LOCK)
	begin
		assume(f_check_axi_lock == 1'b0);
	end else if (OPT_AXI_LOCK == 1)
		assume(f_check_axi_lock == 1'b1);

	initial	f_axi_write_cycle = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || i_clear_cache || !f_check_axi_lock)
		f_axi_write_cycle <= 1'b0;
	else if (i_stb && i_lock && i_op[0])
		f_axi_write_cycle <= 1'b1;
	else if (i_err || i_valid || !i_rdbusy)
		f_axi_write_cycle <= 1'b0;

	always @(*)
	if (!f_check_axi_lock)
		assert(f_axi_write_cycle == 0);

	always @(*)
	if (f_axi_write_cycle)
		`CPU_ASSUME(i_rdbusy || i_valid || i_err || i_done);

	always @(*)
	if (f_axi_write_cycle)
		assert(f_pc);

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
		if (!f_axi_write_cycle)
		begin
			`CPU_ASSUME(!i_rdbusy);
			`CPU_ASSUME(!i_valid);
		end
	end else if (i_done)
	begin
		`CPU_ASSUME(i_valid || i_err);
		if (!i_err)
		`CPU_ASSUME((f_outstanding <= (i_valid ? 1:0)) || i_rdbusy);
	end

	always @(*)
		`CPU_ASSUME(!f_read_cycle || !f_axi_write_cycle);
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

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_result };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
