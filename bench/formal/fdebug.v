////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fdebug.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Formal properties describing the debugging interface of the
//		ZipCPU core.  This is the interface implemented by the
//	ZipSystem, ZipBones, or any other wrapper to the ZipCPU core.  It
//	controls reset, the halt bit, external stepping control, external
//	cache clearing, and any register override bits.
//
// Ports:
//	i_clk
//	i_reset	Positive, synchronous, reset everything
//	i_cpu_reset	The CPU is being reset and only the CPU--not the bus.
//	i_halt		A request is being made to halt the CPU
//	i_halted	Signal from the CPU that it has come to a complete halt
//	i_clear_cache	Request to clear the CPU's cache.  Can only be issued
//			with i_halt true, must hold true once set until
//			i_halted.
//	i_dbg_we	A request to write to a CPU register.  i_halt must
//			also be true.  The request must remain valid until
//			!i_dbg_stall is also true.
//	i_dbg_reg	The register to be written.  Registers 0-15 are in the
//			supervisor set, 16-31 in the user set.  Registers
//			15 and 31 are program counters, 14 and 30 are flags,
//			13 and 29 are (by convention) stack pointers.
//	i_dbg_data	The data to be written to i_dbg_reg when i_dbg_we is
//			set.  Note that there's no byte enables, strobes, or
//			any other mechanism for less than 32-bit writes.  All
//			writes are 32-bits.
//	i_dbg_stall	The CPU is not able to handle a write request at this
//			time.
//	i_dbg_break	The CPU has suffered from a break condition and cannot
//			continue operating.
//	i_dbg_cc	CPU conditions:
//		i_bus_err:	The supervisor has suffered from a bus error
//		gie:		CPU is in user mode
//		sleep:		CPU is asleep (if in user mode), or halted
//				if in supervisor mode (gie is clear)
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	fdebug #(
		// {{{
		// Some FPGA's have no distributed RAM, and so require an extra
		// clock cycle to access CPU register data.  In such cases, CPU
		// reads require an extra clock cycle:
		//	1. Address valid, 2. (wait state), 3. Data available
		// Set OPT_DISTRIBUTED_RAM to 1'b0 if such a wait state is
		// required.
		parameter [0:0]	OPT_DISTRIBUTED_RAM = 1'b1,
		parameter [0:0]	OPT_START_HALTED = 1'b1
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		input	wire		i_reset,
		input	wire		i_cpu_reset,
		input	wire		i_halt,
		input	wire		i_halted,
		input	wire		i_clear_cache,
		//
		input	wire		i_dbg_we,
		input	wire	[4:0]	i_dbg_reg,
		input	wire	[31:0]	i_dbg_data,
		//
		input	wire		i_dbg_stall,
		input	wire		i_dbg_break,
		input	wire	[2:0]	i_dbg_cc
		// }}}
	);

`ifdef	ZIPCPU
`define	CPU_ASSUME	assume
`define	CPU_ASSERT	assert
`else
`define	CPU_ASSUME	assert
`define	CPU_ASSERT	assume
`endif

	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset && !i_cpu_reset))
		`CPU_ASSUME(i_cpu_reset);

	// Stall checking
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && !i_cpu_reset && i_dbg_we && i_dbg_stall))
	begin
		`CPU_ASSUME(i_dbg_we);
		`CPU_ASSUME($stable(i_dbg_reg));
		`CPU_ASSUME($stable(i_dbg_data));
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && !i_cpu_reset
					&& i_clear_cache && i_dbg_stall))
		`CPU_ASSUME(i_clear_cache);
	// }}}

	// Writes will only ever be attempted if/when the CPU is halted
	// {{{
	always @(*)
	if (i_dbg_we)
		`CPU_ASSUME(i_halt);

	always @(posedge i_clk)
	if (f_past_valid && (!i_reset && !i_cpu_reset)
			&& $past(!i_reset && !i_cpu_reset) && $past(i_dbg_we))
		`CPU_ASSUME(i_halt);

	generate if (!OPT_DISTRIBUTED_RAM)
	begin
		always @(posedge i_clk)
		if (f_past_valid && $past(f_past_valid) && $past(i_dbg_we,2))
			`CPU_ASSUME(i_halt);

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clear cache checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The clear cache signal will only ever be applied if/when the
	// CPU is halted
	// {{{
	always @(*)
	if (!i_halt && !i_reset && !i_cpu_reset)
		`CPU_ASSUME(!i_clear_cache);

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && !i_cpu_reset && i_clear_cache))
		`CPU_ASSUME(i_halt);
	// }}}
	// }}}

	// Writes to the program counter will always be aligned
	// always @(posedge i_clk)
	// if (i_dbg_we && i_dbg_reg[3:0] == 4'hf)
	//	`CPU_ASSUME(i_dbg_data[1:0] == 2'b00);

	// The CPU will always come to a halt on a break
	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && !i_cpu_reset && i_dbg_break))
		`CPU_ASSUME(i_halt || i_reset || i_cpu_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Complete halt assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// If the CPU isn't halted, stall will be asserted
	// {{{
	always @(*)
	if (!i_halted)
		`CPU_ASSERT(i_dbg_stall);
	// }}}

	// A halted CPU won't restart without being released
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		`CPU_ASSERT(i_halted == OPT_START_HALTED);
	end else if (f_past_valid && $past(i_halt && i_halted))
		`CPU_ASSERT(i_halted);
	// }}}

	// Once requested, the halt request will remain active until the CPU
	// comes to a complete halt
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && !i_cpu_reset && i_halt && !i_halted))
		`CPU_ASSUME(i_halt);
	// }}}

	// }}}
endmodule
