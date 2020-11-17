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
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	fdebug #(
		parameter [0:0]	OPT_DISTRIBUTED_RAM = 1'b0
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

	// Stall checking
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && $past(i_dbg_we && i_dbg_stall))
	begin
		`CPU_ASSUME(i_dbg_we);
		`CPU_ASSUME($stable(i_dbg_reg));
		`CPU_ASSUME($stable(i_dbg_data));
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(i_clear_cache && i_dbg_stall))
		`CPU_ASSUME(i_clear_cache);
	// }}}

	// Writes will only ever be attempted if/when the CPU is halted
	// {{{
	always @(*)
	if (i_dbg_we)
		`CPU_ASSUME(i_halt);

	always @(posedge i_clk)
	if (f_past_valid && $past(i_dbg_we))
		`CPU_ASSUME(i_halt);

	generate if (OPT_DISTRIBUTED_RAM)
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
	always @(posedge i_clk)
	if (!i_halt)
		`CPU_ASSUME(!i_clear_cache);

	always @(posedge i_clk)
	if (f_past_valid && $past(i_clear_cache))
		`CPU_ASSUME(i_halt);
	// }}}
	// }}}

	// Writes to the program counter will always be aligned
	// always @(posedge i_clk)
	// if (i_dbg_we && i_dbg_reg[3:0] == 4'hf)
	//	`CPU_ASSUME(i_dbg_data[1:0] == 2'b00);

	// The CPU will always come to a halt on a break
	always @(posedge i_clk)
	if (f_past_valid && $past(i_dbg_break))
		`CPU_ASSUME(i_halt);
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
	if (f_past_valid && $past(i_halt && i_halted))
		`CPU_ASSERT(i_halted);
	// }}}

	// Once requested, the halt request will remain activve until the CPU
	// comes to a complete halt
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && $past(i_halt && !i_halted))
		`CPU_ASSUME(i_halt);
	// }}}

	// }}}
endmodule
