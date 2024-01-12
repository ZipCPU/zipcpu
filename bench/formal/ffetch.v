////////////////////////////////////////////////////////////////////////////////
//
// Filename:	ffetch.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A set of memory properties, with the goal that if any memory
//		can meet these properties, then the ZipCPU should be able to
//	interact with that memory properly.
//
//	This particular property set regards the instruction fetch.
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
//
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
module	ffetch #(
		// {{{
		// Address width -- from the CPU's perspective, not the bus'es
		parameter	ADDRESS_WIDTH = 30,
		parameter [0:0]	OPT_ALIGNED  = 1'b0,
		parameter [0:0]	OPT_CONTRACT = 1'b1,
		parameter   INSN_WIDTH = 32, // Number of bits in an instruction
		parameter [0:0]	F_OPT_ASYNC_RESET = 1'b0,
		localparam	AW=ADDRESS_WIDTH, // Shorthand for ADDRESS_WIDTH
		localparam	BW=AW + $clog2(INSN_WIDTH/8)	// Byte addr wid
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		// The interface with the rest of the CPU
		input	wire			cpu_new_pc,
		input	wire			cpu_clear_cache,
		input	wire	[BW-1:0]	cpu_pc,
		input	wire			pf_valid,
		input	wire			cpu_ready,
		input	wire	[BW-1:0]	pf_pc,
		input	wire	[(INSN_WIDTH-1):0]	pf_insn,
		//
		// o_illegal will be true if this instruction was the result of
		// a bus error (This is also part of the CPU interface)
		input	wire			pf_illegal,
		//
		output	wire	[BW-1:0]	fc_pc,
		output	wire			fc_illegal,
		output	wire	[INSN_WIDTH-1:0]	fc_insn,
		output	reg	[BW-1:0]	f_address
		// }}}
	);

	// Declarations
	// {{{
`ifdef	ZIPCPU
`define	CPU_ASSUME	assume
`define	CPU_ASSERT	assert
`else
`define	CPU_ASSUME	assert
`define	CPU_ASSERT	assume
`endif
	localparam	INSN_LSB = $clog2(INSN_WIDTH/8);
	reg	[BW-1:0]	f_next_address;
	reg		f_past_valid;

	reg		need_new_pc, past_stalled, past_illegal;
	reg	[INSN_WIDTH-1:0]	past_insn;

	// Verilator lint_off UNDRIVEN
	(* anyconst *)	reg	[BW-1:0]	r_fc_pc;
	(* anyconst *)	reg			r_fc_illegal;
	(* anyconst *)	reg	[INSN_WIDTH-1:0]	r_fc_insn;
	// Verilator lint_on  UNDRIVEN

	assign	fc_pc		= r_fc_pc;
	assign	fc_illegal	= r_fc_illegal;
	assign	fc_insn		= r_fc_insn;
	// }}}

	// f_address, f_next_address -- address tracking
	// {{{
	always @(posedge i_clk)
	if (cpu_new_pc)
		f_address <= cpu_pc;
	else if (pf_valid && cpu_ready)
	begin
		f_address[BW-1:INSN_LSB] <= f_address[BW-1:INSN_LSB] + 1'b1;
		if (INSN_LSB > 0)
			f_address[INSN_LSB-1:0] <= 0;
	end

	always @(*)
	begin
		f_next_address = f_address + (1<<INSN_LSB);
		if (INSN_LSB > 0)
			f_next_address[INSN_LSB-1:0] <= 0;
	end
	// }}}

	// f_past_valid
	// {{{
	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	//
	// Assume we start from a reset condition
	initial	`CPU_ASSERT(i_reset);

	always @(*)
	if (!f_past_valid)
		`CPU_ASSERT(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our return responses to the CPU
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// pf_pc, and cpu_pc alignment
	// {{{
	generate if (OPT_ALIGNED && INSN_LSB > 0)
	begin

		always @(*)
		if (cpu_new_pc)
			`CPU_ASSERT(cpu_pc[INSN_LSB-1:0] == 0);

		always @(*)
		if (pf_valid)
			`CPU_ASSUME(pf_pc[INSN_LSB-1:0] == 0);

	end endgenerate
	// }}}

	// Some things to know from the CPU ... there will always be a
	// i_new_pc request following any reset or clear cache request
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		`CPU_ASSUME(!pf_valid);
		`CPU_ASSUME(!pf_illegal);
	end

	initial	need_new_pc = 1'b1;
	always @(posedge i_clk)
		need_new_pc <= (i_reset || cpu_clear_cache);

	initial	past_stalled = 1'b1;
	always @(posedge i_clk)
		past_stalled <= pf_valid && !cpu_ready && !cpu_new_pc;

	initial	past_illegal = 1'b0;
	always @(posedge i_clk)
		past_illegal <= pf_illegal;

	always @(posedge i_clk)
		past_insn <= pf_insn;

	always @(*)
	if (!F_OPT_ASYNC_RESET || !i_reset)
	begin
		if (need_new_pc)
		begin
			`CPU_ASSERT(i_reset || cpu_clear_cache || cpu_new_pc);
			`CPU_ASSUME(!pf_valid);
			`CPU_ASSUME(!pf_illegal);
		end else if (past_stalled)
		begin
			`CPU_ASSUME(past_illegal == pf_illegal);
			`CPU_ASSUME(pf_illegal || (past_insn == pf_insn));
			if (!cpu_new_pc)
				`CPU_ASSERT(cpu_pc[BW-1:INSN_LSB]== f_next_address[BW-1:INSN_LSB]);
		end else if (!cpu_new_pc && !i_reset && !cpu_clear_cache)
		begin
			`CPU_ASSERT(cpu_pc[BW-1:INSN_LSB]== f_next_address[BW-1:INSN_LSB]);
		end
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset || cpu_clear_cache)
			|| (F_OPT_ASYNC_RESET && i_reset))
	begin
		if (!F_OPT_ASYNC_RESET || !i_reset)
		begin
			assert(need_new_pc);
			`CPU_ASSERT(cpu_new_pc || i_reset || cpu_clear_cache);
			`CPU_ASSUME(!pf_valid);
			`CPU_ASSUME(!pf_illegal);
		end
	end else if (!$past(cpu_new_pc) && $past(pf_valid && !cpu_ready))
	begin
		//
		// Once an instruction has been presented, it must hold valid
		// until accepted
		assert(!need_new_pc);
		`CPU_ASSUME(pf_valid);
		`CPU_ASSUME($stable(pf_pc));
		`CPU_ASSUME(pf_illegal || $stable(pf_insn));
		`CPU_ASSUME($stable(pf_illegal));
	end else if ($past(pf_illegal && !cpu_new_pc))
		// Once illegal is raised, it stays raised until a new PC,
		// reset, or cache clear
		`CPU_ASSUME(pf_illegal);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset || cpu_clear_cache))
	begin
		`CPU_ASSUME(!pf_valid);
	end else if ((f_past_valid)&&(!$past(pf_illegal && !cpu_new_pc))&&(pf_illegal))
		// pf_illegal can only rise if pf_valid is true
		`CPU_ASSUME(pf_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset || cpu_new_pc || cpu_clear_cache)))
	begin
		`CPU_ASSUME(!pf_illegal || pf_valid);
	end else if (f_past_valid && $past(pf_illegal))
		`CPU_ASSUME(pf_illegal);

	always @(*)
	if (pf_valid && !pf_illegal)
		`CPU_ASSUME(f_address == pf_pc);

	always @(posedge i_clk)
	if (f_past_valid && !i_reset && !cpu_new_pc && !need_new_pc)
		`CPU_ASSERT(f_next_address == cpu_pc);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		assume(fc_pc[1:0] == 2'b00);

	generate if (OPT_CONTRACT)
	begin : CHECK_CONTRACT
		always @(*)
		if (pf_valid && fc_pc[BW-1:INSN_LSB] == f_address[BW-1:INSN_LSB])
		begin
			if (fc_illegal)
			begin
				`CPU_ASSUME(pf_illegal);
			end else if (!pf_illegal)
				`CPU_ASSUME(fc_insn == pf_insn);
		end

		always @(posedge i_clk)
		if (f_past_valid && !$past(pf_illegal) && pf_valid
				&& fc_pc[BW-1:INSN_LSB] == f_address[BW-1:INSN_LSB])
			`CPU_ASSUME(fc_illegal == pf_illegal);

	end endgenerate
	// }}}
endmodule
