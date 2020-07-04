////////////////////////////////////////////////////////////////////////////////
//
// Filename:	ffetch.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
module	ffetch(i_clk, i_reset, cpu_new_pc, cpu_clear_cache, cpu_pc,
			pf_valid, cpu_ready, pf_pc, pf_insn, pf_illegal,
			fc_pc, fc_illegal, fc_insn, f_address);
	parameter	ADDRESS_WIDTH = 30;
	parameter [0:0]	OPT_ALIGNED  = 1'b0;
	parameter [0:0]	OPT_CONTRACT = 1'b1;
	localparam	BUSW = 32;	// Number of data lines on the bus
	localparam	AW=ADDRESS_WIDTH; // Shorthand for ADDRESS_WIDTH
	//
	input	wire			i_clk, i_reset;
	//
	// The interface with the rest of the CPU
	input	wire			cpu_new_pc;
	input	wire			cpu_clear_cache;
	input	wire	[(AW+1):0]	cpu_pc;
	input	wire			pf_valid;
	input	wire			cpu_ready;
	input	wire	[(AW+1):0]	pf_pc;
	input	wire	[(BUSW-1):0]	pf_insn;
	//
	// o_illegal will be true if this instruction was the result of
	// a bus error (This is also part of the CPU interface)
	input	wire			pf_illegal;
	//
	(* anyconst *) output	reg	[(AW+1):0]	fc_pc;
	(* anyconst *) output	reg			fc_illegal;
	(* anyconst *) output	reg	[BUSW-1:0]	fc_insn;
	output	reg	[(AW+1):0]	f_address;

`ifdef	ZIPCPU
`define	CPU_ASSUME	assume
`define	CPU_ASSERT	assert
`else
`define	CPU_ASSUME	assert
`define	CPU_ASSERT	assume
`endif
	reg	[(AW+1):0]	f_next_address;

	always @(posedge i_clk)
	if (cpu_new_pc)
		f_address <= cpu_pc;
	else if (pf_valid && cpu_ready)
	begin
		f_address[AW+1:2] <= f_address[AW+1:2] + 1'b1;
		f_address[1:0] <= 0;
	end

	always @(*)
	begin
		f_next_address = f_address + 4;
		f_next_address[1:0] = 2'b00;
	end

	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	always @(*)
	if (!f_past_valid)
		`CPU_ASSERT(i_reset);

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////

	//
	// Assume we start from a reset condition
	initial	`CPU_ASSERT(i_reset);
	//

	/////////////////////////////////////////////////////
	//
	//
	// Assertions about our return responses to the CPU
	//
	//
	/////////////////////////////////////////////////////

	generate if (OPT_ALIGNED)
	begin

		always @(*)
		if (cpu_new_pc)
			`CPU_ASSERT(cpu_pc[1:0] == 2'b00);

		always @(*)
		if (pf_valid)
			`CPU_ASSUME(pf_pc[1:0] == 2'b00);

	end endgenerate

	// Some things to know from the CPU ... there will always be a
	// i_new_pc request following any reset or clear cache request
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset || cpu_clear_cache)))
	begin
		`CPU_ASSERT(cpu_new_pc);
		`CPU_ASSERT(!pf_valid);
		`CPU_ASSERT(!pf_illegal);
	end else if (f_past_valid && !$past(cpu_new_pc)
		&& $past(pf_valid && !cpu_ready))
	begin
		//
		// Once an instruction has been presented, it must hold valid
		// until accepted
		`CPU_ASSUME(pf_valid);
		`CPU_ASSUME($stable(pf_pc));
		`CPU_ASSUME($stable(pf_insn));
		`CPU_ASSUME($stable(pf_illegal));
	end else if (f_past_valid && $past(pf_illegal && !cpu_new_pc))
		// Once illegal is raised, it stays raised until a new PC,
		// reset, or cache clear
		`CPU_ASSUME(pf_illegal);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset || cpu_clear_cache))
		`CPU_ASSUME(!pf_valid);
	else if ((f_past_valid)&&(!$past(pf_illegal && !cpu_new_pc))&&(pf_illegal))
		// pf_illegal can only rise if pf_valid is true
		`CPU_ASSUME(pf_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset || cpu_new_pc || cpu_clear_cache)))
		`CPU_ASSUME(!pf_illegal || pf_valid);
	else if (f_past_valid && $past(pf_illegal))
		`CPU_ASSUME(pf_illegal);

	always @(*)
	if (pf_valid && !pf_illegal)
		`CPU_ASSUME(f_address == pf_pc);

	always @(posedge i_clk)
	if (f_past_valid && !i_reset && !cpu_new_pc)
		`CPU_ASSERT(f_next_address == cpu_pc);

	// The CPU is always ready following either a reset or a clear cache
	// signal
	always @(posedge i_clk)
	if (f_past_valid && $past(i_reset || cpu_clear_cache || cpu_new_pc))
		`CPU_ASSERT(cpu_ready);

	// If the CPU was ready in the past and hasn't accepted a new
	// instruction, then it must still be ready
	always @(posedge i_clk)
	if (f_past_valid && $past(cpu_ready || !pf_valid))
		`CPU_ASSERT(cpu_ready);

	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		assume(fc_pc[1:0] == 2'b00);

	generate if (OPT_CONTRACT)
	begin : CHECK_CONTRACT
		always @(*)
		if (pf_valid && fc_pc[AW+1:2] == f_address[AW+1:2])
		begin
			if (fc_illegal)
				`CPU_ASSUME(pf_illegal);
			else if (!pf_illegal)
				`CPU_ASSUME(fc_insn == pf_insn);
		end

		always @(posedge i_clk)
		if (f_past_valid && !$past(pf_illegal) && pf_valid
				&& fc_pc[AW+1:2] == f_address[AW+1:2])
			`CPU_ASSUME(fc_illegal == pf_illegal);

	end endgenerate

endmodule
