////////////////////////////////////////////////////////////////////////////////
//
// Filename:	abs_prefetch.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Rather than feed our CPU with actual valid instructions returned
//		from memory, this is an abstract prefetch.  It's not even a
//	perfect or complete abstract prefetch at that--it doesn't actually
//	access memory.  However, it will maintain the abstract interface with
//	the CPU.s
//
//	In other words, this abs_prefetch may produce the exact same results a
//	true prefetch would have produced--whether it be prefetch.v, dblfetch.v,
//	or even pfcache.v.  On the other hand, it might not.  If the CPU can
//	pass either way, then it can most certainly pass with a true prefetch.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2018, Gisselquist Technology, LLC
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
module	abs_prefetch(i_clk, i_reset, i_new_pc, i_clear_cache,
			// i_early_branch, i_from_addr,
			i_stall_n, i_pc, o_insn, o_pc, o_valid,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
			o_illegal);
	parameter	ADDRESS_WIDTH = 30;
	localparam	BUSW = 32;	// Number of data lines on the bus
	localparam	AW=ADDRESS_WIDTH; // Shorthand for ADDRESS_WIDTH
	//
	input	wire			i_clk, i_reset;
	//
	// The interface with the rest of the CPU
	input	wire			i_new_pc;
	input	wire			i_clear_cache;
	input	wire			i_stall_n;
	input	wire	[(AW+1):0]	i_pc;
	output	wire	[(BUSW-1):0]	o_insn;
	output	wire	[(AW+1):0]	o_pc;
	output	wire			o_valid;
	//
	// The wishbone bus interface
	output	wire			o_wb_cyc, o_wb_stb;
	output	wire			o_wb_we;
	output	wire	[(AW-1):0]	o_wb_addr;
	output	wire	[(BUSW-1):0]	o_wb_data;
	//
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(BUSW-1):0]	i_wb_data;
	//
	// o_illegal will be true if this instruction was the result of
	// a bus error (This is also part of the CPU interface)
	output	reg			o_illegal;
	//

	// Fixed bus outputs: we read from the bus only, never write.
	// Thus the output data is ... irrelevant and don't care.  We set it
	// to zero just to set it to something.
	assign	o_wb_cyc  = 0;
	assign	o_wb_stb  = 0;
	assign	o_wb_we   = 0;
	assign	o_wb_addr = 0;
	assign	o_wb_data = 0;


	reg	[(AW-1):0]	r_pc;

	always @(posedge i_clk)
	if (i_new_pc)
		r_pc = i_pc[AW+1:2];
	else if ((o_valid)&&(i_stall_n))
		r_pc <= r_pc + 1'b1;

	assign	o_pc = { (o_valid) ? r_pc : $anyseq, 2'b00 };


	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache)||(i_new_pc)||(waiting_on_pc))
		o_illegal <= 1'b0;
	else if ((!o_illegal)&&(wait_for_valid == 1'b1))
		o_illegal <= $anyseq;

	wire	[5:0]	wait_time;
	assign	wait_time = $anyseq;
	always @(*)
		assume(wait_time > 0);

	reg	waiting_on_pc;

	initial	waiting_on_pc <= 1'b1;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache))
		waiting_on_pc <= 1'b1;
	else if (i_new_pc)
		waiting_on_pc <= 1'b0;

	reg	[5:0]	wait_for_valid;

	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache))
		wait_for_valid <= 6'h3f;
	else if ((i_new_pc)||(waiting_on_pc))
		wait_for_valid <= wait_time;
	else if (wait_for_valid > 0)
		wait_for_valid <= wait_for_valid - 1'b1;

	assign	o_valid   = (!waiting_on_pc)&&(wait_for_valid == 0);
	assign	o_insn    = $anyseq;

`ifdef	FORMAL
	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;
	always @(*)
	if (!f_past_valid)
		assert(i_reset);

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////

	//
	// Assume we start from a reset condition
	initial	assert(i_reset);

	// Assume that any reset is either accompanied by a new address,
	// or a new address immediately follows it.
//	always @(posedge i_clk)
//	if ((f_past_valid)&&(!$past(i_reset)))
//		assert((i_new_pc)||($past(i_new_pc)));

	/////////////////////////////////////////////////
	//
	//
	// Assertions about our outputs
	//
	//
	/////////////////////////////////////////////////

	/////////////////////////////////////////////////////
	//
	//
	// Assertions about our return responses to the CPU
	//
	//
	/////////////////////////////////////////////////////

	// Consider it invalid to present the CPU with the same instruction
	// twice in a row.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid))&&($past(i_stall_n))&&(o_valid))
		assert(o_pc != $past(o_pc));

	always @(*)
	begin
		assert(i_pc[1:0] == 2'b00);
		assert(o_pc[1:0] == 2'b00);
	end


	//
	// Assume we start from a reset condition
	initial	assume(i_reset);

	// Assume that any reset is either accompanied by a new address,
	// or a new address immediately follows it.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(i_new_pc);

//	always @(posedge i_clk)
//	if ((f_past_valid)&&($past(i_clear_cache)))
//		assert(!i_clear_cache);

	//
	//
	// The bottom two bits of the PC address register are always zero.
	// They are there to make examining traces easier, but I expect
	// the synthesis tool to remove them.
	//
	always @(*)
		assert(i_pc[1:0] == 2'b00);

	// Some things to know from the CPU ... there will always be a
	// i_new_pc request following any reset
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(i_new_pc);

	// There will also be a i_new_pc request following any request to clear
	// the cache.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_clear_cache)))
		assert(i_new_pc);

	always @(*)
		assume(i_pc[1:0] == 2'b00);

	//
	// Following a reset, all pipelines clear and the next stage is
	// guaranteed to be ready.
	//
	initial	assume(i_stall_n);
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(i_stall_n);

	// The CPU will never suddenly become busy unless it has accepted a
	// valid instruction.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_valid))&&($past(i_stall_n)))
		assert(i_stall_n);

	/////////////////////////////////////////////////
	//
	//
	// Assertions about our outputs
	//
	//
	/////////////////////////////////////////////////

	//
	// Assertions about our return responses to the CPU
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!$past(i_stall_n)))
	begin
		assert($stable(o_pc));
		assume($stable(o_insn));
		assume($stable(o_valid));
		assume($stable(o_illegal));
	end

	//
	// As with i_pc[1:0], the bottom two bits of the address are unused.
	// Let's assert here that they remain zero.
	always @(*)
		assert(o_pc[1:0] == 2'b00);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_illegal))&&(o_illegal))
		assert(o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_new_pc)))
		assert(!o_valid);

`endif	// FORMAL

endmodule
