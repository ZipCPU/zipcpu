////////////////////////////////////////////////////////////////////////////////
//
// Filename:	prefetch.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a very simple instruction fetch approach.  It gets
//		one instruction at a time.  Future versions should pipeline
//	fetches and perhaps even cache results--this doesn't do that.  It
//	should, however, be simple enough to get things running.
//
//	The interface is fascinating.  The 'i_pc' input wire is just a
//	suggestion of what to load.  Other wires may be loaded instead. i_pc
//	is what must be output, not necessarily input.
//
//   20150919 -- Added support for the WB error signal.  When reading an
//	instruction results in this signal being raised, the pipefetch module
//	will set an illegal instruction flag to be returned to the CPU together
//	with the instruction.  Hence, the ZipCPU can trap on it if necessary.
//
//   20171020 -- Added a formal proof to prove that the module works.  This
//	also involved adding a req_addr register, and the logic associated
//	with it.
//
//   20171113 -- Removed the req_addr register, replacing it with a bus abort
//	capability.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017-2018, Gisselquist Technology, LLC
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
//
module	prefetch(i_clk, i_reset, i_new_pc, i_clear_cache, i_stalled_n, i_pc,
			o_insn, o_pc, o_valid, o_illegal,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data);
	parameter		ADDRESS_WIDTH=30, DATA_WIDTH=32;
	parameter	[0:0]	F_OPT_CLK2FFLOGIC = 1'b0;
	localparam		AW=ADDRESS_WIDTH,
				DW=DATA_WIDTH;
	input	wire			i_clk, i_reset;
	// CPU interaction wires
	input	wire			i_new_pc, i_clear_cache, i_stalled_n;
	// We ignore i_pc unless i_new_pc is true as well
	input	wire	[(AW+1):0]	i_pc;
	output	reg	[(DW-1):0]	o_insn;	// Instruction read from WB
	output	wire	[(AW+1):0]	o_pc;	// Address of that instruction
	output	reg			o_valid; // If the output is valid
	output	reg			o_illegal; // Result is from a bus err
	// Wishbone outputs
	output	reg			o_wb_cyc, o_wb_stb;
	output	wire			o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	wire	[(DW-1):0]	o_wb_data;
	// And return inputs
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(DW-1):0]	i_wb_data;

	// Declare local variables
	reg			invalid;

	// These are kind of obligatory outputs when dealing with a bus, that
	// we'll set them here.  Nothing's going to pay attention to these,
	// though, this is primarily for form.
	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 32'h0000;

	// Let's build it simple and upgrade later: For each instruction
	// we do one bus cycle to get the instruction.  Later we should
	// pipeline this, but for now let's just do one at a time.
	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||((o_wb_cyc)&&((i_wb_ack)||(i_wb_err))))
		begin
			// End any bus cycle on a reset, or a return ACK
			// or error.
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end else if ((!o_wb_cyc)&&(
				// Start if the last instruction output was
				// accepted, *and* it wasn't a bus error
				// response
				((i_stalled_n)&&(!o_illegal))
				// Start if the last bus result ended up
				// invalid
				||(invalid)
				// Start on any request for a new address
				||(i_new_pc)))
		begin
			// Initiate a bus transaction
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
		end else if (o_wb_cyc)
		begin
			// If our request has been accepted, then drop the
			// strobe line
			if (!i_wb_stall)
				o_wb_stb <= 1'b0;

			// Abort on new-pc
			// ... clear_cache  is identical, save that it will
			// immediately be followed by a new PC, so we don't
			// need to worry about that other than to drop
			// CYC and STB here.
			if (i_new_pc)
			begin
				o_wb_cyc <= 1'b0;
				o_wb_stb <= 1'b0;
			end
		end

	//
	// If during the current bus request, a command came in from the CPU
	// that will invalidate the results of that request, then we need to
	// keep track of an "invalid" flag to remember that and so squash
	// the result.
	//
	initial	invalid = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||(!o_wb_cyc))
			invalid <= 1'b0;
		else if (i_new_pc)
			invalid <= 1'b1;

	// The wishbone request address, o_wb_addr
	//
	// The rule regarding this address is that it can *only* be changed
	// when no bus request is active.  Further, since the CPU is depending
	// upon this value to know what "PC" is associated with the instruction
	// it is processing, we can't change until either the CPU has accepted
	// our result, or it is requesting a new PC (and hence not using the
	// output).
	//
	initial	o_wb_addr= 0;
	always @(posedge i_clk)
		if (i_new_pc)
			o_wb_addr  <= i_pc[AW+1:2];
		else if ((o_valid)&&(i_stalled_n)&&(!o_illegal))
			o_wb_addr  <= o_wb_addr + 1'b1;

	// The instruction returned is given by the data returned from the bus.
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			o_insn <= i_wb_data;

	//
	// Finally, the flags associated with the prefetch.  The rule is that
	// if the output represents a return from the bus, then o_valid needs
	// to be true.  o_illegal will be true any time the last bus request
	// resulted in an error.  o_illegal is only relevant to the CPU when
	// o_valid is also true, hence o_valid will be true even in the case
	// of a bus error in our request.
	//
	initial o_valid   = 1'b0;
	initial o_illegal = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||(i_new_pc)||(i_clear_cache))
		begin
			// On any reset, request for a new PC (i.e. a branch),
			// or a request to clear our cache (i.e. the data
			// in memory may have changed), we invalidate any
			// output.
			o_valid   <= 1'b0;
			o_illegal <= 1'b0;
		end else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
		begin
			// Otherwise, at the end of our bus cycle, the
			// answer will be valid.  Well, not quite.  If the
			// user requested something mid-cycle (i_new_pc)
			// or (i_clear_cache), then we'll have to redo the
			// bus request, so we aren't valid.
			//
			o_valid   <= 1'b1;
			o_illegal <= ( i_wb_err);
		end else if (i_stalled_n)
		begin
			// Once the CPU accepts any result we produce, clear
			// the valid flag, lest we send two identical
			// instructions to the CPU.
			//
			o_valid <= 1'b0;
			//
			// o_illegal doesn't change ... that way we don't
			// access the bus again until a new address request
			// is given to us, via i_new_pc, or we are asked
			//  to check again via i_clear_cache
			//
			// o_illegal <= (!i_stalled_n);
		end

	// The o_pc output shares its value with the (last) wishbone address
	assign	o_pc = { o_wb_addr, 2'b00 };

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[1:0]	unused;
	assign	unused = i_pc[1:0];
	// verilator lint_on  UNUSED
`ifdef	FORMAL
	localparam	F_LGDEPTH=2;
	reg	f_past_valid;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks,
					f_outstanding;
	reg	[(AW-1):0]	f_last_pc;
	reg			f_last_pc_valid;
	reg	[(AW-1):0]	f_req_addr;
//
//
// Generic setup
//
//
`ifdef	PREFETCH
`define	ASSUME	assume
	reg	f_last_clk;
	initial	assume(f_last_clk == 1);
	initial	assume(i_clk == 0);
	always @($global_clock)
	begin
		assume(i_clk != f_last_clk);
		f_last_clk <= !f_last_clk;
	end
`else
`define	ASSUME	assert
`endif

	// Assume a clock

	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////

	//
	// Nothing changes, but on the positive edge of a clock
	//
	generate if (F_OPT_CLK2FFLOGIC)
	begin
		always @($global_clock)
		if (!$rose(i_clk))
		begin
			// Control inputs from the CPU
			`ASSUME($stable(i_reset));
			`ASSUME($stable(i_new_pc));
			`ASSUME($stable(i_clear_cache));
			`ASSUME($stable(i_stalled_n));
			`ASSUME($stable(i_pc));
		end
	end endgenerate

	// Assume we start from a reset condition
	initial	`ASSUME(i_reset);
	always @(*)
		if (!f_past_valid)
			`ASSUME(i_reset);
	// Some things to know from the CPU ... there will always be a
	// i_new_pc request following any reset
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_reset)))
			`ASSUME(i_new_pc);

	// There will also be a i_new_pc request following any request to clear
	// the cache.
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_clear_cache)))
			`ASSUME(i_new_pc);
	//
	// Following a reset, all pipelines clear and the next stage is
	// guaranteed to be ready.
	//
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_reset)))
			`ASSUME(i_stalled_n);

	// The CPU will never suddenly become busy unless it has accepted a
	// valid instruction.
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(!o_valid))&&($past(i_stalled_n)))
			`ASSUME(i_stalled_n);

	//
	//
	// Let's make some assumptions about how long it takes our
	// phantom bus and phantom CPU to respond.
	//
	// These delays need to be long enough to flush out any potential
	// errors, yet still short enough that the formal method doesn't
	// take forever to solve.
	//
	localparam	F_CPU_DELAY = 4;
	reg	[4:0]	f_cpu_delay;
	// First, let's assume that any response from the bus comes back
	// within F_WB_DELAY clocks

		// Here's our delay assumption: We'll assume that the
	// wishbone will always respond within F_WB_DELAY clock ticks
	// of the beginning of any cycle.
	//
	// This includes both dropping the stall line, as well as
	// acknowledging any request.  While this may not be
	// a reasonable assumption for a piped master, it should
	// work here for us.

	// Count the number of clocks it takes the CPU to respond to our
	// instruction.
	always @(posedge i_clk)
		// If no instruction is ready, then keep our counter at zero
		if ((i_reset)||(!o_valid)||(i_stalled_n))
			f_cpu_delay <= 0;
		else
			// Otherwise, count the clocks the CPU takes to respond
			f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	PREFETCH
	// Only *assume* that we are less than F_CPU_DELAY if we are not
	// integrated into the CPU
	always @(posedge i_clk)
		assume(f_cpu_delay < F_CPU_DELAY);
`endif

	fwb_master #(.AW(AW), .DW(DW),.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS(1), .F_OPT_SOURCE(1),
			.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
			.F_OPT_RMW_BUS_OPTION(0),
			.F_OPT_DISCONTINUOUS(0))
		f_wbm(i_clk, i_reset,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding);

	/////////////////////////////////////////////////
	//
	//
	// Assertions about our outputs
	//
	//
	/////////////////////////////////////////////////
	//
	// Assertions about our wishbone control outputs first
	// Prefetches don't write
	always @(posedge i_clk)
		if (o_wb_stb)
			assert(!o_wb_we);
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(f_past_valid))
				&&($past(i_clear_cache,2))
				&&($past(o_wb_cyc,2)))
			// Make sure any clear-cache transaction is aborted,
			// *and* that no valid instructions get sent to the
			// CPU
			assert((!$past(o_wb_cyc))||(!o_wb_cyc));

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_valid))&&(o_valid))
			assert(o_wb_addr == $past(o_wb_addr));

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(!i_reset))&&($past(invalid)))
			assert(o_wb_cyc);

	// Any time the CPU accepts an instruction, assert that on the
	// valid line will be low on the next clock
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_valid))&&($past(i_stalled_n)))
			assert(!o_valid);

	// Since we only change our output on a response from the bus, we
	// need to insist that the item has been read by the CPU before
	// we go looking/asking for a next value.
	//
	// This routine should never be requesting a new instruction when
	// one is valid--lest the CPU never accept the old instruction and we
	// have nothing to do with the data when the bus request returns.
	always @(*)
		if (o_wb_cyc)
			assert(!o_valid);

	// If we just got a valid instruction from the wishbone, assert that
	// the instruction is listed as valid on the next instruction cycle
	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_reset))
			&&($past(o_wb_cyc))
			&&($past(!i_clear_cache))
			&&($past(i_wb_ack))&&(!$past(i_wb_err)))
		begin
			if (!invalid)
				assert(o_valid);
		end

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_clear_cache)))
			assert(!o_valid);

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(f_past_valid))
				&&($past(i_clear_cache,2))
				&&($past(o_wb_cyc,2)))
			// Make sure any clear-cache transaction is aborted,
			// *and* that no valid instructions get sent to the
			// CPU
			assert(!o_valid);

	//
	// Assertions about our return responses
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!$past(i_stalled_n)))
		assert(o_valid == $past(o_valid));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid))&&(o_valid))
	begin
		assert($stable(o_pc));
		assert($stable(o_insn));
		assert($stable(o_illegal));
	end

	//
	// The o_illegal line is the one we use to remind us not to go
	// back and retry the last value if it returned a bus error.  Hence,
	// let's assert that this line stays constant any time o_wb_cyc
	// is low, and we haven't received any new requests.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(!o_wb_cyc)))
		assert(o_illegal == $past(o_illegal));


	//
	//
	// Let's examine whether or not we "walk" though PC addresses one
	// at a time like we expect.
	//
	initial	f_last_pc_valid = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||(i_clear_cache)||(i_new_pc)||(invalid))
			f_last_pc_valid <= 1'b0;
		else if (o_valid)
			f_last_pc_valid <= (!o_illegal);

	// initial	f_last_pc = 0;
	always @(posedge i_clk)
		if (o_valid)
			f_last_pc  <= o_pc[AW+1:2];
		else if (f_last_pc_valid)
			assert(o_pc[AW+1:2] == f_last_pc + 1'b1);

	always @(*)
		assert(o_pc[1:0] == 2'b00);

	// If we are producing a new result, and no new-pc or clear cache
	// has come through (i.e. f_last_pc_valid is true), then the resulting
	// PC should be one more than the last time.
	//
	// The o_valid && !$past(o_valid) is necessary because f_last_pc_valid
	// will be different by the second o_valid.
	always @(posedge i_clk)
		if ((f_past_valid)&&(o_valid)
				&&(!$past(o_valid))&&(f_last_pc_valid))
			assert(o_pc[AW+1:2] == (f_last_pc + 1'b1));

	// Let's also keep track of the address the CPU wants us to return.
	// Any time the CPU branches to a new_pc, we'll record that request.
	// Likewise, any time an instruction is returned from the bus,
	// we'll increment this address so as to automatically walk through
	// memory.
	//
	always @(*)
		assume(i_pc[1:0] == 2'b00);
	initial	f_req_addr = 0;
	always @(posedge i_clk)
		if (i_new_pc)
			f_req_addr <= i_pc[AW+1:2];
		else if ((!invalid)&&(o_wb_cyc)&&(i_wb_ack)&&(!i_wb_err))
			f_req_addr <= f_req_addr + 1'b1;

	// Let's also keep the formal methods on track.  Any time we are
	// requesting a value, it should either be from the req_addr, or if
	// not a new value should've come in rendering this one invalid.
	always @(posedge i_clk)
		if (o_wb_cyc)
			assert((invalid)||(f_req_addr == o_wb_addr));
		// This isn't good enough for induction, so we'll need to
		// constrain this further
		else if ((!o_valid)&&(!i_new_pc)&&(!i_reset))
			assert(f_req_addr == o_wb_addr);

	// In this version, invalid should only ever be high for one cycle.
	// CYC should be high on the cycle following--if ever.
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(invalid)))
			assert(!invalid);
`endif
endmodule
//
// Usage:	(this)	(mid)	(past)
//    Cells	167	230	175
//	FDRE	 67	 97	 69
//	LUT1	  1	  1	  1
//	LUT2	  1	  3	  3
//	LUT3	 31	 63	 33
//	LUT4	  5	  3	  3
//	LUT5	  1	  3	  3
//	LUT6	  2	  1	  3
//	MUXCY	 29	 29	 31
//	XORCY	 30	 30	 32
