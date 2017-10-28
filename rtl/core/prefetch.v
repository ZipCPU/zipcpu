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
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017, Gisselquist Technology, LLC
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
module	prefetch(i_clk, i_rst, i_new_pc, i_clear_cache, i_stalled_n, i_pc,
			o_i, o_pc, o_valid, o_illegal,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data);
	parameter		ADDRESS_WIDTH=30, DATA_WIDTH=32;
	localparam		AW=ADDRESS_WIDTH,
				DW=DATA_WIDTH;
	input	wire			i_clk, i_rst;
	// CPU interaction wires
	input	wire			i_new_pc, i_clear_cache, i_stalled_n;
	// We ignore i_pc unless i_new_pc is true as well
	input	wire	[(AW-1):0]	i_pc;
	output	reg	[(DW-1):0]	o_i;	// Instruction read from WB
	output	wire	[(AW-1):0]	o_pc;	// Address of that instruction
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
	reg	[(AW-1):0]	req_addr;

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
	initial	o_wb_addr= 0;
	always @(posedge i_clk)
		if ((i_rst)||((o_wb_cyc)&&((i_wb_ack)||(i_wb_err))))
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
				// Start any time we don't have a valid
				// output
				||((!o_valid)&&(!o_illegal))
				// Start on any request for a new address
				||(i_new_pc)))
		begin
			// Initiate a bus cycle
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
		end else if (o_wb_cyc)
		begin
			// If our request has been accepted, then drop the
			// strobe line
			if (!i_wb_stall)
				o_wb_stb <= 1'b0;
		end

	//
	// If during the current bus request, a command came in from the CPU
	// that will invalidate the results of that request, then we need to
	// keep track of an "invalid" flag to remember that and so squash
	// the result.
	//
	initial	invalid = 1'b0;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			invalid <= 1'b0;
		else if ((i_new_pc)||(i_clear_cache))
			invalid <= 1'b1;

	// Let's also keep track of the address the CPU wants us to return.
	// Any time the CPU branches to a new_pc, we'll record that request.
	// Likewise, any time an instruction is returned from the bus,
	// we'll increment this address so as to automatically walk through
	// memory.
	//
	always @(posedge i_clk)
		if (i_new_pc)
			req_addr <= i_pc;
		else if ((!invalid)&&(!i_clear_cache)&&(o_wb_cyc)
				&&(i_wb_ack)&&(!i_wb_err))
			req_addr <= req_addr + 1'b1;

	// The wishboen request address, o_wb_addr
	//
	// The rule regarding this address is that it can *only* be changed
	// when no bus request is active.  Further, since the CPU is depending
	// upon this value to know what "PC" is associated with the instruction
	// it is processing, we can't change until either the CPU has accepted
	// our result, or it is requesting a new PC (and hence not using the
	// output).
	//
	always @(posedge i_clk)
		if (!o_wb_cyc)
		begin
			if (i_new_pc)
				o_wb_addr  <= i_pc;
			else if ((i_stalled_n)||(!o_valid))
				o_wb_addr  <= req_addr;
		end

	// The instruction returned is given by the data returned from the bus.
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			o_i <= i_wb_data;

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
		if ((i_rst)||(i_new_pc)||(i_clear_cache))
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
			o_valid   <= (!invalid);
			o_illegal <= ( i_wb_err)&&(!invalid);
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
	assign	o_pc = o_wb_addr;

`ifdef	FORMAL
//
//
// Generic setup
//
//
`ifdef	PREFETCH
`define	ASSUME	assume
`define	STEP_CLOCK	assume(i_clk != f_last_clk);
`else
`define	ASSUME	assert
`define	STEP_CLOCK
`endif

	// Assume a clock
	reg	f_last_clk, f_past_valid;
	always @($global_clock)
	begin
		`STEP_CLOCK
		f_last_clk <= i_clk;
	end

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
	always @($global_clock)
	if (!$rose(i_clk))
	begin
		// Control inputs from the CPU
		`ASSUME($stable(i_rst));
		`ASSUME($stable(i_new_pc));
		`ASSUME($stable(i_clear_cache));
		`ASSUME($stable(i_stalled_n));
		`ASSUME($stable(i_pc));
		// Wishbone inputs
		`ASSUME($stable(i_wb_ack));
		`ASSUME($stable(i_wb_stall));
		`ASSUME($stable(i_wb_err));
		`ASSUME($stable(i_wb_data));
	end


`ifdef	PREFETCH
	//
	// Assume that resets, new-pc commands, and clear-cache commands
	// are never more than pulses--one clock wide at most.
	//
	// It may be that the CPU treats us differently.  We'll only restrict
	// our solver to this here.
	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if ($past(i_rst))
			restrict(!i_rst);
		if ($past(i_new_pc))
			restrict(!i_new_pc);
		if ($past(i_clear_cache))
			assume(!i_clear_cache);
	end
`endif

	//
	// Assume we start from a reset condition
	initial	`ASSUME(i_rst);
	//
	// Let's make some assumptions about how long it takes our
	// phantom bus and phantom CPU to respond.
	//
	// These delays need to be long enough to flush out any potential
	// errors, yet still short enough that the formal method doesn't
	// take forever to solve.
	//
	localparam	F_WB_DELAY = 6, F_CPU_DELAY = 4;
	reg	[4:0]	f_wb_delay = 0, f_cpu_delay;

	// First, let's assume that any response from the bus comes back
	// within F_WB_DELAY clocks
	always @(posedge i_clk)
	if (!o_wb_cyc) // No delay accumulates except during bus requests
		f_wb_delay <= 0;
	else begin
		if (o_wb_stb)
		begin
			// In the process, let's assert a reality: nothing
			// will acknowledge or error during the request
			// cycle.  All acknowledgement's or errors will be
			// at least one clock after (o_wb_stb)&&(!i_wb_stall)
			`ASSUME(!i_wb_ack);
			`ASSUME(!i_wb_err);
		end

		f_wb_delay <= f_wb_delay + 1;

		// Here's our delay assumption: We'll assume that the
		// wishbone will always respond within F_WB_DELAY clock ticks
		// of the beginning of any cycle.
		//
		// This includes both dropping the stall line, as well as
		// acknowledging any request.  While this may not be
		// a reasonable assumption for a piped master, it should
		// work here for us.
		`ASSUME(f_wb_delay < F_WB_DELAY);
	end

	// Now, let's repeat this bit but now looking at the delay the CPU
	// takes to accept an instruction.
	always @(posedge i_clk)
		// If no instruction is ready, then keep our counter at zero
		if ((!o_valid)||(i_stalled_n))
			f_cpu_delay <= 0;
		else
			// Otherwise, count the clocks the CPU takes to respond
			f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	PREFETCH
	always @(posedge i_clk)
		assume(f_cpu_delay < F_CPU_DELAY);
`endif

// `define	SPEED_PROOF
`ifdef	SPEED_PROOF
	// In many ways, we don't care what happens on the bus return lines
	// if the cycle line is low, so restricting them to a known value
	// makes a lot of sense.
	//
	// On the other hand, if something above *does* depend upon these
	// values (when it shouldn't), then we might want to know about it.
	//
	//
	always @(posedge i_clk)
		if (!o_wb_cyc)
		begin
			restrict(!i_wb_ack);
			restrict(!i_wb_stall);
			restrict(!i_wb_err);
			restrict($stable(i_wb_data));
		end else if (!$past(i_wb_ack))
			restrict($stable(i_wb_data));
`endif

	/////////////////////////////////////////////////
	//
	//
	// Assertions about our outputs
	//
	//
	/////////////////////////////////////////////////
	initial	assert(!o_wb_cyc);
	initial	assert(!o_wb_stb);

	always @(posedge i_clk)
		if (o_wb_stb)
		begin
			assert( o_wb_cyc);
			assert(!o_wb_we);
		end

	// Any time the CPU accepts an instruction, assume that on the
	// next clock the valid line has been de-asserted
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_valid))&&($past(i_stalled_n)))
			assert(!o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_rst)))
	begin
		if (($past(o_wb_stb))&&($past(i_wb_stall))
				&&(!$past(i_wb_err)))
			assert(o_wb_stb);
	end

	always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_wb_cyc)))
			assert($stable(o_wb_addr));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_rst)))
	begin
		if (($past(o_wb_cyc))
				&&(($past(i_wb_ack))||($past(i_wb_err))))
			assert(!o_wb_cyc);
	end

	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_rst))&&($past(o_wb_cyc))
			&&($past(i_wb_ack))&&(!$past(i_wb_err)))
		begin
			if ((req_addr == $past(o_wb_addr))&&(!invalid))
				assert(o_valid);
		end
	//
	// Assertions about our return responses
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_rst))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!$past(i_stalled_n)))
	begin
		assert($stable(o_pc));
		assert($stable(o_i));
		assert($stable(o_valid));
		assert($stable(o_illegal));
	end

	//
	// The o_illegal line is the one we use to remind us not to go
	// back and retry the last value if it returned a bus error.  Hence,
	// let's assert that this line stays constant any time o_wb_cyc
	// is low, and we haven't received any new requests.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_rst))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(!o_wb_cyc)))
		assert($stable(o_illegal));

	//
	//
	// Let's examin whether or not we "walk" though PC addresses one
	// at a time like we expect.
	//
	reg	[(AW-1):0]	f_last_pc;
	reg			f_last_pc_valid;

	initial	f_last_pc_valid = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_cache)||(i_new_pc)||(invalid))
			f_last_pc_valid <= 1'b0;
		else if (o_valid)
			f_last_pc_valid <= (!o_illegal);

	// initial	f_last_pc = 0;
	always @(posedge i_clk)
		if (o_valid)
			f_last_pc  <= o_pc;

	// If we are producing a new result, and no new-pc or clear cache
	// has come through (i.e. f_last_pc_valid is true), then the resulting
	// PC should be one more than the last time.
	//
	// The o_valid && !$past(o_valid) is necessary because f_last_pc_valid
	// will be different by the second o_valid.
	always @(posedge i_clk)
		if ((f_past_valid)&&(o_valid)
				&&(!$past(o_valid))&&(f_last_pc_valid))
			assert(o_pc == (f_last_pc + 1'b1));

	// Since we only change our output on a response from the bus, we
	// need to insist that the item has been read by the CPU before
	// we go looking/asking for a next value.
	always @(posedge i_clk)
		if (o_wb_cyc)
			assert(!o_valid);

	// Let's also keep the formal methods on track.  Any time we are
	// requesting a value, it should either be from the req_addr, or if
	// not a new value should've come in rendering this one invalid.
	always @(posedge i_clk)
		if (o_wb_cyc)
			assert((invalid)||(req_addr == o_wb_addr));
`endif
endmodule
