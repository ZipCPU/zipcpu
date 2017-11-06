////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dblfetch.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is one step beyond the simplest instruction fetch,
//		prefetch.v.  dblfetch.v uses memory pipelining to fetch two
//	instruction words in one cycle, figuring that the unpipelined CPU can't
//	go through both at once, but yet recycles itself fast enough for the
//	next instruction that would follow.  It is designed to be a touch
//	faster than the single instruction prefetch, although not as fast as
//	the prefetch and cache found elsewhere.
//
//	There are some gotcha's in this logic, however.  For example, it's 
//	illegal to switch devices mid-transaction, since the second device
//	might have different timing.  I.e. the first device might take 8
//	clocks to create an ACK, and the second device might take 2 clocks, the
//	acks might therefore come on top of each other, or even out of order.
//	But ... in order to keep logic down, we keep track of the PC in the
//	o_wb_addr register.  Hence, this register gets changed on any i_new_pc.
//	The i_pc value associated with i_new_pc will only be valid for one
//	clock, hence we can't wait to change.  To keep from violating the WB
//	rule, therefore, we *must* immediately stop requesting any transaction,
//	and then terminate the bus request as soon as possible.
//
//	This has consequences in terms of logic used, leaving this routine
//	anything but simple--even though the number of wires affected by
//	this is small (o_wb_cyc, o_wb_stb, and last_ack).
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
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
module	dblfetch(i_clk, i_rst, i_new_pc, i_clear_cache,
			i_stall_n, i_pc, o_i, o_pc, o_v,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
		o_illegal);
	parameter		ADDRESS_WIDTH=32, AUX_WIDTH = 1;
	localparam		AW=ADDRESS_WIDTH, DW = 32;
	input	wire			i_clk, i_rst, i_new_pc, i_clear_cache,
						i_stall_n;
	input	wire	[(AW-1):0]	i_pc;
	output	reg	[(DW-1):0]	o_i;
	output	reg	[(AW-1):0]	o_pc;
	output	wire			o_v;
	// Wishbone outputs
	output	reg			o_wb_cyc, o_wb_stb;
	output	wire			o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	wire	[(DW-1):0]	o_wb_data;
	// And return inputs
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(DW-1):0]	i_wb_data;
	// And ... the result if we got an error
	output	reg		o_illegal;

	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 32'h0000;

	reg	last_ack, last_stb, invalid_bus_cycle;

	reg	[(DW-1):0]	cache	[0:1];
	reg			cache_read_addr, cache_write_addr;
	reg	[1:0]		cache_valid;

	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||((o_wb_cyc)&&(i_wb_err)))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end else if (o_wb_cyc)
		begin
			if ((o_wb_stb)&&(!i_wb_stall))
				o_wb_stb <= (!last_stb)&&(!invalid_bus_cycle)
						&&(!i_new_pc);;

			// Relase the bus on the second ack
			if ((i_wb_ack)&&((last_ack)||(!o_wb_stb)))
			begin
				o_wb_cyc <= 1'b0;
				o_wb_stb <= 1'b0;
			end

		end else if ((invalid_bus_cycle)
			||((o_v)&&(i_stall_n)&&(cache_read_addr))) // Initiate a bus cycle
		begin
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			// last_stb <= 1'b0;
			// last_ack <= 1'b0;
		end

	initial	last_stb = 1'b0;
	always @(posedge i_clk)
		if (o_wb_stb)
		begin
			if (!i_wb_stall)
				last_stb <= 1'b1;
			else if ((invalid_bus_cycle)
					||(i_new_pc)
					||(i_clear_cache))
				last_stb <= 1'b1;
		end else if (!o_wb_stb)
			last_stb <= 1'b0;

	initial	last_ack = 1'b0;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			last_ack <= 1'b0;
		else if (i_wb_ack)
			last_ack <= 1'b1;
		else if ((o_wb_stb)&&(!i_wb_stall)
				&&(invalid_bus_cycle)&&(!last_stb))
			last_ack <= 1'b1;

	initial	invalid_bus_cycle = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			invalid_bus_cycle <= 1'b0;
		else if ((i_new_pc)||(i_clear_cache))
			invalid_bus_cycle <= 1'b1;
		else if (!o_wb_cyc)
			invalid_bus_cycle <= 1'b0;

	reg	[(AW-1):0]	req_addr;
	initial	req_addr = {(AW){1'b1}};
	always @(posedge i_clk)
		if (i_new_pc)
			req_addr <= i_pc;
		else if ((o_wb_stb)&&(!i_wb_stall)&&(!invalid_bus_cycle))
			req_addr <= req_addr + 1'b1;

	initial	o_wb_addr = {(AW){1'b1}};
	always @(posedge i_clk)
		if (o_wb_stb)
		begin
			if ((!i_wb_stall)&&(!invalid_bus_cycle))
				o_wb_addr <= o_wb_addr + 1'b1;
		end else if (!o_wb_cyc)
			o_wb_addr <= req_addr;

	initial	cache_write_addr = 1'b0;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			cache_write_addr <= 1'b0;
		else if ((o_wb_cyc)&&(i_wb_ack))
			cache_write_addr <= cache_write_addr + 1'b1;

	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			cache[cache_write_addr] <= i_wb_data;

	initial	cache_read_addr = 1'b0;
	always @(posedge i_clk)
		if ((i_new_pc)||(invalid_bus_cycle)
				||((o_v)&&(cache_read_addr)&&(i_stall_n)))
			cache_read_addr <= 1'b0;
		else if ((o_v)&&(i_stall_n))
			cache_read_addr <= 1'b1;

	initial	cache_valid = 2'b00;
	always @(posedge i_clk)
		if ((i_rst)||(i_new_pc)||(invalid_bus_cycle))
			cache_valid <= 2'b00;
		else begin
			if ((o_v)&&(i_stall_n))
				cache_valid[cache_read_addr] <= 1'b0;
			if ((o_wb_cyc)&&(i_wb_ack))
				cache_valid[cache_write_addr] <= 1'b1;
		end

	initial	o_i = {(32){1'b1}};
	always @(posedge i_clk)
		if (((i_stall_n)||(!o_v))&&(o_wb_cyc)&&(i_wb_ack))
			o_i <= i_wb_data;
		else
			o_i <= cache[cache_read_addr];

	initial	o_pc = 0;
	always @(posedge i_clk)
		if (i_new_pc)
			o_pc <= i_pc;
		else if ((o_v)&&(i_stall_n))
			o_pc <= o_pc + 1'b1;

	assign	o_v = cache_valid[cache_read_addr];

	initial	o_illegal = 1'b0;
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_err))
			o_illegal <= 1'b1;
		else if ((!o_wb_cyc)&&((i_new_pc)||(invalid_bus_cycle)))
			o_illegal <= 1'b0;

`ifdef	FORMAL
//
//
// Generic setup
//
//
`ifdef	DBLFETCH
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
		`ASSUME($stable(i_stall_n));
		`ASSUME($stable(i_pc));
		// Wishbone inputs
		`ASSUME($stable(i_wb_ack));
		`ASSUME($stable(i_wb_stall));
		`ASSUME($stable(i_wb_err));
		`ASSUME($stable(i_wb_data));
	end


`ifdef	DBLFETCH
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

	localparam	F_LGDEPTH=2;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;

	// Add a bunch of wishbone-based asserts
	formal_master #(.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH),
				.F_MAX_REQUESTS(2))
		f_wbm(i_clk, i_rst,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding);


	// Assume that any reset is either accompanied by a new address,
	// or a new address immediately follows it.
	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_rst)))
			`ASSUME((i_new_pc)||($past(i_new_pc)));
	//
	// Let's make some assumptions about how long it takes our phantom
	// (i.e. assumed) CPU to respond.
	//
	// This delay needs to be long enough to flush out any potential
	// errors, yet still short enough that the formal method doesn't
	// take forever to solve.
	//
	localparam	F_CPU_DELAY = 4;
	reg	[4:0]	f_cpu_delay;

	// Now, let's look at the delay the CPU takes to accept an instruction.
	always @(posedge i_clk)
		// If no instruction is ready, then keep our counter at zero
		if ((!o_v)||(i_stall_n))
			f_cpu_delay <= 0;
		else
			// Otherwise, count the clocks the CPU takes to respond
			f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	DBLFETCH
	always @(posedge i_clk)
		assume(f_cpu_delay < F_CPU_DELAY);
`endif

	/////////////////////////////////////////////////
	//
	//
	// Assertions about our outputs
	//
	//
	/////////////////////////////////////////////////

	reg	[3:0]	f_wb_nreqs, f_wb_acks;

	initial	f_wb_nreqs = 0;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			f_wb_nreqs <= 0;
		else if ((o_wb_stb)&&(!i_wb_stall))
			f_wb_nreqs <= f_wb_nreqs + 1'b1;
	always @(posedge i_clk)
		assert(f_wb_nreqs <= 2);

	initial	f_wb_acks = 0;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			f_wb_acks <= 0;
		else if ((i_wb_ack)||(i_wb_err))
			f_wb_acks <= f_wb_acks + 1'b1;
	always @(posedge i_clk)
		`ASSUME(f_wb_acks <= 2);
	// Can't have an ACK or an ERR coming back during the request
	always @(posedge i_clk)
		`ASSUME((!o_wb_stb)||((!i_wb_ack)&&(!i_wb_err))||(f_wb_acks < f_wb_nreqs));

	// Grab a copy of the requested address for comparison later
	reg	[(AW-1):0]	f_wb_req_addr	[0:15];
	reg	[(DW-1):0]	f_wb_ack_data	[0:15];
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(!invalid_bus_cycle))
		begin
			f_wb_req_addr[f_wb_nreqs] <= o_wb_addr;

			// Insist that any subsequent addresses are separated
			// by one.
			if (f_wb_nreqs > 0)
				assert(f_wb_req_addr[f_wb_nreqs-1]
					== o_wb_addr - 1);
		end

	// Grab a copy of the return data (instruction) for comparison later
	always @(posedge i_clk)
		if (o_wb_cyc)
			f_wb_ack_data[f_wb_acks] <= i_wb_data;

	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_rst))&&($past(o_wb_cyc))
			&&($past(i_wb_ack))&&(!$past(i_wb_err)))
		begin
			if (!invalid_bus_cycle)
				assert(o_v);
		end
	//
	// Assertions about our return responses to the CPU
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_rst))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_v))&&(!$past(i_stall_n)))
	begin
		assert($stable(o_pc));
		assert($stable(o_i));
		assert($stable(o_v));
		assert($stable(o_illegal));
	end

	// Consider it invalid to present the CPU with the same instruction
	// twice in a row.
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_v))&&($past(i_stall_n))&&(o_v))
			assert(o_pc != $past(o_pc));


	//
	// The o_illegal line is the one we use to remind us not to go
	// back and retry the last value if it returned a bus error.  Hence,
	// let's assert that this line stays constant any time o_wb_cyc
	// is low, and we haven't received any new requests.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_rst))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(!o_wb_cyc)))
		assert((o_wb_cyc)||($stable(o_illegal)));

	reg	[3:0]	f_nread;
	initial	f_nread = 0;
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_wb_cyc)&&(o_wb_cyc)))
		f_nread <= 0;
	else if ((o_v)&&(i_stall_n))
	begin
		f_nread <= f_nread + 1'b1;
	end

	always @(*)
		if ((o_v)&&(!o_illegal))
		begin
			assert(o_pc == f_wb_req_addr[f_nread]);
			assert(o_i  == f_wb_ack_data[f_nread]);
		end
		
`endif	// FORMAL
endmodule
