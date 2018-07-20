////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dblfetch.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is one step beyond the simplest instruction fetch,
//		prefetch.v.  dblfetch.v uses memory pipelining to fetch two
//	(or more) instruction words in one bus cycle.  If the CPU consumes
//	either of these before the bus cycle completes, a new request will be
//	made of the bus.  In this way, we can keep the CPU filled in spite
//	of a (potentially) slow memory operation.  The bus request will end
//	when both requests have been sent and both result locations are empty.
//
//	This routine is designed to be a touch faster than the single
//	instruction prefetch (prefetch.v), although not as fast as the
//	prefetch and cache approach found elsewhere (pfcache.v).
//
//	20180222: Completely rebuilt.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2018, Gisselquist Technology, LLC
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
module	dblfetch(i_clk, i_reset, i_new_pc, i_clear_cache,
			i_stall_n, i_pc, o_insn, o_pc, o_valid,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
		o_illegal);
	parameter		ADDRESS_WIDTH=30, AUX_WIDTH = 1;
	parameter	[0:0]	F_OPT_CLK2FFLOGIC=1'b0;
	localparam		AW=ADDRESS_WIDTH, DW = 32;
	input	wire			i_clk, i_reset, i_new_pc, i_clear_cache,
						i_stall_n;
	input	wire	[(AW+1):0]	i_pc;
	output	reg	[(DW-1):0]	o_insn;
	output	reg	[(AW+1):0]	o_pc;
	output	reg			o_valid;
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

	reg	last_stb, invalid_bus_cycle;

	reg	[(DW-1):0]	cache_word;
	reg			cache_valid;

	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||((o_wb_cyc)&&(i_wb_err)))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end else if (o_wb_cyc)
		begin
			if ((!o_wb_stb)||(!i_wb_stall))
				o_wb_stb <= (!last_stb);

			// Relase the bus on the second ack
			if (((i_wb_ack)&&(!o_wb_stb)&&(inflight<=1))
				||((!o_wb_stb)&&(inflight == 0))
				// Or any new transaction request
				||((i_new_pc)||(i_clear_cache)))
			begin
				o_wb_cyc <= 1'b0;
				o_wb_stb <= 1'b0;
			end

		end else if ((i_new_pc)||(invalid_bus_cycle)
			||((o_valid)&&(i_stall_n)&&(!o_illegal)))
		begin
			// Initiate a bus cycle if ... the last bus cycle was
			// aborted (bus error or new_pc), we've been given a
			// new PC to go get, or we just exhausted our one
			// instruction cache
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
		end

	reg	[1:0]	inflight;
	initial	inflight = 2'b00;
	always @(posedge i_clk)
	if (!o_wb_cyc)
		inflight <= 2'b00;
	else begin
		case({ ((o_wb_stb)&&(!i_wb_stall)), i_wb_ack })
		2'b01:	inflight <= inflight - 1'b1;
		2'b10:	inflight <= inflight + 1'b1;
		// If neither ack nor request, then no change.  Likewise
		// if we have both an ack and a request, there's no change
		// in the number of requests in flight.
		default: begin end
		endcase
	end

	always @(*)
		last_stb = (inflight != 2'b00)||((o_valid)&&(!i_stall_n));

	initial	invalid_bus_cycle = 1'b0;
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_new_pc))
			invalid_bus_cycle <= 1'b1;
		else if (!o_wb_cyc)
			invalid_bus_cycle <= 1'b0;

	initial	o_wb_addr = {(AW){1'b1}};
	always @(posedge i_clk)
		if (i_new_pc)
			o_wb_addr <= i_pc[AW+1:2];
		else if ((o_wb_stb)&&(!i_wb_stall))
			o_wb_addr <= o_wb_addr + 1'b1;

	//////////////////
	//
	// Now for the immediate output word to the CPU
	//
	//////////////////

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||(i_new_pc)||(i_clear_cache))
			o_valid <= 1'b0;
		else if ((o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
			o_valid <= 1'b1;
		else if (i_stall_n)
			o_valid <= cache_valid;

	initial	o_insn = {(32){1'b1}};
	always @(posedge i_clk)
	if ((!o_valid)||(i_stall_n))
	begin
		if (cache_valid)
			o_insn <= cache_word;
		else
			o_insn <= i_wb_data;
	end

	initial o_pc[1:0] = 2'b00;
	always @(posedge i_clk)
	if (i_new_pc)
		o_pc <= i_pc;
	else if ((o_valid)&&(i_stall_n))
		o_pc[AW+1:2] <= o_pc[AW+1:2] + 1'b1;

	initial	o_illegal = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||(i_new_pc)||(i_clear_cache))
			o_illegal <= 1'b0;
		else if ((!o_valid)||(i_stall_n))
		begin
			if (cache_valid)
				o_illegal <= (o_illegal)||(cache_illegal);
			else if ((o_wb_cyc)&&(i_wb_err))
				o_illegal <= 1'b1;
		end


	//////////////////
	//
	// Now for the output/cached word
	//
	//////////////////

	initial	cache_valid = 1'b0;
	always @(posedge i_clk)
		if ((i_reset)||(i_new_pc)||(i_clear_cache))
			cache_valid <= 1'b0;
		else begin
			if ((o_valid)&&(o_wb_cyc)&&((i_wb_ack)||(i_wb_err)))
				cache_valid <= (!i_stall_n)||(cache_valid);
			else if (i_stall_n)
				cache_valid <= 1'b0;
		end

	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			cache_word <= i_wb_data;

	reg	cache_illegal;
	initial	cache_illegal = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache)||(i_new_pc))
		cache_illegal <= 1'b0;
	else if ((o_wb_cyc)&&(i_wb_err)&&(o_valid)&&(!i_stall_n))
		cache_illegal <= 1'b1;

//
// Some of these properties can be done in yosys-smtbmc, *or* Verilator
//
// Ver1lator is different from yosys, however, in that Verilator doesn't support
// the $past() directive.  Further, any `assume`'s turn into `assert()`s
// within Verilator.  We can use this to help prove that the properties
// of interest truly hold, and that any contracts we create or assumptions we
// make truly hold in practice (i.e. in simulation).
//
`ifdef	FORMAL
`define	VERILATOR_FORMAL
`else
`ifdef	VERILATOR
//
// Define VERILATOR_FORMAL here to have Verilator check your formal properties
// during simulation.  assert() and assume() statements will both have the
// same effect within VERILATOR of causing your simulation to suddenly end.
//
// I have this property commented because it only works on the newest versions
// of Verilator (3.9 something and later), and I tend to still use Verilator
// 3.874.
//
// `define	VERILATOR_FORMAL
`endif
`endif

`ifdef	VERILATOR_FORMAL
	// Keep track of a flag telling us whether or not $past()
	// will return valid results
 	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	// Keep track of some alternatives to $past that can still be used
	// in a VERILATOR environment
	reg	f_past_reset, f_past_clear_cache, f_past_o_valid,
		f_past_stall_n;

	initial	f_past_reset = 1'b1;
	initial	f_past_clear_cache = 1'b0;
	initial	f_past_o_valid = 1'b0;
	initial	f_past_stall_n = 1'b1;
	always @(posedge i_clk)
	begin
		f_past_reset       <= i_reset;
		f_past_clear_cache <= i_clear_cache;
		f_past_o_valid     <= o_valid;
		f_past_stall_n     <= i_stall_n;
	end
`endif

`ifdef	FORMAL
//
//
// Generic setup
//
//
`ifdef	DBLFETCH
`define	ASSUME	assume

	generate if (F_OPT_CLK2FFLOGIC)
	begin
		// Assume a clock
		reg	f_last_clk;
		always @($global_clock)
		begin
			assume(i_clk != f_last_clk);
			f_last_clk <= i_clk;
		end
	end endgenerate

`else
`define	ASSUME	assert
`endif

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////

	always @(*)
		if (!f_past_valid)
			`ASSUME(i_reset);

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
			`ASSUME($stable(i_stall_n));
			`ASSUME($stable(i_pc));
			// Wishbone inputs
			`ASSUME($stable(i_wb_ack));
			`ASSUME($stable(i_wb_stall));
			`ASSUME($stable(i_wb_err));
			`ASSUME($stable(i_wb_data));
		end
	end endgenerate


	//
	// Assume that resets, new-pc commands, and clear-cache commands
	// are never more than pulses--one clock wide at most.
	//
	// It may be that the CPU treats us differently.  We'll only restrict
	// our solver to this here.
	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if (f_past_reset)
			restrict(!i_reset);
		if ($past(i_new_pc))
			restrict(!i_new_pc);
	end

	//
	// Assume we start from a reset condition
	initial	assume(i_reset);

	/////////////////////////////////////////////////
	//
	//
	// Wishbone bus properties
	//
	//
	/////////////////////////////////////////////////

	localparam	F_LGDEPTH=2;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;

	//
	// Add a bunch of wishbone-based asserts
	fwb_master #(.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH),
				.F_MAX_STALL(2),
				.F_MAX_REQUESTS(0), .F_OPT_SOURCE(1),
				.F_OPT_CLK2FFLOGIC(F_OPT_CLK2FFLOGIC),
				.F_OPT_RMW_BUS_OPTION(1),
				.F_OPT_DISCONTINUOUS(0))
		f_wbm(i_clk, i_reset,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding);

`endif

//
// Now, apply the following to Verilator *or* yosys-smtbmc
//
`ifdef	VERILATOR_FORMAL
	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our interaction with the CPU
	//
	//
	/////////////////////////////////////////////////

	// Assume that any reset is either accompanied by a new address,
	// or a new address immediately follows it.
	always @(posedge i_clk)
		if ((f_past_valid)&&(f_past_reset))
			assume(i_new_pc);

	always @(posedge i_clk)
	if (f_past_clear_cache)
		assume(!i_clear_cache);

	//
	//
	// The bottom two bits of the PC address register are always zero.
	// They are there to make examining traces easier, but I expect
	// the synthesis tool to remove them.
	//
	always @(*)
		assume(i_pc[1:0] == 2'b00);

	// Some things to know from the CPU ... there will always be a
	// i_new_pc request following any reset
	always @(posedge i_clk)
		if ((f_past_valid)&&(f_past_reset))
			assume(i_new_pc);

	// There will also be a i_new_pc request following any request to clear
	// the cache.
	always @(posedge i_clk)
		if ((f_past_valid)&&(f_past_clear_cache))
			assume(i_new_pc);

	always @(posedge i_clk)
	if (f_past_clear_cache)
		assume(!i_clear_cache);

	always @(*)
		assume(i_pc[1:0] == 2'b00);
`endif

`ifdef	FORMAL
	//
	// Let's make some assumptions about how long it takes our phantom
	// (i.e. assumed) CPU to respond.
	//
	// This delay needs to be long enough to flush out any potential
	// errors, yet still short enough that the formal method doesn't
	// take forever to solve.
	//
`ifdef	DBLFETCH
	localparam	F_CPU_DELAY = 4;
	reg	[4:0]	f_cpu_delay;

	// Now, let's look at the delay the CPU takes to accept an instruction.
	always @(posedge i_clk)
		// If no instruction is ready, then keep our counter at zero
		if ((!o_valid)||(i_stall_n))
			f_cpu_delay <= 0;
		else
			// Otherwise, count the clocks the CPU takes to respond
			f_cpu_delay <= f_cpu_delay + 1'b1;

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
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_stb))&&(!$past(i_wb_stall))
			&&(!$past(i_new_pc)))
		assert(o_wb_addr <= $past(o_wb_addr)+1'b1);

	//
	// Assertions about our return responses to the CPU
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!$past(i_stall_n)))
	begin
		assert($stable(o_pc));
		assert($stable(o_insn));
		assert($stable(o_valid));
		assert($stable(o_illegal));
	end

	// The same is true of the cache as well.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!$past(i_stall_n))
			&&($past(cache_valid)))
	begin
		assert($stable(cache_valid));
		assert($stable(cache_word));
		assert($stable(cache_illegal));
	end

	// Consider it invalid to present the CPU with the same instruction
	// twice in a row.  Any effort to present the CPU with the same
	// instruction twice in a row must go through i_new_pc, and thus a
	// new bus cycle--hence the assertion below makes sense.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_new_pc))
			&&($past(o_valid))&&($past(i_stall_n)))
		assert(o_pc[AW+1:2] == $past(o_pc[AW+1:2])+1'b1);


	//
	// As with i_pc[1:0], the bottom two bits of the address are unused.
	// Let's assert here that they remain zero.
	always @(*)
		assert(o_pc[1:0] == 2'b00);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))
			&&(!$past(i_clear_cache))
			&&($past(o_wb_cyc))&&($past(i_wb_err)))
		assert( ((o_valid)&&(o_illegal))
			||((cache_valid)&&(cache_illegal)) );

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(o_illegal))&&(o_illegal))
		assert(o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(cache_illegal))&&(!cache_valid))
		assert(!cache_illegal);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_new_pc)))
		assert(!o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!o_valid)&&(!o_illegal))
		assert((o_wb_cyc)||(invalid_bus_cycle));

	/////////////////////////////////////////////////
	//
	//
	// Our "contract" with the CPU
	//
	//
	/////////////////////////////////////////////////
	//
	// For any particular address, that address is associated with an
	// instruction and a flag regarding whether or not it is illegal.
	//
	// Any attempt to return to the CPU a value from this address,
	// must return the value and the illegal flag.
	//
	wire	[AW-1:0]	f_const_addr;
	wire	[DW-1:0]	f_const_insn;
	wire			f_const_illegal;

	//
	// Here's the illegal flag, address in question, and the instruction
	// at that address.
	//
	assign	f_const_addr    = $anyconst;
	assign	f_const_insn    = $anyconst;
	assign	f_const_illegal = $anyconst;

	//
	// While these wires may seem like overkill, and while they make the
	// following logic perhaps a bit more obscure, these predicates make
	// it easier to follow the complex logic on a scope.  They don't
	// affect anything synthesized.
	//
	wire	f_this_addr, f_this_pc, f_this_req, f_this_data,
		f_this_insn;

	assign	f_this_addr = (o_wb_addr ==   f_const_addr);
	assign	f_this_pc   = (o_pc      == { f_const_addr, 2'b00 });
	assign	f_this_req  = (i_pc      == { f_const_addr, 2'b00 });
	assign	f_this_data = (i_wb_data ==   f_const_insn);
	assign	f_this_insn = (o_insn    ==   f_const_insn);


	//
	//
	// Here's our contract:
	//
	// Any time we return a value for the address above, it *must* be
	// the "right" value.
	//
	always @(*)
	if ((o_valid)&&(f_this_pc))
	begin
		if (f_const_illegal)
			assert(o_illegal);
		if (!o_illegal)
			assert(f_this_insn);
	end

	//
	// The contract will only work if we assume the return from the
	// bus at this address will be the right return.
	wire	f_this_return;
	assign	f_this_return = (o_wb_addr - f_outstanding == f_const_addr);
	always @(*)
	if ((o_wb_cyc)&&(f_this_return))
	begin
		if (i_wb_ack)
			assume(i_wb_data == f_const_insn);

		if (f_const_illegal)
			assume(!i_wb_ack);
		else
			assume(!i_wb_err);
	end

	//
	// Here is a corrollary to our contract.  Anything in the one-word
	// cache must also match the contract as well.
	//
	always @(*)
	if ((o_pc[AW+1:2] + 1'b1 == f_const_addr)&&(cache_valid))
	begin
		if (!cache_illegal)
			assert(cache_word == f_const_insn);

		if (f_const_illegal)
			assert(cache_illegal);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(cache_illegal))&&(!cache_valid))
		assert(!cache_illegal);

	////////////////////////////////////////////////////////
	//
	//
	// Additional assertions necessary to pass induction
	//
	//
	////////////////////////////////////////////////////////
	//
	// We have only a one word cache.  Hence, we shouldn't be asking
	// for more data any time we have nowhere to put it.
	always @(*)
	if (o_wb_stb)
		assert((!cache_valid)||(i_stall_n));

	always @(*)
	if ((o_valid)&&(cache_valid))
		assert((f_outstanding == 0)&&(!o_wb_stb));

	always @(*)
	if ((o_valid)&&(!i_stall_n))
		assert(f_outstanding < 2);

	always @(*)
	if ((!o_valid)||(i_stall_n))
		assert(f_outstanding <= 2);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc))&&(!$past(o_wb_stb))
			&&(o_wb_cyc))
		assert(inflight != 0);

	always @(*)
	if ((o_wb_cyc)&&(i_wb_ack))
		assert(!cache_valid);

	always @(posedge i_clk)
	if (o_wb_cyc)
		assert(inflight == f_outstanding);

	wire	[AW-1:0]	this_return_address,
				next_pc_address;
	assign	this_return_address = o_wb_addr - f_outstanding;
	assign	next_pc_address = o_pc[AW+1:2] + 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc))
			&&(!$past(i_reset))
			&&(!$past(i_new_pc))
			&&(!$past(i_clear_cache))
			&&(!$past(invalid_bus_cycle))
			&&(($past(i_wb_ack))||($past(i_wb_err)))
			&&((!$past(o_valid))||($past(i_stall_n)))
			&&(!$past(cache_valid)))
		assert(o_pc[AW+1:2] == $past(this_return_address));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc))&&(!o_valid)&&(!$past(i_new_pc))
			&&(o_wb_cyc))
		assert(o_pc[AW+1:2] == this_return_address);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc))
			&&(!$past(cache_valid))&&(cache_valid))
		assert(next_pc_address == $past(this_return_address));



	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc))&&(o_wb_cyc))
	begin
		if ((o_valid)&&(!cache_valid))
			assert(this_return_address == next_pc_address);
		else if (!o_valid)
			assert(this_return_address == o_pc[AW+1:2]);
	end else if ((f_past_valid)&&(!invalid_bus_cycle)
			&&(!o_wb_cyc)&&(o_valid)&&(!o_illegal)
			&&(!cache_valid))
		assert(o_wb_addr == next_pc_address);


	always @(*)
	if (invalid_bus_cycle)
		assert(!o_wb_cyc);
	always @(*)
	if (cache_valid)
		assert(o_valid);

	/////////////////////////////////////////////////////
	//
	//
	// Cover statements
	//
	//
	/////////////////////////////////////////////////////

	always @(posedge i_clk)
	cover((f_past_valid)&&($past(f_nacks)==3)
		&&($past(i_wb_ack))&&($past(o_wb_cyc)));


	/////////////////////////////////////////////////////
	//
	//
	// Temporary simplifications
	//
	//
	/////////////////////////////////////////////////////

//	always @(*)
//		assume((!i_wb_err)&&(!f_const_illegal));


`endif	// FORMAL
endmodule
//
// Usage:		(this)	(prior)	(old)  (S6)
//    Cells		374	387	585	459
//	FDRE		135	108	203	171
//	LUT1		  2	  3	  2
//	LUT2		  9	  3	  4	  5
//	LUT3		 98	 76	104	 71
//	LUT4		  2	  0	  2	  2
//	LUT5		  3	 35	 35	  3
//	LUT6		  6	  5	 10	 43
//	MUXCY		 58	 62	 93	 62
//	MUXF7		  1	  0	  2	  3
//	MUXF8		  0	  1	  1
//	RAM64X1D	  0	 32	 32	 32
//	XORCY		 60	 64	 96	 64
//
