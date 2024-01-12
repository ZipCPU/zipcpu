////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dblfetch.v
// {{{
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
// }}}
// Copyright (C) 2017-2024, Gisselquist Technology, LLC
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
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	dblfetch #(
		// {{{
		parameter		ADDRESS_WIDTH=30,	// Byte addr
		parameter		INSN_WIDTH=32,
		parameter		DATA_WIDTH = INSN_WIDTH,
		localparam		AW=ADDRESS_WIDTH,
					DW=DATA_WIDTH,
		parameter	[0:0]	OPT_LITTLE_ENDIAN = 1'b1
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// CPU signals--from the CPU
		input	wire			i_new_pc, i_clear_cache,i_ready,
		input	wire	[AW-1:0]	i_pc,
		// ... and in return
		output	reg			o_valid,
		output	reg			o_illegal,
		output	reg [INSN_WIDTH-1:0]	o_insn,
		output	reg	[AW-1:0]	o_pc,
		// Wishbone outputs
		output	reg			o_wb_cyc, o_wb_stb,
		// verilator coverage_off
		output	wire			o_wb_we,
		// verilator coverage_on
		output	reg [AW-$clog2(DW/8)-1:0] o_wb_addr,
		// verilator coverage_off
		output	wire	[DW-1:0]	o_wb_data,
		// verilator coverage_on
		// And return inputs
		input	wire			i_wb_stall, i_wb_ack, i_wb_err,
		input	wire	[DW-1:0]	i_wb_data
		// }}}
	);

	// Local declarations
	// {{{
	wire			last_stb;
	reg			invalid_bus_cycle;

	reg	[(DW-1):0]	cache_word;
	reg			cache_valid;
	reg	[1:0]		inflight;
	reg			cache_illegal;

	wire				r_valid;
	wire	[DATA_WIDTH-1:0]	r_insn, i_wb_shifted;
	// }}}

	assign	o_wb_we = 1'b0;
	assign	o_wb_data = {(DATA_WIDTH){1'b0}};

	// o_wb_cyc, o_wb_stb
	// {{{
	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_clear_cache || (o_wb_cyc && i_wb_err))
	begin : RESET_ABORT
		// {{{
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
		// }}}
	end else if (o_wb_cyc)
	begin : END_CYCLE
		// {{{
		if (!o_wb_stb || !i_wb_stall)
			o_wb_stb <= (!last_stb);

		// Relase the bus on the second ack
		if ((!o_wb_stb || !i_wb_stall) && last_stb
			&& inflight + (o_wb_stb ? 1:0) == (i_wb_ack ? 1:0))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end

		if (i_new_pc) // || i_clear_cache)
			{ o_wb_cyc, o_wb_stb } <= 2'b0;
		// }}}
	end else if ((i_new_pc || invalid_bus_cycle)
		||(o_valid && i_ready && !r_valid && !cache_illegal))
	begin : START_CYCLE
		// {{{
		// Initiate a bus cycle if ... the last bus cycle was
		// aborted (bus error or new_pc), we've been given a
		// new PC to go get, or we just exhausted our one
		// instruction cache
		o_wb_cyc <= 1'b1;
		o_wb_stb <= 1'b1;
		// }}}
	end
	// }}}

	// inflight
	// {{{
	initial	inflight = 2'b00;
	always @(posedge i_clk)
	if (!o_wb_cyc)
		inflight <= 2'b00;
	else begin
		case({ (o_wb_stb && !i_wb_stall), i_wb_ack })
		2'b01:	inflight <= inflight - 1'b1;
		2'b10:	inflight <= inflight + 1'b1;
		// If neither ack nor request, then no change.  Likewise
		// if we have both an ack and a request, there's no change
		// in the number of requests in flight.
		default: begin end
		endcase
	end
	// }}}

	// last_stb
	// {{{
	// assign last_stb = (inflight != 2'b00)||(o_valid&& (!i_ready||r_valid));
	assign	last_stb = (!o_wb_stb||!i_wb_stall)&&(inflight
		+ (o_wb_stb ? 1:0)
		+ (o_valid&&(!i_ready || r_valid)) >= 2'b10);
	// }}}

	// invalid_bus_cycle
	// {{{
	initial	invalid_bus_cycle = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		invalid_bus_cycle <= 1'b0;
	else if (o_wb_cyc && i_new_pc)
		invalid_bus_cycle <= 1'b1;
	else if (!o_wb_cyc)
		invalid_bus_cycle <= 1'b0;
	// }}}

	// o_wb_addr
	// {{{
	initial	o_wb_addr = {(AW-$clog2(DATA_WIDTH/8)){1'b1}};
	always @(posedge i_clk)
	if (i_new_pc)
		o_wb_addr <= i_pc[AW-1:$clog2(DATA_WIDTH/8)];
	// else if (i_clear_cache)
	//	o_wb_addr <= o_pc[AW-1:$clog2(DATA_WIDTH/8)];
	else if (o_wb_stb && !i_wb_stall)
		o_wb_addr <= o_wb_addr + 1'b1;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Now for the immediate output word to the CPU
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// This only applies when the bus size doesn't match the instruction
	// word size.  Here, we only support bus sizes greater than the
	// instruction word size.
`ifdef	FORMAL
	wire	[DATA_WIDTH-1:0]	f_bus_word;
`endif

	generate if (DATA_WIDTH > INSN_WIDTH)
	begin : GEN_SUBSHIFT
		// {{{
		localparam	NSHIFT = $clog2(DATA_WIDTH/INSN_WIDTH);

		reg			rg_valid;
		reg [DATA_WIDTH-1:0]	rg_insn;
		reg	[NSHIFT:0]	r_count;
		reg	[NSHIFT-1:0]	r_shift;

		// rg_valid
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_new_pc) // || i_clear_cache)
			rg_valid <= 1'b0;
		else if (r_valid)
			rg_valid <= !i_ready || (r_count > 1);
		else if (!o_valid || i_ready)
		begin
			rg_valid <= 1'b0;
			if (cache_valid)
				rg_valid <= 1'b1;
			if (o_wb_cyc && i_wb_ack && !(&r_shift))
				rg_valid <= 1'b1;
		end
		// }}}

		// rg_insn
		// {{{
		always @(posedge i_clk)
		if (!o_valid || i_ready)
		begin
			if (cache_valid && !r_valid)
			begin
				if (OPT_LITTLE_ENDIAN)
					rg_insn <= cache_word >> INSN_WIDTH;
				else
					rg_insn <= cache_word << INSN_WIDTH;
			end else if (i_wb_ack && !r_valid)
			begin
				rg_insn <= i_wb_data;
				if (OPT_LITTLE_ENDIAN)
					rg_insn <= i_wb_shifted >> INSN_WIDTH;
				else
					rg_insn <= i_wb_shifted << INSN_WIDTH;
			end else begin
				if (OPT_LITTLE_ENDIAN)
					rg_insn <= rg_insn >> INSN_WIDTH;
				else
					rg_insn <= rg_insn << INSN_WIDTH;
			end
		end
		// }}}

		// r_count
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_new_pc) // || i_clear_cache)
			r_count <= 0;
		else if (o_valid && i_ready && r_valid)
		begin
			r_count <= r_count - 1;
		end else if (!o_valid || (i_ready && !r_valid))
		begin
			if (cache_valid)
				r_count <= { 1'b0, {(NSHIFT){1'b1}} };
			else if (o_wb_cyc && i_wb_ack)
				r_count <= { 1'b0, ~r_shift };
		end
`ifdef	FORMAL
		always @(*)
		if (!i_reset && !i_new_pc && !i_clear_cache)
		begin
			if (!o_valid)
				assert(!r_valid);
			assert(r_valid == (r_count > 0));
			assert(r_count <= (1<<NSHIFT));
			if (r_valid)
			begin
				assert(!cache_valid || !o_wb_cyc);
				assert(r_shift == 0);
			end else if (!i_new_pc && !i_clear_cache && !o_illegal)
				assert(invalid_bus_cycle || o_valid || o_wb_cyc);
		end
`endif
		// }}}

		// r_shift
		// {{{
		always @(posedge i_clk)
		if (i_new_pc)
			r_shift <= i_pc[$clog2(DW/8)-1:$clog2(INSN_WIDTH/8)];
		// else if (i_clear_cache)
		//	r_shift <= o_pc[$clog2(DW/8)-1:$clog2(INSN_WIDTH/8)];
		else if (o_wb_cyc && (i_wb_ack || i_wb_err))
			r_shift <= 0;

`ifdef	FORMAL
		always @(*)
		if (!i_reset && r_shift > 0)
			assert(!o_valid && !r_valid);
`endif
		// }}}

		assign	r_valid = rg_valid;
		assign	r_insn  = rg_insn;
		if (OPT_LITTLE_ENDIAN)
		begin : GEN_LITTLE_ENDIAN_SHIFT
			assign	i_wb_shifted = i_wb_data >> (r_shift * INSN_WIDTH);
		end else begin : GEN_BIGENDIAN_SHIFT
			assign	i_wb_shifted = i_wb_data << (r_shift * INSN_WIDTH);
		end

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_shift;
		assign	unused_shift = &{ 1'b0,
				r_insn[DATA_WIDTH-1:INSN_WIDTH],
				i_wb_shifted[DATA_WIDTH-1:INSN_WIDTH] };
		// Verilator lint_on  UNUSED
		// }}}
`ifdef	FORMAL
		assign	f_bus_word = rg_insn << ((r_count-1)* INSN_WIDTH);
		always @(*)
		if (!i_reset && r_valid)
		begin
			assert(i_clear_cache || i_new_pc || o_valid);
			assert(r_shift == 0);
			assert((r_count + o_pc[$clog2(DW/8)-1:$clog2(INSN_WIDTH/8)])
				== ((1<<NSHIFT)-1));
		end else if (!i_reset && !o_valid && o_wb_cyc && !invalid_bus_cycle)
		begin
			assert(r_shift == o_pc[$clog2(DW/8)-1:$clog2(INSN_WIDTH/8)]);
		end
`endif
		// }}}
	end else begin : NO_SUBSHIFT
		// {{{
		assign	r_valid = 1'b0;
		assign	r_insn  = {(INSN_WIDTH){1'b0}};
		assign	i_wb_shifted = i_wb_data;
		// }}}
	end endgenerate

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_new_pc || i_clear_cache)
		o_valid <= 1'b0;
	else if (o_wb_cyc &&(i_wb_ack || i_wb_err))
		o_valid <= 1'b1;
	else if (i_ready)
		o_valid <= cache_valid || r_valid;
	// }}}

	// o_insn
	// {{{
	always @(posedge i_clk)
	if (!o_valid || i_ready)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			if (r_valid)
				o_insn <= r_insn[INSN_WIDTH-1:0];
			else if (cache_valid)
				o_insn <= cache_word[INSN_WIDTH-1:0];
			else
				o_insn <= i_wb_shifted[INSN_WIDTH-1:0];
		end else begin
			if (r_valid)
				o_insn <= r_insn[DW-1:DW-INSN_WIDTH];
			else if (cache_valid)
				o_insn <= cache_word[DW-1:DW-INSN_WIDTH];
			else
				o_insn <= i_wb_shifted[DW-1:DW-INSN_WIDTH];
		end
	end
	// }}}

	// o_pc
	// {{{
	always @(posedge i_clk)
	if (i_new_pc)
		o_pc <= i_pc;
	else if (o_valid && i_ready) // && !i_clear_cache
	begin
		o_pc <= 0;
		o_pc[AW-1:$clog2(INSN_WIDTH/8)]
			<= o_pc[AW-1:$clog2(INSN_WIDTH/8)] + 1'b1;
	end
	// }}}

	// o_illegal
	// {{{
	initial	o_illegal = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_new_pc || i_clear_cache)
		o_illegal <= 1'b0;
	else if (!r_valid && (!o_valid || i_ready) && !o_illegal)
	begin
		if (cache_valid)
			o_illegal <= cache_illegal;
		else if (o_wb_cyc && i_wb_err)
			o_illegal <= 1'b1;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Now for the output/cached word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// cache_valid
	// {{{
	initial	cache_valid = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(i_new_pc)||(i_clear_cache))
		cache_valid <= 1'b0;
	else begin
		if (o_valid && o_wb_cyc &&(i_wb_ack || i_wb_err))
			cache_valid <= !i_ready || r_valid;
		else if (i_ready && !r_valid)
			cache_valid <= 1'b0;
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset && cache_valid && o_wb_cyc)
		assert(!i_wb_ack && !i_wb_err);
`endif
	// }}}

	// cache_word
	// {{{
	always @(posedge i_clk)
	if (i_wb_ack)
		cache_word <= i_wb_data;
	// }}}

	// cache_illegal
	// {{{
	initial	cache_illegal = 1'b0;
	always @(posedge i_clk)
	if (i_reset || i_clear_cache || i_new_pc)
		cache_illegal <= 1'b0;
	// Older logic ...
	// else if ((o_wb_cyc)&&(i_wb_err)&&(o_valid)&&(!i_ready))
	//	cache_illegal <= 1'b1;
	else if (o_wb_cyc && i_wb_err)
			//  && o_valid && (!i_ready || r_valid))
		cache_illegal <= 1'b1;
	// }}}

	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Local declarations
	// {{{
	// Keep track of a flag telling us whether or not $past()
	// will return valid results
 	reg	f_past_valid;

	// Keep track of some alternatives to $past that can still be used
	// in a VERILATOR environment
	reg	[AW-1:0]	f_next_addr, f_dbl_next, f_cache_addr; //bytaddr
	localparam	F_LGDEPTH=2;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;
	wire		[AW-1:0]	f_const_addr;
	wire		[DW-1:0]	f_const_insn;
	wire				f_const_illegal;
	wire	f_this_pc,
		f_this_insn, f_this_return;
	wire	[AW-$clog2(DATA_WIDTH/8)-1:0]	this_return_address,
				f_const_bus_addr, next_pc_address;
	wire	[AW-1:0]	f_address;
	(* anyconst *)	wire	[DW-1:0]	f_const_bus_word;
	reg	[AW-$clog2(DW/8)-1:0]	pc_bus_addr, pc_bus_addr_next,
					pc_bus_addr_dbl;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	// }}}

	generate if (INSN_WIDTH == 8)
	begin : F_NEXT_BYTE_ADDR
		// {{{
		// BUS addresses
		always @(*)
			f_next_addr = o_pc + (r_valid ? 0:1);
		// }}}
	end else begin : F_NEXT_ADDR
		// {{{
		// BUS addresses
		always @(*)
		if (r_valid)
			f_next_addr = o_pc;
		else begin
			f_next_addr = o_pc + (INSN_WIDTH/8);
			f_next_addr[$clog2(INSN_WIDTH/8)-1:0] = 0;
		end
		// }}}
	end endgenerate

	always @(*)
	begin
		// BUS addresses
		f_dbl_next = f_next_addr + (DATA_WIDTH/8);
		if (r_valid)
			f_dbl_next = f_dbl_next + (DATA_WIDTH/8);
		f_dbl_next[$clog2(DATA_WIDTH/8)-1:0] = 0;

		f_cache_addr = o_pc + (DATA_WIDTH/8);
		f_cache_addr[$clog2(DATA_WIDTH/8)-1:0] = 0;
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	//

	//
	// Assume that resets, new-pc commands, and clear-cache commands
	// are never more than pulses--one clock wide at most.
	//
	// It may be that the CPU treats us differently.  We'll only restrict
	// our solver to this here.
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Add a bunch of wishbone-based asserts
	fwb_master #(
		// {{{
		.AW(AW-$clog2(DATA_WIDTH/8)), .DW(DW), .F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(2),
			.F_MAX_REQUESTS(0), .F_OPT_SOURCE(1),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(0)
		// }}}
	) f_wbm(
		// {{{
		i_clk, i_reset,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
				{(DW/8){1'b1}},
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our interaction with the CPU
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	ffetch #(
		// {{{
		.ADDRESS_WIDTH(AW-$clog2(INSN_WIDTH/8)),
		.INSN_WIDTH(INSN_WIDTH)
		// }}}
	) cpu(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.cpu_new_pc(i_new_pc), .cpu_clear_cache(i_clear_cache),
		.cpu_pc(i_pc), .pf_valid(o_valid), .cpu_ready(i_ready),
		.pf_pc(o_pc), .pf_insn(o_insn), .pf_illegal(o_illegal),
		.fc_illegal(f_const_illegal), .fc_insn(f_const_insn),
		.fc_pc(f_const_addr), .f_address(f_address)
		// }}}
	);

	assign	f_const_bus_addr = f_const_addr[AW-1:$clog2(DATA_WIDTH/8)];

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
	if ((!o_valid)||(i_ready))
		f_cpu_delay <= 0;
	else
		// Otherwise, count the clocks the CPU takes to respond
		f_cpu_delay <= f_cpu_delay + 1'b1;

	always @(posedge i_clk)
		assume(f_cpu_delay < F_CPU_DELAY);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our outputs
	// {{{
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_stb))&&(!$past(i_wb_stall))
			&&($past(!i_new_pc && !i_clear_cache)))
		assert(o_wb_addr <= $past(o_wb_addr)+1'b1);

	//
	// The cache doesn't change if we are stalled
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&(!$past(i_new_pc))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!$past(i_ready || r_valid))
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
	if ((f_past_valid)&& $past(!i_new_pc && !i_clear_cache)
			&&($past(o_valid && i_ready)))
		assert(o_pc == f_address);

	always @(posedge i_clk)
	if (!i_reset && !i_clear_cache && !i_new_pc)
		assert(o_pc == f_address);


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
	if (!i_reset && cache_illegal)
		assert(!o_wb_cyc);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_new_pc)))
		assert(!o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(i_clear_cache))
			&&($past(o_valid))&&(!o_valid)&&(!o_illegal))
		assert((o_wb_cyc)||(invalid_bus_cycle));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Our "contract" with the CPU
	// {{{
	//
	////////////////////////////////////////////////////////////////////////
	//
	// For any particular address, that address is associated with an
	// instruction and a flag regarding whether or not it is illegal.
	//
	// Any attempt to return to the CPU a value from this address,
	// must return the value and the illegal flag.
	//

	//
	// While these wires may seem like overkill, and while they make the
	// following logic perhaps a bit more obscure, these predicates make
	// it easier to follow the complex logic on a scope.  They don't
	// affect anything synthesized.
	//
	assign	f_this_pc   = (o_pc[AW-1:$clog2(INSN_WIDTH/8)]
				== f_const_addr[AW-1:$clog2(INSN_WIDTH/8)]);
	assign	f_this_insn = (o_insn    ==   f_const_insn);

	// Verilator lint_off WIDTH
	assign	f_this_return = (o_wb_addr - f_outstanding == f_const_addr[AW-1:$clog2(DATA_WIDTH/8)]);
	// Verilator lint_on  WIDTH


	//
	//
	// Here's our contract:
	//
	// Any time we return a value for the address above, it *must* be
	// the "right" value.
	//
	always @(*)
	if (o_valid && f_this_pc)
	begin
		if (f_const_illegal)
			assert(o_illegal);
		if (!o_illegal)
			assert(f_this_insn);
	end

	//
	// The contract will only work if we assume the return from the
	// bus at this address will be the right return.
	always @(*)
	if ((o_wb_cyc)&&(f_this_return))
	begin
		if (i_wb_ack)
			assume(i_wb_data == f_const_bus_word);

		if (f_const_illegal)
		begin
			assume(!i_wb_ack);
		end else
			assume(!i_wb_err);
	end

	generate if (INSN_WIDTH == DATA_WIDTH)
	begin : F_SAME_BUS_WORD
		// {{{
		always @(*)
			assume(f_const_bus_word == f_const_insn);
		// }}}
	end else begin : F_CHECK_SHIFTED_WORD
		// {{{
		wire	[DW-1:0]	f_shifted_insn;
		localparam		IW = INSN_WIDTH;

		if (OPT_LITTLE_ENDIAN)
		begin
			assign  f_shifted_insn = f_const_bus_word
				>> (f_const_addr[$clog2(DW/8)-1:$clog2(IW/8)] * IW);
			always @(*)
				assume(f_shifted_insn[IW-1:0] == f_const_insn);
			
		end else begin
			assign  f_shifted_insn = f_const_bus_word
				<< (f_const_addr[$clog2(DW/8)-1:$clog2(IW/8)] * IW);

			always @(*)
				assume(f_shifted_insn[DW-1:DW-IW]
					== f_const_insn);

		end
                // }}}
	end endgenerate

	//
	// Here is a corrollary to our contract.  Anything in the one-word
	// cache must also match the contract as well.
	//
	always @(*)
	if ((f_cache_addr[AW-1:$clog2(DATA_WIDTH/8)] == f_const_bus_addr)
			&&(cache_valid))
	begin
		if (!cache_illegal)
			assert(cache_word == f_const_bus_word);

		if (f_const_illegal)
			assert(cache_illegal);
		else
			assert(o_illegal || !cache_illegal);
	end

	// always @(posedge i_clk)
	// if ((f_past_valid)&&(!$past(cache_illegal))&&(!cache_valid))
	//	assert(!cache_illegal);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Additional assertions necessary to pass induction
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// We have only a one word cache.  Hence, we shouldn't be asking
	// for more data any time we have nowhere to put it.
	always @(*)
	if (o_wb_stb)
		assert(!cache_valid || i_ready);

	always @(*)
	if (o_valid && cache_valid)
		assert((f_outstanding == 0)&&(!o_wb_stb));

	always @(*)
	if (o_valid && (r_valid || !i_ready))
		assert(f_outstanding < 2);

	always @(*)
	if (!o_valid || (i_ready && !r_valid))
		assert(f_outstanding <= 2);

	// always @(posedge i_clk)
	// if ((f_past_valid)&&($past(o_wb_cyc && !o_wb_stb)) &&(o_wb_cyc))
	//	assert(inflight != 0);

	always @(*)
	if (o_wb_cyc && i_wb_ack)
		assert(!cache_valid);

	always @(posedge i_clk)
	if (o_wb_cyc)
		assert(inflight == f_outstanding);

	// Verilator lint_off WIDTH
	assign	this_return_address = o_wb_addr - f_outstanding;
	// Verilator lint_on  WIDTH
	assign	next_pc_address = f_next_addr[AW-1:$clog2(DATA_WIDTH/8)];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Address checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		pc_bus_addr      = o_pc[AW-1:$clog2(DW/8)];
		pc_bus_addr_next = pc_bus_addr + 1;
		pc_bus_addr_dbl  = pc_bus_addr + 2;
	end

	always @(*)
	if (i_reset || o_illegal || invalid_bus_cycle)
	begin
	end else if (!o_valid)
	begin
		if (o_wb_cyc)
		begin
			if (inflight == 0)
				assert(o_wb_addr == pc_bus_addr);
			assert(pc_bus_addr == this_return_address);
		end
	end else if (cache_valid || (o_wb_cyc && !o_wb_stb))
	begin
		assert(o_wb_addr == pc_bus_addr_dbl);
	end else if (o_valid)
		assert(o_wb_addr == pc_bus_addr_next);

	always @(posedge i_clk)
	if (f_past_valid &&($past(!i_reset && !i_new_pc && !i_clear_cache))
			&&(!$past(invalid_bus_cycle)))
	begin
		if (($past(o_wb_cyc && (i_wb_ack || i_wb_err)))
			&&($past(!o_valid || (i_ready && !r_valid)))
			&&(!$past(cache_valid)))
		begin
			assert(o_pc[AW-1:$clog2(DW/8)] == $past(this_return_address));
		end else if (cache_valid)
		begin
			assert(o_wb_addr == pc_bus_addr_dbl);
			assert(f_outstanding == 0);
		end else if (o_valid)
		begin
			if (f_outstanding == 0)
				assert(o_illegal || o_wb_addr == pc_bus_addr_next);
			else if (f_outstanding == 1)
				assert(o_illegal || o_wb_addr == pc_bus_addr_dbl);
			else if (f_outstanding == 2)
				assert(o_wb_addr == pc_bus_addr_dbl);
		end else if (o_wb_cyc)
			assert(o_pc[AW-1:$clog2(DW/8)] == this_return_address);
	end

	always @(posedge i_clk)
	if (!i_reset && o_illegal)
	begin
		assert(!o_wb_cyc);
		assert(cache_illegal);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc && !i_new_pc))&&(!o_valid)
			&&(o_wb_cyc))
		assert(o_pc[AW-1:$clog2(DW/8)] == this_return_address);

	always @(posedge i_clk)
	if (o_valid && !o_wb_cyc && !o_illegal)
	begin
		if (cache_valid)
			assert(f_dbl_next[AW-1:$clog2(DW/8)] == o_wb_addr);
		else
			assert(pc_bus_addr_next == o_wb_addr);

	end

	always @(*)
	if (o_wb_cyc || o_valid)
	begin
		assert(o_wb_addr == pc_bus_addr
			|| o_wb_addr == pc_bus_addr_next
			|| o_wb_addr == pc_bus_addr_dbl);
	end

//	always @(posedge i_clk)
//	if ((f_past_valid)&& $past(o_wb_cyc && !cache_valid) && cache_valid)
//		assert(next_pc_address == $past(this_return_address));

	//
	//

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc))&&(o_wb_cyc))
	begin
		if (o_valid && !cache_valid)
		begin
			// assert(this_return_address == next_pc_address);
		end else if (!o_valid)
			assert(this_return_address == o_pc[AW-1:$clog2(DW/8)]);
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
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover statements
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_cvr_aborted, f_cvr_fourth_ack;

	always @(posedge i_clk)
	cover((f_past_valid)&&($past(f_nacks)==3)
		&&($past(i_wb_ack))&&($past(o_wb_cyc)));

	initial	f_cvr_aborted = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_cvr_aborted <= 0;
	else if (!o_wb_cyc && (f_nreqs != f_nacks))
		f_cvr_aborted <= 1;

	initial	f_cvr_fourth_ack = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_cvr_fourth_ack <= 0;
	else if ((f_nacks == 3)&&(o_wb_cyc && i_wb_ack))
		f_cvr_fourth_ack <= 1;

	always @(posedge i_clk)
		cover(!o_wb_cyc && (f_nreqs == f_nacks)
			&& !f_cvr_aborted && f_cvr_fourth_ack);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Temporary simplifications
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}

	// Make Verilator happy -- formal section
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ f_dbl_next[1:0], f_const_addr[1:0] };
	// Verilator lint_on  UNUSED
	// }}}
`endif	// FORMAL
// }}}
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
