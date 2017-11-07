////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pfcache.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Keeping our CPU fed with instructions, at one per clock and
//		with no stalls.  An unusual feature of this cache is the
//	requirement that the entire cache may be cleared (if necessary).
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
module	pfcache(i_clk, i_rst, i_new_pc, i_clear_cache,
			// i_early_branch, i_from_addr,
			i_stall_n, i_pc, o_i, o_pc, o_v,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
			o_illegal);
	parameter	LGCACHELEN = 5, ADDRESS_WIDTH=24,
			LGLINES=2; // Log of the number of separate cache lines
	localparam	CACHELEN=(1<<LGCACHELEN); // Size of our cache memory
	localparam	CW=LGCACHELEN;	// Short hand for LGCACHELEN
	localparam	PW=LGCACHELEN-LGLINES; // Size of a cache line
	localparam	BUSW = 32;	// Number of data lines on the bus
	localparam	AW=ADDRESS_WIDTH; // Shorthand for ADDRESS_WIDTH
	input	wire			i_clk, i_rst, i_new_pc;
	input	wire			i_clear_cache;
	input	wire			i_stall_n;
	input	wire	[(AW-1):0]	i_pc;
	output	wire	[(BUSW-1):0]	o_i;
	output	wire	[(AW-1):0]	o_pc;
	output	wire			o_v;
	//
	output	reg		o_wb_cyc, o_wb_stb;
	output	wire		o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	wire	[(BUSW-1):0]	o_wb_data;
	//
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(BUSW-1):0]	i_wb_data;
	//
	output	reg			o_illegal;

	// Fixed bus outputs: we read from the bus only, never write.
	// Thus the output data is ... irrelevant and don't care.  We set it
	// to zero just to set it to something.
	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 0;

	wire			r_v;
	reg	[(BUSW-1):0]	cache	[0:((1<<CW)-1)];
	reg	[(AW-CW-1):0]	tags	[0:((1<<(LGLINES))-1)];
	reg	[((1<<(LGLINES))-1):0]	vmask;

	reg	[(AW-1):0]	lastpc;
	reg	[(CW-1):0]	rdaddr;
	reg	[(AW-1):CW]	tagvalipc, tagvallst;
	wire	[(AW-1):CW]	tagval;
	wire	[(AW-1):PW]	lasttag;
	reg			illegal_valid;
	reg	[(AW-1):PW]	illegal_cache;

	// initial	o_i = 32'h76_00_00_00;	// A NOOP instruction
	// initial	o_pc = 0;
	reg	[(BUSW-1):0]	r_pc_cache, r_last_cache;
	reg	[(AW-1):0]	r_pc, r_lastpc;
	reg	isrc;
	always @(posedge i_clk)
	begin
		// We don't have the logic to select what to read, we must
		// read both the value at i_pc and lastpc.  cache[i_pc] is
		// the value we return if the cache is good, cacne[lastpc] is
		// the value we return if we've been stalled, weren't valid,
		// or had to wait a clock or two.  (Remember i_pc can't stop
		// changing for a clock, so we need to keep track of the last
		// one from before it stopped.)
		//
		// Here we keep track of which answer we want/need
		isrc <= ((r_v)&&(i_stall_n))||(i_new_pc);

		// Here we read both, and select which was write using isrc
		// on the next clock.
		r_pc_cache <= cache[i_pc[(CW-1):0]];
		r_last_cache <= cache[lastpc[(CW-1):0]];
		r_pc <= i_pc;
		r_lastpc <= lastpc;
	end
	assign	o_pc = (isrc) ? r_pc : r_lastpc;
	assign	o_i  = (isrc) ? r_pc_cache : r_last_cache;

	reg	tagsrc;
	always @(posedge i_clk)
		// It may be possible to recover a clock once the cache line
		// has been filled, but our prior attempt to do so has lead
		// to a race condition, so we keep this logic simple.
		if (((r_v)&&(i_stall_n))||(i_clear_cache)||(i_new_pc))
			tagsrc <= 1'b1;
		else
			tagsrc <= 1'b0;
	initial	tagvalipc = 0;
	always @(posedge i_clk)
		tagvalipc <= tags[i_pc[(CW-1):PW]];
	initial	tagvallst = 0;
	always @(posedge i_clk)
		tagvallst <= tags[lastpc[(CW-1):PW]];
	assign	tagval = (tagsrc)?tagvalipc : tagvallst;

	// i_pc will only increment when everything else isn't stalled, thus
	// we can set it without worrying about that.   Doing this enables
	// us to work in spite of stalls.  For example, if the next address
	// isn't valid, but the decoder is stalled, get the next address
	// anyway.
	initial	lastpc = 0;
	always @(posedge i_clk)
		if (((r_v)&&(i_stall_n))||(i_clear_cache)||(i_new_pc))
			lastpc <= i_pc;

	assign	lasttag = lastpc[(AW-1):PW];

	wire	w_v_from_pc, w_v_from_last;
	assign	w_v_from_pc = ((i_pc[(AW-1):PW] == lasttag)
				&&(tagvalipc == i_pc[(AW-1):CW])
				&&(vmask[i_pc[(CW-1):PW]]));
	assign	w_v_from_last = (
				//(lastpc[(AW-1):PW] == lasttag)&&
				(tagval == lastpc[(AW-1):CW])
				&&(vmask[lastpc[(CW-1):PW]]));

	reg	[1:0]	delay;

	initial	delay = 2'h3;
	reg	rvsrc;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_cache)||(i_new_pc)||((r_v)&&(i_stall_n)))
		begin
			// r_v <= r_v_from_pc;
			rvsrc <= 1'b1;
			delay <= 2'h2;
		end else if (!r_v) begin // Otherwise, r_v was true and we were
			// stalled, hence only if ~r_v
			rvsrc <= 1'b0;
			if (o_wb_cyc)
				delay <= 2'h2;
			else if (delay != 0)
				delay <= delay + 2'b11; // i.e. delay -= 1;
		end
	reg	r_v_from_pc, r_v_from_last;
	reg	r_new_request;
	wire	w_new_request;
	initial	r_new_request = 0;
	assign	w_new_request = (i_rst)||(i_new_pc)||(i_clear_cache);
	always @(posedge i_clk)
		r_new_request <= w_new_request;
	always @(posedge i_clk)
		r_v_from_pc   <= (w_v_from_pc)&&(!w_new_request);
	always @(posedge i_clk)
		r_v_from_last <= (w_v_from_last)&&(!w_new_request);

	assign	r_v = ((rvsrc)?(r_v_from_pc):(r_v_from_last))&&(!r_new_request);
	assign	o_v = (((rvsrc)?(r_v_from_pc):(r_v_from_last))
				||((o_illegal)&&(!o_wb_cyc)))
			&&(!i_new_pc)&&(!i_rst)&&(!i_clear_cache);

	reg	last_ack;
	initial	last_ack = 1'b0;
	always @(posedge i_clk)
		last_ack <= (o_wb_cyc)&&(
				(rdaddr[(PW-1):1]=={(PW-1){1'b1}})
				&&((rdaddr[0])||(i_wb_ack)));

	reg	needload;
	initial	needload = 1'b0;
	always @(posedge i_clk)
		needload <= ((!r_v)&&(delay==0)
			&&((tagvallst != lastpc[(AW-1):CW])
				||(!vmask[lastpc[(CW-1):PW]]))
			&&((!illegal_valid)
				||(lastpc[(AW-1):PW] != illegal_cache)));

	reg	last_addr;
	initial	last_addr = 1'b0;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			last_addr <= 1'b0;
		else if ((o_wb_addr[(PW-1):1] == {(PW-1){1'b1}})
				&&((!i_wb_stall)|(o_wb_addr[0])))
			last_addr <= 1'b1;

	reg	bus_abort;
	always @(posedge i_clk)
		if (!o_wb_cyc)
			bus_abort <= 1'b0;
		else if (i_clear_cache)
			bus_abort <= 1'b1;

	initial	o_wb_cyc  = 1'b0;
	initial	o_wb_stb  = 1'b0;
	initial	o_wb_addr = {(AW){1'b0}};
	initial	rdaddr    = 0;
	always @(posedge i_clk)
		if (i_rst)
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end else if (o_wb_cyc)
		begin
			if (i_wb_err)
				o_wb_stb <= 1'b0;
			else if ((o_wb_stb)&&(!i_wb_stall)&&(last_addr))
				o_wb_stb <= 1'b0;

			if (((i_wb_ack)&&(last_ack))||(i_wb_err))
				o_wb_cyc <= 1'b0;

			// else if (rdaddr[(PW-1):1] == {(PW-1){1'b1}})
			//	tags[lastpc[(CW-1):PW]] <= lastpc[(AW-1):CW];

		end else if (needload)
		begin
			o_wb_cyc  <= 1'b1;
			o_wb_stb  <= 1'b1;
		end

	always @(posedge i_clk)
		if ((o_wb_cyc)&&(!last_addr))
			tags[o_wb_addr[(CW-1):PW]] <= o_wb_addr[(AW-1):CW];
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			rdaddr <= rdaddr + 1;
		else if (!o_wb_cyc)
			rdaddr <= { lastpc[(CW-1):PW], {(PW){1'b0}} };
			
	always @(posedge i_clk)
		if ((o_wb_stb)&&(!i_wb_stall)&&(!last_addr))
			o_wb_addr[(PW-1):0] <= o_wb_addr[(PW-1):0]+1;
		else if (!o_wb_cyc)
			o_wb_addr <= { lastpc[(AW-1):PW], {(PW){1'b0}} };

	// Can't initialize an array, so leave cache uninitialized
	// We'll also never get an ack without sys being active, so skip
	// that check.  Or rather, let's just use o_wb_cyc instead.  This
	// will work because multiple writes to the same address, ending with
	// a valid write, aren't a problem.
	always @(posedge i_clk)
		if (o_wb_cyc) // &&(i_wb_ack)
			cache[rdaddr] <= i_wb_data;

	// VMask ... is a section loaded?
	// Note "svmask".  It's purpose is to delay the vmask setting by one
	// clock, so that we can insure the right value of the cache is loaded
	// before declaring that the cache line is valid.  Without this, the
	// cache line would get read, and the instruction would read from the
	// last cache line.
	reg	svmask;
	initial	vmask = 0;
	initial	svmask = 1'b0;
	reg	[(LGLINES-1):0]	saddr;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_cache))
		begin
			vmask <= 0;
			svmask<= 1'b0;
		end
		else begin
			svmask <= ((o_wb_cyc)&&(i_wb_ack)&&(last_ack));
			
			if (svmask)
				vmask[saddr] <= (!bus_abort);
			if ((!o_wb_cyc)&&(needload))
				vmask[lastpc[(CW-1):PW]] <= 1'b0;
		end
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			saddr <= rdaddr[(CW-1):PW];

	initial	illegal_cache = 0;
	initial	illegal_valid = 0;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_cache))
		begin
			illegal_cache <= 0;
			illegal_valid <= 0;
		end else if ((o_wb_cyc)&&(i_wb_err))
		begin
			illegal_cache <= o_wb_addr[(AW-1):PW];
			illegal_valid <= 1'b1;
		end

	initial o_illegal = 1'b0;
	always @(posedge i_clk)
		if ((w_new_request)||(o_wb_cyc))
			o_illegal <= 1'b0;
		else
			o_illegal <= (illegal_valid)
				&&(illegal_cache == i_pc[(AW-1):PW]);

`ifdef	FORMAL
//
//
// Generic setup
//
//
`ifdef	PFCACHE
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


`ifdef	PFCACHE
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

	// Assume that any reset is either accompanied by a new address,
	// or a new address immediately follows it.
	always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_rst)))
			`ASSUME((i_new_pc)||($past(i_new_pc)));
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

	// Now, let's repeat this bit but now looking at the delay the CPU
	// takes to accept an instruction.
	always @(posedge i_clk)
		// If no instruction is ready, then keep our counter at zero
		if ((!o_v)||(i_stall_n))
			f_cpu_delay <= 0;
		else
			// Otherwise, count the clocks the CPU takes to respond
			f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	PFCACHE
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

	localparam	F_LGDEPTH=PW+1;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;

	formal_master #(.AW(AW), .DW(BUSW), .F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(2), .F_MAX_ACK_DELAY(3),
			.F_MAX_REQUESTS((1<<PW)-1), .F_OPT_SOURCE(1),
			.F_OPT_RMW_BUS_OPTION(0),
			.F_OPT_DISCONTINUOUS(0))
		f_wbm(i_clk, i_rst,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding);

	// writes are also illegal for a prefetch.
	always @(posedge i_clk)
		if (o_wb_stb)
			assert(!o_wb_we);

	always @(posedge i_clk)
	begin
		assert(f_nreqs <= (1<<PW));
		if ((o_wb_cyc)&&(o_wb_stb))
			assert(f_nreqs == o_wb_addr[(PW-1):0]);
		if ((f_past_valid)&&($past(o_wb_cyc))
			&&(!o_wb_stb)&&(!$past(i_wb_err))&&(!$past(i_rst)))
			assert(f_nreqs == (1<<PW));
	end

	always @(posedge i_clk)
	begin
		if ((!o_wb_cyc)&&($past(o_wb_cyc))&&(!$past(i_rst))
				&&(!$past(i_wb_err)))
			`ASSUME(f_nacks == (1<<PW));
		else if (o_wb_cyc)
			assert(f_nacks[(PW-1):0] == rdaddr);

	end

	// The last-ack line
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(f_nreqs != (1<<PW)))
			assert(!last_ack);

	/////////////////////////////////////////////////////
	//
	//
	// Assertions about our return responses to the CPU
	//
	//
	/////////////////////////////////////////////////////

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

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc)))
		assert(o_wb_addr[(AW-1):PW] == $past(o_wb_addr[(AW-1):PW]));

	// Consider it invalid to present the CPU with the same instruction
	// twice in a row.
	always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_v))&&($past(i_stall_n))&&(o_v))
			assert(o_pc != $past(o_pc));

	always @(posedge i_clk)
	if (o_v)
	begin
		assert(tags[o_pc[(CW-1):PW]] == o_pc[(AW-1):CW]);
		assert(vmask[o_pc[(CW-1):PW]]);
		assert(o_i == cache[o_pc[(CW-1):0]]);
		assert(o_illegal == (illegal_cache == o_pc[(AW-1):PW]));
	end

	always @(posedge i_clk)
		if ((f_past_valid)&&(o_v)&&($past(o_v))
			&&(!$past(i_rst))
			&&(!$past(i_new_pc))
			&&(!$past(i_stall_n)))
		begin
			assert(tags[o_pc[(CW-1):PW]] == o_pc[(AW-1):CW]);
		end

`endif	// FORMAL

endmodule
