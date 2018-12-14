////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pfcache.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Keeping our CPU fed with instructions, at one per clock and
//		with only a minimum number stalls.  The entire cache may also
//	be cleared (if necessary).
//
//	This logic is driven by a couple realities:
//	1. It takes a clock to read from a block RAM address, and hence a clock
//		to read from the cache.
//	2. It takes another clock to check that the tag matches
//
//		Our goal will be to avoid this second check if at all possible.
//		Hence, we'll test on the clock of any given request whether
//		or not the request matches the last tag value, and on the next
//		clock whether it new tag value (if it has changed).  Hence,
//		for anything found within the cache, there will be a one
//		cycle delay on any branch.
//
//
//	Address Words are separated into three components:
//	[ Tag bits ] [ Cache line number ] [ Cache position w/in the line ]
//
//	On any read from the cache, only the second two components are required.
//	On any read from memory, the first two components will be fixed across
//	the bus, and the third component will be adjusted from zero to its
//	maximum value.
//
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
module	pfcache(i_clk, i_reset, i_new_pc, i_clear_cache,
			// i_early_branch, i_from_addr,
			i_stall_n, i_pc, o_insn, o_pc, o_valid,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
			o_illegal
`ifdef	NOT_YET_READY
		, i_mmu_ack, i_mmu_we, i_mmu_paddr
`endif
`ifdef	FORMAL
		, f_pc_wb
`endif
		);
`ifdef	FORMAL
	parameter	LGCACHELEN = 4, ADDRESS_WIDTH=30,
			LGLINES=2; // Log of the number of separate cache lines
`else
	parameter	LGCACHELEN = 12, ADDRESS_WIDTH=30,
			LGLINES=6; // Log of the number of separate cache lines
`endif
	localparam	CACHELEN=(1<<LGCACHELEN); //Wrd Size of our cache memory
	localparam	CW=LGCACHELEN;	// Short hand for LGCACHELEN
	localparam	LS=LGCACHELEN-LGLINES; // Size of a cache line
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
	output	reg			o_wb_cyc, o_wb_stb;
	output	wire			o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	wire	[(BUSW-1):0]	o_wb_data;
	//
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(BUSW-1):0]	i_wb_data;
	//
	// o_illegal will be true if this instruction was the result of a
	// bus error (This is also part of the CPU interface)
	output	reg			o_illegal;
	//
`ifdef	NOT_YET_READY
	input	wire			i_mmu_ack, i_mmu_we;
	input	wire	[(PAW-1):0]	i_mmu_paddr;
`endif

	// Fixed bus outputs: we read from the bus only, never write.
	// Thus the output data is ... irrelevant and don't care.  We set it
	// to zero just to set it to something.
	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 0;

`ifdef	NOT_YET_READY
	// These wires will be used below as part of the cache invalidation
	// routine, should the MMU be used.  This allows us to snoop on the
	// physical side of the MMU bus, and invalidate any results should
	// we need to do so.
	wire			mmu_inval;
	wire	[(PAW-CW-1):0]	mmu_mskaddr;
`endif
`ifdef	FORMAL
	output	wire	[AW-1:0]	f_pc_wb;
	assign	f_pc_wb = i_pc[AW+1:2];
`endif


	wire			r_v;
	reg	[(BUSW-1):0]	cache	[0:((1<<CW)-1)];
	reg	[(AW-CW-1):0]	cache_tags	[0:((1<<(LGLINES))-1)];
	reg	[((1<<(LGLINES))-1):0]	valid_mask;

	reg			r_v_from_pc, r_v_from_last, r_new_request;
	reg			rvsrc;
	wire			w_v_from_pc, w_v_from_last;
	reg	[(AW+1):0]	lastpc;
	reg	[(CW-1):0]	wraddr;
	reg	[(AW-1):CW]	tagvalipc, tagvallst;
	wire	[(AW-1):CW]	tagval;
	wire	[(AW-1):LS]	lasttag;
	reg			illegal_valid;
	reg	[(AW-1):LS]	illegal_cache;

	// initial	o_i = 32'h76_00_00_00;	// A NOOP instruction
	// initial	o_pc = 0;
	reg	[(BUSW-1):0]	r_pc_cache, r_last_cache;
	reg	[(AW+1):0]	r_pc, r_lastpc;
	reg			isrc;
	reg	[1:0]		delay;
	reg			svmask, last_ack, needload, last_addr,
				bus_abort;
	reg	[(LGLINES-1):0]	saddr;

	wire			w_advance;
	assign	w_advance = (i_new_pc)||((r_v)&&(i_stall_n));

	/////////////////////////////////////////////////
	//
	// Read the instruction from the cache
	//
	/////////////////////////////////////////////////
	//
	//
	// We'll read two values from the cache, the first is the value if
	// i_pc contains the address we want, the second is the value we'd read
	// if lastpc (i.e. $past(i_pc)) was the address we wanted.
	initial	r_pc = 0;
	initial	r_lastpc = 0;
	always @(posedge i_clk)
	begin
		// We don't have the logic to select what to read, we must
		// read both the value at i_pc and lastpc.  cache[i_pc] is
		// the value we return if the last cache request was in the
		// cache on the last clock, cacne[lastpc] is the value we
		// return if we've been stalled, weren't valid, or had to wait
		// a clock or two.
		//
		// Part of the issue here is that i_pc is going to increment
		// on this clock before we know whether or not the cache entry
		// we've just read is valid.  We can't stop this.  Hence, we
		// need to read from the lastpc entry.
		//
		//
		// Here we keep track of which answer we want/need.
		// If we reported a valid value to the CPU on the last clock,
		// and the CPU wasn't stalled, then we want to use i_pc.
		// Likewise if the CPU gave us an i_new_pc request, then we'll
		// want to return the value associated with reading the cache
		// at i_pc.
		isrc <= w_advance;

		// Here we read both cache entries, at i_pc and lastpc.
		// We'll select from among these cache possibilities on the
		// next clock
		r_pc_cache <= cache[i_pc[(CW+1):2]];
		r_last_cache <= cache[lastpc[(CW+1):2]];
		//
		// Let's also register(delay) the r_pc and r_lastpc values
		// for the next clock, so we can accurately report the address
		// of the cache value we just looked up.
		r_pc <= i_pc;
		r_lastpc <= lastpc;
	end

	// On our next clock, our result with either be the registered i_pc
	// value from the last clock (if isrc), otherwise r_lastpc
	assign	o_pc  = (isrc) ? r_pc : r_lastpc;
	// The same applies for determining what the next output instruction
	// will be.  We just read it in the last clock, now we just need to
	// select between the two possibilities we just read.
	assign	o_insn= (isrc) ? r_pc_cache : r_last_cache;


	/////////////////////////////////////////////////
	//
	// Read the tag value associated with this tcache line
	//
	/////////////////////////////////////////////////
	//
	//

	//
	// Read the tag value associated with this i_pc value
	initial	tagvalipc = 0;
	always @(posedge i_clk)
		tagvalipc <= cache_tags[i_pc[(CW+1):LS+2]];


	//
	// Read the tag value associated with the lastpc value, from what
	// i_pc was when we could not tell if this value was in our cache or
	// not, or perhaps from when we determined that i was not in the cache.
	initial	tagvallst = 0;
	always @(posedge i_clk)
		tagvallst <= cache_tags[lastpc[(CW+1):LS+2]];

	// Select from between these two values on the next clock
	assign	tagval = (isrc)?tagvalipc : tagvallst;

	// i_pc will only increment when everything else isn't stalled, thus
	// we can set it without worrying about that.   Doing this enables
	// us to work in spite of stalls.  For example, if the next address
	// isn't valid, but the decoder is stalled, get the next address
	// anyway.
	initial	lastpc = 0;
	always @(posedge i_clk)
	if (w_advance)
		lastpc <= i_pc;

	assign	lasttag = lastpc[(AW+1):LS+2];

	/////////////////////////////////////////////////
	//
	// Use the tag value to determine if our output instruction will be
	// valid.
	//
	/////////////////////////////////////////////////
	//
	//
	assign	w_v_from_pc = ((i_pc[(AW+1):LS+2] == lasttag)
				&&(tagval == i_pc[(AW+1):CW+2])
				&&(valid_mask[i_pc[(CW+1):LS+2]]));
	assign	w_v_from_last = ((tagval == lastpc[(AW+1):CW+2])
				&&(valid_mask[lastpc[(CW+1):LS+2]]));

	initial	delay = 2'h3;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache)||(w_advance))
	begin
		// Source our valid signal from i_pc
		rvsrc <= 1'b1;
		// Delay at least two clocks before declaring that
		// we have an invalid result.  This will give us time
		// to check the tag value of what's in the cache.
		delay <= 2'h2;
	end else if ((!r_v)&&(!o_illegal)) begin
		// If we aren't sourcing our valid signal from the
		// i_pc clock, then we are sourcing it from the
		// lastpc clock (one clock later).  If r_v still
		// isn't valid, we may need to make a bus request.
		// Apply our timer and timeout.
		rvsrc <= 1'b0;

		// Delay is two once the bus starts, in case the
		// bus transaction needs to be restarted upon completion
		// This might happen if, after we start loading the
		// cache, we discover a branch.  The cache load will
		// still complete, but the branches address needs to be
		// the onen we jump to.  This may mean we need to load
		// the cache twice.
		if (o_wb_cyc)
			delay <= 2'h2;
		else if (delay != 0)
			delay <= delay + 2'b11; // i.e. delay -= 1;
	end else begin
		// After sourcing our output from i_pc, if it wasn't
		// accepted, source the instruction from the lastpc valid
		// determination instead
		rvsrc <= 1'b0;
		if (o_illegal)
			delay <= 2'h2;
	end

	wire	w_invalidate_result;
	assign	w_invalidate_result = (i_reset)||(i_clear_cache);

	reg	r_prior_illegal;
	initial	r_prior_illegal = 0;
	initial	r_new_request = 0;
	initial	r_v_from_pc = 0;
	initial	r_v_from_last = 0;
	always @(posedge i_clk)
	begin
		r_new_request <= w_invalidate_result;
		r_v_from_pc   <= (w_v_from_pc)&&(!w_invalidate_result)
					&&(!o_illegal);
		r_v_from_last <= (w_v_from_last)&&(!w_invalidate_result);

		r_prior_illegal <= (o_wb_cyc)&&(i_wb_err);
	end

	// Now use rvsrc to determine which of the two valid flags we'll be
	// using: r_v_from_pc (the i_pc address), or r_v_from_last (the lastpc
	// address)
	assign	r_v = ((rvsrc)?(r_v_from_pc):(r_v_from_last))&&(!r_new_request);
	assign	o_valid = (((rvsrc)?(r_v_from_pc):(r_v_from_last))
			||(o_illegal))
			&&(!i_new_pc)&&(!r_prior_illegal);

	/////////////////////////////////////////////////
	//
	// If the instruction isn't in our cache, then we need to load
	// a new cache line from memory.
	//
	/////////////////////////////////////////////////
	//
	//
	initial	needload = 1'b0;
	always @(posedge i_clk)
	if ((i_clear_cache)||(o_wb_cyc))
		needload <= 1'b0;
	else if ((w_advance)&&(!o_illegal))
		needload <= 1'b0;
	else
		needload <= (delay==0)&&(!w_v_from_last)
			// Prevent us from reloading an illegal address
			// (i.e. one that produced a bus error) over and over
			// and over again
			&&((!illegal_valid)
				||(lastpc[(AW+1):LS+2] != illegal_cache));

	//
	// Working from the rule that you want to keep complex logic out of
	// a state machine if possible, we calculate a "last_stb" value one
	// clock ahead of time.  Hence, any time a request is accepted, if
	// last_stb is also true we'll know we need to drop the strobe line,
	// having finished requesting a complete cache  line.
	initial	last_addr = 1'b0;
	always @(posedge i_clk)
	if (!o_wb_cyc)
		last_addr <= 1'b0;
	else if ((o_wb_addr[(LS-1):1] == {(LS-1){1'b1}})
			&&((!i_wb_stall)|(o_wb_addr[0])))
		last_addr <= 1'b1;

	//
	// "last_ack" is almost identical to last_addr, save that this
	// will be true on the same clock as the last acknowledgment from the
	// bus.  The state machine logic will use this to determine when to
	// get off the bus and end the wishbone bus cycle.
	initial	last_ack = 1'b0;
	always @(posedge i_clk)
		last_ack <= (o_wb_cyc)&&(
				(wraddr[(LS-1):1]=={(LS-1){1'b1}})
				&&((wraddr[0])||(i_wb_ack)));

	initial	bus_abort = 1'b0;
	always @(posedge i_clk)
	if (!o_wb_cyc)
		bus_abort <= 1'b0;
	else if ((i_clear_cache)||(i_new_pc))
		bus_abort <= 1'b1;

	//
	// Here's the difficult piece of state machine logic--the part that
	// determines o_wb_cyc and o_wb_stb.  We've already moved most of the
	// complicated logic off of this statemachine, calculating it one cycle
	// early.  As a result, this is a fairly easy piece of logic.
	initial	o_wb_cyc  = 1'b0;
	initial	o_wb_stb  = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache))
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

	end else if ((needload)&&(!i_new_pc))
	begin
		o_wb_cyc  <= 1'b1;
		o_wb_stb  <= 1'b1;
	end

	// If we are reading from this cache line, then once we get the first
	// acknowledgement, this cache line has the new tag value
	always @(posedge i_clk)
	if ((o_wb_cyc)&&(i_wb_ack))
		cache_tags[o_wb_addr[(CW-1):LS]] <= o_wb_addr[(AW-1):CW];


	// On each acknowledgment, increment the address we use to write into
	// our cache.  Hence, this is the write address into our cache block
	// RAM.
	initial	wraddr    = 0;
	always @(posedge i_clk)
	if ((o_wb_cyc)&&(i_wb_ack)&&(!last_ack))
		wraddr <= wraddr + 1'b1;
	else if (!o_wb_cyc)
		wraddr <= { lastpc[(CW+1):LS+2], {(LS){1'b0}} };

	//
	// The wishbone request address.  This has meaning anytime o_wb_stb
	// is active, and needs to be incremented any time an address is
	// accepted--WITH THE EXCEPTION OF THE LAST ADDRESS.  We need to keep
	// this steady for that last address, unless the last address returns
	// a bus error.  In that case, the whole cache line will be marked as
	// invalid--but we'll need the value of this register to know how
	// to do that propertly.
	initial	o_wb_addr = {(AW){1'b0}};
	always @(posedge i_clk)
	if ((o_wb_stb)&&(!i_wb_stall)&&(!last_addr))
		o_wb_addr[(LS-1):0] <= o_wb_addr[(LS-1):0]+1'b1;
	else if (!o_wb_cyc)
		o_wb_addr <= { lastpc[(AW+1):LS+2], {(LS){1'b0}} };

	// Since it is impossible to initialize an array, our cache will start
	// up cache uninitialized.  We'll also never get a valid ack without
	// cyc being active, although we might get one on the clock after
	// cyc was active--so we need to test and gate on whether o_wb_cyc
	// is true.
	//
	// wraddr will advance forward on every clock cycle where ack is true,
	// hence we don't need to check i_wb_ack here.  This will work because
	// multiple writes to the same address, ending with a valid write,
	// will always yield the valid write's value only after our bus cycle
	// is over.
	always @(posedge i_clk)
	if (o_wb_cyc)
		cache[wraddr] <= i_wb_data;

	// VMask ... is a section loaded?
	// Note "svmask".  It's purpose is to delay the valid_mask setting by
	// one clock, so that we can insure the right value of the cache is
	// loaded before declaring that the cache line is valid.  Without
	// this, the cache line would get read, and the instruction would
	// read from the last cache line.
	initial	valid_mask = 0;
	initial	svmask = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache))
	begin
		valid_mask <= 0;
		svmask<= 1'b0;
	end else begin
		svmask <= ((o_wb_cyc)&&(i_wb_ack)&&(last_ack)&&(!bus_abort));

		if (svmask)
			valid_mask[saddr] <= (!bus_abort);
		if ((!o_wb_cyc)&&(needload))
			valid_mask[lastpc[(CW+1):LS+2]] <= 1'b0;
`ifdef	NOT_YET_READY
		//
		// MMU code
		//
		if (mmu_inval)
			valid_mask[mmu_mskadr] <= 1'b0;
`endif
	end

	always @(posedge i_clk)
	if ((o_wb_cyc)&&(i_wb_ack))
		saddr <= wraddr[(CW-1):LS];
	// MMU code
	//
	//
`ifdef	NOT_YET_READY
	parameter	[0:0]	USE_MMU = 1'b1;
	generate if (USE_MMU)
	begin
		reg	[(PAW-CW-1):0]	ptag	[0:((1<<(LGLINES))-1)];
		reg			mmu_pre_inval, r_mmu_inval;
		reg	[(PAW-CW-1):0]	mmu_pre_tag, mmu_pre_padr;
		reg	[(CW-LS-1):0]	r_mmu_mskadr;

		initial	mmu_pre_inval   = 0;
		initial	mmu_pre_tag     = 0;
		initial	mmu_pre_padr    = 0;
		initial	mmu_pre2_inval  = 0;
		initial	mmu_pre2_mskadr = 0;

		always @(posedge i_clk)
		if ((o_wb_cyc)&&(!last_addr)&&(i_mmu_ack))
			ptag[i_mmu_paddr[(CW-1):LS]] <= i_mmu_paddr[(PAW-1):CW];

		always @(posedge i_clk)
		if (i_reset)
		begin
			mmu_pre_inval <= 0;
			r_mmu_inval     <= 0;
		end else begin
			mmu_pre_inval <= (i_mmu_ack)&&(i_mmu_we);
			r_mmu_inval  <= (mmu_pre_inval)&&(mmu_pre_inval)
						&&(mmu_pre_tag == mmu_pre_paddr);
		end

		always @(posedge i_clk)
			mmu_pre_tag   <= ptag[i_mmu_paddr[(CW-1):LS]];

		always @(posedge i_clk)
		begin
			mmu_pre_padr  <= i_mmu_paddr[(PAW-1):CW];
	
			r_mmu_mskadr <= mmu_pre_padr[(PAW-LS-1):(CW-LS)];
		end

		assign	mmu_inval  = r_mmu_inval;
		assign	mmu_mskadr = r_mmu_mskadr;
	end else begin
		assign	mmu_inval  = 0;
		assign	mmu_mskadr = 0;
	end endgenerate
`endif

	/////////////////////////////////////////////////
	//
	// Handle bus errors here.  If a bus read request
	// returns an error, then we'll mark the entire
	// line as having a (valid) illegal value.
	//
	/////////////////////////////////////////////////
	//
	//
	//
	//
	initial	illegal_cache = 0;
	initial	illegal_valid = 0;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache))
	begin
		illegal_cache <= 0;
		illegal_valid <= 0;
	end else if ((o_wb_cyc)&&(i_wb_err))
	begin
		illegal_cache <= o_wb_addr[(AW-1):LS];
		illegal_valid <= 1'b1;
	end

	initial o_illegal = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(i_clear_cache)||(i_new_pc))
		o_illegal <= 1'b0;
	else if ((o_illegal)||((o_valid)&&(i_stall_n)))
		o_illegal <= 1'b0;
	else
		o_illegal <= (illegal_valid)
			&&(illegal_cache == lastpc[(AW+1):LS+2]);

`ifdef	FORMAL
//
//
// Generic setup
//
//
`ifdef	PFCACHE
`define	ASSUME	assume
`else
`define	ASSUME	assert
`define	STEP_CLOCK
`endif

	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	/////////////////////////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	/////////////////////////////////////////////////


`ifdef	PFCACHE
	//
	// Assume that resets, new-pc commands, and clear-cache commands
	// are never more than pulses--one clock wide at most.
	//
	// It may be that the CPU treats us differently.  We'll only assume
	// our solver to this here.
	always @(posedge i_clk)
	if (!f_past_valid)
	begin
		if ($past(i_reset))
			assume(!i_reset);
		if ($past(i_new_pc))
			assume(!i_new_pc);
		if ($past(i_clear_cache))
			assume(!i_clear_cache);
	end
`endif

	//
	// Assume we start from a reset condition
	initial	`ASSUME(i_reset);

	// Assume that any reset is either accompanied by a new address,
	// or a new address immediately follows it.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		`ASSUME(i_new_pc);
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
	if ((!o_valid)||(i_stall_n))
		f_cpu_delay <= 0;
	else
		// Otherwise, count the clocks the CPU takes to respond
		f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	PFCACHE
	always @(posedge i_clk)
		assume(f_cpu_delay < F_CPU_DELAY);
`endif

	always @(posedge i_clk)
	if ($past(i_reset || i_clear_cache))
		assume(i_stall_n);
	else if ($past(i_stall_n && !o_valid))
		assume(i_stall_n);
	else if (i_new_pc)
		assume(i_stall_n);

	/////////////////////////////////////////////////
	//
	//
	// Assertions about our outputs
	//
	//
	/////////////////////////////////////////////////

	localparam	F_LGDEPTH=LS+1;
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;

	fwb_master #(.AW(AW), .DW(BUSW), .F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(2), .F_MAX_ACK_DELAY(3),
			.F_MAX_REQUESTS(1<<LS), .F_OPT_SOURCE(1),
			.F_OPT_RMW_BUS_OPTION(0),
			.F_OPT_DISCONTINUOUS(0))
		f_wbm(i_clk, i_reset,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, 4'h0,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
			f_nreqs, f_nacks, f_outstanding);

	// writes are also illegal for a prefetch.
	always @(posedge i_clk)
	if (o_wb_stb)
		assert(!o_wb_we);

	always @(posedge i_clk)
	begin
		assert(f_nreqs <= (1<<LS));
		if ((o_wb_cyc)&&(o_wb_stb))
			assert(f_nreqs == o_wb_addr[(LS-1):0]);
		if ((f_past_valid)&&($past(o_wb_cyc))
			&&(!o_wb_stb)&&(!$past(i_wb_err || i_reset || i_clear_cache)))
			assert(f_nreqs == (1<<LS));
	end

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if ((!o_wb_cyc)&&($past(o_wb_cyc))&&(!$past(i_reset))
				&&(!$past(i_clear_cache)) &&(!$past(i_wb_err)))
			assert(f_nacks == (1<<LS));
		else if (o_wb_cyc)
			assert(f_nacks[(LS-1):0] == wraddr[(LS-1):0]);
	end

	// The last-ack line
	always @(posedge i_clk)
	if (o_wb_cyc)
		assert(last_ack == (f_nacks == ((1<<LS)-1)));

	// The valid line for whats being read
	always @(posedge i_clk)
	if (o_wb_cyc)
		assert(!valid_mask[o_wb_addr[CW-1:LS]]);

	always @(posedge i_clk)
	if ((illegal_valid)&&(o_wb_cyc))
		assert(o_wb_addr[AW-1:LS] != illegal_cache);

	reg	[((1<<(LGLINES))-1):0]	f_past_valid_mask;
	initial	f_past_valid_mask = 0;
	always @(posedge i_clk)
		f_past_valid_mask = valid_mask;

	always @(posedge i_clk)
	if ((o_valid)&&($past(!o_valid || !o_illegal)))
		assert((!o_wb_cyc)
			||(o_wb_addr[AW-1:LS] != o_pc[AW+1:LS+2]));
	always @(posedge i_clk)
	if (illegal_valid)
	begin
		assert((!o_wb_cyc)
			||(o_wb_addr[AW-1:LS] != illegal_cache));

		// The illegal cache line should never be valid within our
		// cache
		assert((!valid_mask[illegal_cache[CW-1:LS]])
			||(cache_tags[illegal_cache[CW-1:LS]]
					!= illegal_cache[AW-1:CW]));
	end

	/////////////////////////////////////////////////////
	//
	//
	// Assertions about our return responses to the CPU
	//
	//
	/////////////////////////////////////////////////////


	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_wb_cyc)))
		assert(o_wb_addr[(AW-1):LS] == $past(o_wb_addr[(AW-1):LS]));

	// Consider it invalid to present the CPU with the same instruction
	// twice in a row.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid))&&($past(i_stall_n))&&(o_valid))
		assert(o_pc != $past(o_pc));

	always @(posedge i_clk)
	if (o_valid)
	begin
		if (!o_illegal)
		begin
			assert(cache_tags[o_pc[(CW+1):LS+2]] == o_pc[(AW+1):CW+2]);
			assert(valid_mask[o_pc[(CW+1):LS+2]] || (o_illegal));
			assert(o_insn == cache[o_pc[(CW+1):2]]);
			assert((!illegal_valid)
				||((illegal_cache != o_pc[(AW+1):LS+2])));
		end

		assert(o_illegal == ($past(illegal_valid)
				&&($past(illegal_cache)== o_pc[(AW+1):LS+2])));
	end

	always @(*)
	begin
		`ASSUME(i_pc[1:0] == 2'b00);
		assert(o_pc[1:0] == 2'b00);
		assert(r_pc[1:0] == 2'b00);
		assert(r_lastpc[1:0] == 2'b00);
	end

	reg	[(AW+1):0]	f_next_pc;

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin
		if (isrc)
			assert(lastpc == r_pc);
		else
			assert(lastpc + 4== r_pc);
	end

	always @(posedge i_clk)
	if (i_new_pc)
		f_next_pc <= { i_pc[AW+1:2] + 1'b1, 2'b00 };
	else if ((i_stall_n)&&(r_v))
		f_next_pc <= { i_pc[AW+1:2] + 1'b1, 2'b00 };
	always @(*)
	if (!i_new_pc)
		`ASSUME(i_pc == f_next_pc);

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_valid)&&($past(o_valid))
		&&(!$past(i_reset))
		&&(!$past(i_new_pc))
		&&(!$past(i_stall_n))
		&&(!o_illegal))
	begin
		assert(cache_tags[o_pc[(CW+1):LS+2]] == o_pc[(AW+1):CW+2]);
	end

	//
	// If an instruction is accepted, we should *always* move on to another
	// instruction.  The only exception is following an i_new_pc (or
	// other invalidator), at which point the next instruction should
	// be invalid.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid))&&($past(i_stall_n)))
	begin
		// Should always advance the instruction
		assert((!o_valid)||(o_pc != $past(o_pc)));
	end

	//
	// Once an instruction becomes valid, it should never become invalid
	// unless there's been a request for a new instruction.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_reset && !i_clear_cache && !i_new_pc))
		&&($past(o_valid && !i_stall_n))
		&&(!i_new_pc))
	begin
		if ((!$past(o_illegal))&&(!$past(o_wb_cyc && i_wb_err)))
		begin
			assert(o_valid);
			assert($stable(o_illegal));
			assert($stable(o_insn));
		end else
			assert((o_illegal)||(!o_valid));
	end
`ifdef	PFCACHE
	/////////////////////////////////////////////////////
	//
	//
	// Assertions associated with a response to a known
	// address request
	//
	//
	/////////////////////////////////////////////////////


	(* anyconst *)	reg	[AW:0]		f_const_addr;
	(* anyconst *)	reg	[BUSW-1:0]	f_const_insn;

	wire		f_this_pc, f_this_insn, f_this_data, f_this_line,
			f_this_ack, f_this_tag; // f_this_addr;
	assign	f_this_pc   = (o_pc == { f_const_addr[AW-1:0], 2'b00 });
	// assign	f_this_addr = (o_wb_addr == f_const_addr[AW-1:0] );
	assign	f_this_insn = (o_insn == f_const_insn);
	assign	f_this_data = (i_wb_data == f_const_insn);
	assign	f_this_line = (o_wb_addr[AW-1:LS] == f_const_addr[AW-1:LS]);
	assign	f_this_ack  = (f_this_line)&&(f_nacks == f_const_addr[LS-1:0]);
	assign	f_this_tag  = (tagval == f_const_addr[AW-1:CW]);

	always @(posedge i_clk)
	if ((o_valid)&&(f_this_pc)&&(!$past(o_illegal)))
	begin
		assert(o_illegal == f_const_addr[AW]);
		if (!o_illegal)
		begin
			assert(f_this_insn);
			assert(f_this_tag);
		end
	end

	always @(*)
	if ((valid_mask[f_const_addr[CW-1:LS]])
			&&(cache_tags[f_const_addr[(CW-1):LS]]==f_const_addr[AW-1:CW]))
		assert(f_const_insn == cache[f_const_addr[CW-1:0]]);
	else if ((o_wb_cyc)&&(o_wb_addr[AW-1:LS] == f_const_addr[AW-1:LS])
				&&(f_nacks > f_const_addr[LS-1:0]))
	begin
		assert(f_const_insn == cache[f_const_addr[CW-1:0]]);
	end

	always @(*)
	if (o_wb_cyc)
		assert(wraddr[CW-1:LS] == o_wb_addr[CW-1:LS]);

	always @(*)
	if (!f_const_addr[AW])
		assert((!illegal_valid)
			||(illegal_cache != f_const_addr[AW-1:LS]));
	else
		assert((cache_tags[f_const_addr[CW-1:LS]]!=f_const_addr[AW-1:CW])
			||(!valid_mask[f_const_addr[CW-1:LS]]));

	always @(*)
	if ((f_this_line)&&(o_wb_cyc))
	begin
		if (f_const_addr[AW])
			assume(!i_wb_ack);
		else
			assume(!i_wb_err);

		if ((f_this_ack)&&(i_wb_ack))
			assume(f_this_data);
	end

	always @(*)
	if ((f_this_line)&&(!f_const_addr[AW]))
		assume(!i_wb_err);

	always @(*)
	if (!f_const_addr[AW])
		assume((!valid_mask[f_const_addr[CW-1:LS]])
			||(cache_tags[f_const_addr[CW-1:LS]] != f_const_addr[AW-1:CW]));
`endif

	//
	//
	// Cover properties
	//
	//
	reg	f_valid_legal;
	always @(*)
		f_valid_legal = o_valid && (!o_illegal);
	always @(posedge i_clk)		// Trace 0
		cover((o_valid)&&( o_illegal));
	always @(posedge i_clk)		// Trace 1
		cover(f_valid_legal);
	always @(posedge i_clk)		// Trace 2
		cover((f_valid_legal)
			&&($past(!o_valid && !i_new_pc))
			&&($past(i_new_pc,2)));
	always @(posedge i_clk)		// Trace 3
		cover((f_valid_legal)&&($past(i_stall_n))&&($past(i_new_pc)));
	always @(posedge i_clk)		// Trace 4
		cover((f_valid_legal)&&($past(f_valid_legal && i_stall_n)));
	always @(posedge i_clk)		// Trace 5
		cover((f_valid_legal)
			&&($past(f_valid_legal && i_stall_n))
			&&($past(f_valid_legal && i_stall_n,2))
			&&($past(f_valid_legal && i_stall_n,3)));
	always @(posedge i_clk)		// Trace 6
		cover((f_valid_legal)
			&&($past(f_valid_legal && i_stall_n))
			&&($past(f_valid_legal && i_stall_n,2))
			&&($past(!o_illegal && i_stall_n && i_new_pc,3))
			&&($past(f_valid_legal && i_stall_n,4))
			&&($past(f_valid_legal && i_stall_n,5))
			&&($past(f_valid_legal && i_stall_n,6)));

`endif	// FORMAL
endmodule
