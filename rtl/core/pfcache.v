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
	parameter	LGCACHELEN = 8, ADDRESS_WIDTH=24,
			LGLINES=5; // Log of the number of separate cache lines
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
		end else if (~r_v) begin // Otherwise, r_v was true and we were
			// stalled, hence only if ~r_v
			rvsrc <= 1'b0;
			if (o_wb_cyc)
				delay <= 2'h2;
			else if (delay != 0)
				delay <= delay + 2'b11; // i.e. delay -= 1;
		end
	reg	r_v_from_pc, r_v_from_last;
	always @(posedge i_clk)
		r_v_from_pc <= w_v_from_pc;
	always @(posedge i_clk)
		r_v_from_last <= w_v_from_last;

	assign	r_v = ((rvsrc)?(r_v_from_pc):(r_v_from_last));
	assign	o_v = (((rvsrc)?(r_v_from_pc):(r_v_from_last))
				||((o_illegal)&&(~o_wb_cyc)))
			&&(~i_new_pc)&&(~i_rst);

	reg	last_ack;
	initial	last_ack = 1'b0;
	always @(posedge i_clk)
		last_ack <= (o_wb_cyc)&&(
				(rdaddr[(PW-1):1]=={(PW-1){1'b1}})
				&&((rdaddr[0])||(i_wb_ack)));

	reg	needload;
	initial	needload = 1'b0;
	always @(posedge i_clk)
		needload <= ((~r_v)&&(delay==0)
			&&((tagvallst != lastpc[(AW-1):CW])
				||(~vmask[lastpc[(CW-1):PW]]))
			&&((~illegal_valid)
				||(lastpc[(AW-1):PW] != illegal_cache)));

	reg	last_addr;
	initial	last_addr = 1'b0;
	always @(posedge i_clk)
		last_addr <= (o_wb_cyc)&&(o_wb_addr[(PW-1):1] == {(PW-1){1'b1}})
				&&((~i_wb_stall)|(o_wb_addr[0]));

	initial	o_wb_cyc  = 1'b0;
	initial	o_wb_stb  = 1'b0;
	initial	o_wb_addr = {(AW){1'b0}};
	initial	rdaddr    = 0;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_cache))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end else if (o_wb_cyc)
		begin
			if (i_wb_err)
				o_wb_stb <= 1'b0;
			else if ((o_wb_stb)&&(~i_wb_stall)&&(last_addr))
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
		if (o_wb_cyc) // &&(i_wb_ack)
			tags[o_wb_addr[(CW-1):PW]] <= o_wb_addr[(AW-1):CW];
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			rdaddr <= rdaddr + 1;
		else if (~o_wb_cyc)
			rdaddr <= { lastpc[(CW-1):PW], {(PW){1'b0}} };
			
	always @(posedge i_clk)
		if ((o_wb_stb)&&(~i_wb_stall)&&(~last_addr))
			o_wb_addr[(PW-1):0] <= o_wb_addr[(PW-1):0]+1;
		else if (~o_wb_cyc)
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
				vmask[saddr] <= 1'b1;
			if ((~o_wb_cyc)&&(needload))
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
		if ((i_rst)||(i_clear_cache)||(o_wb_cyc))
			o_illegal <= 1'b0;
		else
			o_illegal <= (illegal_valid)
				&&(illegal_cache == i_pc[(AW-1):PW]);

endmodule
