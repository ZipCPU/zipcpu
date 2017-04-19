////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pipefetch.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Keeping our CPU fed with instructions, at one per clock and
//		with no stalls, can be quite a chore.  Worse, the Wishbone
//		takes a couple of cycles just to read one instruction from
//		the bus.  However, if we use pipeline accesses to the Wishbone
//		bus, then we can read more and faster.  Further, if we cache
//		these results so that we have them before we need them, then
//		we have a chance of keeping our CPU from stalling.  Those are
//		the purposes of this instruction fetch module: 1) Pipeline
//		wishbone accesses, and 2) an instruction cache.
//
//	20150919 -- Fixed a nasty race condition whereby the pipefetch routine
//		would produce either the same instruction twice, or skip
//		an instruction.  This condition was dependent on the CPU stall
//		condition, and would only take place if the pipeline wasn't 
//		completely full throughout the stall.
//
//		Interface support was also added for trapping on illegal
//		instructions (i.e., instruction fetches that cause bus errors),
//		however the internal interface has not caught up to supporting
//		these exceptions yet.
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
module	pipefetch(i_clk, i_rst, i_new_pc, i_clear_cache, i_stall_n, i_pc,
			o_i, o_pc, o_v,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data, i_wb_request,
			o_illegal);
	parameter	RESET_ADDRESS=32'h0010_0000,
			LGCACHELEN = 6, ADDRESS_WIDTH=24,
			CACHELEN=(1<<LGCACHELEN), BUSW=32, AW=ADDRESS_WIDTH;
	input	wire			i_clk, i_rst, i_new_pc,
					i_clear_cache, i_stall_n;
	input	wire	[(AW-1):0]	i_pc;
	output	reg	[(BUSW-1):0]	o_i;
	output	reg	[(AW-1):0]	o_pc;
	output	wire			o_v;
	//
	output	reg		o_wb_cyc, o_wb_stb;
	output	wire		o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	wire	[(BUSW-1):0]	o_wb_data;
	//
	input	wire		i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(BUSW-1):0]	i_wb_data;
	//
	// Is the (data) memory unit also requesting access to the bus?
	input	wire			i_wb_request;
	output	wire			o_illegal;

	// Fixed bus outputs: we read from the bus only, never write.
	// Thus the output data is ... irrelevant and don't care.  We set it
	// to zero just to set it to something.
	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 0;

	reg	[(AW-1):0]		r_cache_base;
	reg	[(LGCACHELEN):0]	r_nvalid, r_acks_waiting;
	reg	[(BUSW-1):0]		cache[0:(CACHELEN-1)];

	wire	[(LGCACHELEN-1):0]	w_cache_offset;
	reg	[1:0]			r_cache_offset;

	reg			r_addr_set;
	reg	[(AW-1):0]	r_addr;

	wire	[(AW-1):0]	bus_nvalid;
	assign	bus_nvalid = { {(AW-LGCACHELEN-1){1'b0}}, r_nvalid };

	// What are some of the conditions for which we need to restart the
	// cache?
	wire	w_pc_out_of_bounds;
	assign	w_pc_out_of_bounds = ((i_new_pc)&&((r_nvalid == 0)
					||(i_pc < r_cache_base)
					||(i_pc >= r_cache_base + CACHELEN)
					||(i_pc >= r_cache_base + bus_nvalid+5)));
	wire	w_ran_off_end_of_cache;
	assign	w_ran_off_end_of_cache =((r_addr_set)&&((r_addr < r_cache_base)
					||(r_addr >= r_cache_base + CACHELEN)
					||(r_addr >= r_cache_base + bus_nvalid+5)));
	wire	w_running_out_of_cache;
	assign	w_running_out_of_cache = (r_addr_set)
			&&(r_addr >= r_cache_base +
				// {{(AW-LGCACHELEN-1),{1'b0}},2'b11,
				// 		{(LGCACHELEN-1){1'b0}}})
				// (1<<(LGCACHELEN-2)) + (1<<(LGCACHELEN-1)))
				+(3<<(LGCACHELEN-2)))
			&&(|r_nvalid[(LGCACHELEN):(LGCACHELEN-1)]);

	initial	r_cache_base = RESET_ADDRESS;
	always @(posedge i_clk)
	begin
		if ((i_rst)||(i_clear_cache)||((o_wb_cyc)&&(i_wb_err)))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
			// r_cache_base <= RESET_ADDRESS;
		// end else if ((~o_wb_cyc)&&(i_new_pc)&&(r_nvalid != 0)
		//		&&(i_pc >= r_cache_base)
		//		&&(i_pc < r_cache_base + bus_nvalid))
		// begin
			// The new instruction is in our cache, do nothing
			// with the bus here.
		end else if ((o_wb_cyc)&&(w_pc_out_of_bounds))
		begin
			// We need to abandon our bus action to start over in
			// a new region, setting up a new cache.  This may
			// happen mid cycle while waiting for a result.  By
			// dropping o_wb_cyc, we state that we are no longer
			// interested in that result--whatever it might be.
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end else if ((~o_wb_cyc)&&(~r_nvalid[LGCACHELEN])&&(~i_wb_request)&&(r_addr_set))
		begin
			// Restart a bus cycle that was interrupted when the
			// data section wanted access to our bus.
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			// o_wb_addr <= r_cache_base + bus_nvalid;
		end else if ((~o_wb_cyc)&&(
				(w_pc_out_of_bounds)||(w_ran_off_end_of_cache)))
		begin
			// Start a bus transaction
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			// o_wb_addr <= (i_new_pc) ? i_pc : r_addr;
			// r_nvalid <= 0;
			// r_cache_base <= (i_new_pc) ? i_pc : r_addr;
			// w_cache_offset <= 0;
		end else if ((~o_wb_cyc)&&(w_running_out_of_cache))
		begin
			// If we're using the last quarter of the cache, then
			// let's start a bus transaction to extend the cache.
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;
			// o_wb_addr <= r_cache_base + (1<<(LGCACHELEN));
			// r_nvalid <= r_nvalid - (1<<(LGCACHELEN-2));
			// r_cache_base <= r_cache_base + (1<<(LGCACHELEN-2));
			// w_cache_offset <= w_cache_offset + (1<<(LGCACHELEN-2));
		end else if (o_wb_cyc)
		begin
			// This handles everything ... but the case where
			// while reading we need to extend our cache.
			if ((o_wb_stb)&&(~i_wb_stall))
			begin
				// o_wb_addr <= o_wb_addr + 1;
				if ((o_wb_addr - r_cache_base >= CACHELEN-1)
					||(i_wb_request))
					o_wb_stb <= 1'b0;
			end

			if (i_wb_ack)
			begin
				// r_nvalid <= r_nvalid + 1;
				if ((r_acks_waiting == 1)&&(~o_wb_stb))
					o_wb_cyc <= 1'b0;
			end else if ((r_acks_waiting == 0)&&(~o_wb_stb))
				o_wb_cyc <= 1'b0;
		end
	end

	
	initial	r_nvalid = 0;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_cache)) // Required, so we can reload memoy and then reset
			r_nvalid <= 0;
		else if ((~o_wb_cyc)&&(
				(w_pc_out_of_bounds)||(w_ran_off_end_of_cache)))
			r_nvalid <= 0;
		else if ((~o_wb_cyc)&&(w_running_out_of_cache))
			r_nvalid[LGCACHELEN:(LGCACHELEN-2)]
				<= r_nvalid[LGCACHELEN:(LGCACHELEN-2)] +3'b111;
					// i.e.  - (1<<(LGCACHELEN-2));
		else if ((o_wb_cyc)&&(i_wb_ack))
			r_nvalid <= r_nvalid + {{(LGCACHELEN){1'b0}},1'b1}; // +1;

	always @(posedge i_clk)
		if (i_clear_cache)
			r_cache_base <= i_pc;
		else if ((~o_wb_cyc)&&(
				(w_pc_out_of_bounds)
				||(w_ran_off_end_of_cache)))
			r_cache_base <= (i_new_pc) ? i_pc : r_addr;
		else if ((~o_wb_cyc)&&(w_running_out_of_cache))
			r_cache_base[(AW-1):(LGCACHELEN-2)]
				<= r_cache_base[(AW-1):(LGCACHELEN-2)]
					+ {{(AW-LGCACHELEN+1){1'b0}},1'b1};
					// i.e.  + (1<<(LGCACHELEN-2));

	always @(posedge i_clk)
		if (i_clear_cache)
			r_cache_offset <= 0;
		else if ((~o_wb_cyc)&&(
				(w_pc_out_of_bounds)
				||(w_ran_off_end_of_cache)))
			r_cache_offset <= 0;
		else if ((~o_wb_cyc)&&(w_running_out_of_cache))
			r_cache_offset[1:0] <= r_cache_offset[1:0] + 2'b01;
	assign	w_cache_offset = { r_cache_offset, {(LGCACHELEN-2){1'b0}} };

	always @(posedge i_clk)
		if (i_clear_cache)
			o_wb_addr <= i_pc;
		else if ((o_wb_cyc)&&(w_pc_out_of_bounds))
		begin
			if (i_wb_ack)
				o_wb_addr <= r_cache_base + bus_nvalid+1;
			else
				o_wb_addr <= r_cache_base + bus_nvalid;
		end else if ((~o_wb_cyc)&&((w_pc_out_of_bounds)
					||(w_ran_off_end_of_cache)))
			o_wb_addr <= (i_new_pc) ? i_pc : r_addr;
		else if ((o_wb_stb)&&(~i_wb_stall))	// && o_wb_cyc
			o_wb_addr <= o_wb_addr + 1;

	initial	r_acks_waiting = 0;
	always @(posedge i_clk)
		if (~o_wb_cyc)
			r_acks_waiting <= 0;
		// o_wb_cyc *must* be true for all following
		else if ((o_wb_stb)&&(~i_wb_stall)&&(~i_wb_ack)) //&&(o_wb_cyc)
			r_acks_waiting <= r_acks_waiting + {{(LGCACHELEN){1'b0}},1'b1};
		else if ((i_wb_ack)&&((~o_wb_stb)||(i_wb_stall))) //&&(o_wb_cyc)
			r_acks_waiting <= r_acks_waiting + {(LGCACHELEN+1){1'b1}}; // - 1;

	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			cache[r_nvalid[(LGCACHELEN-1):0]+w_cache_offset]
					<= i_wb_data;

	initial	r_addr_set = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(i_new_pc))
			r_addr_set <= 1'b1;
		else if (i_clear_cache)
			r_addr_set <= 1'b0;

	// Now, read from the cache
	wire	w_cv;	// Cache valid, address is in the cache
	reg	r_cv;
	assign	w_cv = ((r_nvalid != 0)&&(r_addr>=r_cache_base)
			&&(r_addr-r_cache_base < bus_nvalid));
	always @(posedge i_clk)
		r_cv <= (~i_new_pc)&&((w_cv)||((~i_stall_n)&&(r_cv)));
	assign	o_v = (r_cv)&&(~i_new_pc);

	always @(posedge i_clk)
		if (i_new_pc)
			r_addr <= i_pc;
		else if ( ((i_stall_n)&&(w_cv)) || ((~i_stall_n)&&(w_cv)&&(r_addr == o_pc)) )
			r_addr <= r_addr + {{(AW-1){1'b0}},1'b1};

	wire	[(LGCACHELEN-1):0]	c_rdaddr, c_cache_base;
	assign	c_cache_base   = r_cache_base[(LGCACHELEN-1):0];
	assign	c_rdaddr = r_addr[(LGCACHELEN-1):0]-c_cache_base+w_cache_offset;
	always @(posedge i_clk)
		if ((~o_v)||((i_stall_n)&&(o_v)))
			o_i <= cache[c_rdaddr];
	always @(posedge i_clk)
		if ((~o_v)||((i_stall_n)&&(o_v)))
			o_pc <= r_addr;

	reg	[(AW-1):0]	ill_address;
	initial	ill_address = 0;
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_err))
			ill_address <= o_wb_addr - {{(AW-LGCACHELEN-1){1'b0}}, r_acks_waiting};

	assign	o_illegal = (o_pc == ill_address)&&(~i_rst)&&(~i_new_pc)&&(~i_clear_cache);


endmodule
