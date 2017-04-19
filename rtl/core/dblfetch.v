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
module	dblfetch(i_clk, i_rst, i_new_pc, i_clear_cache,
			i_stall_n, i_pc, o_i, o_pc, o_v,
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err, i_wb_data,
		o_illegal);
	parameter		ADDRESS_WIDTH=32, AUX_WIDTH = 1;
	localparam		AW=ADDRESS_WIDTH;
	input	wire			i_clk, i_rst, i_new_pc, i_clear_cache,
						i_stall_n;
	input	wire	[(AW-1):0]	i_pc;
	output	reg	[31:0]		o_i;
	output	reg	[(AW-1):0]	o_pc;
	output	wire			o_v;
	// Wishbone outputs
	output	reg			o_wb_cyc, o_wb_stb;
	output	wire			o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	wire	[31:0]		o_wb_data;
	// And return inputs
	input	wire		i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[31:0]	i_wb_data;
	// And ... the result if we got an error
	output	reg		o_illegal;

	assign	o_wb_we = 1'b0;
	assign	o_wb_data = 32'h0000;

	reg	last_ack, last_stb, invalid_bus_cycle;

	reg	[31:0]		cache	[0:1];
	reg	cache_read_addr, cache_write_addr;
	reg	[1:0]		cache_valid;

	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(i_wb_err))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
			// last_stb <= 1'b0;
			// last_ack <= 1'b0;
		end else if (o_wb_cyc)
		begin
			if ((o_wb_stb)&&(!i_wb_stall))
			begin
				// last_stb <= 1'b1;
				o_wb_stb <= !last_stb;
			end
			// if (i_wb_ack)
			//	last_ack <= 1'b1;
			if ((i_new_pc)||(invalid_bus_cycle))
				o_wb_stb <= 1'b0;

			if ((i_wb_ack)&&(
				// Relase the bus on the second ack
				(last_ack)
				// Or on the first ACK, if we've been told
				// we have an invalid bus cycle
				||((o_wb_stb)&&(i_wb_stall)&&(last_stb)&&(
					(i_new_pc)||(invalid_bus_cycle)))
				))
			begin
				o_wb_cyc <= 1'b0;
				o_wb_stb <= 1'b0;
			end

			if ((!last_stb)&&(i_wb_stall)&&((i_new_pc)||(invalid_bus_cycle)))
				// Also release the bus with no acks, if we
				// haven't made any requests
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
		if ((o_wb_cyc)&&(o_wb_stb)&&(!i_wb_stall))
			last_stb <= 1'b1;
		else if (!o_wb_cyc)
			last_stb <= 1'b0;

	initial	last_ack = 1'b0;
	always @(posedge i_clk)
		if ((o_wb_cyc)&&(i_wb_ack))
			last_ack <= 1'b1;
		else if ((o_wb_cyc)&&(o_wb_stb)&&(i_wb_stall)&&(
				(i_new_pc)||(invalid_bus_cycle)))
			last_ack <= 1'b1;
		else if ((o_wb_cyc)&&(o_wb_stb)&&(!i_wb_stall)&&(!last_stb)&&(
				(i_new_pc)||(invalid_bus_cycle)))
			last_ack <= 1'b1;
		else if (!o_wb_cyc)
			last_ack <= 1'b0;

	initial	invalid_bus_cycle = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			invalid_bus_cycle <= 1'b0;
		else if ((i_new_pc)||(i_clear_cache))
			invalid_bus_cycle <= 1'b1;
		else if (!o_wb_cyc)
			invalid_bus_cycle <= 1'b0;

	initial	o_wb_addr = {(AW){1'b1}};
	always @(posedge i_clk)
		if (i_new_pc)
			o_wb_addr <= i_pc;
		else if ((o_wb_stb)&&(!i_wb_stall)&&(!invalid_bus_cycle))
			o_wb_addr <= o_wb_addr + 1'b1;

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

	always @(posedge i_clk)
		if ((i_new_pc)||(invalid_bus_cycle))
			cache_valid <= 2'b00;
		else begin
			if ((o_v)&&(i_stall_n))
				cache_valid[cache_read_addr] <= 1'b0;
			if ((o_wb_cyc)&&(i_wb_ack))
				cache_valid[cache_write_addr] <= 1'b1;
		end

	initial	o_i = {(32){1'b1}};
	always @(posedge i_clk)
		if ((i_stall_n)&&(o_wb_cyc)&&(i_wb_ack))
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

endmodule
