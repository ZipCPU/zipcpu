////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_check.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To test the ZipDMA.  This module has two bus ports, one control
//		port and one high speed data port.
//
//	The control port has two 32b registers.
//
//	Addr 0:
//		Contains two counters and an error flag.
//	   BIT[0]:	An error flag.  This will be set on any write where the
//			written data doesn't match the internal pseudorandom
//			state.
//	   BITS[15: 4]:	Read count.  Counts the number of bytes read from the
//			high speed data port.  Reading more than this amount
//			will simply overflow.
//	   BITS[31:20]:	Write data count.  Counts the number of bytes written
//			to the high speed data port.
//
//	Addr 4:
//		Reads from this register return the current state of the
//		shift register.  Writes to this register will both update the
//		shift register, and clear the read and write counters.
//
//	The high speed data port has two purposes.  When read, the high speed
//	port returns a pseudorandom data stream.  When written, bytes written
//	are compared against the pseudorandom data stream.  Any failure to
//	match will set the error flag bit in the control register.
//
//	Although the high speed data port has many bits to its address, these
//	address bits are unused.  The "address", or rather the position in the
//	pseudorandom stream, is determined by the order in which the bytes in
//	the high speed port are accessed.  The first byte read (or written) will
//	always be the first byte in the pseudorandom stream--regardless of the
//	address used when reading (or writing) the port.  This is to allow this
//	checking facility to verify whether or not the DMA can properly
//	read from (or write to) ports with a fixed address, as well as reading
//	from (or writing to) ports with more memory-type addressing.  As long
//	as the reads (or writes) are done in order, there (should) be no issues
//	with this approach.
//
// Creator:	Sukru Uzun
// Updated by:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
`timescale 1ns/1ps
`default_nettype none
// }}}
module	zipdma_check #(
		// {{{
		parameter	ADDRESS_WIDTH = 30,
		parameter	BUS_WIDTH = 64,
		localparam	DW = BUS_WIDTH,
		localparam	AW = ADDRESS_WIDTH-$clog2(DW/8)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// High-speed, high width Wishbone test/data port
		// {{{
		input	wire		i_wb_cyc, i_wb_stb,
		input	wire		i_wb_we,
		input	wire [AW-1:0]	i_wb_addr,
		input	wire [DW-1:0]	i_wb_data,
		input	wire [DW/8-1:0]	i_wb_sel,
		//
		// verilator coverage_off
		output	wire		o_wb_stall,
		// verilator coverage_on
		output	reg		o_wb_ack,
		output	wire [DW-1:0]	o_wb_data,
		// verilator coverage_off
		output	wire 		o_wb_err,
		// verilator coverage_on
		// }}}
		// Wishbone status/control port
		// {{{
		input	wire		i_st_cyc, i_st_stb,
		input	wire		i_st_we,
		input	wire		i_st_addr,
		input	wire [31:0]	i_st_data,
		input	wire [3:0]	i_st_sel,
		//
		// verilator coverage_off
		output	wire		o_st_stall,
		// verilator coverage_on
		output	reg		o_st_ack,
		output	reg [31:0]	o_st_data,
		// verilator coverage_off
		output	wire		o_st_err
		// verilator coverage_on
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	SR = 32;	// Shift register width
	localparam [SR-1:0]	POLY = 32'h0040_1003;

	reg [SR-1:0]	lfsr_state;
	wire [SR-1:0]	rewrite_state;

	wire		read_beat, write_beat, ctrl_write_ready;
	reg	[11:0]	rd_count, wr_count;
	reg	[DW/8-1:0]	wrmatchb;
	reg	[2*DW-1:0]	wide_state, shift_state;

	integer	rk, rkp;
	reg	[DW-1:0]	nxt_rddata, read_data;

	integer	wk, wkp;
	reg			err_flag;
	// }}}

	// read_beat, write_beat
	assign read_beat  = i_wb_stb && !i_wb_we && (i_wb_sel != 0);
	assign write_beat = i_wb_stb &&  i_wb_we && (i_wb_sel != 0);
	assign ctrl_write_ready = i_st_stb && !o_st_stall && i_st_we
					&& i_st_sel != 0;

	// Wishbone outputs
	assign o_wb_stall = 1'b0;
	assign o_wb_err   = 1'b0;
	assign o_wb_data  = read_data;

	assign o_st_stall = 1'b0;
	assign o_st_err   = 1'b0;

	// o_st_ack
	// {{{
	initial	o_st_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_st_ack <= 1'b0;
	else
		o_st_ack <= i_st_stb;
	// }}}

	// wide_state
	// {{{
	always @(*)
	begin
		wide_state = 0;
		wide_state[0 +: SR] = lfsr_state;
		for(wk=0; wk<2*DW/SR-1; wk=wk+1)
			wide_state[SR+(wk*SR) +: SR]
				= advance_lfsr(wide_state[(wk*SR) +: SR]);
	end
	// }}}

	// lfsr_state
	// {{{
	always @(*)
		shift_state = wide_state >> (8*$countones(i_wb_sel));
	assign	rewrite_state = new_state(lfsr_state, i_st_data, i_st_sel);

	always @(posedge i_clk)
	if (i_reset)
		lfsr_state <= 0; // initial state
	else begin
		// feedback
		if (read_beat || write_beat)
			lfsr_state <= shift_state[0 +: SR];

		if (ctrl_write_ready)
		begin // set an initial per-test state
			lfsr_state <= rewrite_state;
		end
	end
	// }}}

	// o_wb_ack
	// {{{
	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 0;
	else
		o_wb_ack <= i_wb_stb && !o_wb_stall;
	// }}}

	// read_data (i.e. o_wb_data)
	// {{{
	always @(*)
	begin
		nxt_rddata = 0;
		rkp = 0;
		if (read_beat)
		for(rk=0; rk<DW/8; rk=rk+1)
		begin
			if (i_wb_sel[DW/8-1-rk])
			begin
				nxt_rddata[(DW/8-1-rk)*8 +: 8]
					= wide_state[(8*rkp) +: 8];
				rkp = rkp+1;
			end
		end
	end

	always @(posedge i_clk)
	if (i_reset || !read_beat)
		read_data <= 0;
	else
		read_data <= nxt_rddata;
	// }}}
	
	// rd_count, wr_count
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		rd_count <= 0;
		wr_count <= 0;
	end else if (ctrl_write_ready)
	begin
		// reset counter on any write--either to the LFSR state, or to
		// the counters themselves.
		rd_count <= 0;
		wr_count <= 0;
	end else if (i_wb_stb && !o_wb_stall)
	begin
		if (i_wb_we)
			wr_count <= wr_count + $countones(i_wb_sel);
		else
			rd_count <= rd_count + $countones(i_wb_sel);
	end
	// }}}

	// o_st_data: Error detectıon
	// {{{
	always @(*)
	begin
		wrmatchb = -1; wkp = 0;
		if (write_beat)
		for(wk=0; wk<DW/8; wk=wk+1)
		if (i_wb_sel[DW/8-1-wk])
		begin
			wrmatchb[DW/8-1-wk] = (i_wb_data[(DW/8-1-wk)*8 +: 8]
					== wide_state[(8*wkp) +: 8]);
			wkp = wkp+1;
		end
	end

	always @(posedge i_clk)
	if (i_reset)
		err_flag <= 1'b0;
	else begin
		if (write_beat && |(~wrmatchb))
			err_flag <= 1'b1;

		if (i_st_stb && i_st_we && |i_st_sel)
			// Clear the error flag on any status write
			err_flag <= 1'b0;
	end

	always @(posedge i_clk)
	if (i_st_stb && !i_st_we)
	begin
		o_st_data <= 0;
		case(i_st_addr)
		1'b0: o_st_data <= { wr_count, 4'h0, rd_count, 3'h0, err_flag };
		1'b1: o_st_data[SR-1:0] <= lfsr_state;
		endcase
	end
	// }}}

	function automatic [SR-1:0] advance_lfsr(input [SR-1:0] istate);
		// {{{
		integer ak;
		reg	[SR-1:0]	fill;
	begin
		fill = istate;
		for(ak=0; ak<SR; ak=ak+1)
		begin
			if (^(fill & POLY))
				fill = { 1'b1, fill[SR-1:1] };
			else
				fill = { 1'b0, fill[SR-1:1] };
		end

		advance_lfsr = fill;
	end endfunction
	// }}}

	function automatic [SR-1:0] new_state(input [SR-1:0] current,
		// {{{
				input [31:0] bus_word, input[3:0] bus_strb);
		reg	[31:0]	sr_state;
		integer		lfsrk;
	begin
		sr_state = 0;
		sr_state[SR-1:0] = current;
		for (lfsrk = 0; lfsrk < 4; lfsrk = lfsrk + 1)
		if (bus_strb[lfsrk])
			sr_state[(lfsrk*8) +: 8] = bus_word[(lfsrk*8) +: 8];
		new_state = sr_state[SR-1:0];
	end endfunction
	// }}}

	// Keep Verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_st_cyc, i_st_addr, i_wb_addr,
			shift_state[2*DW-1:SR] };
	// verilator lint_on UNUSED
	// verilator coverage_on
	// }}}
endmodule
