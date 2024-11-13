////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_check.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA --
//
//
// Creator:	Sukru Uzun
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
		parameter	ADDRESS_WIDTH = 30,
		parameter	BUS_WIDTH = 64,
		localparam	DW = BUS_WIDTH,
		localparam	AW = ADDRESS_WIDTH-$clog2(DW/8)
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
		// Wishbone status port
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
	localparam	BW = DW/8;   // BIT_WIDTH
	localparam	SR = 32;	// Shift register width
	localparam	[SR-1:0]	POLY = 32'hc000_0000;

	reg [2*DW-1:0]	wide_state, shift_state;
	reg [SR-1:0]	lfsr_state;

	wire		rd_data_en, wr_data_en, ctrl_write_ready;
	reg	[11:0]	rd_count, wr_count;
	reg	[11:0]	rd_count_reg, wr_count_reg;

	integer	rk, rkp;
	reg	[DW-1:0]	nxt_rddata, read_data;

	integer	wk, wkp;
	reg	[DW/8-1:0]	wrmatchb;
	reg			err_flag;
	// }}}

	// rd_data_en, wr_data_en
	assign rd_data_en = i_wb_stb && !i_wb_we && (i_wb_sel != 0);
	assign wr_data_en = i_wb_stb &&  i_wb_we && (i_wb_sel != 0);
	assign	ctrl_write_ready = i_st_stb && !o_st_stall && i_st_we && (i_st_sel != 0);

	// Wishbone outputs
	assign o_wb_stall = 1'b0;
	assign o_wb_err   = 1'b0;
	assign o_wb_data  = read_data;

	assign o_st_stall = 1'b0;
	assign o_st_err   = 1'b0;

	assign	ctrl_write_ready = i_st_stb && !o_st_stall && i_st_we
					&& i_st_sel != 0;

	// o_st_ack
	always @(posedge i_clk)
	if (i_reset)
		o_st_ack <= 1'b0;
	else
		o_st_ack <= i_st_stb;

	// wide_state
	// {{{
	always @(*)
	begin
		wide_state = 0;
		wide_state[2*DW-SR +: SR] = lfsr_state;
		for(wk=1; wk<2*DW/SR; wk=wk+1)
			wide_state[2*DW-SR-(SR*wk) +: SR]
				= advance_lfsr(wide_state[2*DW-(SR*wk) +: SR]);
	end
	// }}}

	// lfsr_state
	// {{{
	always @(*)
		shift_state = wide_state >>((2*DW-SR)-(8*$countones(i_wb_sel)));
	always @(posedge i_clk)
	if (i_reset)
		lfsr_state <= 0; // initial state
	else begin
		// feedback
		if (rd_data_en || wr_data_en)
			lfsr_state <= shift_state[SR-1:0];

		if (ctrl_write_ready)
		begin // set an initial per-test state
			if (i_st_sel[0])
				lfsr_state[ 0 +: 8] <= i_st_data[ 0 +: 8];
			if (i_st_sel[1])
				lfsr_state[ 8 +: 8] <= i_st_data[ 8 +: 8];
			if (i_st_sel[2])
				lfsr_state[16 +: 8] <= i_st_data[16 +: 8];
			if (i_st_sel[3])
				lfsr_state[24 +: 8] <= i_st_data[24 +: 8];
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
		if (rd_data_en)
		for(rk=0; rk<DW/8; rk=rk+1)
		begin
			if (i_wb_sel[DW/8-1-rk])
			begin
				nxt_rddata[(DW/8-1-rk)*8 +: 8]
					= wide_state[(2*DW-8)-8*rkp +: 8];
				rkp = rkp+1;
			end
		end
	end

	always @(posedge i_clk)
	if (i_reset || !rd_data_en)
		read_data <= 0;
	else
		read_data <= nxt_rddata;
	// }}}
	
	// rd_count, wr_count
	// {{{
	always @(*)
	begin
		rd_count = rd_count_reg;
		wr_count = wr_count_reg;

		// reset counter after lfsr initialization
		if (i_st_stb && i_st_we && (i_st_sel != 0))
		begin
			rd_count = 0;
			wr_count = 0;
		end else for (int i = 0; i < BW; i++)
		if (i_wb_sel[i])
		begin
			rd_count = rd_count + (rd_data_en ? 1 : 0);
			wr_count = wr_count + (wr_data_en ? 1 : 0);
		end
	end

	always @(posedge i_clk)
	if (i_reset)
	begin
		rd_count_reg <= 0;
		wr_count_reg <= 0;
	end else begin
		rd_count_reg <= rd_count;
		wr_count_reg <= wr_count;
	end
	// }}}

	// o_st_data: Error detectıon
	// {{{
	always @(*)
	begin
		wrmatchb = -1;
		wkp = 0;
		if (wr_data_en)
		for(wk=0; wk<DW/8; wk=wk+1)
		if (i_wb_sel[wk])
		begin
			wrmatchb[wk] = (i_wb_data[(DW/8-1-wk)*8 +: 8]
					== lfsr_state[(DW/8-1-wkp)*8 +: 8]);
			wkp = wkp+1;
		end
	end

	always @(posedge i_clk)
	if (i_reset)
		err_flag <= 1'b0;
	else begin
		if (wr_data_en && |(~wrmatchb))
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
		integer	ak;
		reg	[SR-1:0]	fill;
	begin
		fill = istate;
		for(ak=0; ak<SR; ak=ak+1)
		begin
			if (^(fill & POLY))
				fill = { fill[SR-2:0], 1'b1 };
			else
				fill = { fill[SR-2:0], 1'b0 };
		end

		advance_lfsr = fill;
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
