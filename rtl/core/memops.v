///////////////////////////////////////////////////////////////////////////
//
// Filename:	memops.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU.
//
//	In the interests of code simplicity, this memory operator is 
//	susceptible to unknown results should a new command be sent to it
//	before it completes the last one.  Unpredictable results might then
//	occurr.
//
//	20150919 -- Added support for handling BUS ERR's (i.e., the WB
//		error signal).
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015, Gisselquist Technology, LLC
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
///////////////////////////////////////////////////////////////////////////
//
module	memops(i_clk, i_rst, i_stb, i_lock,
		i_op, i_addr, i_data, i_oreg,
			o_busy, o_valid, o_err, o_wreg, o_result,
		o_wb_cyc_gbl, o_wb_cyc_lcl,
			o_wb_stb_gbl, o_wb_stb_lcl,
			o_wb_we, o_wb_addr, o_wb_data,
		i_wb_ack, i_wb_stall, i_wb_err, i_wb_data);
	parameter	ADDRESS_WIDTH=32, IMPLEMENT_LOCK=0;
	localparam	AW=ADDRESS_WIDTH;
	input			i_clk, i_rst;
	input			i_stb, i_lock;
	// CPU interface
	input			i_op;
	input		[31:0]	i_addr;
	input		[31:0]	i_data;
	input		[4:0]	i_oreg;
	// CPU outputs
	output	wire		o_busy;
	output	reg		o_valid;
	output	reg		o_err;
	output	reg	[4:0]	o_wreg;
	output	reg	[31:0]	o_result;
	// Wishbone outputs
	output	wire		o_wb_cyc_gbl;
	output	reg		o_wb_stb_gbl;
	output	wire		o_wb_cyc_lcl;
	output	reg		o_wb_stb_lcl;
	output	reg		o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	reg	[31:0]	o_wb_data;
	// Wishbone inputs
	input			i_wb_ack, i_wb_stall, i_wb_err;
	input		[31:0]	i_wb_data;

	reg	r_wb_cyc_gbl, r_wb_cyc_lcl;
	wire	gbl_stb, lcl_stb;
	assign	lcl_stb = (i_stb)&&(i_addr[31:24]==8'hff);
	assign	gbl_stb = (i_stb)&&(i_addr[31:24]!=8'hff);

	initial	r_wb_cyc_gbl = 1'b0;
	initial	r_wb_cyc_lcl = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
		begin
			r_wb_cyc_gbl <= 1'b0;
			r_wb_cyc_lcl <= 1'b0;
		end else if ((r_wb_cyc_gbl)||(r_wb_cyc_lcl))
		begin
			if ((i_wb_ack)||(i_wb_err))
			begin
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
			end
		end else if (i_stb) // New memory operation
		begin // Grab the wishbone
			r_wb_cyc_lcl <= lcl_stb;
			r_wb_cyc_gbl <= gbl_stb;
		end
	always @(posedge i_clk)
		if (o_wb_cyc_gbl)
			o_wb_stb_gbl <= (o_wb_stb_gbl)&&(i_wb_stall);
		else
			o_wb_stb_gbl <= gbl_stb; // Grab wishbone on new operation
	always @(posedge i_clk)
		if (o_wb_cyc_lcl)
			o_wb_stb_lcl <= (o_wb_stb_lcl)&&(i_wb_stall);
		else
			o_wb_stb_lcl  <= lcl_stb; // Grab wishbone on new operation
	always @(posedge i_clk)
		if (i_stb)
		begin
			o_wb_we   <= i_op;
			o_wb_data <= i_data;
			o_wb_addr <= i_addr[(AW-1):0];
		end

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
		o_valid <= ((o_wb_cyc_gbl)||(o_wb_cyc_lcl))&&(i_wb_ack)&&(~o_wb_we);
	initial	o_err = 1'b0;
	always @(posedge i_clk)
		o_err <= ((o_wb_cyc_gbl)||(o_wb_cyc_lcl))&&(i_wb_err);
	assign	o_busy = (o_wb_cyc_gbl)||(o_wb_cyc_lcl);

	always @(posedge i_clk)
		if (i_stb)
			o_wreg    <= i_oreg;
	always @(posedge i_clk)
		if (i_wb_ack)
			o_result <= i_wb_data;

	generate
	if (IMPLEMENT_LOCK != 0)
	begin
		reg	lock_gbl, lock_lcl;

		initial	lock_gbl = 1'b0;
		initial	lock_lcl = 1'b0;

		always @(posedge i_clk)
		begin
			lock_gbl <= (i_lock)&&((r_wb_cyc_gbl)||(lock_gbl));
			lock_lcl <= (i_lock)&&((r_wb_cyc_lcl)||(lock_lcl));
		end

		assign	o_wb_cyc_gbl = (r_wb_cyc_gbl)||(lock_gbl);
		assign	o_wb_cyc_lcl = (r_wb_cyc_lcl)||(lock_lcl);
	end else begin
		assign	o_wb_cyc_gbl = (r_wb_cyc_gbl);
		assign	o_wb_cyc_lcl = (r_wb_cyc_lcl);
	end endgenerate
endmodule
