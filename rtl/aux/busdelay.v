///////////////////////////////////////////////////////////////////////////
//
// Filename:	busdelay.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Delay any access to the wishbone bus by a single clock.
//
//	When the first Zip System would not meet the timing requirements of
//	the board it was placed upon, this bus delay was added to help out.
//	It may no longer be necessary, having cleaned some other problems up
//	first, but it will remain here as a means of alleviating timing
//	problems.
//
//	The specific problem takes place on the stall line: a wishbone master
//	*must* know on the first clock whether or not the bus will stall.
//
//
//
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
module	busdelay(i_clk,
		// The input bus
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
			o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
		// The delayed bus
		o_dly_cyc, o_dly_stb, o_dly_we, o_dly_addr, o_dly_data,
			i_dly_ack, i_dly_stall, i_dly_data, i_dly_err);
	parameter	AW=32, DW=32;
	input	i_clk;
	// Input/master bus
	input				i_wb_cyc, i_wb_stb, i_wb_we;
	input		[(AW-1):0]	i_wb_addr;
	input		[(DW-1):0]	i_wb_data;
	output	reg			o_wb_ack;
	output	wire			o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;
	output	wire			o_wb_err;
	// Delayed bus
	output	reg			o_dly_cyc, o_dly_stb, o_dly_we;
	output	reg	[(AW-1):0]	o_dly_addr;
	output	reg	[(DW-1):0]	o_dly_data;
	input				i_dly_ack;
	input				i_dly_stall;
	input		[(DW-1):0]	i_dly_data;
	input				i_dly_err;

	initial	o_dly_cyc = 1'b0;
	initial	o_dly_stb = 1'b0;

	always @(posedge i_clk)
		o_dly_cyc <= i_wb_cyc;
	// Add the i_wb_cyc criteria here, so we can simplify the o_wb_stall
	// criteria below, which would otherwise *and* these two.
	always @(posedge i_clk)
		if (~o_wb_stall)
			o_dly_stb <= ((i_wb_cyc)&&(i_wb_stb));
	always @(posedge i_clk)
		if (~o_wb_stall)
			o_dly_we  <= i_wb_we;
	always @(posedge i_clk)
		if (~o_wb_stall)
			o_dly_addr<= i_wb_addr;
	always @(posedge i_clk)
		if (~o_wb_stall)
			o_dly_data <= i_wb_data;
	always @(posedge i_clk)
		o_wb_ack  <= (i_dly_ack)&&(o_dly_cyc)&&(i_wb_cyc);
	always @(posedge i_clk)
		o_wb_data <= i_dly_data;

	// Our only non-delayed line, yet still really delayed.  Perhaps
	// there's a way to register this?
	// o_wb_stall <= (i_wb_cyc)&&(i_wb_stb) ... or some such?
	// assign o_wb_stall=((i_wb_cyc)&&(i_dly_stall)&&(o_dly_stb));//&&o_cyc
	assign	o_wb_stall = ((i_dly_stall)&&(o_dly_stb));//&&o_cyc
	assign	o_wb_err   = i_dly_err;

endmodule
