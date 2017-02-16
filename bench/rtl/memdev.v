///////////////////////////////////////////////////////////////////////////
//
// Filename:	memdev.v
//
// Project:	XuLA2 board
//
// Purpose:	This file is really simple: it creates an on-chip memory,
//		accessible via the wishbone bus, that can be used in this
//	project.  The memory has single cycle access--although getting to the
//	memory from the ZipCPU may cost another cycle or two in access.  Either
//	way, operations can be pipelined for greater speed.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
//
module	memdev(i_clk, i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
		o_wb_ack, o_wb_stall, o_wb_data);
	parameter	AW=15, DW=32;
	input				i_clk, i_wb_cyc, i_wb_stb, i_wb_we;
	input		[(AW-1):0]	i_wb_addr;
	input		[(DW-1):0]	i_wb_data;
	output	reg			o_wb_ack;
	output	wire			o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;

	reg	[(DW-1):0]	mem	[0:((1<<AW)-1)];
	always @(posedge i_clk)
		o_wb_data <= mem[i_wb_addr];
	always @(posedge i_clk)
		if ((i_wb_stb)&&(i_wb_we))
			mem[i_wb_addr] <= i_wb_data;
	always @(posedge i_clk)
		o_wb_ack <= (i_wb_stb);
	assign	o_wb_stall = 1'b0;

endmodule
