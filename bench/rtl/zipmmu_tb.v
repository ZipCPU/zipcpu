////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipmmu_tb.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
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
////////////////////////////////////////////////////////////////////////////////
//
//
module zipmmu_tb(i_clk, i_reset, i_ctrl_cyc_stb, i_wbm_cyc, i_wbm_stb, i_wb_we,
				i_wb_addr, i_wb_data,
			o_rtn_stall, o_rtn_ack, o_rtn_err,
				o_rtn_miss, o_rtn_data);
	parameter	CPU_ADDRESS_WIDTH=28,
			MEMORY_ADDRESS_WIDTH=15;
	localparam	AW= CPU_ADDRESS_WIDTH,
			MAW= MEMORY_ADDRESS_WIDTH;
	input			i_clk, i_reset;
	//
	input			i_ctrl_cyc_stb;
	//
	input			i_wbm_cyc, i_wbm_stb;
	//
	input			i_wb_we;
	input	[(32-1):0]	i_wb_addr;
	input	[(32-1):0]	i_wb_data;
	//
	// Here's where we return information on either our slave/control bus
	// or the memory bus we are controlled from.  Note that we share these
	// wires ...
	output	wire		o_rtn_stall, o_rtn_ack, o_rtn_err, o_rtn_miss;
	output	wire	[(32-1):0]	o_rtn_data;


	wire	mem_cyc, mem_stb, mem_we, mem_ack, mem_stall;
	wire	[31:0]	mem_idata, mem_odata;
	wire	[27:0]	mem_addr;
	reg		mem_err;

	wire	ign_stb, ign_we, ign_cache;
	wire	[15:0]	ign_p;
	wire	[19:0]	ign_v;

	//
	// mut = Module Under Test
	//
	zipmmu	#(.ADDRESS_WIDTH(CPU_ADDRESS_WIDTH))
		mut(i_clk, i_reset, i_ctrl_cyc_stb, i_wbm_cyc, i_wbm_stb,
			i_wb_we, i_wb_addr, i_wb_data,
			mem_cyc, mem_stb, mem_we, mem_addr,
					mem_idata,
				mem_stall, mem_ack, mem_err, mem_odata,
			o_rtn_stall, o_rtn_ack, o_rtn_err, o_rtn_miss,
				o_rtn_data,
			ign_stb, ign_we, ign_p, ign_v, ign_cache);

	memdev #(MAW) ram(i_clk, mem_cyc, mem_stb,mem_we, mem_addr[(MAW-1):0],
		mem_idata, mem_ack, mem_stall, mem_odata);

	always@(posedge i_clk)
		mem_err <= ((mem_stb)&&(!mem_cyc))||((mem_stb)&&(mem_addr[(AW-1):MAW]!={{(AW-MAW-1){1'b0}}, 1'b1}));

endmodule
