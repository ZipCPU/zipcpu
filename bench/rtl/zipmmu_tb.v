////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipmmu_tb.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a test-bench wrapper for the MMU.  It's used to
//		test whether or not the MMU works independent of the ZipCPU
//	itself.  The rest of the test bench is a C++ Verilator-enabled program.
//
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
module zipmmu_tb(i_clk, i_reset, i_ctrl_cyc_stb, i_wbm_cyc, i_wbm_stb, i_wb_we,
				i_exe, i_wb_addr, i_wb_data, i_wb_sel, i_gie,
			o_rtn_stall, o_rtn_ack, o_rtn_err,
				o_rtn_miss, o_rtn_data);
	parameter	CPU_ADDRESS_WIDTH=30,
			MEMORY_ADDRESS_WIDTH=15;
	localparam	AW= CPU_ADDRESS_WIDTH,
			MAW= MEMORY_ADDRESS_WIDTH,
			LGTBL = 6,
			LGPGSZB=12;
	input			i_clk, i_reset;
	//
	input			i_ctrl_cyc_stb;
	//
	input			i_wbm_cyc, i_wbm_stb;
	//
	input			i_exe;
	input			i_wb_we;
	input	[(32-3):0]	i_wb_addr;
	input	[(32-1):0]	i_wb_data;
	input	[(32/8-1):0]	i_wb_sel;
	input			i_gie;
	//
	// Here's where we return information on either our slave/control bus
	// or the memory bus we are controlled from.  Note that we share these
	// wires ...
	output	wire		o_rtn_stall, o_rtn_ack, o_rtn_err, o_rtn_miss;
	output	wire	[(32-1):0]	o_rtn_data;



	wire			mem_cyc	/* verilator public_flat */,
				mem_stb	/* verilator public_flat */,
				mem_we	/* verilator public_flat */,
				mem_ack	/* verilator public_flat */,
				mem_stall	/* verilator public_flat */;
	wire	[31:0]		mem_idata	/* verilator public_flat */,
				mem_odata	/* verilator public_flat */;
	wire	[(32/8-1):0]	mem_sel;
	wire	[(CPU_ADDRESS_WIDTH-1):0]	mem_addr /* verilator public_flat */;
	reg			mem_err	/* verilator public_flat */;

	wire		mmus_ack, mmus_stall;
	wire	[31:0]	mmus_data;

	wire		rtn_ack, rtn_stall;
	wire	[31:0]	rtn_data;

	wire	ign_stb, ign_we, ign_cache;
	wire	[(32-LGPGSZB-1):0]	ign_p;
	wire	[(32-LGPGSZB-1):0]	ign_v;

	//
	// mut = Module Under Test
	//
	zipmmu	#(.ADDRESS_WIDTH(CPU_ADDRESS_WIDTH),
		.LGTBL(LGTBL),.PLGPGSZB(LGPGSZB))
		mut(i_clk, i_reset,
			// Slave access
			i_ctrl_cyc_stb, i_wb_we, i_wb_addr[(LGTBL+1):0],
				i_wb_data,
				mmus_ack, mmus_stall, mmus_data,
			i_wbm_cyc, i_wbm_stb, i_wb_we, i_exe,
				i_wb_addr, i_wb_data, i_wb_sel, i_gie,
			mem_cyc, mem_stb, mem_we, mem_addr, mem_idata, mem_sel,
				mem_stall, (mem_ack)&&(!mem_err), mem_err, mem_odata,
			rtn_stall, rtn_ack, o_rtn_err, o_rtn_miss,
				rtn_data,
			ign_stb, ign_we, ign_p, ign_v, ign_cache);

	memdev #(MAW+2) ram(i_clk,
		mem_cyc, mem_stb, mem_we, mem_addr[(MAW-1):0], mem_idata,
				mem_sel,
			mem_ack, mem_stall, mem_odata);

	always@(posedge i_clk)
	if (i_reset)
		mem_err <= 1'b0;
	else if (!mem_cyc)
		mem_err <= 1'b0;
	else
		mem_err <= (mem_err)||((mem_stb)&&(mem_addr[(AW-1):MAW]
					!= {{(AW-MAW-1){1'b0}}, 1'b1}));


	assign	o_rtn_stall = (i_wbm_cyc)&&(rtn_stall);
	assign	o_rtn_ack   = (i_wbm_cyc)?(rtn_ack) :mmus_ack;
	assign	o_rtn_data  = (i_wbm_cyc)?(rtn_data):mmus_data;

	// Make Verilator happy
	// verilator lint_on UNUSED
	wire	[2+(32-LGPGSZB)+(32-LGPGSZB)+1+1-1:0]	unused;
	assign	unused = { ign_stb, ign_we, ign_p, ign_v, ign_cache, mmus_stall };
	// verilator lint_off UNUSED
endmodule
