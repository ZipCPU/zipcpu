////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipmmu_tb.v
// {{{
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
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
module zipmmu_tb #(
		// {{{
		parameter	CPU_ADDRESS_WIDTH=30,
				MEMORY_ADDRESS_WIDTH=15,
		localparam	AW= CPU_ADDRESS_WIDTH,
				MAW= MEMORY_ADDRESS_WIDTH,
				LGTBL = 6,
				LGPGSZB=12
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_ctrl_cyc_stb,
		//
		input	wire			i_wbm_cyc, i_wbm_stb,
		//
		input	wire			i_wb_we,
		input	wire			i_exe,
		input	wire	[(32-3):0]	i_wb_addr,
		input	wire	[(32-1):0]	i_wb_data,
		input	wire	[(32/8-1):0]	i_wb_sel,
		input	wire			i_gie,
		//
		// Here's where we return information on either our
		// slave/control bus, or the memory bus we are controlled
		// from.  Note that we share these wires ...
		output	wire			o_rtn_stall, o_rtn_ack,
						o_rtn_err, o_rtn_miss,
		output	wire	[(32-1):0]	o_rtn_data
`ifdef	VZIPMMU_TB
		, output	wire		r_valid, wr_vtable,
						wr_ptable,
						wr_control,
						z_context,
		output	wire	[15:0]		r_context_word,
		output	wire			r_pending,
						r_we,
		output	wire	[29:0]		r_addr,
		output	wire	[31:0]		r_data,
		output	wire			mem_cyc, mem_stb, mem_we,
		output	wire	[31:0]		mem_odata,
		output	wire	[(CPU_ADDRESS_WIDTH-1):0]	mem_addr,
		output	reg			mem_err,
		output	wire			kernel_context,
		output	wire	[5:0]		s_tlb_addr,
		output	wire			s_pending,
		output	wire			s_tlb_hit, s_tlb_miss,
						ro_flag, simple_miss,
						ro_miss, exe_miss, table_err,
		output	wire			tlb_valid,
		output	wire	[19:0]		tlb_pdata,
		output	wire	[19:0]		tlb_vdata,
		output	wire	[15:0]		tlb_cdata
`endif
		// }}}
	);

`ifndef	VZIPMMU_TB
	wire			mem_cyc,
				mem_stb,
				mem_we;
	wire	[(CPU_ADDRESS_WIDTH-1):0]	mem_addr;
	reg			mem_err;
	wire	[31:0]		mem_odata;
`endif
	wire			mem_ack, mem_stall;
	wire	[31:0]		mem_idata;
	wire	[(32/8-1):0]	mem_sel;

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
	zipmmu	#(
		.ADDRESS_WIDTH(CPU_ADDRESS_WIDTH),
		.LGTBL(LGTBL),.PLGPGSZB(LGPGSZB)
	) mut (
		// {{{
		i_clk, i_reset,
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
			ign_stb, ign_we, ign_p, ign_v, ign_cache
		// }}}
	);

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

`ifdef	VZIPMMU_TB
	reg	[5:0]	last_index, r_last_index;
	wire	[63:0]	pre_valid, shifted_valid;

	assign	r_we = mut.r_we;
	assign	r_valid = mut.r_valid;
	assign	wr_vtable = mut.wr_vtable;
	assign	wr_ptable = mut.wr_ptable;
	assign	wr_control = mut.wr_control;
	assign	z_context  = mut.z_context ;
	assign	r_context_word  = mut.r_context_word;
	assign	r_pending  = mut.r_pending;
	assign	r_we       = mut.r_we;
	assign	r_addr     = mut.r_addr;
	assign	r_data     = mut.r_data;
	assign	kernel_context = mut.kernel_context;

	assign	s_tlb_addr = mut.s_tlb_addr;
	assign	s_pending  = mut.s_pending;
	assign	s_tlb_hit  = mut.s_tlb_hit;
	assign	s_tlb_miss = mut.s_tlb_miss;
	assign	ro_flag = mut.ro_flag;
	assign	simple_miss = mut.simple_miss;
	assign	ro_miss = mut.ro_miss;
	assign	exe_miss = mut.exe_miss;
	assign	table_err = mut.table_err;
	assign	pre_valid = mut.tlb_valid;
	assign	shifted_valid = pre_valid >> last_index;
	assign	tlb_valid = shifted_valid[0];
	assign	tlb_pdata = mut.tlb_pdata[last_index];
	assign	tlb_vdata = mut.tlb_vdata[last_index];
	assign	tlb_cdata = mut.tlb_cdata[last_index];

	always @(*)
	if (i_ctrl_cyc_stb && i_wb_we && i_wb_addr[7])
		last_index = i_wb_addr[6:1];
	else
		last_index = r_last_index;

	always @(posedge i_clk)
	if (i_ctrl_cyc_stb && i_wb_we && i_wb_addr[7])
		r_last_index <= i_wb_addr[6:1];

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	unused_vbench;
	assign	unused_vbench = &{ 1'b0, shifted_valid[63:1] };
	// verilator lint_on UNUSED
`endif

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_stb, ign_we, ign_p, ign_v,
				ign_cache, mmus_stall };
	// verilator lint_on  UNUSED
endmodule
