////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/rtl/axi_tb.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Top level test infrastructure for all AXI and AXI-lite
//		configurations of the ZipCPU.  Contains:
//
//	- Memory
//	- Console port	(Not a serial port--$write's directly to console here)
//	- External debug access
//	- WBScope
//
//	Since these are the capabilities that will be required to test the
//	ZipCPU.
//
//	The goal is to be able to run the CPU test program, in all of the
//	ZipCPU's various AXI and AXI-lite configurations, and by using it to
//	routinely smoke out any bugs before making any releases.
//
//	A similar test bench exists for testing the Wishbone version(s) of
//	the ZipCPU.
//
// Creator:	Dan Gisselquist, Ph.D.
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
//
`default_nettype none
`timescale 1ns/1ns
// }}}
module	axi_tb #(
		// {{{
		parameter	ADDRESS_WIDTH        = 28,	//Width in bytes
		parameter	BUS_WIDTH            = 32,
		// Verilator lint_off WIDTH
		parameter [0:0]	OPT_ZIPAXIL          = 1'b1,
		parameter [0:0]	OPT_PIPELINED        = 1'b1,
		parameter	OPT_LGICACHE         = 12,
		parameter	OPT_LGDCACHE         = 12,
		parameter	OPT_MPY              = 3,
		parameter [0:0]	OPT_DIV              = 1'b1,
		parameter [0:0]	OPT_SHIFTS           = 1'b1,
		parameter [0:0]	OPT_LOCK             = 1'b1,
		parameter [0:0]	OPT_EARLY_BRANCHING  = 1'b1,
		parameter [0:0]	OPT_LOWPOWER         = 1'b1,
		parameter [0:0]	OPT_DISTRIBUTED_REGS = 1'b1,
		parameter [0:0]	OPT_USERMODE         = 1'b1,
		parameter [0:0]	OPT_CLKGATE          = 1'b1,
		parameter [0:0]	OPT_DBGPORT          = 1'b1,
		parameter [0:0]	OPT_TRACE_PORT       = 1'b1,
		parameter [0:0]	OPT_CIS              = 1'b1,
		// verilator lint_off UNUSED
		parameter [0:0]	OPT_WRAP             = 1'b1,
		// verilator lint_on UNUSED
		parameter	OPT_SMP              = 1,
		parameter	MEM_FILE = "cput3st",
		parameter	CONSOLE_FILE = "console.txt",
		parameter	ID_WIDTH = 4,
		localparam	IW = ID_WIDTH,
		parameter	LGMEMSZ = ADDRESS_WIDTH-2,
		// Verilator lint_off UNUSED
		parameter [0:0]	DUMP_TO_VCD = 1'b0,
		parameter	VCD_FILE = "dump.vcd"
		// Verilator lint_on  UNUSED
		// Verilator lint_on  WIDTH
		// }}}
	) (
		// {{{
`ifdef	VERILATOR
		input	wire				i_aclk, i_aresetn,
		// Sim control input(s)
		// {{{
		input	wire				sim_awvalid,
		output	wire				sim_awready,
		input	wire	[ADDRESS_WIDTH:0]	sim_awaddr,
		input	wire	[2:0]			sim_awprot,

		input	wire				sim_wvalid,
		output	wire				sim_wready,
		input	wire	[31:0]			sim_wdata,
		input	wire	[3:0]			sim_wstrb,

		output	wire				sim_bvalid,
		input	wire				sim_bready,
		output	wire	[1:0]			sim_bresp,

		input	wire				sim_arvalid,
		output	wire				sim_arready,
		input	wire	[ADDRESS_WIDTH:0]	sim_araddr,
		input	wire	[2:0]			sim_arprot,

		output	wire				sim_rvalid,
		input	wire				sim_rready,
		output	wire	[31:0]			sim_rdata,
		output	wire	[1:0]			sim_rresp,
		// }}}
		input	wire				i_sim_int,
		//
		// "Profiler" support.  This is a simulation only port.
		// {{{
		output	wire				o_prof_stb,
		output	wire	[ADDRESS_WIDTH-1:0]	o_prof_addr,
		output	wire	[31:0]			o_prof_ticks
		// }}}
`endif
		// }}}
	);

	// Local declarations
	// {{{
	genvar	gk;
	parameter [31:0]	RESET_ADDRESS = { {(32-ADDRESS_WIDTH){1'b0}}, MEMORY_ADDR };
	localparam	AW = ADDRESS_WIDTH;
	parameter [AW-1:0]	SCOPE_ADDR   = { 4'b0001, {(AW-4){1'b0}} };
	parameter [AW-1:0]	CONSOLE_ADDR = { 4'b0010, {(AW-4){1'b0}} };
	parameter [AW-1:0]	SMP_BASE_ADDR= { 4'b0011, {(AW-4){1'b0}} };
	parameter [AW-1:0]	MEMORY_ADDR  = { 2'b01, {(AW-2){1'b0}} };
	parameter [AW-1:0]	AXILP_ADDR   = { {(AW-24){1'b1}},{(24){1'b0}} };

	localparam	MIN_SMP = (OPT_SMP < 2) ? 1:OPT_SMP;
	parameter [OPT_SMP*AW-1:0]	SMP_ADDR= SMP_ADDR_fn(MIN_SMP);
	parameter [OPT_SMP*AW-1:0]	SMP_MASK= SMP_MASK_fn(MIN_SMP);

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	function automatic [OPT_SMP*AW-1:0] SMP_ADDR_fn(input integer min_smp);
		// {{{
		integer	ik, offset;
	begin
		SMP_ADDR_fn = {(OPT_SMP){SMP_BASE_ADDR}};

		for(ik=1; ik<OPT_SMP; ik=ik+1)
		begin
			offset = ik;
			SMP_ADDR_fn[ik * AW + 9 +: $clog2(OPT_SMP)+1]
						= offset[$clog2(OPT_SMP):0];
		end

	end endfunction
	// }}}

	function automatic [OPT_SMP*AW-1:0] SMP_MASK_fn(input integer min_smp);
		// {{{
		integer	ik;
	begin
		SMP_MASK_fn = {(OPT_SMP){ 4'b1111, {(AW-4){1'b0}} }};

		for(ik=0; ik<OPT_SMP; ik=ik+1)
		begin
			SMP_MASK_fn[ik * AW + 9 +: $clog2(OPT_SMP)+1]
						= {($clog2(OPT_SMP)+1){1'b1}};
		end

	end endfunction
	// }}}
	// Verilator coverage_on
	// Verilator lint_on  UNUSED

	// localparam	LGFIFO = 4;

	// CPU declarations
	// {{{
	localparam		RESET_DURATION = 10;
	localparam	[0:0]	OPT_SIM = 1'b1;
`ifdef	VERILATOR
	localparam	[0:0]	OPT_PROFILER = 1'b1;
`else
	localparam	[0:0]	OPT_PROFILER = 1'b0;
`endif
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire		cpu_int;
	// Verilator lint_on  UNUSED
	wire		scope_int;
	wire	[31:0]	cpu_trace;
	// Verilator coverage_on

	wire	[OPT_SMP-1:0]	cpu_reset;
	wire	[OPT_SMP-1:0]	cpu_halted;
	wire	[OPT_SMP-1:0]	cpu_gie;
	wire	[OPT_SMP-1:0]	cpu_op_stall, cpu_pf_stall, cpu_i_count;

	wire	pic_interrupt, watchdog_reset;

	// dbg*
	// {{{
	wire			dbg_awvalid, dbg_awready;
	wire	[AW:0]		dbg_awaddr;
	wire	[2:0]		dbg_awprot;

	wire			dbg_wvalid, dbg_wready;
	wire	[31:0]		dbg_wdata;
	wire	[3:0]		dbg_wstrb;

	wire			dbg_bvalid, dbg_bready;
	wire	[1:0]		dbg_bresp;

	wire			dbg_arvalid, dbg_arready;
	wire	[AW:0]		dbg_araddr;
	wire	[2:0]		dbg_arprot;

	wire			dbg_rvalid, dbg_rready;
	wire	[31:0]		dbg_rdata;
	wire	[1:0]		dbg_rresp;
	// }}}

	// cpui*
	// {{{
	wire	[OPT_SMP-1:0]		cpui_awvalid, cpui_awready;
	wire	[OPT_SMP*IW-1:0]	cpui_awid;
	wire	[OPT_SMP*AW-1:0]	cpui_awaddr;
	wire	[OPT_SMP*8-1:0]		cpui_awlen;
	wire	[OPT_SMP*3-1:0]		cpui_awsize;
	wire	[OPT_SMP*2-1:0]		cpui_awburst;
	wire	[OPT_SMP-1:0]		cpui_awlock;
	wire	[OPT_SMP*4-1:0]		cpui_awcache;
	wire	[OPT_SMP*3-1:0]		cpui_awprot;
	wire	[OPT_SMP*4-1:0]		cpui_awqos;

	wire	[OPT_SMP-1:0]		cpui_wvalid, cpui_wready;
	wire	[OPT_SMP*BUS_WIDTH-1:0]	cpui_wdata;
	wire [OPT_SMP*BUS_WIDTH/8-1:0]	cpui_wstrb;
	wire	[OPT_SMP-1:0]		cpui_wlast;

	wire	[OPT_SMP-1:0]		cpui_bvalid, cpui_bready;
	wire	[OPT_SMP*IW-1:0]	cpui_bid;
	wire	[OPT_SMP*2-1:0]		cpui_bresp;

	wire	[OPT_SMP-1:0]		cpui_arvalid, cpui_arready;
	wire	[OPT_SMP*IW-1:0]	cpui_arid;
	wire	[OPT_SMP*AW-1:0]	cpui_araddr;
	wire	[OPT_SMP*8-1:0]		cpui_arlen;
	wire	[OPT_SMP*3-1:0]		cpui_arsize;
	wire	[OPT_SMP*2-1:0]		cpui_arburst;
	wire	[OPT_SMP-1:0]		cpui_arlock;
	wire	[OPT_SMP*4-1:0]		cpui_arcache;
	wire	[OPT_SMP*3-1:0]		cpui_arprot;
	wire	[OPT_SMP*4-1:0]		cpui_arqos;


	wire	[OPT_SMP-1:0]		cpui_rvalid, cpui_rready;
	wire	[OPT_SMP*IW-1:0]	cpui_rid;
	wire	[OPT_SMP*BUS_WIDTH-1:0]	cpui_rdata;
	wire	[OPT_SMP*2-1:0]		cpui_rresp;
	wire	[OPT_SMP-1:0]		cpui_rlast;
	// }}}

	// cpud*
	// {{{
	wire	[OPT_SMP-1:0]	cpud_awvalid, cpud_awready;
	wire	[OPT_SMP*IW-1:0]	cpud_awid;
	wire	[OPT_SMP*AW-1:0]	cpud_awaddr;
	wire	[OPT_SMP*8-1:0]		cpud_awlen;
	wire	[OPT_SMP*3-1:0]		cpud_awsize;
	wire	[OPT_SMP*2-1:0]		cpud_awburst;
	wire	[OPT_SMP-1:0]		cpud_awlock;
	wire	[OPT_SMP*4-1:0]		cpud_awcache;
	wire	[OPT_SMP*3-1:0]		cpud_awprot;
	wire	[OPT_SMP*4-1:0]		cpud_awqos;

	wire	[OPT_SMP-1:0]		cpud_wvalid, cpud_wready;
	wire	[OPT_SMP*BUS_WIDTH-1:0]	cpud_wdata;
	wire [OPT_SMP*BUS_WIDTH/8-1:0]	cpud_wstrb;
	wire	[OPT_SMP-1:0]		cpud_wlast;

	wire	[OPT_SMP-1:0]		cpud_bvalid, cpud_bready;
	wire	[OPT_SMP*IW-1:0]	cpud_bid;
	wire	[OPT_SMP*2-1:0]		cpud_bresp;

	wire	[OPT_SMP-1:0]		cpud_arvalid, cpud_arready;
	wire	[OPT_SMP*IW-1:0]	cpud_arid;
	wire	[OPT_SMP*AW-1:0]	cpud_araddr;
	wire	[OPT_SMP*8-1:0]		cpud_arlen;
	wire	[OPT_SMP*3-1:0]		cpud_arsize;
	wire	[OPT_SMP*2-1:0]		cpud_arburst;
	wire	[OPT_SMP-1:0]		cpud_arlock;
	wire	[OPT_SMP*4-1:0]		cpud_arcache;
	wire	[OPT_SMP*3-1:0]		cpud_arprot;
	wire	[OPT_SMP*4-1:0]		cpud_arqos;


	wire	[OPT_SMP-1:0]		cpud_rvalid, cpud_rready;
	wire	[OPT_SMP*IW-1:0]	cpud_rid;
	wire	[OPT_SMP*BUS_WIDTH-1:0]	cpud_rdata;
	wire	[OPT_SMP*2-1:0]		cpud_rresp;
	wire	[OPT_SMP-1:0]		cpud_rlast;
	// }}}

	// smpfull*
	// {{{
	wire	[OPT_SMP-1:0]	smpfull_awvalid, smpfull_awready;
	wire [OPT_SMP*IW-1:0]	smpfull_awid;
	wire [OPT_SMP*AW-1:0]	smpfull_awaddr;
	wire	[OPT_SMP*8-1:0]	smpfull_awlen;
	wire	[OPT_SMP*3-1:0]	smpfull_awsize;
	wire	[OPT_SMP*2-1:0]	smpfull_awburst;
	wire	[OPT_SMP-1:0]	smpfull_awlock;
	wire	[OPT_SMP*4-1:0]	smpfull_awcache;
	wire	[OPT_SMP*3-1:0]	smpfull_awprot;
	wire	[OPT_SMP*4-1:0]	smpfull_awqos;

	wire	[OPT_SMP-1:0]		smpfull_wvalid, smpfull_wready;
	wire [OPT_SMP*BUS_WIDTH-1:0]	smpfull_wdata;
	wire [OPT_SMP*BUS_WIDTH/8-1:0]	smpfull_wstrb;
	wire	[OPT_SMP-1:0]		smpfull_wlast;

	wire	[OPT_SMP-1:0]	smpfull_bvalid, smpfull_bready;
	wire [OPT_SMP*IW-1:0]	smpfull_bid;
	wire	[OPT_SMP*2-1:0]	smpfull_bresp;

	wire	[OPT_SMP-1:0]	smpfull_arvalid, smpfull_arready;
	wire [OPT_SMP*IW-1:0]	smpfull_arid;
	wire [OPT_SMP*AW-1:0]	smpfull_araddr;
	wire	[OPT_SMP*8-1:0]	smpfull_arlen;
	wire	[OPT_SMP*3-1:0]	smpfull_arsize;
	wire	[OPT_SMP*2-1:0]	smpfull_arburst;
	wire	[OPT_SMP-1:0]	smpfull_arlock;
	wire	[OPT_SMP*4-1:0]	smpfull_arcache;
	wire	[OPT_SMP*3-1:0]	smpfull_arprot;
	wire	[OPT_SMP*4-1:0]	smpfull_arqos;

	wire	[OPT_SMP-1:0]	smpfull_rvalid, smpfull_rready;
	wire [OPT_SMP*IW-1:0]	smpfull_rid;
	wire [OPT_SMP*BUS_WIDTH-1:0]	smpfull_rdata;
	wire	[OPT_SMP*2-1:0]	smpfull_rresp;
	wire	[OPT_SMP-1:0]	smpfull_rlast;
	// }}}

	// }}}

	// Memory declarations
	// {{{
	integer	rk;
	wire	ram_we, ram_rd;
	wire	[LGMEMSZ-$clog2(BUS_WIDTH/8)-1:0]	ram_waddr, ram_raddr;
	wire	[BUS_WIDTH-1:0]	ram_wdata;
	wire [BUS_WIDTH/8-1:0]	ram_wstrb;
	wire	[BUS_WIDTH-1:0]	ram_rdata;

	wire	[BUS_WIDTH-1:0]	ram_wdata_swap;
	reg	[BUS_WIDTH-1:0]	ram_rdata_swap;
	wire [BUS_WIDTH/8-1:0]	ram_wstrb_swap;


	reg	[BUS_WIDTH-1:0]	ram [0:(1<<(LGMEMSZ-$clog2(BUS_WIDTH/8)))-1];

	// mem*
	// {{{
	wire			mem_awvalid, mem_awready;
	wire	[IW-1:0]	mem_awid;
	wire	[AW-1:0]	mem_awaddr;
	wire	[7:0]		mem_awlen;
	wire	[2:0]		mem_awsize;
	wire	[1:0]		mem_awburst;
	wire			mem_awlock;
	wire	[3:0]		mem_awcache;
	wire	[2:0]		mem_awprot;
	wire	[3:0]		mem_awqos;

	wire			mem_wvalid, mem_wready;
	wire	[BUS_WIDTH-1:0]	mem_wdata;
	wire [BUS_WIDTH/8-1:0]	mem_wstrb;
	wire			mem_wlast;

	wire			mem_bvalid, mem_bready;
	wire	[IW-1:0]	mem_bid;
	wire	[1:0]		mem_bresp;

	wire			mem_arvalid, mem_arready;
	wire	[IW-1:0]	mem_arid;
	wire	[AW-1:0]	mem_araddr;
	wire	[7:0]		mem_arlen;
	wire	[2:0]		mem_arsize;
	wire	[1:0]		mem_arburst;
	wire			mem_arlock;
	wire	[3:0]		mem_arcache;
	wire	[2:0]		mem_arprot;
	wire	[3:0]		mem_arqos;


	wire			mem_rvalid, mem_rready;
	wire	[IW-1:0]	mem_rid;
	wire	[BUS_WIDTH-1:0]		mem_rdata;
	wire	[1:0]		mem_rresp;
	wire			mem_rlast;
	// }}}

	// }}}

	// Console declarations
	// {{{

	// con*
	// {{{
	wire			con_awvalid, con_awready;
	wire	[IW-1:0]	con_awid;
	wire	[AW-1:0]	con_awaddr;
	wire	[7:0]		con_awlen;
	wire	[2:0]		con_awsize;
	wire	[1:0]		con_awburst;
	wire			con_awlock;
	wire	[3:0]		con_awcache;
	wire	[2:0]		con_awprot;
	wire	[3:0]		con_awqos;

	wire			con_wvalid, con_wready;
	wire	[BUS_WIDTH-1:0]	con_wdata;
	wire [BUS_WIDTH/8-1:0]	con_wstrb;
	wire			con_wlast;

	wire			con_bvalid, con_bready;
	wire	[IW-1:0]	con_bid;
	wire	[1:0]		con_bresp;

	wire			con_arvalid, con_arready;
	wire	[IW-1:0]	con_arid;
	wire	[AW-1:0]	con_araddr;
	wire	[7:0]		con_arlen;
	wire	[2:0]		con_arsize;
	wire	[1:0]		con_arburst;
	wire			con_arlock;
	wire	[3:0]		con_arcache;
	wire	[2:0]		con_arprot;
	wire	[3:0]		con_arqos;

	wire			con_rvalid, con_rready;
	wire	[IW-1:0]	con_rid;
	wire	[BUS_WIDTH-1:0]	con_rdata;
	wire	[1:0]		con_rresp;
	wire			con_rlast;
	// }}}

	// conl*
	// {{{
	wire			conl_awvalid, conl_awready;
	wire	[AW-4:0]	conl_awaddr;
	wire	[2:0]		conl_awprot;

	wire			conl_wvalid, conl_wready;
	wire	[31:0]		conl_wdata;
	wire	[3:0]		conl_wstrb;

	wire			conl_bvalid, conl_bready;
	wire	[1:0]		conl_bresp;

	wire			conl_arvalid, conl_arready;
	wire	[AW-4:0]	conl_araddr;
	wire	[2:0]		conl_arprot;

	wire			conl_rvalid, conl_rready;
	wire	[31:0]		conl_rdata;
	wire	[1:0]		conl_rresp;
	// }}}
	// }}}

	// scope*
	// {{{
	wire			scope_awvalid, scope_awready;
	wire	[IW-1:0]	scope_awid;
	wire	[AW-1:0]	scope_awaddr;
	wire	[7:0]		scope_awlen;
	wire	[2:0]		scope_awsize;
	wire	[1:0]		scope_awburst;
	wire			scope_awlock;
	wire	[3:0]		scope_awcache;
	wire	[2:0]		scope_awprot;
	wire	[3:0]		scope_awqos;

	wire			scope_wvalid, scope_wready;
	wire	[BUS_WIDTH-1:0]	scope_wdata;
	wire [BUS_WIDTH/8-1:0]	scope_wstrb;
	wire			scope_wlast;

	wire			scope_bvalid, scope_bready;
	wire	[IW-1:0]	scope_bid;
	wire	[1:0]		scope_bresp;

	wire			scope_arvalid, scope_arready;
	wire	[IW-1:0]	scope_arid;
	wire	[AW-1:0]	scope_araddr;
	wire	[7:0]		scope_arlen;
	wire	[2:0]		scope_arsize;
	wire	[1:0]		scope_arburst;
	wire			scope_arlock;
	wire	[3:0]		scope_arcache;
	wire	[2:0]		scope_arprot;
	wire	[3:0]		scope_arqos;


	wire			scope_rvalid, scope_rready;
	wire	[IW-1:0]	scope_rid;
	wire	[BUS_WIDTH-1:0]	scope_rdata;
	wire	[1:0]		scope_rresp;
	wire			scope_rlast;
	// }}}

	// AXI Peripheral set declarations
	// {{{

	// axip_* - The AXI4 (full) connection to the peripheral set
	// {{{
	wire			axip_awvalid, axip_awready;
	wire	[IW-1:0]	axip_awid;
	wire	[AW-1:0]	axip_awaddr;
	wire	[7:0]		axip_awlen;
	wire	[2:0]		axip_awsize;
	wire	[1:0]		axip_awburst;
	wire			axip_awlock;
	wire	[3:0]		axip_awcache;
	wire	[2:0]		axip_awprot;
	wire	[3:0]		axip_awqos;

	wire			axip_wvalid, axip_wready;
	wire	[BUS_WIDTH-1:0]	axip_wdata;
	wire [BUS_WIDTH/8-1:0]	axip_wstrb;
	wire			axip_wlast;

	wire			axip_bvalid, axip_bready;
	wire	[IW-1:0]	axip_bid;
	wire	[1:0]		axip_bresp;

	wire			axip_arvalid, axip_arready;
	wire	[IW-1:0]	axip_arid;
	wire	[AW-1:0]	axip_araddr;
	wire	[7:0]		axip_arlen;
	wire	[2:0]		axip_arsize;
	wire	[1:0]		axip_arburst;
	wire			axip_arlock;
	wire	[3:0]		axip_arcache;
	wire	[2:0]		axip_arprot;
	wire	[3:0]		axip_arqos;


	wire			axip_rvalid, axip_rready;
	wire	[IW-1:0]	axip_rid;
	wire	[BUS_WIDTH-1:0]	axip_rdata;
	wire	[1:0]		axip_rresp;
	wire			axip_rlast;


	// }}}

	// axilp_* - The AXI-Lite connection to the peripheral set
	// {{{
	wire			axilp_awvalid, axilp_awready;
	wire	[AW-4:0]	axilp_awaddr;
	wire	[2:0]		axilp_awprot;

	wire			axilp_wvalid, axilp_wready;
	wire	[31:0]		axilp_wdata;
	wire	[3:0]		axilp_wstrb;

	wire			axilp_bvalid, axilp_bready;
	wire	[1:0]		axilp_bresp;

	wire			axilp_arvalid, axilp_arready;
	wire	[AW-4:0]	axilp_araddr;
	wire	[2:0]		axilp_arprot;

	wire			axilp_rvalid, axilp_rready;
	wire	[31:0]		axilp_rdata;
	wire	[1:0]		axilp_rresp;
	// }}}
	// }}}

`ifdef	VERILATOR
	// simfull_*
	// {{{
	wire				simfull_awvalid;
	wire				simfull_awready;
	wire	[IW-1:0]		simfull_awid;
	wire	[ADDRESS_WIDTH:0]	simwide_awaddr;
	wire	[ADDRESS_WIDTH-1:0]	simfull_awaddr;
	wire	[7:0]			simfull_awlen;
	wire	[2:0]			simfull_awsize;
	wire	[1:0]			simfull_awburst;
	wire				simfull_awlock;
	wire	[3:0]			simfull_awcache;
	wire	[2:0]			simfull_awprot;
	wire	[3:0]			simfull_awqos;

	wire				simfull_wvalid;
	wire				simfull_wready;
	wire	[BUS_WIDTH-1:0]		simfull_wdata;
	wire	[BUS_WIDTH/8-1:0]	simfull_wstrb;
	wire				simfull_wlast;

	wire				simfull_bvalid;
	wire				simfull_bready;
	wire	[IW-1:0]		simfull_bid;
	wire	[1:0]			simfull_bresp;

	wire				simfull_arvalid;
	wire				simfull_arready;
	wire	[IW-1:0]		simfull_arid;
	wire	[ADDRESS_WIDTH:0]	simwide_araddr;
	wire	[ADDRESS_WIDTH-1:0]	simfull_araddr;
	wire	[7:0]			simfull_arlen;
	wire	[2:0]			simfull_arsize;
	wire	[1:0]			simfull_arburst;
	wire				simfull_arlock;
	wire	[3:0]			simfull_arcache;
	wire	[2:0]			simfull_arprot;
	wire	[3:0]			simfull_arqos;

	wire				simfull_rvalid;
	wire				simfull_rready;
	wire	[IW-1:0]		simfull_rid;
	wire	[BUS_WIDTH-1:0]		simfull_rdata;
	wire				simfull_rlast;
	wire	[1:0]			simfull_rresp;
	// }}}
`else
	// Traditional TB only declarations
	// {{{
	// sim*
	// {{{
	wire				sim_awvalid;
	wire				sim_awready;
	wire	[ADDRESS_WIDTH-1:0]	sim_awaddr;
	wire	[2:0]			sim_awprot;

	wire				sim_wvalid;
	wire				sim_wready;
	wire	[31:0]			sim_wdata;
	wire	[3:0]			sim_wstrb;

	wire				sim_bvalid;
	wire				sim_bready;
	wire	[1:0]			sim_bresp;

	wire				sim_arvalid;
	wire				sim_arready;
	wire	[ADDRESS_WIDTH-1:0]	sim_araddr;
	wire	[2:0]			sim_arprot;

	wire				sim_rvalid;
	wire				sim_rready;
	wire	[31:0]			sim_rdata;
	wire	[1:0]			sim_rresp;
	// }}}

	wire				i_sim_int;
	wire				o_prof_stb;
	// wire	[31:0]			o_prof_addr;
	wire	[ADDRESS_WIDTH-1:0]	o_prof_addr;
	wire	[31:0]			o_prof_ticks;

	reg	i_aclk, i_aresetn, reset_pipe;
	// }}}
`endif

	// Watchdog timer
	// {{{
	localparam	TB_WATCHDOG_TIMEOUT = 1_000_00;	// 1ms
	reg	[$clog2(TB_WATCHDOG_TIMEOUT+2)-1:0]	watchdog_counter;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Traditional TB support
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

`ifndef	VERILATOR
	initial	i_aclk = 0;
	always
		#5 i_aclk = !i_aclk;

	initial	{ i_aresetn, reset_pipe } = 0;
	always @(posedge i_aclk)
		{ i_aresetn, reset_pipe } <= { reset_pipe, 1'b1 };

	// Tie off (unused) Sim control input(s)
	// {{{
	assign	sim_awvalid = 1'b0;
	assign	sim_awaddr  = 0;
	assign	sim_awprot  = 0;

	assign	sim_wvalid  = 1'b0;
	assign	sim_wdata   = 0;
	assign	sim_wstrb   = 0;

	assign	sim_bready  = 1'b1;

	assign	sim_arvalid = 1'b0;
	assign	sim_araddr  = 0;
	assign	sim_arprot  = 0;

	assign	sim_rready  = 1'b1;
	// }}}
	assign	i_sim_int  = 1'b0;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// External sim port: Either controls ZipCPU or wide WB bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

`ifdef	VERILATOR
	// Only required if we are using Verilator.  Other test benches won't
	// use this input port
	wire		simsub_arvalid, simsub_arready;
	wire	[31:0]	simsub_wdata, simsub_rdata;
	wire	[3:0]	simsub_wstrb;

	axilxbar #(
		// {{{
		.NM(1), .NS(2),
		.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH+1),
		.C_AXI_DATA_WIDTH(32),
		.SLAVE_ADDR({
			{ 1'b0, {(ADDRESS_WIDTH){1'b0}} },
			{ 1'b1, {(ADDRESS_WIDTH){1'b0}} }}), // CPU
		.SLAVE_MASK({
			{ 1'b0, {(ADDRESS_WIDTH){1'b0}} },
			{ 1'b1, {(ADDRESS_WIDTH){1'b0}} }})  // CPU
		// }}}
	) simxbar (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		// One master: the SIM bus input
		// {{{
		.S_AXI_AWVALID(sim_awvalid),
		.S_AXI_AWREADY(sim_awready),
		.S_AXI_AWADDR(sim_awaddr),
		.S_AXI_AWPROT(sim_awprot),
		//
		.S_AXI_WVALID(sim_wvalid),
		.S_AXI_WREADY(sim_wready),
		.S_AXI_WDATA(sim_wdata),
		.S_AXI_WSTRB(sim_wstrb),
		//
		.S_AXI_BVALID(sim_bvalid),
		.S_AXI_BREADY(sim_bready),
		.S_AXI_BRESP(sim_bresp),
		//
		.S_AXI_ARVALID(sim_arvalid),
		.S_AXI_ARREADY(sim_arready),
		.S_AXI_ARADDR(sim_araddr),
		.S_AXI_ARPROT(sim_arprot),
		//
		.S_AXI_RVALID(sim_rvalid),
		.S_AXI_RREADY(sim_rready),
		.S_AXI_RDATA(sim_rdata),
		.S_AXI_RRESP(sim_rresp),
		// }}}
		// Two slaves: The wide bus the ZipCPU masters, and the ZipCPU's
		// debug port
		// {{{
		.M_AXI_AWVALID({ simfull_awvalid, dbg_awvalid }),
		.M_AXI_AWREADY({ simfull_awready, dbg_awready }),
		.M_AXI_AWADDR({  simwide_awaddr,  dbg_awaddr  }),
		.M_AXI_AWPROT({  simfull_awprot,  dbg_awprot }),
		//
		.M_AXI_WVALID({ simfull_wvalid, dbg_wvalid }),
		.M_AXI_WREADY({ simfull_wready, dbg_wready }),
		.M_AXI_WDATA({  simsub_wdata,  dbg_wdata }),
		.M_AXI_WSTRB({  simsub_wstrb,  dbg_wstrb }),
		//
		.M_AXI_BVALID({ simfull_bvalid, dbg_bvalid }),
		.M_AXI_BREADY({ simfull_bready, dbg_bready }),
		.M_AXI_BRESP({  simfull_bresp,  dbg_bresp }),
		//
		.M_AXI_ARVALID({ simsub_arvalid, dbg_arvalid }),
		.M_AXI_ARREADY({ simsub_arready, dbg_arready }),
		.M_AXI_ARADDR({  simwide_araddr,  dbg_araddr }),
		.M_AXI_ARPROT({  simfull_arprot,  dbg_arprot }),
		//
		.M_AXI_RVALID({ simfull_rvalid, dbg_rvalid }),
		.M_AXI_RREADY({ simfull_rready, dbg_rready }),
		.M_AXI_RDATA({  simsub_rdata,  dbg_rdata }),
		.M_AXI_RRESP({  simfull_rresp,  dbg_rresp })
		// }}}
		// }}}
	);

	assign	simfull_awid    = 0;
	assign	simfull_awaddr  = simwide_awaddr[ADDRESS_WIDTH-1:0];
	assign	simfull_awlen   = 0;
	assign	simfull_awsize  = 3'h2;
	assign	simfull_awburst = 2'b01;
	assign	simfull_awlock  = 1'b0;
	assign	simfull_awcache = 4'h3;
	assign	simfull_awqos   = 0;

	assign	simfull_wdata = {(BUS_WIDTH/32){simsub_wdata}};
	generate if (BUS_WIDTH == 32)
	begin : GEN_SIMFULL
		assign	simfull_wstrb = simsub_wstrb;
	end else begin : GEN_SIMWIDE
		assign	simfull_wstrb = { {((BUS_WIDTH-32)/8){1'b0}},
							simsub_wstrb }
				<< (simfull_awaddr[$clog2(BUS_WIDTH/8)-1:2]*4);
	end endgenerate
	assign	simfull_wlast   = 1;

	assign	simfull_arid    = 0;
	assign	simfull_araddr  = simwide_araddr[ADDRESS_WIDTH-1:0];
	assign	simfull_arlen   = 0;
	assign	simfull_arsize  = 3'h2;
	assign	simfull_arburst = 2'b01;
	assign	simfull_arlock  = 1'b0;
	assign	simfull_arcache = 4'h3;
	assign	simfull_arqos   = 0;

	generate if (BUS_WIDTH == 32)
	begin : NO_RETURN_DATA_SHIFT

		assign	simfull_arvalid = simsub_arvalid;
		assign	simsub_arready  = simfull_arready;
		assign	simsub_rdata    = simfull_rdata;

	end else begin : SHIFT_RETURN_DATA
		// {{{
		localparam	LGFIFO = 5;

		wire					rfif_full, rfif_empty;
		wire	[$clog2(BUS_WIDTH/32)-1:0]	rfif_shift;
		wire	[LGFIFO:0]			rfif_fill;
		wire	[BUS_WIDTH-1:0]			shifted_rdata;

		sfifo #(
			.LGFLEN(LGFIFO),
			.BW($clog2(BUS_WIDTH/32))
		) rdata_addr_fifo (
			.i_clk(i_aclk), .i_reset(!i_aresetn),
			.i_wr(simfull_arvalid && simfull_arready),
			.i_data(simfull_araddr[$clog2(BUS_WIDTH/32)+1:2]),
				.o_full(rfif_full), .o_fill(rfif_fill),
			.i_rd(simfull_rvalid && simfull_rready),
				.o_data(rfif_shift), .o_empty(rfif_empty)
		);

		assign	shifted_rdata = simfull_rdata >> (rfif_shift*32);
		assign	simsub_rdata = shifted_rdata[31:0];
		assign	simfull_arvalid = simsub_arvalid && !rfif_full;
		assign	simsub_arready  = !rfif_full && simfull_arready;

		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_rfif;
		assign	unused_rfif = &{ 1'b0, rfif_fill, rfif_empty,
					shifted_rdata[BUS_WIDTH-1:32] };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	end endgenerate

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_sim;
	assign	unused_sim = &{ 1'b0,
				simwide_awaddr[ADDRESS_WIDTH],
				simwide_araddr[ADDRESS_WIDTH],
				simfull_rlast, simfull_bid, simfull_rid,
				dbg_awaddr[AW:8], dbg_araddr[AW:8]
			};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
`else
	// If we aren't using Verilator, then there's no external bus driver.
	// Cap off the debug port therefore.
	//

	assign	dbg_awvalid= 1'b0;
	assign	dbg_awaddr = 0;
	assign	dbg_awprot = 0;

	assign	dbg_wvalid= 1'b0;
	assign	dbg_wdata = 0;
	assign	dbg_wstrb = 0;

	assign	dbg_bready = 1'b0;

	assign	dbg_arvalid= 1'b0;
	assign	dbg_araddr = 0;
	assign	dbg_arprot = 0;

	assign	dbg_rready = 1'b0;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The CPU itself
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_ZIPAXIL)
	begin : GEN_ZIPAXIL
		// Local declarations
		// {{{
		wire			cpuil_awvalid, cpuil_awready;
		wire	[AW-1:0]	cpuil_awaddr;
		wire	[2:0]		cpuil_awprot;

		wire			cpuil_wvalid, cpuil_wready;
		wire	[BUS_WIDTH-1:0]	cpuil_wdata;
		wire [BUS_WIDTH/8-1:0]	cpuil_wstrb;

		wire			cpuil_bvalid, cpuil_bready;
		wire	[1:0]		cpuil_bresp;

		wire			cpuil_arvalid, cpuil_arready;
		wire	[AW-1:0]	cpuil_araddr;
		wire	[2:0]		cpuil_arprot;

		wire			cpuil_rvalid, cpuil_rready;
		wire	[BUS_WIDTH-1:0]	cpuil_rdata;
		wire	[1:0]		cpuil_rresp;
		//
		wire			cpudl_awvalid, cpudl_awready;
		wire	[AW-1:0]	cpudl_awaddr;
		wire	[2:0]		cpudl_awprot;

		wire			cpudl_wvalid, cpudl_wready;
		wire	[BUS_WIDTH-1:0]	cpudl_wdata;
		wire [BUS_WIDTH/8-1:0]	cpudl_wstrb;

		wire			cpudl_bvalid, cpudl_bready;
		wire	[1:0]		cpudl_bresp;

		wire			cpudl_arvalid, cpudl_arready;
		wire	[AW-1:0]	cpudl_araddr;
		wire	[2:0]		cpudl_arprot;

		wire			cpudl_rvalid, cpudl_rready;
		wire	[BUS_WIDTH-1:0]	cpudl_rdata;
		wire	[1:0]		cpudl_rresp;
		// }}}

		zipaxil #(
			// {{{
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.RESET_ADDRESS(RESET_ADDRESS[ADDRESS_WIDTH-1:0]),
			.OPT_PIPELINED(OPT_PIPELINED),
			.C_AXI_DATA_WIDTH(BUS_WIDTH),
			.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
			.OPT_LGICACHE(OPT_LGICACHE),
			.OPT_LGDCACHE(OPT_LGDCACHE),
			.START_HALTED(1'b0),
			.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
			.OPT_MPY(OPT_MPY),
			.OPT_DIV(OPT_DIV),
			.OPT_SHIFTS(OPT_SHIFTS),
			.OPT_LOCK(OPT_LOCK),
			.OPT_CIS(OPT_CIS),
			.OPT_USERMODE(OPT_USERMODE),
			.OPT_DBGPORT(OPT_DBGPORT),
			.OPT_TRACE_PORT(OPT_TRACE_PORT),
			.OPT_PROFILER(OPT_PROFILER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_SIM(OPT_SIM),
			.OPT_CLKGATE(OPT_CLKGATE),
			.RESET_DURATION(RESET_DURATION)
			// }}}
		) u_cpu (
			// {{{
			.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
			.i_interrupt(pic_interrupt),
			.i_cpu_reset(!i_aresetn || watchdog_reset),
			// Debug control port
			// {{{
			.S_DBG_AWVALID(dbg_awvalid),
			.S_DBG_AWREADY(dbg_awready),
			.S_DBG_AWADDR(dbg_awaddr[7:0]),
			.S_DBG_AWPROT(dbg_awprot),
			//
			.S_DBG_WVALID(dbg_wvalid),
			.S_DBG_WREADY(dbg_wready),
			.S_DBG_WDATA( dbg_wdata),
			.S_DBG_WSTRB( dbg_wstrb),
			//
			.S_DBG_BVALID(dbg_bvalid),
			.S_DBG_BREADY(dbg_bready),
			.S_DBG_BRESP( dbg_bresp),
			//
			.S_DBG_ARVALID(dbg_arvalid),
			.S_DBG_ARREADY(dbg_arready),
			.S_DBG_ARADDR(dbg_araddr[7:0]),
			.S_DBG_ARPROT(dbg_arprot),
			//
			.S_DBG_RVALID(dbg_rvalid),
			.S_DBG_RREADY(dbg_rready),
			.S_DBG_RDATA( dbg_rdata),
			.S_DBG_RRESP( dbg_rresp),
			// }}}
			// Master instruction bus
			// {{{
			.M_INSN_AWVALID(cpuil_awvalid),
			.M_INSN_AWREADY(cpuil_awready),
			.M_INSN_AWADDR(cpuil_awaddr),
			.M_INSN_AWPROT(cpuil_awprot),
			//
			.M_INSN_WVALID(cpuil_wvalid),
			.M_INSN_WREADY(cpuil_wready),
			.M_INSN_WDATA( cpuil_wdata),
			.M_INSN_WSTRB( cpuil_wstrb),
			//
			.M_INSN_BVALID(cpuil_bvalid),
			.M_INSN_BREADY(cpuil_bready),
			.M_INSN_BRESP( cpuil_bresp),
			//
			.M_INSN_ARVALID(cpuil_arvalid),
			.M_INSN_ARREADY(cpuil_arready),
			.M_INSN_ARADDR( cpuil_araddr),
			.M_INSN_ARPROT( cpuil_arprot),
			//
			.M_INSN_RVALID(cpuil_rvalid),
			.M_INSN_RREADY(cpuil_rready),
			.M_INSN_RDATA( cpuil_rdata),
			.M_INSN_RRESP( cpuil_rresp),
			// }}}
			// Master data bus
			// {{{
			.M_DATA_AWVALID(cpudl_awvalid),
			.M_DATA_AWREADY(cpudl_awready),
			.M_DATA_AWADDR( cpudl_awaddr),
			.M_DATA_AWPROT( cpudl_awprot),
			//
			.M_DATA_WVALID(cpudl_wvalid),
			.M_DATA_WREADY(cpudl_wready),
			.M_DATA_WDATA( cpudl_wdata),
			.M_DATA_WSTRB( cpudl_wstrb),
			//
			.M_DATA_BVALID(cpudl_bvalid),
			.M_DATA_BREADY(cpudl_bready),
			.M_DATA_BRESP( cpudl_bresp),
			//
			.M_DATA_ARVALID(cpudl_arvalid),
			.M_DATA_ARREADY(cpudl_arready),
			.M_DATA_ARADDR( cpudl_araddr),
			.M_DATA_ARPROT( cpudl_arprot),
			//
			.M_DATA_RVALID(cpudl_rvalid),
			.M_DATA_RREADY(cpudl_rready),
			.M_DATA_RDATA( cpudl_rdata),
			.M_DATA_RRESP( cpudl_rresp),
			// }}}
			.o_cpu_debug(cpu_trace),
			// Accounting outputs
			// {{{
			.o_cmd_reset(cpu_reset[0]),
			.o_halted(   cpu_halted[0]),
			.o_gie(      cpu_gie[0]),
			.o_op_stall( cpu_op_stall[0]),
			.o_pf_stall( cpu_pf_stall[0]),
			.o_i_count(  cpu_i_count[0]),
			// }}}
			// (Optional) Profiler
			// {{{
			.o_prof_stb(  o_prof_stb),
			.o_prof_addr( o_prof_addr),
			.o_prof_ticks(o_prof_ticks)
			// }}}
			// }}}
		);

		axilite2axi #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_ADDR_WIDTH(AW),
			.C_AXI_DATA_WIDTH(BUS_WIDTH)
			// }}}
		) u_iaxi (
			.ACLK(i_aclk), .ARESETN(i_aresetn),
			// Slave interface, from CPU
			// {{{
			.S_AXI_AWVALID(cpuil_awvalid),
			.S_AXI_AWREADY(cpuil_awready),
			.S_AXI_AWADDR( cpuil_awaddr),
			.S_AXI_AWPROT( cpuil_awprot),

			.S_AXI_WVALID(cpuil_wvalid),
			.S_AXI_WREADY(cpuil_wready),
			.S_AXI_WDATA( cpuil_wdata),
			.S_AXI_WSTRB( cpuil_wstrb),

			.S_AXI_BVALID(cpuil_bvalid),
			.S_AXI_BREADY(cpuil_bready),
			.S_AXI_BRESP( cpuil_bresp),

			.S_AXI_ARVALID(cpuil_arvalid),
			.S_AXI_ARREADY(cpuil_arready),
			.S_AXI_ARADDR( cpuil_araddr),
			.S_AXI_ARPROT( cpuil_arprot),

			.S_AXI_RVALID(cpuil_rvalid),
			.S_AXI_RREADY(cpuil_rready),
			.S_AXI_RDATA( cpuil_rdata),
			.S_AXI_RRESP( cpuil_rresp),
			// }}}
			// Master interface, to the bus
			// {{{
			.M_AXI_AWVALID(cpui_awvalid[0]),
			.M_AXI_AWREADY(cpui_awready[0]),
			.M_AXI_AWID(   cpui_awid[IW-1:0]),
			.M_AXI_AWADDR( cpui_awaddr[AW-1:0]),
			.M_AXI_AWLEN(  cpui_awlen[7:0]),
			.M_AXI_AWSIZE( cpui_awsize[2:0]),
			.M_AXI_AWBURST(cpui_awburst[1:0]),
			.M_AXI_AWLOCK( cpui_awlock[0]),
			.M_AXI_AWCACHE(cpui_awcache[3:0]),
			.M_AXI_AWPROT( cpui_awprot[2:0]),
			.M_AXI_AWQOS(  cpui_awqos[3:0]),

			.M_AXI_WVALID(cpui_wvalid[0]),
			.M_AXI_WREADY(cpui_wready[0]),
			.M_AXI_WDATA( cpui_wdata[BUS_WIDTH-1:0]),
			.M_AXI_WSTRB( cpui_wstrb[BUS_WIDTH/8-1:0]),
			.M_AXI_WLAST( cpui_wlast[0]),

			.M_AXI_BVALID(cpui_bvalid[0]),
			.M_AXI_BREADY(cpui_bready[0]),
			.M_AXI_BID(   cpui_bid[IW-1:0]),
			.M_AXI_BRESP( cpui_bresp[1:0]),

			.M_AXI_ARVALID(cpui_arvalid[0]),
			.M_AXI_ARREADY(cpui_arready[0]),
			.M_AXI_ARID(   cpui_arid[IW-1:0]),
			.M_AXI_ARADDR( cpui_araddr[AW-1:0]),
			.M_AXI_ARLEN(  cpui_arlen[7:0]),
			.M_AXI_ARSIZE( cpui_arsize[2:0]),
			.M_AXI_ARBURST(cpui_arburst[1:0]),
			.M_AXI_ARLOCK( cpui_arlock[0]),
			.M_AXI_ARCACHE(cpui_arcache[3:0]),
			.M_AXI_ARPROT( cpui_arprot[2:0]),
			.M_AXI_ARQOS(  cpui_arqos[3:0]),

			.M_AXI_RVALID(cpui_rvalid[0]),
			.M_AXI_RREADY(cpui_rready[0]),
			.M_AXI_RID(   cpui_rid[IW-1:0]),
			.M_AXI_RDATA( cpui_rdata[BUS_WIDTH-1:0]),
			.M_AXI_RLAST( cpui_rlast[0]),
			.M_AXI_RRESP( cpui_rresp[1:0])
			// }}}
		);

		axilite2axi #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_ADDR_WIDTH(AW),
			.C_AXI_DATA_WIDTH(BUS_WIDTH)
			// }}}
		) u_daxi (
			.ACLK(i_aclk), .ARESETN(i_aresetn),
			// Slave interface, from CPU
			// {{{
			.S_AXI_AWVALID(cpudl_awvalid),
			.S_AXI_AWREADY(cpudl_awready),
			.S_AXI_AWADDR( cpudl_awaddr),
			.S_AXI_AWPROT( cpudl_awprot),

			.S_AXI_WVALID(cpudl_wvalid),
			.S_AXI_WREADY(cpudl_wready),
			.S_AXI_WDATA( cpudl_wdata),
			.S_AXI_WSTRB( cpudl_wstrb),

			.S_AXI_BVALID(cpudl_bvalid),
			.S_AXI_BREADY(cpudl_bready),
			.S_AXI_BRESP( cpudl_bresp),

			.S_AXI_ARVALID(cpudl_arvalid),
			.S_AXI_ARREADY(cpudl_arready),
			.S_AXI_ARADDR( cpudl_araddr),
			.S_AXI_ARPROT( cpudl_arprot),

			.S_AXI_RVALID(cpudl_rvalid),
			.S_AXI_RREADY(cpudl_rready),
			.S_AXI_RDATA( cpudl_rdata),
			.S_AXI_RRESP( cpudl_rresp),
			// }}}
			// Master interface, to the bus
			// {{{
			.M_AXI_AWVALID(cpud_awvalid[0]),
			.M_AXI_AWREADY(cpud_awready[0]),
			.M_AXI_AWID(   cpud_awid[IW-1:0]),
			.M_AXI_AWADDR( cpud_awaddr[AW-1:0]),
			.M_AXI_AWLEN(  cpud_awlen[7:0]),
			.M_AXI_AWSIZE( cpud_awsize[2:0]),
			.M_AXI_AWBURST(cpud_awburst[1:0]),
			.M_AXI_AWLOCK( cpud_awlock[0]),
			.M_AXI_AWCACHE(cpud_awcache[3:0]),
			.M_AXI_AWPROT( cpud_awprot[2:0]),
			.M_AXI_AWQOS(  cpud_awqos[3:0]),

			.M_AXI_WVALID(cpud_wvalid[0]),
			.M_AXI_WREADY(cpud_wready[0]),
			.M_AXI_WDATA( cpud_wdata[BUS_WIDTH-1:0]),
			.M_AXI_WSTRB( cpud_wstrb[BUS_WIDTH/8-1:0]),
			.M_AXI_WLAST( cpud_wlast[0]),

			.M_AXI_BVALID(cpud_bvalid[0]),
			.M_AXI_BREADY(cpud_bready[0]),
			.M_AXI_BID(   cpud_bid[IW-1:0]),
			.M_AXI_BRESP( cpud_bresp[1:0]),

			.M_AXI_ARVALID(cpud_arvalid[0]),
			.M_AXI_ARREADY(cpud_arready[0]),
			.M_AXI_ARID(   cpud_arid[IW-1:0]),
			.M_AXI_ARADDR( cpud_araddr[AW-1:0]),
			.M_AXI_ARLEN(  cpud_arlen[7:0]),
			.M_AXI_ARSIZE( cpud_arsize[2:0]),
			.M_AXI_ARBURST(cpud_arburst[1:0]),
			.M_AXI_ARLOCK( cpud_arlock[0]),
			.M_AXI_ARCACHE(cpud_arcache[3:0]),
			.M_AXI_ARPROT( cpud_arprot[2:0]),
			.M_AXI_ARQOS(  cpud_arqos[3:0]),

			.M_AXI_RVALID(cpud_rvalid[0]),
			.M_AXI_RREADY(cpud_rready[0]),
			.M_AXI_RID(   cpud_rid[IW-1:0]),
			.M_AXI_RDATA( cpud_rdata[BUS_WIDTH-1:0]),
			.M_AXI_RLAST( cpud_rlast[0]),
			.M_AXI_RRESP( cpud_rresp[1:0])
			// }}}
		);

	end else begin : GEN_ZIPAXI

		zipaxi #(
			// {{{
			.RESET_ADDRESS(RESET_ADDRESS[ADDRESS_WIDTH-1:0]),
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(BUS_WIDTH),
			.OPT_PIPELINED(OPT_PIPELINED),
			.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
			.OPT_LGICACHE(OPT_LGICACHE),
			.OPT_LGDCACHE(OPT_LGDCACHE),
			.START_HALTED(1'b0),
			.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
			.OPT_MPY(OPT_MPY),
			.OPT_DIV(OPT_DIV),
			.OPT_SHIFTS(OPT_SHIFTS),
			.OPT_LOCK(OPT_LOCK),
			.OPT_CIS(OPT_CIS),
			.OPT_WRAP(OPT_WRAP),
			.OPT_USERMODE(OPT_USERMODE),
			.OPT_DBGPORT(OPT_DBGPORT),
			.OPT_TRACE_PORT(OPT_TRACE_PORT),
			.OPT_PROFILER(OPT_PROFILER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_SIM(OPT_SIM),
			.OPT_CLKGATE(OPT_CLKGATE),
			.RESET_DURATION(RESET_DURATION)
			// }}}
		) u_cpu (
			// {{{
			.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
			.i_interrupt(pic_interrupt),
			.i_cpu_reset(!i_aresetn || watchdog_reset),
			// Debug control port
			// {{{
			.S_DBG_AWVALID(dbg_awvalid),
			.S_DBG_AWREADY(dbg_awready),
			.S_DBG_AWADDR(dbg_awaddr[7:0]),
			.S_DBG_AWPROT(dbg_awprot),
			//
			.S_DBG_WVALID(dbg_wvalid),
			.S_DBG_WREADY(dbg_wready),
			.S_DBG_WDATA( dbg_wdata),
			.S_DBG_WSTRB( dbg_wstrb),
			//
			.S_DBG_BVALID(dbg_bvalid),
			.S_DBG_BREADY(dbg_bready),
			.S_DBG_BRESP( dbg_bresp),
			//
			.S_DBG_ARVALID(dbg_arvalid),
			.S_DBG_ARREADY(dbg_arready),
			.S_DBG_ARADDR(dbg_araddr[7:0]),
			.S_DBG_ARPROT(dbg_arprot),
			//
			.S_DBG_RVALID(dbg_rvalid),
			.S_DBG_RREADY(dbg_rready),
			.S_DBG_RDATA( dbg_rdata),
			.S_DBG_RRESP( dbg_rresp),
			// }}}
			// Master instruction bus
			// {{{
			.M_INSN_AWVALID(cpui_awvalid[0]),
			.M_INSN_AWREADY(cpui_awready[0]),
			.M_INSN_AWID(   cpui_awid[   0 +: IW]),
			.M_INSN_AWADDR( cpui_awaddr[ 0 +: AW]),
			.M_INSN_AWLEN(  cpui_awlen[  0 +: 8]),
			.M_INSN_AWSIZE( cpui_awsize[ 0 +: 3]),
			.M_INSN_AWBURST(cpui_awburst[0 +: 2]),
			.M_INSN_AWLOCK( cpui_awlock[ 0]),
			.M_INSN_AWCACHE(cpui_awcache[0 +: 4]),
			.M_INSN_AWPROT( cpui_awprot[ 0 +: 3]),
			.M_INSN_AWQOS(  cpui_awqos[  0 +: 4]),
			//
			.M_INSN_WVALID(cpui_wvalid[0]),
			.M_INSN_WREADY(cpui_wready[0]),
			.M_INSN_WDATA( cpui_wdata[0 +: BUS_WIDTH]),
			.M_INSN_WSTRB( cpui_wstrb[0 +: BUS_WIDTH/8]),
			.M_INSN_WLAST( cpui_wlast[0]),
			//
			.M_INSN_BVALID(cpui_bvalid[0]),
			.M_INSN_BREADY(cpui_bready[0]),
			.M_INSN_BID(   cpui_bid[  0*IW +: IW]),
			.M_INSN_BRESP( cpui_bresp[0*2  +: 2]),
			//
			.M_INSN_ARVALID(cpui_arvalid[0]),
			.M_INSN_ARREADY(cpui_arready[0]),
			.M_INSN_ARID(   cpui_arid[   0*IW +: IW]),
			.M_INSN_ARADDR( cpui_araddr[ 0*AW +: AW]),
			.M_INSN_ARLEN(  cpui_arlen[  0 *8 +: 8]),
			.M_INSN_ARSIZE( cpui_arsize[ 0 *3 +: 3]),
			.M_INSN_ARBURST(cpui_arburst[0 *2 +: 2]),
			.M_INSN_ARLOCK( cpui_arlock[ 0]),
			.M_INSN_ARCACHE(cpui_arcache[0 *4 +: 4]),
			.M_INSN_ARPROT( cpui_arprot[ 0 *3 +: 3]),
			.M_INSN_ARQOS(  cpui_arqos[  0 *4 +: 4]),
			//
			.M_INSN_RVALID(cpui_rvalid[0]),
			.M_INSN_RREADY(cpui_rready[0]),
			.M_INSN_RID(   cpui_rid[0*IW +: IW]),
			.M_INSN_RDATA( cpui_rdata[0*BUS_WIDTH +: BUS_WIDTH]),
			.M_INSN_RLAST( cpui_rlast[0]),
			.M_INSN_RRESP( cpui_rresp[0 *2 +: 2]),
			// }}}
			// Master data bus
			// {{{
			.M_DATA_AWVALID(cpud_awvalid[0]),
			.M_DATA_AWREADY(cpud_awready[0]),
			.M_DATA_AWID(   cpud_awid[0*IW +: IW]),
			.M_DATA_AWADDR( cpud_awaddr[0*AW +: AW]),
			.M_DATA_AWLEN(  cpud_awlen[0*8 +: 8]),
			.M_DATA_AWSIZE( cpud_awsize[0*3 +: 3]),
			.M_DATA_AWBURST(cpud_awburst[0*2 +: 2]),
			.M_DATA_AWLOCK( cpud_awlock[0]),
			.M_DATA_AWCACHE(cpud_awcache[0*4 +: 4]),
			.M_DATA_AWPROT( cpud_awprot[0*3 +: 3]),
			.M_DATA_AWQOS(  cpud_awqos[0*4 +: 4]),
			//
			.M_DATA_WVALID(cpud_wvalid[0]),
			.M_DATA_WREADY(cpud_wready[0]),
			.M_DATA_WDATA( cpud_wdata[0*BUS_WIDTH +: BUS_WIDTH]),
			.M_DATA_WSTRB( cpud_wstrb[0*BUS_WIDTH/8 +: BUS_WIDTH/8]),
			.M_DATA_WLAST( cpud_wlast[0]),
			//
			.M_DATA_BVALID(cpud_bvalid[0]),
			.M_DATA_BREADY(cpud_bready[0]),
			.M_DATA_BID(   cpud_bid[0*IW +: IW]),
			.M_DATA_BRESP( cpud_bresp[0*2 +: 2]),
			//
			.M_DATA_ARVALID(cpud_arvalid[0]),
			.M_DATA_ARREADY(cpud_arready[0]),
			.M_DATA_ARID(   cpud_arid[0*IW +: IW]),
			.M_DATA_ARADDR( cpud_araddr[0*AW +: AW]),
			.M_DATA_ARLEN(  cpud_arlen[0*8 +: 8]),
			.M_DATA_ARSIZE( cpud_arsize[0*3 +: 3]),
			.M_DATA_ARBURST(cpud_arburst[0*2 +: 2]),
			.M_DATA_ARLOCK( cpud_arlock[0]),
			.M_DATA_ARCACHE(cpud_arcache[0*4 +: 4]),
			.M_DATA_ARPROT( cpud_arprot[0*3 +: 3]),
			.M_DATA_ARQOS(  cpud_arqos[0*4 +: 4]),
			//
			.M_DATA_RVALID(cpud_rvalid[0]),
			.M_DATA_RREADY(cpud_rready[0]),
			.M_DATA_RID(   cpud_rid[0*IW +: IW]),
			.M_DATA_RDATA( cpud_rdata[0*BUS_WIDTH +: BUS_WIDTH]),
			.M_DATA_RLAST( cpud_rlast[0]),
			.M_DATA_RRESP( cpud_rresp[0*2 +: 2]),
			// }}}
			.o_cpu_debug(cpu_trace),
			// Accounting outputs
			// {{{
			.o_cmd_reset(cpu_reset[0]),
			.o_halted(   cpu_halted[0]),
			.o_gie(      cpu_gie[0]),
			.o_op_stall( cpu_op_stall[0]),
			.o_pf_stall( cpu_pf_stall[0]),
			.o_i_count(  cpu_i_count[0]),
			// }}}
			// (Optional) Profiler
			// {{{
			.o_prof_stb(  o_prof_stb),
			.o_prof_addr( o_prof_addr),
			.o_prof_ticks(o_prof_ticks)
			// }}}
			// }}}
		);

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Extra CPU's, if running in multiprocessor mode (OPT_SMP > 1)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Nothing at the first SMP control address
	// {{{
	axiempty #(
		// {{{
		.C_AXI_ID_WIDTH(IW),
		.C_AXI_ADDR_WIDTH(AW),
		.C_AXI_DATA_WIDTH(BUS_WIDTH)
		// }}}
	) u_nosmp (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		//
		.S_AXI_AWVALID(smpfull_awvalid[0]),
		.S_AXI_AWREADY(smpfull_awready[0]),
		.S_AXI_AWID(   smpfull_awid[IW-1:0]),
		// .S_AXI_AWADDR( smpfull_awaddr),
		// .S_AXI_AWLEN(  smpfull_awlen),
		// .S_AXI_AWSIZE( smpfull_awsize),
		// .S_AXI_AWBURST(smpfull_awburst),
		// .S_AXI_AWLOCK( smpfull_awlock),
		// .S_AXI_AWCACHE(smpfull_awcache),
		// .S_AXI_AWPROT( smpfull_awprot),
		// .S_AXI_AWQOS(  smpfull_awqos),
		//
		.S_AXI_WVALID(smpfull_wvalid[0]),
		.S_AXI_WREADY(smpfull_wready[0]),
		// .S_AXI_WDATA( smpfull_wdata),
		// .S_AXI_WSTRB( smpfull_wstrb),
		.S_AXI_WLAST( smpfull_wlast[0]),
		//
		.S_AXI_BVALID(smpfull_bvalid[0]),
		.S_AXI_BREADY(smpfull_bready[0]),
		.S_AXI_BID(   smpfull_bid[IW-1:0]),
		.S_AXI_BRESP( smpfull_bresp[1:0]),
		//
		.S_AXI_ARVALID(smpfull_arvalid[0]),
		.S_AXI_ARREADY(smpfull_arready[0]),
		.S_AXI_ARID(   smpfull_arid[IW-1:0]),
		// .S_AXI_ARADDR( smpfull_araddr),
		.S_AXI_ARLEN(  smpfull_arlen[7:0]),
		// .S_AXI_ARSIZE( smpfull_arsize),
		// .S_AXI_ARBURST(smpfull_arburst),
		// .S_AXI_ARLOCK( smpfull_arlock),
		// .S_AXI_ARCACHE(smpfull_arcache),
		// .S_AXI_ARPROT( smpfull_arprot),
		// .S_AXI_ARQOS(  smpfull_arqos),
		//
		.S_AXI_RVALID(smpfull_rvalid[0]),
		.S_AXI_RREADY(smpfull_rready[0]),
		.S_AXI_RID(   smpfull_rid[IW-1:0]),
		.S_AXI_RDATA( smpfull_rdata[BUS_WIDTH-1:0]),
		.S_AXI_RRESP( smpfull_rresp[1:0]),
		.S_AXI_RLAST( smpfull_rlast[0])
		// }}}
	);

	// Keep Verilator happy for this set
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_base_smp;
	assign	unused_base_smp = &{ 1'b0,
			smpfull_awaddr[AW-1:0], smpfull_awlen[7:0],
			smpfull_awsize[2:0],    smpfull_awburst[1:0],
			smpfull_awlock[0],      smpfull_awcache[3:0],
			smpfull_awprot[2:0],    smpfull_awqos[3:0],
			smpfull_wdata[BUS_WIDTH-1:0],
						smpfull_wstrb[BUS_WIDTH/8-1:0],
			smpfull_araddr[AW-1:0],
			smpfull_arsize[2:0],    smpfull_arburst[1:0],
			smpfull_arlock[0],      smpfull_arcache[3:0],
			smpfull_arprot[2:0],    smpfull_arqos[3:0]
			};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}

	// }}}

	generate for(gk=1; gk<OPT_SMP; gk=gk+1)
	begin : GEN_SMPCPU
		// Local declarations
		// {{{
		wire	[31:0]			smp_trace;
		wire				smp_prof_stb;
		wire	[ADDRESS_WIDTH-1:0]	smp_prof_addr;
		wire	[31:0]			smp_prof_ticks;

		wire			smp_awvalid, smp_awready;
		wire	[8-1:0]		smp_awaddr;
		wire	[3-1:0]		smp_awprot;

		wire			smp_wvalid, smp_wready;
		wire	[32-1:0]	smp_wdata;
		wire	[4-1:0]		smp_wstrb;

		wire			smp_bvalid, smp_bready;
		wire	[2-1:0]		smp_bresp;

		wire			smp_arvalid, smp_arready;
		wire	[8-1:0]		smp_araddr;
		wire	[3-1:0]		smp_arprot;

		wire			smp_rvalid, smp_rready;
		wire 	[32-1:0]	smp_rdata;
		wire	[2-1:0]		smp_rresp;
		// }}}

		axi2axilsub #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_ADDR_WIDTH(8),
			.C_S_AXI_DATA_WIDTH(BUS_WIDTH),
			.C_M_AXI_DATA_WIDTH(32),
			.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_WRITES(1), .OPT_READS(1)
			// }}}
		) u_smpdown (
			// {{{
			.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
			// The "Wide" slave connection
			// {{{
			.S_AXI_AWVALID(smpfull_awvalid[ gk]),
			.S_AXI_AWREADY(smpfull_awready[ gk]),
			.S_AXI_AWID(   smpfull_awid[    gk*IW +: IW]),
			.S_AXI_AWADDR( smpfull_awaddr[  gk*AW +:  8]),
			.S_AXI_AWLEN(  smpfull_awlen[   gk*8  +:  8]),
			.S_AXI_AWSIZE( smpfull_awsize[  gk*3  +:  3]),
			.S_AXI_AWBURST(smpfull_awburst[ gk*2  +:  2]),
			.S_AXI_AWLOCK( smpfull_awlock[  gk]),
			.S_AXI_AWCACHE(smpfull_awcache[ gk*4  +:  4]),
			.S_AXI_AWPROT( smpfull_awprot[  gk*3  +:  3]),
			.S_AXI_AWQOS(  smpfull_awqos[   gk*4  +:  4]),

			.S_AXI_WVALID(smpfull_wvalid[gk]),
			.S_AXI_WREADY(smpfull_wready[gk]),
			.S_AXI_WDATA( smpfull_wdata[ gk*BUS_WIDTH +: BUS_WIDTH]),
			.S_AXI_WSTRB( smpfull_wstrb[ gk*BUS_WIDTH/8 +: BUS_WIDTH/8]),
			.S_AXI_WLAST( smpfull_wlast[ gk]),

			.S_AXI_BVALID(smpfull_bvalid[gk]),
			.S_AXI_BREADY(smpfull_bready[gk]),
			.S_AXI_BID(   smpfull_bid[gk*IW +: IW]),
			.S_AXI_BRESP( smpfull_bresp[gk*2 +: 2]),

			.S_AXI_ARVALID(smpfull_arvalid[gk]),
			.S_AXI_ARREADY(smpfull_arready[gk]),
			.S_AXI_ARID(   smpfull_arid[   gk*IW +: IW]),
			.S_AXI_ARADDR( smpfull_araddr[ gk*AW +: 8]),
			.S_AXI_ARLEN(  smpfull_arlen[  gk*8 +:  8]),
			.S_AXI_ARSIZE( smpfull_arsize[ gk*3 +:  3]),
			.S_AXI_ARBURST(smpfull_arburst[gk*2 +:  2]),
			.S_AXI_ARLOCK( smpfull_arlock[ gk]),
			.S_AXI_ARCACHE(smpfull_arcache[gk*4 +:  4]),
			.S_AXI_ARPROT( smpfull_arprot[ gk*3 +:  3]),
			.S_AXI_ARQOS(  smpfull_arqos[  gk*4 +:  4]),

			.S_AXI_RVALID(smpfull_rvalid[gk]),
			.S_AXI_RREADY(smpfull_rready[gk]),
			.S_AXI_RID(   smpfull_rid[  gk*IW +: IW]),
			.S_AXI_RDATA( smpfull_rdata[gk*BUS_WIDTH +: BUS_WIDTH]),
			.S_AXI_RLAST( smpfull_rlast[gk]),
			.S_AXI_RRESP( smpfull_rresp[gk*2 +: 2]),
			// }}}
			// The downsized connection
			// {{{
			.M_AXI_AWVALID(smp_awvalid),
			.M_AXI_AWREADY(smp_awready),
			.M_AXI_AWADDR( smp_awaddr),
			.M_AXI_AWPROT( smp_awprot),

			.M_AXI_WVALID(smp_wvalid),
			.M_AXI_WREADY(smp_wready),
			.M_AXI_WDATA( smp_wdata),
			.M_AXI_WSTRB( smp_wstrb),

			.M_AXI_BVALID(smp_bvalid),
			.M_AXI_BREADY(smp_bready),
			.M_AXI_BRESP( smp_bresp),

			.M_AXI_ARVALID(smp_arvalid),
			.M_AXI_ARREADY(smp_arready),
			.M_AXI_ARADDR( smp_araddr),
			.M_AXI_ARPROT( smp_arprot),

			.M_AXI_RVALID(smp_rvalid),
			.M_AXI_RREADY(smp_rready),
			.M_AXI_RDATA( smp_rdata),
			.M_AXI_RRESP( smp_rresp)
			// }}}
			// }}}
		);

		if (OPT_ZIPAXIL)
		begin : GEN_ZIPAXIL
			// Local declarations
			// {{{
			wire			cpuil_awvalid, cpuil_awready;
			wire	[AW-1:0]	cpuil_awaddr;
			wire	[2:0]		cpuil_awprot;

			wire			cpuil_wvalid, cpuil_wready;
			wire	[BUS_WIDTH-1:0]	cpuil_wdata;
			wire [BUS_WIDTH/8-1:0]	cpuil_wstrb;

			wire			cpuil_bvalid, cpuil_bready;
			wire	[1:0]		cpuil_bresp;

			wire			cpuil_arvalid, cpuil_arready;
			wire	[AW-1:0]	cpuil_araddr;
			wire	[2:0]		cpuil_arprot;

			wire			cpuil_rvalid, cpuil_rready;
			wire	[BUS_WIDTH-1:0]	cpuil_rdata;
			wire	[1:0]		cpuil_rresp;
			//
			wire			cpudl_awvalid, cpudl_awready;
			wire	[AW-1:0]	cpudl_awaddr;
			wire	[2:0]		cpudl_awprot;

			wire			cpudl_wvalid, cpudl_wready;
			wire	[BUS_WIDTH-1:0]	cpudl_wdata;
			wire [BUS_WIDTH/8-1:0]	cpudl_wstrb;

			wire			cpudl_bvalid, cpudl_bready;
			wire	[1:0]		cpudl_bresp;

			wire			cpudl_arvalid, cpudl_arready;
			wire	[AW-1:0]	cpudl_araddr;
			wire	[2:0]		cpudl_arprot;

			wire			cpudl_rvalid, cpudl_rready;
			wire	[BUS_WIDTH-1:0]	cpudl_rdata;
			wire	[1:0]		cpudl_rresp;
			// }}}

			zipaxil #(
				// {{{
				.ADDRESS_WIDTH(ADDRESS_WIDTH),
				.RESET_ADDRESS(RESET_ADDRESS[ADDRESS_WIDTH-1:0]),
				.OPT_PIPELINED(OPT_PIPELINED),
				.C_AXI_DATA_WIDTH(BUS_WIDTH),
				.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
				.OPT_LGICACHE(OPT_LGICACHE),
				.OPT_LGDCACHE(OPT_LGDCACHE),
				.START_HALTED(1'b1),
				.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
				.OPT_MPY(OPT_MPY),
				.OPT_DIV(OPT_DIV),
				.OPT_SHIFTS(OPT_SHIFTS),
				.OPT_LOCK(OPT_LOCK),
				.OPT_CIS(OPT_CIS),
				.OPT_USERMODE(OPT_USERMODE),
				.OPT_DBGPORT(1'b1 || OPT_DBGPORT),
				.OPT_TRACE_PORT(OPT_TRACE_PORT),
				.OPT_PROFILER(OPT_PROFILER),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.OPT_SIM(OPT_SIM),
				.OPT_CLKGATE(OPT_CLKGATE),
				.RESET_DURATION(RESET_DURATION)
				// }}}
			) u_cpu (
				// {{{
				.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
				.i_interrupt(pic_interrupt),
				.i_cpu_reset(!i_aresetn || watchdog_reset),
				// Debug control port
				// {{{
				.S_DBG_AWVALID(smp_awvalid),
				.S_DBG_AWREADY(smp_awready),
				.S_DBG_AWADDR(smp_awaddr),
				.S_DBG_AWPROT(smp_awprot),
				//
				.S_DBG_WVALID(smp_wvalid),
				.S_DBG_WREADY(smp_wready),
				.S_DBG_WDATA( smp_wdata),
				.S_DBG_WSTRB( smp_wstrb),
				//
				.S_DBG_BVALID(smp_bvalid),
				.S_DBG_BREADY(smp_bready),
				.S_DBG_BRESP( smp_bresp),
				//
				.S_DBG_ARVALID(smp_arvalid),
				.S_DBG_ARREADY(smp_arready),
				.S_DBG_ARADDR(smp_araddr),
				.S_DBG_ARPROT(smp_arprot),
				//
				.S_DBG_RVALID(smp_rvalid),
				.S_DBG_RREADY(smp_rready),
				.S_DBG_RDATA( smp_rdata),
				.S_DBG_RRESP( smp_rresp),
				// }}}
				// Master instruction bus
				// {{{
				.M_INSN_AWVALID(cpuil_awvalid),
				.M_INSN_AWREADY(cpuil_awready),
				.M_INSN_AWADDR(cpuil_awaddr),
				.M_INSN_AWPROT(cpuil_awprot),
				//
				.M_INSN_WVALID(cpuil_wvalid),
				.M_INSN_WREADY(cpuil_wready),
				.M_INSN_WDATA( cpuil_wdata),
				.M_INSN_WSTRB( cpuil_wstrb),
				//
				.M_INSN_BVALID(cpuil_bvalid),
				.M_INSN_BREADY(cpuil_bready),
				.M_INSN_BRESP( cpuil_bresp),
				//
				.M_INSN_ARVALID(cpuil_arvalid),
				.M_INSN_ARREADY(cpuil_arready),
				.M_INSN_ARADDR( cpuil_araddr),
				.M_INSN_ARPROT( cpuil_arprot),
				//
				.M_INSN_RVALID(cpuil_rvalid),
				.M_INSN_RREADY(cpuil_rready),
				.M_INSN_RDATA( cpuil_rdata),
				.M_INSN_RRESP( cpuil_rresp),
				// }}}
				// Master data bus
				// {{{
				.M_DATA_AWVALID(cpudl_awvalid),
				.M_DATA_AWREADY(cpudl_awready),
				.M_DATA_AWADDR( cpudl_awaddr),
				.M_DATA_AWPROT( cpudl_awprot),
				//
				.M_DATA_WVALID(cpudl_wvalid),
				.M_DATA_WREADY(cpudl_wready),
				.M_DATA_WDATA( cpudl_wdata),
				.M_DATA_WSTRB( cpudl_wstrb),
				//
				.M_DATA_BVALID(cpudl_bvalid),
				.M_DATA_BREADY(cpudl_bready),
				.M_DATA_BRESP( cpudl_bresp),
				//
				.M_DATA_ARVALID(cpudl_arvalid),
				.M_DATA_ARREADY(cpudl_arready),
				.M_DATA_ARADDR( cpudl_araddr),
				.M_DATA_ARPROT( cpudl_arprot),
				//
				.M_DATA_RVALID(cpudl_rvalid),
				.M_DATA_RREADY(cpudl_rready),
				.M_DATA_RDATA( cpudl_rdata),
				.M_DATA_RRESP( cpudl_rresp),
				// }}}
				.o_cpu_debug(smp_trace),
				// Accounting outputs
				// {{{
				.o_cmd_reset(cpu_reset[gk]),
				.o_halted(   cpu_halted[gk]),
				.o_gie(      cpu_gie[gk]),
				.o_op_stall( cpu_op_stall[gk]),
				.o_pf_stall( cpu_pf_stall[gk]),
				.o_i_count(  cpu_i_count[gk]),
				// }}}
				// (Optional) Profiler
				// {{{
				.o_prof_stb(  smp_prof_stb),
				.o_prof_addr( smp_prof_addr),
				.o_prof_ticks(smp_prof_ticks)
				// }}}
				// }}}
			);

			axilite2axi #(
				// {{{
				.C_AXI_ID_WIDTH(IW),
				.C_AXI_ADDR_WIDTH(AW),
				.C_AXI_DATA_WIDTH(BUS_WIDTH)
				// }}}
			) u_iaxi (
				.ACLK(i_aclk), .ARESETN(i_aresetn),
				// Slave interface, from CPU
				// {{{
				.S_AXI_AWVALID(cpuil_awvalid),
				.S_AXI_AWREADY(cpuil_awready),
				.S_AXI_AWADDR( cpuil_awaddr),
				.S_AXI_AWPROT( cpuil_awprot),

				.S_AXI_WVALID(cpuil_wvalid),
				.S_AXI_WREADY(cpuil_wready),
				.S_AXI_WDATA( cpuil_wdata),
				.S_AXI_WSTRB( cpuil_wstrb),

				.S_AXI_BVALID(cpuil_bvalid),
				.S_AXI_BREADY(cpuil_bready),
				.S_AXI_BRESP( cpuil_bresp),

				.S_AXI_ARVALID(cpuil_arvalid),
				.S_AXI_ARREADY(cpuil_arready),
				.S_AXI_ARADDR( cpuil_araddr),
				.S_AXI_ARPROT( cpuil_arprot),

				.S_AXI_RVALID(cpuil_rvalid),
				.S_AXI_RREADY(cpuil_rready),
				.S_AXI_RDATA( cpuil_rdata),
				.S_AXI_RRESP( cpuil_rresp),
				// }}}
				// Master interface, to the bus
				// {{{
				.M_AXI_AWVALID(cpui_awvalid[gk]),
				.M_AXI_AWREADY(cpui_awready[gk]),
				.M_AXI_AWID(   cpui_awid[   gk*IW +: IW]),
				.M_AXI_AWADDR( cpui_awaddr[ gk*AW +: AW]),
				.M_AXI_AWLEN(  cpui_awlen[  gk*8  +:  8]),
				.M_AXI_AWSIZE( cpui_awsize[ gk*3  +:  3]),
				.M_AXI_AWBURST(cpui_awburst[gk*2  +:  2]),
				.M_AXI_AWLOCK( cpui_awlock[ gk]),
				.M_AXI_AWCACHE(cpui_awcache[gk*4  +:  4]),
				.M_AXI_AWPROT( cpui_awprot[ gk*3  +:  3]),
				.M_AXI_AWQOS(  cpui_awqos[  gk*4  +:  4]),

				.M_AXI_WVALID(cpui_wvalid[gk]),
				.M_AXI_WREADY(cpui_wready[gk]),
				.M_AXI_WDATA( cpui_wdata[gk * BUS_WIDTH +: BUS_WIDTH]),
				.M_AXI_WSTRB( cpui_wstrb[gk * BUS_WIDTH/8 +: BUS_WIDTH/8]),
				.M_AXI_WLAST( cpui_wlast[gk]),

				.M_AXI_BVALID(cpui_bvalid[gk]),
				.M_AXI_BREADY(cpui_bready[gk]),
				.M_AXI_BID(   cpui_bid  [gk*IW +: IW]),
				.M_AXI_BRESP( cpui_bresp[gk*2  +:  2]),

				.M_AXI_ARVALID(cpui_arvalid[gk]),
				.M_AXI_ARREADY(cpui_arready[gk]),
				.M_AXI_ARID(   cpui_arid[   gk*IW +: IW]),
				.M_AXI_ARADDR( cpui_araddr[ gk*AW +: AW]),
				.M_AXI_ARLEN(  cpui_arlen[  gk*8  +:  8]),
				.M_AXI_ARSIZE( cpui_arsize[ gk*3  +:  3]),
				.M_AXI_ARBURST(cpui_arburst[gk*2  +:  2]),
				.M_AXI_ARLOCK( cpui_arlock[ gk]),
				.M_AXI_ARCACHE(cpui_arcache[gk*4  +:  4]),
				.M_AXI_ARPROT( cpui_arprot[ gk*3  +:  3]),
				.M_AXI_ARQOS(  cpui_arqos[  gk*4  +:  4]),

				.M_AXI_RVALID(cpui_rvalid[gk]),
				.M_AXI_RREADY(cpui_rready[gk]),
				.M_AXI_RID(   cpui_rid[gk * IW  +: IW]),
				.M_AXI_RDATA( cpui_rdata[gk * BUS_WIDTH +: BUS_WIDTH]),
				.M_AXI_RLAST( cpui_rlast[gk]),
				.M_AXI_RRESP( cpui_rresp[gk*2  +:  2])
				// }}}
			);

			axilite2axi #(
				// {{{
				.C_AXI_ID_WIDTH(IW),
				.C_AXI_ADDR_WIDTH(AW),
				.C_AXI_DATA_WIDTH(BUS_WIDTH)
				// }}}
			) u_daxi (
				.ACLK(i_aclk), .ARESETN(i_aresetn),
				// Slave interface, from CPU
				// {{{
				.S_AXI_AWVALID(cpudl_awvalid),
				.S_AXI_AWREADY(cpudl_awready),
				.S_AXI_AWADDR( cpudl_awaddr),
				.S_AXI_AWPROT( cpudl_awprot),

				.S_AXI_WVALID(cpudl_wvalid),
				.S_AXI_WREADY(cpudl_wready),
				.S_AXI_WDATA( cpudl_wdata),
				.S_AXI_WSTRB( cpudl_wstrb),

				.S_AXI_BVALID(cpudl_bvalid),
				.S_AXI_BREADY(cpudl_bready),
				.S_AXI_BRESP( cpudl_bresp),

				.S_AXI_ARVALID(cpudl_arvalid),
				.S_AXI_ARREADY(cpudl_arready),
				.S_AXI_ARADDR( cpudl_araddr),
				.S_AXI_ARPROT( cpudl_arprot),

				.S_AXI_RVALID(cpudl_rvalid),
				.S_AXI_RREADY(cpudl_rready),
				.S_AXI_RDATA( cpudl_rdata),
				.S_AXI_RRESP( cpudl_rresp),
				// }}}
				// Master interface, to the bus
				// {{{
				.M_AXI_AWVALID(cpud_awvalid[gk]),
				.M_AXI_AWREADY(cpud_awready[gk]),
				.M_AXI_AWID(   cpud_awid[   gk*IW +: IW]),
				.M_AXI_AWADDR( cpud_awaddr[ gk*AW +: AW]),
				.M_AXI_AWLEN(  cpud_awlen[  gk*8  +:  8]),
				.M_AXI_AWSIZE( cpud_awsize[ gk*3  +:  3]),
				.M_AXI_AWBURST(cpud_awburst[gk*2  +:  2]),
				.M_AXI_AWLOCK( cpud_awlock[ gk]),
				.M_AXI_AWCACHE(cpud_awcache[gk*4  +:  4]),
				.M_AXI_AWPROT( cpud_awprot[ gk*3  +:  3]),
				.M_AXI_AWQOS(  cpud_awqos[  gk*4  +:  4]),

				.M_AXI_WVALID(cpud_wvalid[gk]),
				.M_AXI_WREADY(cpud_wready[gk]),
				.M_AXI_WDATA( cpud_wdata[gk * BUS_WIDTH +: BUS_WIDTH]),
				.M_AXI_WSTRB( cpud_wstrb[gk * BUS_WIDTH/8 +: BUS_WIDTH/8]),
				.M_AXI_WLAST( cpud_wlast[gk]),

				.M_AXI_BVALID(cpud_bvalid[gk]),
				.M_AXI_BREADY(cpud_bready[gk]),
				.M_AXI_BID(   cpud_bid[  gk*IW +: IW]),
				.M_AXI_BRESP( cpud_bresp[gk*2  +:  2]),

				.M_AXI_ARVALID(cpud_arvalid[gk]),
				.M_AXI_ARREADY(cpud_arready[gk]),
				.M_AXI_ARID(   cpud_arid[   gk*IW +: IW]),
				.M_AXI_ARADDR( cpud_araddr[ gk*AW +: AW]),
				.M_AXI_ARLEN(  cpud_arlen[  gk*8  +:  8]),
				.M_AXI_ARSIZE( cpud_arsize[ gk*3  +:  3]),
				.M_AXI_ARBURST(cpud_arburst[gk*2  +:  2]),
				.M_AXI_ARLOCK( cpud_arlock[ gk]),
				.M_AXI_ARCACHE(cpud_arcache[gk*4  +:  4]),
				.M_AXI_ARPROT( cpud_arprot[ gk*3  +:  3]),
				.M_AXI_ARQOS(  cpud_arqos[  gk*4  +:  4]),

				.M_AXI_RVALID(cpud_rvalid[gk]),
				.M_AXI_RREADY(cpud_rready[gk]),
				.M_AXI_RID(   cpud_rid[gk*IW +: IW]),
				.M_AXI_RDATA( cpud_rdata[gk * BUS_WIDTH +: BUS_WIDTH]),
				.M_AXI_RLAST( cpud_rlast[gk]),
				.M_AXI_RRESP( cpud_rresp[gk*2 +: 2])
				// }}}
			);

		end else begin : GEN_ZIPAXI

			zipaxi #(
				// {{{
				.RESET_ADDRESS(RESET_ADDRESS[ADDRESS_WIDTH-1:0]),
				.ADDRESS_WIDTH(ADDRESS_WIDTH),
				.C_AXI_ID_WIDTH(IW),
				.C_AXI_DATA_WIDTH(BUS_WIDTH),
				.OPT_PIPELINED(OPT_PIPELINED),
				.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
				.OPT_LGICACHE(OPT_LGICACHE),
				.OPT_LGDCACHE(OPT_LGDCACHE),
				.START_HALTED(1'b1),
				.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
				.OPT_MPY(OPT_MPY),
				.OPT_DIV(OPT_DIV),
				.OPT_SHIFTS(OPT_SHIFTS),
				.OPT_LOCK(OPT_LOCK),
				.OPT_CIS(OPT_CIS),
				.OPT_USERMODE(OPT_USERMODE),
				.OPT_DBGPORT(1'b1 || OPT_DBGPORT),
				.OPT_TRACE_PORT(OPT_TRACE_PORT),
				.OPT_PROFILER(OPT_PROFILER),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.OPT_SIM(OPT_SIM),
				.OPT_CLKGATE(OPT_CLKGATE),
				.RESET_DURATION(RESET_DURATION)
				// }}}
			) u_cpu (
				// {{{
				.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
				.i_interrupt(pic_interrupt),
				.i_cpu_reset(!i_aresetn || watchdog_reset),
				// Debug control port
				// {{{
				.S_DBG_AWVALID(smp_awvalid),
				.S_DBG_AWREADY(smp_awready),
				.S_DBG_AWADDR(smp_awaddr),
				.S_DBG_AWPROT(smp_awprot),
				//
				.S_DBG_WVALID(smp_wvalid),
				.S_DBG_WREADY(smp_wready),
				.S_DBG_WDATA( smp_wdata),
				.S_DBG_WSTRB( smp_wstrb),
				//
				.S_DBG_BVALID(smp_bvalid),
				.S_DBG_BREADY(smp_bready),
				.S_DBG_BRESP( smp_bresp),
				//
				.S_DBG_ARVALID(smp_arvalid),
				.S_DBG_ARREADY(smp_arready),
				.S_DBG_ARADDR(smp_araddr),
				.S_DBG_ARPROT(smp_arprot),
				//
				.S_DBG_RVALID(smp_rvalid),
				.S_DBG_RREADY(smp_rready),
				.S_DBG_RDATA( smp_rdata),
				.S_DBG_RRESP( smp_rresp),
				// }}}
				// Master instruction bus
				// {{{
				.M_INSN_AWVALID(cpui_awvalid[gk]),
				.M_INSN_AWREADY(cpui_awready[gk]),
				.M_INSN_AWID(   cpui_awid[   gk*IW +: IW]),
				.M_INSN_AWADDR( cpui_awaddr[ gk*AW +: AW]),
				.M_INSN_AWLEN(  cpui_awlen[  gk*8 +: 8]),
				.M_INSN_AWSIZE( cpui_awsize[ gk*3 +: 3]),
				.M_INSN_AWBURST(cpui_awburst[gk*2 +: 2]),
				.M_INSN_AWLOCK( cpui_awlock[ gk]),
				.M_INSN_AWCACHE(cpui_awcache[gk*4 +: 4]),
				.M_INSN_AWPROT( cpui_awprot[ gk*3 +: 3]),
				.M_INSN_AWQOS(  cpui_awqos[  gk*4 +: 4]),
				//
				.M_INSN_WVALID(cpui_wvalid[gk]),
				.M_INSN_WREADY(cpui_wready[gk]),
				.M_INSN_WDATA( cpui_wdata[gk*BUS_WIDTH +: BUS_WIDTH]),
				.M_INSN_WSTRB( cpui_wstrb[gk*BUS_WIDTH/8 +: BUS_WIDTH/8]),
				.M_INSN_WLAST( cpui_wlast[gk]),
				//
				.M_INSN_BVALID(cpui_bvalid[gk]),
				.M_INSN_BREADY(cpui_bready[gk]),
				.M_INSN_BID(   cpui_bid[gk*IW +: IW]),
				.M_INSN_BRESP( cpui_bresp[gk*2 +: 2]),
				//
				.M_INSN_ARVALID(cpui_arvalid[gk]),
				.M_INSN_ARREADY(cpui_arready[gk]),
				.M_INSN_ARID(   cpui_arid[   gk*IW +: IW]),
				.M_INSN_ARADDR( cpui_araddr[ gk*AW +: AW]),
				.M_INSN_ARLEN(  cpui_arlen[  gk*8 +: 8]),
				.M_INSN_ARSIZE( cpui_arsize[ gk*3 +: 3]),
				.M_INSN_ARBURST(cpui_arburst[gk*2 +: 2]),
				.M_INSN_ARLOCK( cpui_arlock[ gk]),
				.M_INSN_ARCACHE(cpui_arcache[gk*4 +: 4]),
				.M_INSN_ARPROT( cpui_arprot[ gk*3 +: 3]),
				.M_INSN_ARQOS(  cpui_arqos[  gk*4 +: 4]),
				//
				.M_INSN_RVALID(cpui_rvalid[gk]),
				.M_INSN_RREADY(cpui_rready[gk]),
				.M_INSN_RID(   cpui_rid[gk*IW +: IW]),
				.M_INSN_RDATA( cpui_rdata[gk*BUS_WIDTH +: BUS_WIDTH]),
				.M_INSN_RLAST( cpui_rlast[gk]),
				.M_INSN_RRESP( cpui_rresp[gk*2 +: 2]),
				// }}}
				// Master data bus
				// {{{
				.M_DATA_AWVALID(cpud_awvalid[gk]),
				.M_DATA_AWREADY(cpud_awready[gk]),
				.M_DATA_AWID(   cpud_awid[   gk*IW +: IW]),
				.M_DATA_AWADDR( cpud_awaddr[ gk*AW +: AW]),
				.M_DATA_AWLEN(  cpud_awlen[  gk*8 +: 8]),
				.M_DATA_AWSIZE( cpud_awsize[ gk*3 +: 3]),
				.M_DATA_AWBURST(cpud_awburst[gk*2 +: 2]),
				.M_DATA_AWLOCK( cpud_awlock[ gk]),
				.M_DATA_AWCACHE(cpud_awcache[gk*4 +: 4]),
				.M_DATA_AWPROT( cpud_awprot[ gk*3 +: 3]),
				.M_DATA_AWQOS(  cpud_awqos[  gk*4 +: 4]),
				//
				.M_DATA_WVALID(cpud_wvalid[gk]),
				.M_DATA_WREADY(cpud_wready[gk]),
				.M_DATA_WDATA( cpud_wdata[gk*BUS_WIDTH +: BUS_WIDTH]),
				.M_DATA_WSTRB( cpud_wstrb[gk*BUS_WIDTH/8 +: BUS_WIDTH/8]),
				.M_DATA_WLAST( cpud_wlast[gk]),
				//
				.M_DATA_BVALID(cpud_bvalid[gk]),
				.M_DATA_BREADY(cpud_bready[gk]),
				.M_DATA_BID(   cpud_bid[   gk*IW +: IW]),
				.M_DATA_BRESP( cpud_bresp[ gk*2 +: 2]),
				//
				.M_DATA_ARVALID(cpud_arvalid[gk]),
				.M_DATA_ARREADY(cpud_arready[gk]),
				.M_DATA_ARID(   cpud_arid[   gk*IW +: IW]),
				.M_DATA_ARADDR( cpud_araddr[ gk*AW +: AW]),
				.M_DATA_ARLEN(  cpud_arlen[  gk*8 +: 8]),
				.M_DATA_ARSIZE( cpud_arsize[ gk*3 +: 3]),
				.M_DATA_ARBURST(cpud_arburst[gk*2 +: 2]),
				.M_DATA_ARLOCK( cpud_arlock[ gk]),
				.M_DATA_ARCACHE(cpud_arcache[gk*4 +: 4]),
				.M_DATA_ARPROT( cpud_arprot[ gk*3 +: 3]),
				.M_DATA_ARQOS(  cpud_arqos[  gk*4 +: 4]),
				//
				.M_DATA_RVALID(cpud_rvalid[gk]),
				.M_DATA_RREADY(cpud_rready[gk]),
				.M_DATA_RID(   cpud_rid[gk*IW +: IW]),
				.M_DATA_RDATA( cpud_rdata[gk*BUS_WIDTH +: BUS_WIDTH]),
				.M_DATA_RLAST( cpud_rlast[gk]),
				.M_DATA_RRESP( cpud_rresp[gk*2 +: 2]),
				// }}}
				.o_cpu_debug(smp_trace),
				// Accounting outputs
				// {{{
				.o_cmd_reset(cpu_reset[gk]),
				.o_halted(   cpu_halted[gk]),
				.o_gie(      cpu_gie[gk]),
				.o_op_stall( cpu_op_stall[gk]),
				.o_pf_stall( cpu_pf_stall[gk]),
				.o_i_count(  cpu_i_count[gk]),
				// }}}
				// (Optional) Profiler
				// {{{
				.o_prof_stb(  smp_prof_stb),
				.o_prof_addr( smp_prof_addr),
				.o_prof_ticks(smp_prof_ticks)
				// }}}
				// }}}
			);

		end

		// Keep Verilator happy with our unused ports
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_smp;
		assign	unused_smp = &{ 1'b0, smp_prof_stb, smp_prof_addr,
					smpfull_awaddr[gk*AW+8 +: (AW-8)],
					smpfull_araddr[gk*AW+8 +: (AW-8)],
					smp_prof_ticks, smp_trace,
					cpu_reset[gk],
					cpu_gie[gk], cpu_op_stall[gk],
					cpu_pf_stall[gk], cpu_i_count[gk] };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The wide bus interconnect
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axixbar #(
		// {{{
`ifdef	VERILATOR
		.NM(1+2*OPT_SMP),
`else
		.NM(2*OPT_SMP),	// ZipAXI(l) CPU is two masters each
`endif
		.NS(4+OPT_SMP),
		.C_AXI_ID_WIDTH(IW),
		.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH), .C_AXI_DATA_WIDTH(BUS_WIDTH),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.SLAVE_ADDR({ AXILP_ADDR, SMP_ADDR, CONSOLE_ADDR, SCOPE_ADDR,
				MEMORY_ADDR }),
		.SLAVE_MASK({
			{ {(AW-24){1'b1}}, {(24){1'b0}} },	// AXI-Lite Periph Set
			SMP_MASK,	// SMP
				{   4'b1111, {(AW-4){1'b0}} },	// Console
				{   4'b1111, {(AW-4){1'b0}} },	// Scope
				{   2'b11,   {(AW-2){1'b0}} } }) // Memory
		// }}}
	) u_main_crossbar (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		// Slave ports from the various bus masters
		// {{{
`ifdef	VERILATOR
		// Three bus masters: the external SIM input, and the CPU
		.S_AXI_AWVALID({ simfull_awvalid, cpui_awvalid, cpud_awvalid }),
		.S_AXI_AWREADY({ simfull_awready, cpui_awready, cpud_awready }),
		.S_AXI_AWID({    simfull_awid,    cpui_awid,    cpud_awid    }),
		.S_AXI_AWADDR({  simfull_awaddr,  cpui_awaddr,  cpud_awaddr  }),
		.S_AXI_AWLEN({   simfull_awlen,   cpui_awlen,   cpud_awlen   }),
		.S_AXI_AWSIZE({  simfull_awsize,  cpui_awsize,  cpud_awsize  }),
		.S_AXI_AWBURST({ simfull_awburst, cpui_awburst, cpud_awburst }),
		.S_AXI_AWLOCK({  simfull_awlock,  cpui_awlock,  cpud_awlock  }),
		.S_AXI_AWCACHE({ simfull_awcache, cpui_awcache, cpud_awcache }),
		.S_AXI_AWPROT({  simfull_awprot,  cpui_awprot,  cpud_awprot  }),
		.S_AXI_AWQOS({   simfull_awqos,   cpui_awqos,   cpud_awqos   }),

		.S_AXI_WVALID({ simfull_wvalid, cpui_wvalid, cpud_wvalid }),
		.S_AXI_WREADY({ simfull_wready, cpui_wready, cpud_wready }),
		.S_AXI_WDATA({  simfull_wdata,  cpui_wdata,  cpud_wdata  }),
		.S_AXI_WSTRB({  simfull_wstrb,  cpui_wstrb,  cpud_wstrb  }),
		.S_AXI_WLAST({  simfull_wlast,  cpui_wlast,  cpud_wlast  }),

		.S_AXI_BVALID({ simfull_bvalid, cpui_bvalid, cpud_bvalid }),
		.S_AXI_BREADY({ simfull_bready, cpui_bready, cpud_bready }),
		.S_AXI_BID({    simfull_bid,    cpui_bid,    cpud_bid    }),
		.S_AXI_BRESP({  simfull_bresp,  cpui_bresp,  cpud_bresp  }),

		.S_AXI_ARVALID({ simfull_arvalid, cpui_arvalid, cpud_arvalid }),
		.S_AXI_ARREADY({ simfull_arready, cpui_arready, cpud_arready }),
		.S_AXI_ARID({    simfull_arid,    cpui_arid,    cpud_arid    }),
		.S_AXI_ARADDR({  simfull_araddr,  cpui_araddr,  cpud_araddr  }),
		.S_AXI_ARLEN({   simfull_arlen,   cpui_arlen,   cpud_arlen   }),
		.S_AXI_ARSIZE({  simfull_arsize,  cpui_arsize,  cpud_arsize  }),
		.S_AXI_ARBURST({ simfull_arburst, cpui_arburst, cpud_arburst }),
		.S_AXI_ARLOCK({  simfull_arlock,  cpui_arlock,  cpud_arlock  }),
		.S_AXI_ARCACHE({ simfull_arcache, cpui_arcache, cpud_arcache }),
		.S_AXI_ARPROT({  simfull_arprot,  cpui_arprot,  cpud_arprot  }),
		.S_AXI_ARQOS({   simfull_arqos,   cpui_arqos,   cpud_arqos   }),

		.S_AXI_RVALID({ simfull_rvalid, cpui_rvalid, cpud_rvalid }),
		.S_AXI_RREADY({ simfull_rready, cpui_rready, cpud_rready }),
		.S_AXI_RID({    simfull_rid,    cpui_rid,    cpud_rid  }),
		.S_AXI_RDATA({  simfull_rdata,  cpui_rdata,  cpud_rdata  }),
		.S_AXI_RLAST({  simfull_rlast,  cpui_rlast,  cpud_rlast  }),
		.S_AXI_RRESP({  simfull_rresp,  cpui_rresp,  cpud_rresp  }),
`else
		// With no external CPU input, there is no simulation port
		.S_AXI_AWVALID({ cpui_awvalid, cpud_awvalid }),
		.S_AXI_AWREADY({ cpui_awready, cpud_awready }),
		.S_AXI_AWID({    cpui_awid,    cpud_awid    }),
		.S_AXI_AWADDR({  cpui_awaddr,  cpud_awaddr  }),
		.S_AXI_AWLEN({   cpui_awlen,   cpud_awlen   }),
		.S_AXI_AWSIZE({  cpui_awsize,  cpud_awsize  }),
		.S_AXI_AWBURST({ cpui_awburst, cpud_awburst }),
		.S_AXI_AWLOCK({  cpui_awlock,  cpud_awlock  }),
		.S_AXI_AWCACHE({ cpui_awcache, cpud_awcache }),
		.S_AXI_AWPROT({  cpui_awprot,  cpud_awprot  }),
		.S_AXI_AWQOS({   cpui_awqos,   cpud_awqos   }),

		.S_AXI_WVALID({ cpui_wvalid, cpud_wvalid }),
		.S_AXI_WREADY({ cpui_wready, cpud_wready }),
		.S_AXI_WDATA({  cpui_wdata,  cpud_wdata  }),
		.S_AXI_WSTRB({  cpui_wstrb,  cpud_wstrb  }),
		.S_AXI_WLAST({  cpui_wlast,  cpud_wlast  }),

		.S_AXI_BVALID({ cpui_bvalid, cpud_bvalid }),
		.S_AXI_BREADY({ cpui_bready, cpud_bready }),
		.S_AXI_BID({    cpui_bid,    cpud_bid    }),
		.S_AXI_BRESP({  cpui_bresp,  cpud_bresp  }),

		.S_AXI_ARVALID({ cpui_arvalid, cpud_arvalid }),
		.S_AXI_ARREADY({ cpui_arready, cpud_arready }),
		.S_AXI_ARID({    cpui_arid,    cpud_arid    }),
		.S_AXI_ARADDR({  cpui_araddr,  cpud_araddr  }),
		.S_AXI_ARLEN({   cpui_arlen,   cpud_arlen   }),
		.S_AXI_ARSIZE({  cpui_arsize,  cpud_arsize  }),
		.S_AXI_ARBURST({ cpui_arburst, cpud_arburst }),
		.S_AXI_ARLOCK({  cpui_arlock,  cpud_arlock  }),
		.S_AXI_ARCACHE({ cpui_arcache, cpud_arcache }),
		.S_AXI_ARPROT({  cpui_arprot,  cpud_arprot  }),
		.S_AXI_ARQOS({   cpui_arqos,   cpud_arqos   }),

		.S_AXI_RVALID({ cpui_rvalid, cpud_rvalid }),
		.S_AXI_RREADY({ cpui_rready, cpud_rready }),
		.S_AXI_RID({    cpui_rid,    cpud_rid  }),
		.S_AXI_RDATA({  cpui_rdata,  cpud_rdata  }),
		.S_AXI_RLAST({  cpui_rlast,  cpud_rlast  }),
		.S_AXI_RRESP({  cpui_rresp,  cpud_rresp  }),
`endif
		// }}}
		// Master port ... to control the slaves w/in this design
		// {{{
		.M_AXI_AWVALID({ axip_awvalid, smpfull_awvalid, con_awvalid, scope_awvalid,  mem_awvalid  }),
		.M_AXI_AWREADY({ axip_awready, smpfull_awready, con_awready, scope_awready,  mem_awready  }),
		.M_AXI_AWID({    axip_awid,    smpfull_awid,    con_awid,    scope_awid,     mem_awid  }),
		.M_AXI_AWADDR({  axip_awaddr,  smpfull_awaddr,  con_awaddr,  scope_awaddr,   mem_awaddr  }),
		.M_AXI_AWLEN({   axip_awlen,   smpfull_awlen,   con_awlen,   scope_awlen,    mem_awlen  }),
		.M_AXI_AWSIZE({  axip_awsize,  smpfull_awsize,  con_awsize,  scope_awsize,   mem_awsize  }),
		.M_AXI_AWBURST({ axip_awburst, smpfull_awburst, con_awburst, scope_awburst,  mem_awburst  }),
		.M_AXI_AWLOCK({  axip_awlock,  smpfull_awlock,  con_awlock,  scope_awlock,   mem_awlock  }),
		.M_AXI_AWCACHE({ axip_awcache, smpfull_awcache, con_awcache, scope_awcache,  mem_awcache  }),
		.M_AXI_AWPROT({  axip_awprot,  smpfull_awprot,  con_awprot,  scope_awprot,   mem_awprot  }),
		.M_AXI_AWQOS({   axip_awqos,   smpfull_awqos,   con_awqos,   scope_awqos,    mem_awqos  }),
		//
		.M_AXI_WVALID({ axip_wvalid, smpfull_wvalid, con_wvalid, scope_wvalid,  mem_wvalid  }),
		.M_AXI_WREADY({ axip_wready, smpfull_wready, con_wready, scope_wready,  mem_wready  }),
		.M_AXI_WDATA({  axip_wdata,  smpfull_wdata,  con_wdata,  scope_wdata,   mem_wdata  }),
		.M_AXI_WSTRB({  axip_wstrb,  smpfull_wstrb,  con_wstrb,  scope_wstrb,   mem_wstrb  }),
		.M_AXI_WLAST({  axip_wlast,  smpfull_wlast,  con_wlast,  scope_wlast,   mem_wlast  }),
		//
		.M_AXI_BVALID({ axip_bvalid, smpfull_bvalid, con_bvalid, scope_bvalid,  mem_bvalid  }),
		.M_AXI_BREADY({ axip_bready, smpfull_bready, con_bready, scope_bready,  mem_bready  }),
		.M_AXI_BID({    axip_bid,    smpfull_bid,    con_bid,    scope_bid,     mem_bid  }),
		.M_AXI_BRESP({  axip_bresp,  smpfull_bresp,  con_bresp,  scope_bresp,   mem_bresp  }),
		//
		.M_AXI_ARVALID({ axip_arvalid, smpfull_arvalid, con_arvalid, scope_arvalid,  mem_arvalid  }),
		.M_AXI_ARREADY({ axip_arready, smpfull_arready, con_arready, scope_arready,  mem_arready  }),
		.M_AXI_ARID({    axip_arid,    smpfull_arid,    con_arid,    scope_arid,     mem_arid  }),
		.M_AXI_ARADDR({  axip_araddr,  smpfull_araddr,  con_araddr,  scope_araddr,   mem_araddr  }),
		.M_AXI_ARLEN({   axip_arlen,   smpfull_arlen,   con_arlen,   scope_arlen,    mem_arlen  }),
		.M_AXI_ARSIZE({  axip_arsize,  smpfull_arsize,  con_arsize,  scope_arsize,   mem_arsize  }),
		.M_AXI_ARBURST({ axip_arburst, smpfull_arburst, con_arburst, scope_arburst,  mem_arburst  }),
		.M_AXI_ARLOCK({  axip_arlock,  smpfull_arlock,  con_arlock,  scope_arlock,   mem_arlock  }),
		.M_AXI_ARCACHE({ axip_arcache, smpfull_arcache, con_arcache, scope_arcache,  mem_arcache  }),
		.M_AXI_ARPROT({  axip_arprot,  smpfull_arprot,  con_arprot,  scope_arprot,   mem_arprot  }),
		.M_AXI_ARQOS({   axip_arqos,   smpfull_arqos,   con_arqos,   scope_arqos,    mem_arqos  }),
		//
		.M_AXI_RVALID({ axip_rvalid, smpfull_rvalid, con_rvalid, scope_rvalid,  mem_rvalid  }),
		.M_AXI_RREADY({ axip_rready, smpfull_rready, con_rready, scope_rready,  mem_rready  }),
		.M_AXI_RID({    axip_rid,    smpfull_rid,    con_rid,    scope_rid,     mem_rid  }),
		.M_AXI_RDATA({  axip_rdata,  smpfull_rdata,  con_rdata,  scope_rdata,   mem_rdata  }),
		.M_AXI_RLAST({  axip_rlast,  smpfull_rlast,  con_rlast,  scope_rlast,   mem_rlast  }),
		.M_AXI_RRESP({  axip_rresp,  smpfull_rresp,  con_rresp,  scope_rresp,   mem_rresp  })
		// }}}
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	demofull #(
		// {{{
		.C_S_AXI_ID_WIDTH(IW),
		.C_S_AXI_DATA_WIDTH(BUS_WIDTH),
		.C_S_AXI_ADDR_WIDTH(LGMEMSZ),
		.OPT_LOCK(1'b1)
		// }}}
	) u_memaxi (
		// {{{
		.o_we(ram_we),
		.o_waddr(ram_waddr),
		.o_wdata(ram_wdata),
		.o_wstrb(ram_wstrb),
		.o_rd(ram_rd),
		.o_raddr(ram_raddr),
		.i_rdata(ram_rdata),
		//
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		//
		.S_AXI_AWVALID(mem_awvalid),
		.S_AXI_AWREADY(mem_awready),
		.S_AXI_AWID(   mem_awid),
		.S_AXI_AWADDR( mem_awaddr[LGMEMSZ-1:0]),
		.S_AXI_AWLEN(  mem_awlen),
		.S_AXI_AWSIZE( mem_awsize),
		.S_AXI_AWBURST(mem_awburst),
		.S_AXI_AWLOCK( mem_awlock),
		.S_AXI_AWCACHE(mem_awcache),
		.S_AXI_AWPROT( mem_awprot),
		.S_AXI_AWQOS(  mem_awqos),
		//
		.S_AXI_WVALID(mem_wvalid),
		.S_AXI_WREADY(mem_wready),
		.S_AXI_WDATA( mem_wdata),
		.S_AXI_WSTRB( mem_wstrb),
		.S_AXI_WLAST( mem_wlast),
		//
		.S_AXI_BVALID(mem_bvalid),
		.S_AXI_BREADY(mem_bready),
		.S_AXI_BID(   mem_bid),
		.S_AXI_BRESP( mem_bresp),
		//
		.S_AXI_ARVALID(mem_arvalid),
		.S_AXI_ARREADY(mem_arready),
		.S_AXI_ARID(   mem_arid),
		.S_AXI_ARADDR( mem_araddr[LGMEMSZ-1:0]),
		.S_AXI_ARLEN(  mem_arlen),
		.S_AXI_ARSIZE( mem_arsize),
		.S_AXI_ARBURST(mem_arburst),
		.S_AXI_ARLOCK( mem_arlock),
		.S_AXI_ARCACHE(mem_arcache),
		.S_AXI_ARPROT( mem_arprot),
		.S_AXI_ARQOS(  mem_arqos),
		//
		.S_AXI_RVALID(mem_rvalid),
		.S_AXI_RREADY(mem_rready),
		.S_AXI_RID(   mem_rid),
		.S_AXI_RDATA( mem_rdata),
		.S_AXI_RLAST( mem_rlast),
		.S_AXI_RRESP( mem_rresp)
		// }}}
	);

	initial	begin
		$display("MEM_FILE     = %s", MEM_FILE);
		$display("CONSOLE_FILE = %s", CONSOLE_FILE);
		$readmemh(MEM_FILE, ram);
	end

	generate for(gk=0; gk<BUS_WIDTH/32; gk=gk+1)
	begin : SWAP_RAM_WORDS
		// The ZipCPU's AXI interface currently maintains a little
		// endian word order, while using big endian word order within
		// a word.
		assign	ram_wstrb_swap[ 4*gk +:  4] = ram_wstrb[ 4*(BUS_WIDTH/32-gk-1) +: 4];
		assign	ram_wdata_swap[32*gk +: 32] = ram_wdata[32*(BUS_WIDTH/32-gk-1) +:32];

		assign	ram_rdata[32*gk +: 32] = ram_rdata_swap[32*(BUS_WIDTH/32-gk-1) +:32];
	end endgenerate

	always @(posedge i_aclk)
	if (ram_we)
	for(rk=0; rk<BUS_WIDTH/8; rk=rk+1)
	if (ram_wstrb_swap[rk])
		ram[ram_waddr][rk*8 +: 8] <= ram_wdata_swap[rk*8 +: 8];

	always @(posedge i_aclk)
	if (ram_rd)
		ram_rdata_swap <= ram[ram_raddr];

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_mem;
	assign	unused_mem = &{ 1'b0,
			mem_awaddr[AW-1:LGMEMSZ], mem_araddr[AW-1:LGMEMSZ]
			};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Console
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axi2axilsub #(
		// {{{
		.C_AXI_ID_WIDTH(IW),
		.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH-3),
		.C_S_AXI_DATA_WIDTH(BUS_WIDTH),
		.C_M_AXI_DATA_WIDTH(32),
		.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_WRITES(1), .OPT_READS(1)
		// }}}
	) u_condown (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		// The "Wide" slave connection
		// {{{
		.S_AXI_AWVALID(con_awvalid),
		.S_AXI_AWREADY(con_awready),
		.S_AXI_AWID(   con_awid),
		.S_AXI_AWADDR( con_awaddr[AW-4:0]),
		.S_AXI_AWLEN(  con_awlen),
		.S_AXI_AWSIZE( con_awsize),
		.S_AXI_AWBURST(con_awburst),
		.S_AXI_AWLOCK( con_awlock),
		.S_AXI_AWCACHE(con_awcache),
		.S_AXI_AWPROT( con_awprot),
		.S_AXI_AWQOS(  con_awqos),

		.S_AXI_WVALID(con_wvalid),
		.S_AXI_WREADY(con_wready),
		.S_AXI_WDATA( con_wdata),
		.S_AXI_WSTRB( con_wstrb),
		.S_AXI_WLAST( con_wlast),

		.S_AXI_BVALID(con_bvalid),
		.S_AXI_BREADY(con_bready),
		.S_AXI_BID(   con_bid),
		.S_AXI_BRESP( con_bresp),

		.S_AXI_ARVALID(con_arvalid),
		.S_AXI_ARREADY(con_arready),
		.S_AXI_ARID(   con_arid),
		.S_AXI_ARADDR( con_araddr[AW-4:0]),
		.S_AXI_ARLEN(  con_arlen),
		.S_AXI_ARSIZE( con_arsize),
		.S_AXI_ARBURST(con_arburst),
		.S_AXI_ARLOCK( con_arlock),
		.S_AXI_ARCACHE(con_arcache),
		.S_AXI_ARPROT( con_arprot),
		.S_AXI_ARQOS(  con_arqos),

		.S_AXI_RVALID(con_rvalid),
		.S_AXI_RREADY(con_rready),
		.S_AXI_RID(   con_rid),
		.S_AXI_RDATA( con_rdata),
		.S_AXI_RLAST( con_rlast),
		.S_AXI_RRESP( con_rresp),
		// }}}
		// The downsized connection
		// {{{
		.M_AXI_AWVALID(conl_awvalid),
		.M_AXI_AWREADY(conl_awready),
		.M_AXI_AWADDR( conl_awaddr),
		.M_AXI_AWPROT( conl_awprot),

		.M_AXI_WVALID(conl_wvalid),
		.M_AXI_WREADY(conl_wready),
		.M_AXI_WDATA( conl_wdata),
		.M_AXI_WSTRB( conl_wstrb),

		.M_AXI_BVALID(conl_bvalid),
		.M_AXI_BREADY(conl_bready),
		.M_AXI_BRESP( conl_bresp),

		.M_AXI_ARVALID(conl_arvalid),
		.M_AXI_ARREADY(conl_arready),
		.M_AXI_ARADDR( conl_araddr),
		.M_AXI_ARPROT( conl_arprot),

		.M_AXI_RVALID(conl_rvalid),
		.M_AXI_RREADY(conl_rready),
		.M_AXI_RDATA( conl_rdata),
		.M_AXI_RRESP( conl_rresp)
		// }}}
		// }}}
	);

	axilcon #(
		.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_SKIDBUFFER(1'b1),
		.CONSOLE_FILE(CONSOLE_FILE)
	) u_console (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		// Slave bus connection(s)
		// {{{
		.S_AXI_AWVALID(conl_awvalid),
		.S_AXI_AWREADY(conl_awready),
		.S_AXI_AWADDR( conl_awaddr[3:0]),
		.S_AXI_AWPROT( conl_awprot),

		.S_AXI_WVALID(conl_wvalid),
		.S_AXI_WREADY(conl_wready),
		.S_AXI_WDATA( conl_wdata),
		.S_AXI_WSTRB( conl_wstrb),

		.S_AXI_BVALID(conl_bvalid),
		.S_AXI_BREADY(conl_bready),
		.S_AXI_BRESP( conl_bresp),

		.S_AXI_ARVALID(conl_arvalid),
		.S_AXI_ARREADY(conl_arready),
		.S_AXI_ARADDR( conl_araddr[3:0]),
		.S_AXI_ARPROT( conl_arprot),

		.S_AXI_RVALID(conl_rvalid),
		.S_AXI_RREADY(conl_rready),
		.S_AXI_RDATA( conl_rdata),
		.S_AXI_RRESP( conl_rresp)
		// }}}
		// }}}
	);

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_con;
	assign	unused_con = &{ 1'b0,
			con_awaddr[AW-1:AW-4], con_araddr[AW-1:AW-4],
			conl_awaddr[AW-4:4],   conl_araddr[AW-4:4]
			};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-Lite peripheral set (timers, counters, PIC, etc.)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axi2axilsub #(
		// {{{
		.C_AXI_ID_WIDTH(IW),
		.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH-3),
		.C_S_AXI_DATA_WIDTH(BUS_WIDTH),
		.C_M_AXI_DATA_WIDTH(32),
		.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_WRITES(1), .OPT_READS(1)
		// }}}
	) u_axilpdown (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		// The "Wide" slave connection
		// {{{
		.S_AXI_AWVALID(axip_awvalid),
		.S_AXI_AWREADY(axip_awready),
		.S_AXI_AWID(   axip_awid),
		.S_AXI_AWADDR( axip_awaddr[AW-4:0]),
		.S_AXI_AWLEN(  axip_awlen),
		.S_AXI_AWSIZE( axip_awsize),
		.S_AXI_AWBURST(axip_awburst),
		.S_AXI_AWLOCK( axip_awlock),
		.S_AXI_AWCACHE(axip_awcache),
		.S_AXI_AWPROT( axip_awprot),
		.S_AXI_AWQOS(  axip_awqos),

		.S_AXI_WVALID(axip_wvalid),
		.S_AXI_WREADY(axip_wready),
		.S_AXI_WDATA( axip_wdata),
		.S_AXI_WSTRB( axip_wstrb),
		.S_AXI_WLAST( axip_wlast),

		.S_AXI_BVALID(axip_bvalid),
		.S_AXI_BREADY(axip_bready),
		.S_AXI_BID(   axip_bid),
		.S_AXI_BRESP( axip_bresp),

		.S_AXI_ARVALID(axip_arvalid),
		.S_AXI_ARREADY(axip_arready),
		.S_AXI_ARID(   axip_arid),
		.S_AXI_ARADDR( axip_araddr[AW-4:0]),
		.S_AXI_ARLEN(  axip_arlen),
		.S_AXI_ARSIZE( axip_arsize),
		.S_AXI_ARBURST(axip_arburst),
		.S_AXI_ARLOCK( axip_arlock),
		.S_AXI_ARCACHE(axip_arcache),
		.S_AXI_ARPROT( axip_arprot),
		.S_AXI_ARQOS(  axip_arqos),

		.S_AXI_RVALID(axip_rvalid),
		.S_AXI_RREADY(axip_rready),
		.S_AXI_RID(   axip_rid),
		.S_AXI_RDATA( axip_rdata),
		.S_AXI_RLAST( axip_rlast),
		.S_AXI_RRESP( axip_rresp),
		// }}}
		// The downsized connection
		// {{{
		.M_AXI_AWVALID(axilp_awvalid),
		.M_AXI_AWREADY(axilp_awready),
		.M_AXI_AWADDR( axilp_awaddr),
		.M_AXI_AWPROT( axilp_awprot),

		.M_AXI_WVALID(axilp_wvalid),
		.M_AXI_WREADY(axilp_wready),
		.M_AXI_WDATA( axilp_wdata),
		.M_AXI_WSTRB( axilp_wstrb),

		.M_AXI_BVALID(axilp_bvalid),
		.M_AXI_BREADY(axilp_bready),
		.M_AXI_BRESP( axilp_bresp),

		.M_AXI_ARVALID(axilp_arvalid),
		.M_AXI_ARREADY(axilp_arready),
		.M_AXI_ARADDR( axilp_araddr),
		.M_AXI_ARPROT( axilp_arprot),

		.M_AXI_RVALID(axilp_rvalid),
		.M_AXI_RREADY(axilp_rready),
		.M_AXI_RDATA( axilp_rdata),
		.M_AXI_RRESP( axilp_rresp)
		// }}}
		// }}}
	);

	axilperiphs #(
		.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_SKIDBUFFER(1'b1),
		.OPT_COUNTERS(1'b1), .EXTERNAL_INTERRUPTS(2)
	) u_axilp (
		// {{{
		.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
		// Slave bus connection(s)
		// {{{
		.S_AXI_AWVALID(axilp_awvalid),
		.S_AXI_AWREADY(axilp_awready),
		.S_AXI_AWADDR( axilp_awaddr[5:0]),
		.S_AXI_AWPROT( axilp_awprot),

		.S_AXI_WVALID(axilp_wvalid),
		.S_AXI_WREADY(axilp_wready),
		.S_AXI_WDATA( axilp_wdata),
		.S_AXI_WSTRB( axilp_wstrb),

		.S_AXI_BVALID(axilp_bvalid),
		.S_AXI_BREADY(axilp_bready),
		.S_AXI_BRESP( axilp_bresp),

		.S_AXI_ARVALID(axilp_arvalid),
		.S_AXI_ARREADY(axilp_arready),
		.S_AXI_ARADDR( axilp_araddr[5:0]),
		.S_AXI_ARPROT( axilp_arprot),

		.S_AXI_RVALID(axilp_rvalid),
		.S_AXI_RREADY(axilp_rready),
		.S_AXI_RDATA( axilp_rdata),
		.S_AXI_RRESP( axilp_rresp),
		// }}}
		.i_cpu_reset(cpu_reset[0]),
		.i_cpu_halted(cpu_halted[0]),
		.i_cpu_gie(cpu_gie[0]),
		.i_cpu_pfstall(cpu_pf_stall[0]),
		.i_cpu_opstall(cpu_op_stall[0]),
		.i_cpu_icount(cpu_i_count[0]),
		.i_ivec({ scope_int, i_sim_int }),
		.o_interrupt(pic_interrupt),
		.o_watchdog_reset(watchdog_reset)
		// }}}
	);

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_axip;
	assign	unused_axip = &{ 1'b0,
			axip_awaddr[AW-1:AW-4], axip_araddr[AW-1:AW-4],
			axilp_awaddr[AW-4:4],   axilp_araddr[AW-4:4]
			};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) AXIL Scope
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_TRACE_PORT)
	begin : GEN_AXILSCOPE
		// {{{
		wire			scopel_awvalid, scopel_awready;
		wire	[AW-4:0]	scopel_awaddr;
		wire	[2:0]		scopel_awprot;

		wire			scopel_wvalid, scopel_wready;
		wire	[BUS_WIDTH-1:0]	scopel_wdata;
		wire [BUS_WIDTH/8-1:0]	scopel_wstrb;

		wire			scopel_bvalid, scopel_bready;
		wire	[1:0]		scopel_bresp;

		wire			scopel_arvalid, scopel_arready;
		wire	[AW-4:0]	scopel_araddr;
		wire	[2:0]		scopel_arprot;

		wire			scopel_rvalid, scopel_rready;
		wire	[BUS_WIDTH-1:0]	scopel_rdata;
		wire	[1:0]		scopel_rresp;
		//

		axi2axilsub #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH-3),
			.C_S_AXI_DATA_WIDTH(BUS_WIDTH),
			.C_M_AXI_DATA_WIDTH(32),
			.OPT_LOWPOWER(OPT_LOWPOWER), .OPT_WRITES(1), .OPT_READS(1)
			// }}}
		) u_scopedown (
			// {{{
			.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
			// The "Wide" slave connection
			// {{{
			.S_AXI_AWVALID(scope_awvalid),
			.S_AXI_AWREADY(scope_awready),
			.S_AXI_AWID(   scope_awid),
			.S_AXI_AWADDR( scope_awaddr[AW-4:0]),
			.S_AXI_AWLEN(  scope_awlen),
			.S_AXI_AWSIZE( scope_awsize),
			.S_AXI_AWBURST(scope_awburst),
			.S_AXI_AWLOCK( scope_awlock),
			.S_AXI_AWCACHE(scope_awcache),
			.S_AXI_AWPROT( scope_awprot),
			.S_AXI_AWQOS(  scope_awqos),

			.S_AXI_WVALID(scope_wvalid),
			.S_AXI_WREADY(scope_wready),
			.S_AXI_WDATA( scope_wdata),
			.S_AXI_WSTRB( scope_wstrb),
			.S_AXI_WLAST( scope_wlast),

			.S_AXI_BVALID(scope_bvalid),
			.S_AXI_BREADY(scope_bready),
			.S_AXI_BID(   scope_bid),
			.S_AXI_BRESP( scope_bresp),

			.S_AXI_ARVALID(scope_arvalid),
			.S_AXI_ARREADY(scope_arready),
			.S_AXI_ARID(   scope_arid),
			.S_AXI_ARADDR( scope_araddr[AW-4:0]),
			.S_AXI_ARLEN(  scope_arlen),
			.S_AXI_ARSIZE( scope_arsize),
			.S_AXI_ARBURST(scope_arburst),
			.S_AXI_ARLOCK( scope_arlock),
			.S_AXI_ARCACHE(scope_arcache),
			.S_AXI_ARPROT( scope_arprot),
			.S_AXI_ARQOS(  scope_arqos),

			.S_AXI_RVALID(scope_rvalid),
			.S_AXI_RREADY(scope_rready),
			.S_AXI_RID(   scope_rid),
			.S_AXI_RDATA( scope_rdata),
			.S_AXI_RLAST( scope_rlast),
			.S_AXI_RRESP( scope_rresp),
			// }}}
			// The downsized connection
			// {{{
			.M_AXI_AWVALID(scopel_awvalid),
			.M_AXI_AWREADY(scopel_awready),
			.M_AXI_AWADDR( scopel_awaddr),
			.M_AXI_AWPROT( scopel_awprot),

			.M_AXI_WVALID(scopel_wvalid),
			.M_AXI_WREADY(scopel_wready),
			.M_AXI_WDATA( scopel_wdata),
			.M_AXI_WSTRB( scopel_wstrb),

			.M_AXI_BVALID(scopel_bvalid),
			.M_AXI_BREADY(scopel_bready),
			.M_AXI_BRESP( scopel_bresp),

			.M_AXI_ARVALID(scopel_arvalid),
			.M_AXI_ARREADY(scopel_arready),
			.M_AXI_ARADDR( scopel_araddr),
			.M_AXI_ARPROT( scopel_arprot),

			.M_AXI_RVALID(scopel_rvalid),
			.M_AXI_RREADY(scopel_rready),
			.M_AXI_RDATA( scopel_rdata),
			.M_AXI_RRESP( scopel_rresp)
			// }}}
			// }}}
		);

		axilscope #(
			.LGMEM(12)
		) u_scope (
			// {{{
			.i_data_clk(i_aclk), .i_ce(1'b1), .i_trigger(1'b0),
			.i_data(cpu_trace), .o_interrupt(scope_int),
			//
			.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),
			// Slave bus connection(s)
			// {{{
			.S_AXI_AWVALID(scopel_awvalid),
			.S_AXI_AWREADY(scopel_awready),
			.S_AXI_AWADDR( scopel_awaddr[2:0]),
			.S_AXI_AWPROT( scopel_awprot),

			.S_AXI_WVALID(scopel_wvalid),
			.S_AXI_WREADY(scopel_wready),
			.S_AXI_WDATA( scopel_wdata),
			.S_AXI_WSTRB( scopel_wstrb),

			.S_AXI_BVALID(scopel_bvalid),
			.S_AXI_BREADY(scopel_bready),
			.S_AXI_BRESP( scopel_bresp),

			.S_AXI_ARVALID(scopel_arvalid),
			.S_AXI_ARREADY(scopel_arready),
			.S_AXI_ARADDR( scopel_araddr[2:0]),
			.S_AXI_ARPROT( scopel_arprot),

			.S_AXI_RVALID(scopel_rvalid),
			.S_AXI_RREADY(scopel_rready),
			.S_AXI_RDATA( scopel_rdata),
			.S_AXI_RRESP( scopel_rresp)
			// }}}
			// }}}
		);
		// }}}
	end else begin : NO_SCOPE
		// {{{
		// The (NULL) slave that does nothing but (validly) return bus
		// errors
		axiempty #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(BUS_WIDTH),
			.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH)
			// }}}
		) u_noscope (
			// {{{
			.S_AXI_ACLK(i_aclk), .S_AXI_ARESETN(i_aresetn),

			.S_AXI_AWVALID(scope_awvalid),
			.S_AXI_AWREADY(scope_awready),
			.S_AXI_AWID(   scope_awid),

			.S_AXI_WVALID(scope_wvalid),
			.S_AXI_WREADY(scope_wready),
			.S_AXI_WLAST( scope_wlast),

			.S_AXI_BVALID(scope_bvalid),
			.S_AXI_BREADY(scope_bready),
			.S_AXI_BID(   scope_bid),
			.S_AXI_BRESP( scope_bresp),

			.S_AXI_ARVALID(scope_arvalid),
			.S_AXI_ARREADY(scope_arready),
			.S_AXI_ARID(   scope_arid),
			.S_AXI_ARLEN(  scope_arlen),

			.S_AXI_RVALID(scope_rvalid),
			.S_AXI_RREADY(scope_rready),
			.S_AXI_RID(   scope_rid),
			.S_AXI_RDATA( scope_rdata),
			.S_AXI_RLAST( scope_rlast),
			.S_AXI_RRESP( scope_rresp)
			// }}}
		);

		assign	scope_int = 1'b0;
		// }}}

		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_scope;
		assign	unused_scope = &{ 1'b0,
				cpu_trace,
				scope_awaddr, scope_awlen, scope_awlock, scope_awburst, scope_awsize, scope_awcache, scope_awprot, scope_awqos,
				scope_wdata, scope_wstrb,
				scope_araddr, scope_arlen, scope_arlock, scope_arburst, scope_arsize, scope_arcache, scope_arprot, scope_arqos
				};
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) VCD generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifndef	VERILATOR
	initial if (DUMP_TO_VCD)
	begin
		$dumpfile(VCD_FILE);
		$dumpvars(0, axi_tb);
	end
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Test bench watchdog
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Don't let the simulation hang.  Let's place a watchdog timeout on the
	// CPU's data bus.  If the databus becomes idle for too long, then
	// stop the simulation with an error.

	initial	watchdog_counter = 0;
	always @(posedge i_aclk)
	// if (!i_aresetn)
	//	watchdog_counter <= 0;
	// else
	if (|(cpud_awvalid & cpud_awready)
				|| |(cpud_arvalid & cpud_arready))
		watchdog_counter <= 0;
	else
		watchdog_counter <= watchdog_counter + 1;

	always @(posedge i_aclk)
	if (watchdog_counter > TB_WATCHDOG_TIMEOUT)
	begin
		$display("\nERROR: Watchdog timeout!");
		$finish;
	end

	always @(posedge i_aclk)
	if (i_aresetn && (&cpu_halted))
	begin
		$display("\nCPU Halted without error: PASS\n");
		$finish;
	end
	// }}}
endmodule
