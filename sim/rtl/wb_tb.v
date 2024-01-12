////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/rtl/wb_tb.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Top level test infrastructure for all Wishbone configurations
//		of the ZipCPU.  Contains:
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
//	ZipCPU's various Wishbone configurations, and by using it to routinely
//	smoke out any bugs before making any releases.
//
//	A similar test bench exists for for testing the Wishbone version(s) of
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
module	wb_tb #(
		// {{{
		parameter	ADDRESS_WIDTH        = 28,	//Width in bytes
		parameter	BUS_WIDTH            = 32,
		// Verilator lint_off WIDTH
		parameter [0:0]	OPT_ZIPBONES         = 1'b1,
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
		parameter [0:0]	OPT_DMA              = 1'b1,
		parameter	OPT_SMP              = 1, // Must be > 0
		parameter	MEM_FILE = "cputest",
		parameter	CONSOLE_FILE = "console.txt",
		parameter	LGMEMSZ = ADDRESS_WIDTH-2,
		//
		parameter [0:0]	DUMP_TO_VCD = 1'b0,
		parameter	VCD_FILE = "dump.vcd"
		// Verilator lint_on  WIDTH
		// }}}
	) (
		// {{{
`ifdef	VERILATOR
		input	wire	i_clk, i_reset,
		// Sim control input(s)
		// {{{
		input	wire	i_sim_cyc, i_sim_stb, i_sim_we,
		input	wire	[ADDRESS_WIDTH-2:0]	i_sim_addr,
		input	wire	[31:0]			i_sim_data,
		input	wire	[3:0]			i_sim_sel,
		output	wire				o_sim_stall,
		output	wire				o_sim_ack,
		output	wire	[31:0]			o_sim_data,
		output	wire				o_sim_err,
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
	genvar		gk;
	localparam	WBLSB = $clog2(BUS_WIDTH/8);
	parameter [31:0] RESET_ADDRESS = { {(32-ADDRESS_WIDTH){1'b0}}, MEMORY_ADDR, {(WBLSB){1'b0}} };
	localparam	WAW = ADDRESS_WIDTH-WBLSB;
	parameter [WAW-1:0]	SCOPE_ADDR   = { 4'b0001, {(WAW-4){1'b0}} };
	parameter [WAW-1:0]	CONSOLE_ADDR = { 4'b0010, {(WAW-4){1'b0}} };
	parameter [WAW-1:0]	SMP_BASE_ADDR = { 4'b0011, {(WAW-4){1'b0}} };
	parameter [WAW-1:0]	ZSYS_ADDR = { {(ADDRESS_WIDTH-24){1'b1}}, {(24-WBLSB){1'b0}} };
	parameter [WAW-1:0]	MEMORY_ADDR  = { 2'b01, {(WAW-2){1'b0}} };
	localparam	LGFIFO = 4;

	localparam	MIN_SMP = (OPT_SMP < 2) ? 1 : OPT_SMP;
	parameter	[OPT_SMP*WAW-1:0]	SMP_ADDR = SMP_ADDR_fn(MIN_SMP);
	parameter	[OPT_SMP*WAW-1:0]	SMP_MASK = SMP_MASK_fn(MIN_SMP);

	// Verilator lint_off UNUSED
	function [OPT_SMP*WAW-1:0]	SMP_ADDR_fn(input integer min_smp);
		// {{{
		integer	ik, offset;
	begin
		SMP_ADDR_fn = {(OPT_SMP){SMP_BASE_ADDR}};

		for(ik=1; ik < OPT_SMP; ik=ik+1)
		begin
			offset = ik;
			SMP_ADDR_fn[ik*WAW+(9-WBLSB) +: $clog2(OPT_SMP)+1]
				= offset[$clog2(OPT_SMP):0];
		end
	end endfunction
	// }}}

	function [OPT_SMP*WAW-1:0]	SMP_MASK_fn(input integer min_smp);
		// {{{
		integer	ik;
	begin
		SMP_MASK_fn = {(OPT_SMP){ 4'b1111, {(WAW-4){1'b0}} }};

		for(ik=0; ik < OPT_SMP; ik=ik+1)
		begin
			SMP_MASK_fn[ik*WAW+(9-WBLSB) +: $clog2(OPT_SMP)+1]
				= {($clog2(OPT_SMP)+1){1'b1}};
		end
	end endfunction
	// Verilator lint_on  UNUSED
	// }}}

	wire	[OPT_SMP-1:0]	cpu_int;
	// Verilator lint_off UNUSED
	wire	[OPT_SMP-1:0]	cpu_halted, cpu_op_stall, cpu_pf_stall,
				cpu_i_count, cpu_gie;
	// Verilator lint_on  UNUSED

	wire			scope_int;
	wire	[31:0]		cpu_trace;

	wire		dbg_cyc, dbg_stb, dbg_we, dbg_stall, dbg_ack, dbg_err;
	wire	[ADDRESS_WIDTH+1-$clog2(32/8)-1:0]	dbg_addr;
	wire	[31:0]	dbg_data, dbg_idata;
	wire	[3:0]	dbg_sel;

	wire	[OPT_SMP-1:0]		smpw_cyc, smpw_stb, smpw_we,
					smpw_stall, smpw_ack, smpw_err;
	wire	[OPT_SMP*WAW-1:0]	smpw_addr;
	wire	[OPT_SMP*BUS_WIDTH-1:0]	smpw_data, smpw_idata;
	wire [OPT_SMP*BUS_WIDTH/8-1:0]	smpw_sel;

	wire		pic_int, timer_a_int, timer_b_int, timer_c_int,
			jiffies_int;

	////////////////////////////////////////////////////////////////////////
	//
	// CPU bus declarations
	// {{{
	wire	[OPT_SMP-1:0]		cpu_cyc, cpu_stb, cpu_we,
					cpu_ack, cpu_stall, cpu_err;
	wire	[OPT_SMP*WAW-1:0]	cpu_addr;
	wire	[OPT_SMP*BUS_WIDTH-1:0]	cpu_data, cpu_idata;
	wire [OPT_SMP*BUS_WIDTH/8-1:0]	cpu_sel;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory bus declarations
	// {{{
	wire	mem_cyc, mem_stb, mem_we, mem_ack, mem_stall, mem_err;
	wire	[WAW-1:0]		mem_addr;
	wire	[BUS_WIDTH-1:0]		mem_data, mem_idata;
	wire	[BUS_WIDTH/8-1:0]	mem_sel;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Console bus declarations
	// {{{
	wire	conw_cyc, conw_stb, conw_we, conw_ack, conw_stall, conw_err;
	wire	[WAW-1:0]		conw_addr;
	wire	[BUS_WIDTH-1:0]		conw_data, conw_idata;
	wire	[BUS_WIDTH/8-1:0]	conw_sel;

	wire	con_cyc, con_stb, con_we, con_ack, con_stall, con_err;
	wire	[ADDRESS_WIDTH-3-$clog2(32/8)-1:0]	con_addr;
	wire	[31:0]	con_data, con_idata;
	wire	[3:0]	con_sel;
	reg	r_con_ack;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// ZipCPU System bus declarations
	// {{{
	wire				zsysw_cyc, zsysw_stb, zsysw_we,
					zsysw_ack, zsysw_stall, zsysw_err;
	wire	[WAW-1:0]		zsysw_addr;
	wire	[BUS_WIDTH-1:0]		zsysw_data, zsysw_idata;
	wire	[BUS_WIDTH/8-1:0]	zsysw_sel;

	wire				zsys_cyc, zsys_stb, zsys_we,
					zsys_ack, zsys_stall, zsys_err;
	wire	[WAW+WBLSB-$clog2(32/8)-5:0]	zsys_addr;
	wire	[31:0]			zsys_data, zsys_idata;
	wire	[3:0]			zsys_sel;
	reg				r_zsys_ack;
	reg	[31:0]			r_zsys_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) DMA bus declarations
	// {{{
	wire				dmac_cyc, dmac_stb, dmac_we;
	wire	[WAW-1:0]		dmac_addr;
	wire	[BUS_WIDTH-1:0]		dmac_data;
	wire	[BUS_WIDTH/8-1:0]	dmac_sel;

	// Verilator lint_off UNUSED
	wire				dmac_int;
	wire				dmac_ack, dmac_stall, dmac_err;
	wire	[BUS_WIDTH-1:0]		dmac_return;
	// Verilator lint_on  UNUSED
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Optional SCOPE
	// {{{
	wire	scopew_cyc, scopew_stb, scopew_we, scopew_ack, scopew_stall,
		scopew_err;
	wire	[ADDRESS_WIDTH-$clog2(BUS_WIDTH/8)-1:0]	scopew_addr;
	wire	[BUS_WIDTH-1:0]		scopew_data, scopew_idata;
	wire	[BUS_WIDTH/8-1:0]	scopew_sel;
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
	wire				i_sim_cyc, i_sim_stb, i_sim_we;
	wire	[ADDRESS_WIDTH-2:0]	i_sim_addr;
	wire	[31:0]			i_sim_data;
	wire	[3:0]			i_sim_sel;
	wire				o_sim_stall;
	wire				o_sim_ack;
	wire	[31:0]			o_sim_data;
	wire				o_sim_err;
	wire				i_sim_int;

	wire				o_prof_stb;
	// wire	[31:0]			o_prof_addr;
	wire	[ADDRESS_WIDTH-1:0]	o_prof_addr;
	wire	[31:0]			o_prof_ticks;

	reg	i_clk, i_reset, reset_pipe;

	initial	i_clk = 0;
	always
		#5 i_clk = !i_clk;

	initial	{ i_reset, reset_pipe } = -1;
	always @(posedge i_clk)
		{ i_reset, reset_pipe } <= { reset_pipe, 1'b0 };

	// Tie off (unused) Sim control input(s)
	// {{{
	assign	i_sim_cyc = 1'b0;
	assign	i_sim_stb = 1'b0;
	assign	i_sim_we  = 1'b0;
	assign	i_sim_addr = 0;
	assign	i_sim_data = 0;
	assign	i_sim_sel  = 0;
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
	wire			sim_cyc, sim_stb, sim_we,
				sim_stall, sim_ack, sim_err;
	wire	[ADDRESS_WIDTH+1-$clog2(32/8)-1:0]	sim_addr;
	wire	[31:0]		sim_data, sim_idata;
	wire	[32/8-1:0]	sim_sel;

	wire			simw_cyc, simw_stb, simw_we,
				simw_stall, simw_ack, simw_err;
	wire	[ADDRESS_WIDTH+1-$clog2(BUS_WIDTH/8)-1:0]	simw_addr;
	wire	[BUS_WIDTH-1:0]	simw_data, simw_idata;
	wire [BUS_WIDTH/8-1:0]	simw_sel;

	wbxbar #(
		// {{{
		.NM(1), .NS(2), .AW(ADDRESS_WIDTH+1-$clog2(32/8)), .DW(32),
		.SLAVE_ADDR({
			{ 1'b0, {(ADDRESS_WIDTH-$clog2(32/8)){1'b0}} },
			{ 1'b1, {(ADDRESS_WIDTH-$clog2(32/8)){1'b0}} }}), // CPU
		.SLAVE_MASK({
			{ 1'b0, {(ADDRESS_WIDTH-$clog2(32/8)){1'b0}} },
			{ 1'b1, {(ADDRESS_WIDTH-$clog2(32/8)){1'b0}} }})  // CPU
		// }}}
	) simxbar (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// One master: the SIM bus input
		// {{{
		.i_mcyc(i_sim_cyc), .i_mstb(i_sim_stb), .i_mwe(i_sim_we),
		.i_maddr(i_sim_addr), .i_mdata(i_sim_data), .i_msel(i_sim_sel),
		//
		.o_mstall(o_sim_stall), .o_mack(o_sim_ack),.o_mdata(o_sim_data),
			.o_merr(o_sim_err),
		// }}}
		// Two slaves: The wide bus the ZipCPU masters, and the ZipCPU's
		// debug port
		// {{{
		.o_scyc({  sim_cyc, dbg_cyc  }),
		.o_sstb({  sim_stb, dbg_stb  }),
		.o_swe({   sim_we,  dbg_we   }),
		.o_saddr({ sim_addr,dbg_addr }),
		.o_sdata({ sim_data,dbg_data }),
		.o_ssel({  sim_sel, dbg_sel  }),
		//
		.i_sstall({ sim_stall, dbg_stall }),
		.i_sack({   sim_ack,   dbg_ack   }),
		.i_sdata({  sim_idata, dbg_idata }),
		.i_serr({   sim_err,   dbg_err   })
		// }}}
		// }}}
	);

	assign	simw_cyc   = sim_cyc;
	assign	simw_we    = sim_we;
	assign	sim_ack    = simw_ack;
	assign	sim_err    = simw_err;

	generate if (BUS_WIDTH == 32)
	begin : NO_EXPAND_SIMBUS
		// {{{
		assign	simw_stb  = sim_stb;
		assign	simw_addr = sim_addr;
		assign	simw_data = sim_data;
		assign	simw_sel  = sim_sel;
		assign	sim_stall = simw_stall;
		assign	sim_idata = simw_idata;
		// }}}
	end else begin : GEN_EXPAND_SIMBUS
		// {{{
		wire			fifo_full, fifo_empty;
		wire	[LGFIFO:0]	fifo_fill;
		wire	[$clog2(BUS_WIDTH/8)-$clog2(32/8)-1:0]	fifo_addr;
		wire	[BUS_WIDTH-1:0]	wide_idata;

		assign	simw_stb   = sim_stb    && !fifo_full;
		assign	sim_stall  = simw_stall ||  fifo_full;

		assign	simw_addr = sim_addr[ADDRESS_WIDTH+1-$clog2(32/8)-1:$clog2(BUS_WIDTH/32)];
		assign	simw_sel  = { sim_sel, {(BUS_WIDTH/8-4){1'b0}} } >> (4*simw_addr[$clog2(BUS_WIDTH/8)-1:2]);
		assign	simw_data = { sim_data, {(BUS_WIDTH-32){1'b0}} } >> (32*simw_addr[$clog2(BUS_WIDTH/8)-1:2]);

		sfifo #(
			// {{{
			.LGFLEN(LGFIFO),
			.OPT_READ_ON_EMPTY(1'b1),
			.BW($clog2(BUS_WIDTH/32))
			// }}}
		) u_simaddr_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_wr(simw_stb && !sim_stall),
			.i_data(simw_addr[$clog2(BUS_WIDTH/8)-1:2]),
			.o_full(fifo_full), .o_fill(fifo_fill),
			.i_rd(simw_ack), .o_data(fifo_addr),
			.o_empty(fifo_empty)
			// }}}
		);

		assign	wide_idata = simw_idata << (32*fifo_addr);
		assign	sim_idata  = wide_idata[BUS_WIDTH-1:BUS_WIDTH-32];

		// Verilator lint_off UNUSED
		wire	unused_sim_expander;
		assign	unused_sim_expander = &{ 1'b0,
			fifo_fill, fifo_empty, wide_idata[BUS_WIDTH-32-1:0],
			sim_addr[$clog2(BUS_WIDTH/32):0] };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate
`else
	// If we aren't using Verilator, then there's no external bus driver.
	// Cap off the debug port therefore.
	//

	assign	dbg_cyc = 1'b0;
	assign	dbg_stb = 1'b0;
	assign	dbg_we  = 1'b0;
	assign	dbg_data= 32'h0;
	assign	dbg_sel = 4'h0;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The CPU itself
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam		RESET_DURATION = 10;
	localparam	[0:0]	OPT_SIM = 1'b1;
`ifdef	VERILATOR
	localparam	[0:0]	OPT_PROFILER = 1'b1;
`else
	localparam	[0:0]	OPT_PROFILER = 1'b0;
`endif

	generate if (OPT_ZIPBONES)
	begin : GEN_ZIPBONES

		zipbones #(
			// {{{
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.RESET_ADDRESS(RESET_ADDRESS),
			.OPT_PIPELINED(OPT_PIPELINED),
			.BUS_WIDTH(BUS_WIDTH),
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
			.i_clk(i_clk), .i_reset(i_reset),
			// Master bus
			// {{{
			.o_wb_cyc(cpu_cyc[0]), .o_wb_stb(cpu_stb[0]),
			.o_wb_we(cpu_we[0]),
			.o_wb_addr(cpu_addr[WAW-1:0]),
				.o_wb_data(cpu_data[BUS_WIDTH-1:0]),
				.o_wb_sel(cpu_sel[BUS_WIDTH/8-1:0]),
			.i_wb_stall(cpu_stall[0]), .i_wb_ack(cpu_ack[0]),
				.i_wb_data(cpu_idata[BUS_WIDTH-1:0]),
				.i_wb_err(cpu_err[0]),
			// }}}
			.i_ext_int(pic_int), .o_ext_int(cpu_int[0]),
			// Debug control port
			// {{{
			.i_dbg_cyc(dbg_cyc), .i_dbg_stb(dbg_stb),
				.i_dbg_we(dbg_we), .i_dbg_addr(dbg_addr[5:0]),
				.i_dbg_data(dbg_data), .i_dbg_sel(dbg_sel),
			.o_dbg_stall(dbg_stall), .o_dbg_ack(dbg_ack),
				.o_dbg_data(dbg_idata),
			// }}}
			.o_cpu_debug(cpu_trace),
			// (Optional) Profiler
			// {{{
			.o_prof_stb(o_prof_stb),
			.o_prof_addr(o_prof_addr),
			.o_prof_ticks(o_prof_ticks)
			// }}}
			// }}}
		);

		assign	cpu_halted[0]   = u_cpu.cpu_has_halted;
		assign	cpu_op_stall[0] = u_cpu.cpu_op_stall;
		assign	cpu_pf_stall[0] = u_cpu.cpu_pf_stall;
		assign	cpu_i_count[0]  = u_cpu.cpu_i_count;
		assign	cpu_gie[0]      = u_cpu.cpu_dbg_cc[1];

	end else begin : GEN_ZIPSYSTEM

		zipsystem #(
			// {{{
			.RESET_ADDRESS(RESET_ADDRESS),
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.BUS_WIDTH(BUS_WIDTH),
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
			.OPT_USERMODE(OPT_USERMODE),
			.OPT_DBGPORT(OPT_DBGPORT),
			.OPT_TRACE_PORT(OPT_TRACE_PORT),
			.OPT_PROFILER(OPT_PROFILER),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_SIM(OPT_SIM),
			.OPT_CLKGATE(OPT_CLKGATE),
			.RESET_DURATION(RESET_DURATION),
			// ZipSystem only parameters
			.OPT_DMA(OPT_DMA),
			.OPT_ACCOUNTING(1'b1),
			.EXTERNAL_INTERRUPTS(1)
			// }}}
		) u_cpu (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			// Master bus
			// {{{
			.o_wb_cyc(cpu_cyc[0]), .o_wb_stb(cpu_stb[0]),
			.o_wb_we(cpu_we[0]),
			.o_wb_addr(cpu_addr[WAW-1:0]), .o_wb_data(cpu_data[BUS_WIDTH-1:0]),
				.o_wb_sel(cpu_sel[BUS_WIDTH/8-1:0]),
			.i_wb_stall(cpu_stall[0]), .i_wb_ack(cpu_ack[0]),
				.i_wb_data(cpu_idata[BUS_WIDTH-1:0]),
				.i_wb_err(cpu_err[0]),
			// }}}
			.i_ext_int({ i_sim_int }),
			.o_ext_int(cpu_int[0]),
			// Debug control port
			// {{{
			.i_dbg_cyc(dbg_cyc), .i_dbg_stb(dbg_stb),
				.i_dbg_we(dbg_we), .i_dbg_addr(dbg_addr[6:0]),
				.i_dbg_data(dbg_data), .i_dbg_sel(dbg_sel),
			.o_dbg_stall(dbg_stall), .o_dbg_ack(dbg_ack),
				.o_dbg_data(dbg_idata),
			// }}}
			.o_cpu_debug(cpu_trace),
			// (Optional) Profiler
			// {{{
			.o_prof_stb(o_prof_stb),
			.o_prof_addr(o_prof_addr),
			.o_prof_ticks(o_prof_ticks)
			// }}}
			// }}}
		);

		assign	cpu_halted[0]   = u_cpu.cpu_has_halted;
		assign	cpu_op_stall[0] = u_cpu.cpu_op_stall;
		assign	cpu_pf_stall[0] = u_cpu.cpu_pf_stall;
		assign	cpu_i_count[0]  = u_cpu.cpu_i_count;
		assign	cpu_gie[0]      = u_cpu.cpu_gie;


		// Verilator lint_off UNUSED
		wire	unused_zipsys;
		assign	unused_zipsys = &{ 1'b0, pic_int };
		// Verilator lint_on  UNUSED
	end endgenerate

	assign	dbg_err = 1'b0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Extra CPU's, if running in multiprocessor mode (OPT_SMP > 1)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// No slave connection
	// {{{
	reg	r_smp_err;

	initial	r_smp_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_smp_err <= 1'b0;
	else
		r_smp_err <= smpw_stb[0];

	assign	smpw_stall[0] = 1'b0;
	assign	smpw_ack[0]   = 1'b0;
	assign	smpw_idata[BUS_WIDTH-1:0] = {(BUS_WIDTH){1'b0}};
	assign	smpw_err[0]   = r_smp_err;

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_smpw;
	assign	unused_smpw = &{ 1'b0, smpw_cyc[0], smpw_we[0],
				smpw_addr[WAW-1:0],
				smpw_data[BUS_WIDTH-1:0],
				smpw_sel[BUS_WIDTH/8-1:0]
				};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}

	generate for (gk=1; gk<OPT_SMP; gk=gk+1)
	begin : GEN_SMPCPU
		// Local declarations
		// {{{
		wire	[31:0]		smp_trace;
		wire			smp_prof_stb;
		wire	[ADDRESS_WIDTH-1:0]	smp_prof_addr;
		wire	[31:0]		smp_prof_ticks;

		wire		smp_cyc, smp_stb, smp_we;
		wire	[6:0]	smp_addr;
		wire	[31:0]	smp_data;
		wire	[3:0]	smp_sel;
		wire		smp_stall, smp_ack, smp_err;
		wire	[31:0]	smp_idata;
		// }}}

		wbdown #(
			// {{{
			.ADDRESS_WIDTH(9),
			.WIDE_DW(BUS_WIDTH), .SMALL_DW(32)
			// }}}
		) u_smpdown (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			// The "Wide" connection
			// {{{
			.i_wcyc(smpw_cyc[gk]), .i_wstb(smpw_stb[gk]), .i_wwe(smpw_we[gk]),
			.i_waddr(smpw_addr[gk * WAW +: (9-WBLSB)]),
				.i_wdata(smpw_data[gk*BUS_WIDTH +: BUS_WIDTH]),
				.i_wsel(smpw_sel[gk*BUS_WIDTH/8 +: BUS_WIDTH/8]),
			//
			.o_wstall(smpw_stall[gk]), .o_wack(smpw_ack[gk]),
				.o_wdata(smpw_idata[gk*BUS_WIDTH +: BUS_WIDTH]),
				.o_werr(smpw_err[gk]),
			// }}}
			// The downsized connection
			// {{{
			.o_cyc(smp_cyc), .o_stb(smp_stb), .o_we(smp_we),
			.o_addr(smp_addr), .o_data(smp_data), .o_sel(smp_sel),
			//
			.i_stall(smp_stall), .i_ack(smp_ack),
				.i_data(smp_idata),
				.i_err(smp_err)
			// }}}
			// }}}
		);

		assign	smp_err = 1'b0;

		if (OPT_ZIPBONES)
		begin : GEN_ZIPBONES

			zipbones #(
				// {{{
				.ADDRESS_WIDTH(ADDRESS_WIDTH),
				.RESET_ADDRESS(RESET_ADDRESS),
				.OPT_PIPELINED(OPT_PIPELINED),
				.BUS_WIDTH(BUS_WIDTH),
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
				.OPT_DBGPORT(OPT_DBGPORT),
				.OPT_TRACE_PORT(OPT_TRACE_PORT),
				.OPT_PROFILER(OPT_PROFILER),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.OPT_SIM(OPT_SIM),
				.OPT_CLKGATE(OPT_CLKGATE),
				.RESET_DURATION(RESET_DURATION)
				// }}}
			) u_smp (
				// {{{
				.i_clk(i_clk), .i_reset(i_reset),
				// Master bus
				// {{{
				.o_wb_cyc(cpu_cyc[gk]),
				.o_wb_stb(cpu_stb[gk]),
				.o_wb_we(cpu_we[gk]),
				.o_wb_addr(cpu_addr[gk*WAW +: WAW]),
				.o_wb_data(cpu_data[gk*BUS_WIDTH +: BUS_WIDTH]),
				.o_wb_sel(cpu_sel[gk*BUS_WIDTH/8 +: BUS_WIDTH/8]),
				.i_wb_stall(cpu_stall[gk]),
					.i_wb_ack(cpu_ack[gk]),
					.i_wb_data(cpu_idata[gk*BUS_WIDTH +: BUS_WIDTH]),
					.i_wb_err(cpu_err[gk]),
				// }}}
				.i_ext_int(pic_int), .o_ext_int(cpu_int[gk]),
				// Debug control port
				// {{{
				.i_dbg_cyc(smp_cyc), .i_dbg_stb(smp_stb),
					.i_dbg_we(smp_we), .i_dbg_addr(smp_addr[5:0]),
					.i_dbg_data(smp_data), .i_dbg_sel(smp_sel),
				.o_dbg_stall(smp_stall), .o_dbg_ack(smp_ack),
					.o_dbg_data(smp_idata),
				// }}}
				.o_cpu_debug(smp_trace),
				// (Optional) Profiler
				// {{{
				.o_prof_stb(smp_prof_stb),
				.o_prof_addr(smp_prof_addr),
				.o_prof_ticks(smp_prof_ticks)
				// }}}
				// }}}
			);

			assign	cpu_halted[gk]   = u_smp.cpu_has_halted;
			assign	cpu_op_stall[gk] = u_smp.cpu_op_stall;
			assign	cpu_pf_stall[gk] = u_smp.cpu_pf_stall;
			assign	cpu_i_count[gk]  = u_smp.cpu_i_count;
			assign	cpu_gie[gk]      = u_smp.cpu_dbg_cc[1];

		end else begin : GEN_ZIPSYSTEM

			zipsystem #(
				// {{{
				.RESET_ADDRESS(RESET_ADDRESS),
				.ADDRESS_WIDTH(ADDRESS_WIDTH),
				.BUS_WIDTH(BUS_WIDTH),
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
				.OPT_DBGPORT(1'b1),
				.OPT_TRACE_PORT(1'b0),
				.OPT_PROFILER(1'b0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.OPT_SIM(OPT_SIM),
				.OPT_CLKGATE(OPT_CLKGATE),
				.RESET_DURATION(RESET_DURATION),
				// ZipSystem only parameters
				.OPT_DMA(OPT_DMA),
				.OPT_ACCOUNTING(1'b1),
				.EXTERNAL_INTERRUPTS(1)
				// }}}
			) u_smp (
				// {{{
				.i_clk(i_clk), .i_reset(i_reset),
				// Master bus
				// {{{
				.o_wb_cyc(cpu_cyc[gk]), .o_wb_stb(cpu_stb[gk]),
					.o_wb_we(cpu_we[gk]),
				.o_wb_addr(cpu_addr[gk*WAW +: WAW]),
				.o_wb_data(cpu_data[gk*BUS_WIDTH +: BUS_WIDTH]),
					.o_wb_sel(cpu_sel[gk*BUS_WIDTH/8 +: BUS_WIDTH/8]),
				.i_wb_stall(cpu_stall[gk]),
					.i_wb_ack(cpu_ack[gk]),
					.i_wb_data(cpu_idata[gk*BUS_WIDTH +: BUS_WIDTH]),
					.i_wb_err(cpu_err[gk]),
				// }}}
				.i_ext_int({ i_sim_int }),
				.o_ext_int(cpu_int[gk]),
				// Debug control port
				// {{{
				.i_dbg_cyc(smp_cyc), .i_dbg_stb(smp_stb),
					.i_dbg_we(smp_we), .i_dbg_addr(smp_addr[6:0]),
					.i_dbg_data(smp_data), .i_dbg_sel(smp_sel),
				.o_dbg_stall(smp_stall), .o_dbg_ack(smp_ack),
					.o_dbg_data(smp_idata),
				// }}}
				.o_cpu_debug(smp_trace),
				// (Optional) Profiler
				// {{{
				.o_prof_stb(smp_prof_stb),
				.o_prof_addr(smp_prof_addr),
				.o_prof_ticks(smp_prof_ticks)
				// }}}
				// }}}
			);

			assign	cpu_halted[gk]   = u_smp.cpu_has_halted;
			assign	cpu_op_stall[gk] = u_smp.cpu_op_stall;
			assign	cpu_pf_stall[gk] = u_smp.cpu_pf_stall;
			assign	cpu_i_count[gk]  = u_smp.cpu_i_count;
			assign	cpu_gie[gk]      = u_smp.cpu_gie;

			// Verilator coverage_off
			// Verilator lint_off UNUSED
			wire	unused_zipsys;
			assign	unused_zipsys = &{ 1'b0, pic_int };
			// Verilator lint_on  UNUSED
			// Verilator coverage_on

		end

		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_smp;
		assign	unused_smp = &{ 1'b0, smp_prof_stb, smp_prof_addr,
				smp_prof_ticks, smp_trace, cpu_int[gk],
				smp_addr[6],
				smpw_addr[gk*WAW + (9-WBLSB) +: (WAW-(9-WBLSB))]
				};
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The wide bus interconnect
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbxbar #(
		// {{{
`ifdef	VERILATOR
		.NM(1+1+OPT_SMP),
`else
		.NM(1+OPT_SMP),
`endif
		.NS(4+OPT_SMP),
		.AW(ADDRESS_WIDTH-$clog2(BUS_WIDTH/8)), .DW(BUS_WIDTH),
		.SLAVE_ADDR({ ZSYS_ADDR, SMP_ADDR,
			CONSOLE_ADDR,
			SCOPE_ADDR,
			MEMORY_ADDR }),
		.SLAVE_MASK({
			{ {(ADDRESS_WIDTH-24){1'b1}},{(24-WBLSB){1'b0}} }, // ZipSys
			SMP_MASK,	// SMP
			{ 4'b1111, {(WAW-4){1'b0}} },	// Console
			{ 4'b1111, {(WAW-4){1'b0}} },	// Scope
			{ 2'b11,   {(WAW-2){1'b0}} } })	// Memory
		// }}}
	) main_crossbar (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// Slave ports from the various bus masters
		// {{{
`ifdef	VERILATOR
		// Two bus masters: the external SIM input, and the CPU
		.i_mcyc({   simw_cyc,   dmac_cyc, cpu_cyc }),
		.i_mstb({   simw_stb,   dmac_stb, cpu_stb }),
		.i_mwe({    simw_we,    dmac_we,  cpu_we }),
		.i_maddr({  simw_addr[ADDRESS_WIDTH-WBLSB-1:0], dmac_addr, cpu_addr }),
		.i_mdata({  simw_data,  dmac_data, cpu_data }),
		.i_msel({   simw_sel,   dmac_sel,  cpu_sel }),
		.o_mstall({ simw_stall, dmac_stall,cpu_stall }),
		.o_mack({   simw_ack,   dmac_ack,  cpu_ack }),
		.o_mdata({  simw_idata, dmac_return,cpu_idata }),
		.o_merr({   simw_err,   dmac_err,   cpu_err }),
`else
		// With no external CPU input, there is no simulation port
		.i_mcyc({ dmac_cyc, cpu_cyc }),
			.i_mstb({  dmac_stb,  cpu_stb }),
			.i_mwe({   dmac_we,   cpu_we }),
			.i_maddr({ dmac_addr, cpu_addr }),
			.i_mdata({ dmac_data, cpu_data }),
			.i_msel({  dmac_sel,  cpu_sel }),
		.o_mstall({ dmac_stall, cpu_stall }),
			.o_mack({  dmac_ack,    cpu_ack }),
			.o_mdata({ dmac_return, cpu_idata }),
			.o_merr({  dmac_err,    cpu_err }),
`endif
		// }}}
		// Master port ... to control the slaves w/in this design
		// {{{
		.o_scyc({   zsysw_cyc,  smpw_cyc,  conw_cyc,  scopew_cyc,  mem_cyc  }),
		.o_sstb({   zsysw_stb,  smpw_stb,  conw_stb,  scopew_stb,  mem_stb  }),
		.o_swe({    zsysw_we,   smpw_we,   conw_we,   scopew_we,   mem_we   }),
		.o_saddr({  zsysw_addr, smpw_addr, conw_addr, scopew_addr, mem_addr }),
		.o_sdata({  zsysw_data, smpw_data, conw_data, scopew_data, mem_data }),
		.o_ssel({   zsysw_sel,  smpw_sel,  conw_sel,  scopew_sel,  mem_sel  }),
		//
		.i_sstall({ zsysw_stall,smpw_stall,conw_stall, scopew_stall, mem_stall }),
		.i_sack({   zsysw_ack,  smpw_ack,  conw_ack,   scopew_ack,   mem_ack   }),
		.i_sdata({  zsysw_idata,smpw_idata,conw_idata, scopew_idata, mem_idata }),
		.i_serr({   zsysw_err,  smpw_err,  conw_err,   scopew_err,   mem_err   })
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

	memdev #(
		// {{{
		.LGMEMSZ(LGMEMSZ),
		.DW(BUS_WIDTH),
		.HEXFILE(MEM_FILE),
		.OPT_ROM(1'b0)
		// }}}
	) u_mem (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(mem_cyc), .i_wb_stb(mem_stb), .i_wb_we(mem_we),
		.i_wb_addr(mem_addr[LGMEMSZ-WBLSB-1:0]), .i_wb_data(mem_data),
			.i_wb_sel(mem_sel),
		.o_wb_stall(mem_stall), .o_wb_ack(mem_ack),
		.o_wb_data(mem_idata)
		// }}}
	);

	assign	mem_err = 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Console
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg		con_write_en;
	reg	[7:0]	con_write_byte;

	integer	sim_console;

	wbdown #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH-3),
		.WIDE_DW(BUS_WIDTH), .SMALL_DW(32)
		// }}}
	) u_condown (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// The "Wide" connection
		// {{{
		.i_wcyc(conw_cyc), .i_wstb(conw_stb), .i_wwe(conw_we),
		.i_waddr(conw_addr[WAW-4:0]),
			.i_wdata(conw_data), .i_wsel(conw_sel),
		//
		.o_wstall(conw_stall), .o_wack(conw_ack), .o_wdata(conw_idata),
			.o_werr(conw_err),
		// }}}
		// The downsized connection
		// {{{
		.o_cyc(con_cyc), .o_stb(con_stb), .o_we(con_we),
		.o_addr(con_addr), .o_data(con_data), .o_sel(con_sel),
		//
		.i_stall(con_stall), .i_ack(con_ack), .i_data(con_idata),
			.i_err(con_err)
		// }}}
		// }}}
	);

	assign	con_stall = 1'b0;

	initial	r_con_ack = 1'b0;
	always @(posedge i_clk)
		r_con_ack <= !i_reset && con_stb;
	assign	con_ack = r_con_ack;

	initial	begin
		sim_console = $fopen(CONSOLE_FILE);
	end

	// Make sure we can read the outgoing console data from the trace
	initial	con_write_en = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		con_write_en <= 1'b0;
	else if (con_stb && con_we && con_addr[1:0] == 2'b11 && con_sel[0])
		con_write_en <= 1'b1;
	else
		con_write_en <= 1'b0;

	initial	con_write_byte = 8'h0;
	always @(posedge i_clk)
	if (con_stb && con_we && con_addr[1:0] == 2'b11 && con_sel[0])
		con_write_byte <= con_data[7:0];

	always @(posedge i_clk)
	if (!i_reset && con_write_en)
	begin
		$fwrite(sim_console, "%1s", con_write_byte);
		$write("%1s", con_write_byte);
	end

	assign	con_idata = 32'h0;
	assign	con_err   = 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Artificial ZipCPU System components, for when running with ZipBones
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire		pic_stall, pic_ack;
	wire	[31:0]	pic_data;

	wire		timer_a_stall, timer_b_stall, timer_c_stall,
			jiffies_stall;	// Jiffies

	wire		timer_a_ack, timer_b_ack, timer_c_ack,
			jiffies_ack;	// Jiffies

	wire	[31:0]	timer_a_data, timer_b_data, timer_c_data,
			jiffies_data;	// Jiffies
	wire	[31:0]	dma_slv_data;

	wire	[31:0]	mtc_data, moc_data, mpc_data, mic_data;
	wire	[31:0]	utc_data, uoc_data, upc_data, uic_data;

	// Verilator lint_off UNUSED
	wire		ign_mtc_stall, ign_moc_stall,
			ign_mpc_stall, ign_mic_stall;
	wire		ign_utc_stall, ign_uoc_stall,
			ign_upc_stall, ign_uic_stall;
	wire		ign_mtc_ack, ign_moc_ack,
			ign_mpc_ack, ign_mic_ack;
	wire		ign_utc_ack, ign_uoc_ack,
			ign_upc_ack, ign_uic_ack;

	wire		mtc_int, moc_int, mpc_int, mic_int;
	wire		utc_int, uoc_int, upc_int, uic_int;
	// Verilator lint_on  UNUSED

	reg		zsys_stb_d;
	reg	[WAW+WBLSB-$clog2(32/8)-5:0]	zsys_addr_d;

	wbdown #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH-4),
		.WIDE_DW(BUS_WIDTH), .SMALL_DW(32)
		// }}}
	) u_zsysdown (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// The "Wide" connection
		// {{{
		.i_wcyc(zsysw_cyc), .i_wstb(zsysw_stb), .i_wwe(zsysw_we),
		.i_waddr(zsysw_addr[WAW-5:0]),
			.i_wdata(zsysw_data), .i_wsel(zsysw_sel),
		//
		.o_wstall(zsysw_stall), .o_wack(zsysw_ack),
			.o_wdata(zsysw_idata), .o_werr(zsysw_err),
		// }}}
		// The downsized connection
		// {{{
		.o_cyc(zsys_cyc), .o_stb(zsys_stb), .o_we(zsys_we),
		.o_addr(zsys_addr), .o_data(zsys_data), .o_sel(zsys_sel),
		//
		.i_stall(zsys_stall), .i_ack(zsys_ack), .i_data(zsys_idata),
			.i_err(zsys_err)
		// }}}
		// }}}
	);

	initial	zsys_stb_d = 1'b0;
	always @(posedge i_clk)
		zsys_stb_d <= !i_reset && zsys_stb;

	always @(posedge i_clk)
		zsys_addr_d <= zsys_addr;

	assign	zsys_stall = 1'b0;

	initial	r_zsys_ack = 1'b0;
	always @(posedge i_clk)
		r_zsys_ack <= !i_reset && zsys_stb_d;
	assign	zsys_ack = r_zsys_ack;

	assign	zsys_idata = 32'h0;
	assign	zsys_err   = 1'b0;

	// SMP[0] Master counters
	// {{{
	zipcounter
	mtask_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(!cpu_halted[0]),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h8),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_mtc_stall),
		.o_wb_ack(ign_mtc_ack),
		.o_wb_data(mtc_data),
		.o_int(mtc_int)
		// }}}
	);

	/*
	zipcounter
	mmstall_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(!halt),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h8),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_mtc_stall),
		.o_wb_ack(ign_mtc_ack),
		.o_wb_data(mtc_data),
		.o_int(mtc_int)
		// }}}
	);
	*/
	assign { ign_moc_ack, ign_moc_stall, moc_int, moc_data } = 35'h0;

	/*
	zipcounter
	mpstall_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(!halt),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h8),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_mtc_stall),
		.o_wb_ack(ign_mtc_ack),
		.o_wb_data(mtc_data),
		.o_int(mtc_int)
		// }}}
	);
	*/
	assign { ign_mpc_ack, ign_mpc_stall, mpc_int, mpc_data } = 35'h0;

	zipcounter
	mins_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(cpu_i_count[0]),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'hb),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_mic_stall),
		.o_wb_ack(ign_mic_ack),
		.o_wb_data(mic_data),
		.o_int(mic_int)
		// }}}
	);
	// }}}

	// SMP[0] User counters
	// {{{
	zipcounter
	utask_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(!cpu_halted[0]),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'hc),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_utc_stall),
		.o_wb_ack(ign_utc_ack),
		.o_wb_data(utc_data),
		.o_int(utc_int)
		// }}}
	);

	/*
	zipcounter
	umstall_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(cpu_op_stall[0]),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'hd),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_uoc_stall),
		.o_wb_ack(ign_uoc_ack),
		.o_wb_data(uoc_data),
		.o_int(uoc_int)
		// }}}
	);
	*/
	assign { ign_uoc_ack, ign_uoc_stall, uoc_int, uoc_data } = 35'h0;

	/*
	zipcounter
	mpstall_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(cpu_pf_stall[0]),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'he),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_mpc_stall),
		.o_wb_ack(ign_mpc_ack),
		.o_wb_data(mpc_data),
		.o_int(mpc_int)
		// }}}
	);
	*/
	assign { ign_upc_ack, ign_upc_stall, upc_int, upc_data } = 35'h0;

	zipcounter
	uins_ctr (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_event(cpu_gie[0] && cpu_i_count[0]),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'hf),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data),
		.o_wb_stall(ign_uic_stall),
		.o_wb_ack(ign_uic_ack),
		.o_wb_data(uic_data),
		.o_int(uic_int)
		// }}}
	);
	// }}}


	always @(posedge i_clk)
	if (zsys_stb_d)
	begin
		r_zsys_data <= 32'h0;
		case(zsys_addr_d)
		 0: r_zsys_data <= pic_data;		// PIC
		 1: begin end	// Watchdog
		 2: begin end	// APIC
		 3: begin end	// Bus Watchdog
		 4: r_zsys_data <= timer_a_data;	// Timer A
		 5: r_zsys_data <= timer_b_data;	// Timer B
		 6: r_zsys_data <= timer_c_data;	// Timer C
		 7: r_zsys_data <= jiffies_data;	// Jiffies
		 8: r_zsys_data <= mtc_data;
		 9: r_zsys_data <= moc_data;
		10: r_zsys_data <= mpc_data;
		11: r_zsys_data <= mic_data;
		12: r_zsys_data <= utc_data;
		13: r_zsys_data <= uoc_data;
		14: r_zsys_data <= upc_data;
		15: r_zsys_data <= uic_data;
		16: r_zsys_data <= dma_slv_data;
		17: r_zsys_data <= dma_slv_data;
		18: r_zsys_data <= dma_slv_data;
		19: r_zsys_data <= dma_slv_data;
		endcase
	end else
		r_zsys_data <= 32'h0;

	assign	zsys_idata = r_zsys_data;

	icontrol #(
		.IUSED(16)
	) u_pic (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h0),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data), .i_wb_sel(zsys_sel),
		.o_wb_stall(pic_stall),
		.o_wb_ack(pic_ack),
		.o_wb_data(pic_data),
		.i_brd_ints({ 9'h0, i_sim_int,
			1'b0, timer_a_int,
			timer_b_int, timer_c_int, jiffies_int, dmac_int }),
		.o_interrupt(pic_int)
		// }}}
	);

	ziptimer
	u_timer_a (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_ce(1'b1),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h4),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data), .i_wb_sel(zsys_sel),
		.o_wb_stall(timer_a_stall),
		.o_wb_ack(timer_a_ack),
		.o_wb_data(timer_a_data),
		.o_int(timer_a_int)
		// }}}
	);

	ziptimer
	u_timer_b (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_ce(1'b1),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h5),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data), .i_wb_sel(zsys_sel),
		.o_wb_stall(timer_b_stall),
		.o_wb_ack(timer_b_ack),
		.o_wb_data(timer_b_data),
		.o_int(timer_b_int)
		// }}}
	);

	ziptimer
	u_timer_c (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_ce(1'b1),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h6),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data), .i_wb_sel(zsys_sel),
		.o_wb_stall(timer_c_stall),
		.o_wb_ack(timer_c_ack),
		.o_wb_data(timer_c_data),
		.o_int(timer_c_int)
		// }}}
	);

	zipjiffies
	u_jiffies (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_ce(1'b1),
		.i_wb_cyc(zsys_cyc),
		.i_wb_stb(zsys_stb && zsys_addr[4:0] == 5'h7),
		.i_wb_we(zsys_we),
		.i_wb_data(zsys_data), .i_wb_sel(zsys_sel),
		.o_wb_stall(jiffies_stall),
		.o_wb_ack(jiffies_ack),
		.o_wb_data(jiffies_data),
		.o_int(jiffies_int)
		// }}}
	);

	generate if (OPT_ZIPBONES && OPT_DMA)
	begin : GEN_BONES_DMA
		// {{{
		localparam	DMA_LGMEM = 10;

		wire		ign_dmac_stall, ign_dmac_ack;
		wire	[31:0]	dmac_int_vec;

		assign	dmac_int_vec = { 16'h0, 9'h0, i_sim_int,
			1'b0, timer_a_int, timer_b_int,
			timer_c_int, jiffies_int, 1'b0 };

		zipdma #(
			// {{{
			.ADDRESS_WIDTH(ADDRESS_WIDTH), .LGMEMLEN(DMA_LGMEM),
			.BUS_WIDTH(BUS_WIDTH), .OPT_LITTLE_ENDIAN(1'b1)
			// }}}
		) u_dma (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			// Slave port
			// {{{
			.i_swb_cyc(zsys_cyc),
				.i_swb_stb(zsys_stb && zsys_addr[4:2]== 3'b100),
				.i_swb_we(zsys_we),
				.i_swb_addr(zsys_addr[1:0]),
				.i_swb_data(zsys_data),
				.i_swb_sel(zsys_sel),
				.o_swb_stall(ign_dmac_stall),
				.o_swb_ack(ign_dmac_ack),
				.o_swb_data(dma_slv_data),
			// }}}
			.o_mwb_cyc(dmac_cyc), .o_mwb_stb(dmac_stb),
				.o_mwb_we(dmac_we), .o_mwb_addr(dmac_addr),
				.o_mwb_data(dmac_data), .o_mwb_sel(dmac_sel),
			.i_mwb_stall(dmac_stall), .i_mwb_ack(dmac_ack),
				.i_mwb_data(dmac_return), .i_mwb_err(dmac_err),
			.i_dev_ints(dmac_int_vec),
			.o_interrupt(dmac_int)
			// }}}
		);

		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_dmac;
		assign	unused_dmac = &{ 1'b0, ign_dmac_stall, ign_dmac_ack };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	end else begin : NO_EXTERNAL_DMA

		assign	dmac_int = 1'b0;
		assign	dma_slv_data = 0;

		assign	{ dmac_cyc, dmac_stb, dmac_we } = 3'h0;
		assign	dmac_addr = 0;
		assign	dmac_data = 0;
		assign	dmac_sel  = 0;

	end endgenerate

	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused_zsys;
	assign	unused_zsys = &{ 1'b0, pic_stall, pic_ack,
			timer_a_stall, timer_a_ack,
			timer_b_stall, timer_b_ack,
			timer_c_stall, timer_c_ack,
			jiffies_stall, jiffies_ack
		};
	// Verilator lint_on  UNUSED
	// Verilator coverage_on

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) WB Scope
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_TRACE_PORT)
	begin : GEN_WBSCOPE
		// {{{
		wire		scope_cyc, scope_stb, scope_we;
		// Verilator lint_off UNUSED
		wire	[ADDRESS_WIDTH-3-$clog2(32/8)-1:0]	scope_addr;
		// Verilator lint_on  UNUSED
		wire	[31:0]	scope_data, scope_idata;
		wire	[3:0]	scope_sel;
		wire		scope_stall, scope_ack, scope_err;

		wbdown #(
			// {{{
			.ADDRESS_WIDTH(ADDRESS_WIDTH-3),
			.WIDE_DW(BUS_WIDTH), .SMALL_DW(32)
			// }}}
		) u_scopedown (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			// The "Wide" connection
			// {{{
			.i_wcyc(scopew_cyc), .i_wstb(scopew_stb), .i_wwe(scopew_we),
			.i_waddr(scopew_addr[WAW-4:0]),
				.i_wdata(scopew_data), .i_wsel(scopew_sel),
			//
			.o_wstall(scopew_stall), .o_wack(scopew_ack),
				.o_wdata(scopew_idata), .o_werr(scopew_err),
			// }}}
			// The downsized connection
			// {{{
			.o_cyc(scope_cyc), .o_stb(scope_stb), .o_we(scope_we),
			.o_addr(scope_addr), .o_data(scope_data),
				.o_sel(scope_sel),
			//
			.i_stall(scope_stall), .i_ack(scope_ack),
				.i_data(scope_idata), .i_err(scope_err)
			// }}}
			// }}}
		);

		wbscope #(
			.LGMEM(12)
		) u_scope (
			// {{{
			.i_data_clk(i_clk), .i_trigger(1'b0), .i_ce(1'b1),
			.i_data(cpu_trace),
			//
			.i_wb_clk(i_clk),
			.i_wb_cyc(scope_cyc), .i_wb_stb(scope_stb),
			.i_wb_we(scope_we),   .i_wb_addr(scope_addr[0]),
			.i_wb_data(scope_data), .i_wb_sel(scope_sel),
			//
			.o_wb_stall(scope_stall),
			.o_wb_ack(scope_ack),
			.o_wb_data(scope_idata),
			//
			.o_interrupt(scope_int)
			// }}}
		);

		assign	scope_err = 1'b0;
		// }}}
	end else begin : NO_SCOPE
		// {{{
		reg	r_scope_ack;

		initial	r_scope_ack = 1'b0;
		always @(posedge i_clk)
			r_scope_ack <= scopew_stb && !i_reset;

		assign	scopew_stall = 1'b0;
		assign	scopew_ack   = r_scope_ack;
		assign	scopew_idata = {(BUS_WIDTH){1'b0}};
		assign	scopew_err   = 1'b0;

		assign	scope_int = 1'b0;

		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_scope;
		assign	unused_scope = &{ 1'b0, scopew_cyc, scopew_we,
					scopew_data, scopew_sel, cpu_trace };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on

		// }}}
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
		$dumpvars(0, wb_tb);
	end
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Test bench watchdog
	// {{{

	localparam	TB_WATCHDOG_TIMEOUT = 1_000_00;	// 1ms
	reg	[$clog2(TB_WATCHDOG_TIMEOUT+2)-1:0]	watchdog_counter;

	initial	watchdog_counter = 0;
	always @(posedge i_clk)
	// if (i_reset)
	//	watchdog_counter <= 0;
	// else
	if (|(cpu_stb & ~cpu_stall))
		watchdog_counter <= 0;
	else
		watchdog_counter <= watchdog_counter + 1;

	always @(posedge i_clk)
	if (watchdog_counter > TB_WATCHDOG_TIMEOUT)
	begin
		$display("\nERROR: Watchdog timeout!");
		$finish;
	end

	always @(posedge i_clk)
	if (!i_reset && cpu_int[0])
		$display("\nCPU Halted without error: PASS\n");
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
		DUMP_TO_VCD, VCD_FILE,
		conw_addr, scopew_addr, zsysw_addr, zsysw_addr,
`ifdef	VERILATOR
		simw_addr,
`endif
		con_addr,  zsys_addr, mem_addr, dbg_addr,
		con_cyc, con_data[31:8], con_sel[3:1],
		timer_a_int, timer_b_int, timer_c_int, jiffies_int,
		timer_a_ack, timer_b_ack, timer_c_ack, jiffies_ack,
		timer_a_stall, timer_b_stall, timer_c_stall, jiffies_stall,
			scope_int };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
endmodule
