////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipbones.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	In the spirit of keeping the Zip CPU small, this implements a
//		Zip System with no peripherals: Any peripherals you wish will
//		need to be implemented off-module.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
// }}}
//		http://www.gnu.org/licenses/gpl.html
// {{{
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
`include "cpudefs.v"
//
`define	RESET_BIT	6
`define	STEP_BIT	8
`define	HALT_BIT	10
`define	CLEAR_CACHE_BIT	11
//
`ifdef	OPT_TRADITIONAL_PFCACHE
`define	LGICACHE_DEFAULT	8
`else
`define	LGICACHE_DEFAULT	0
`endif
//
`ifdef	OPT_DCACHE
`define	LGDCACHE_DEFAULT	10
`else
`define	LGDCACHE_DEFAULT	0
`endif
// }}}
module	zipbones #(
		// {{{
		parameter	RESET_ADDRESS=32'h1000_0000, ADDRESS_WIDTH=30,
				LGICACHE=`LGICACHE_DEFAULT,
				LGDCACHE=`LGDCACHE_DEFAULT,	// Set to zero for no data cache
		parameter [0:0]	START_HALTED=0,
		parameter	EXTERNAL_INTERRUPTS=1,
`ifdef	OPT_MULTIPLY
				IMPLEMENT_MPY = `OPT_MULTIPLY,
`else
				IMPLEMENT_MPY = 0,
`endif
		parameter [0:0]
`ifdef	OPT_DIVIDE
				IMPLEMENT_DIVIDE=1,
`else
				IMPLEMENT_DIVIDE=0,
`endif
`ifdef	OPT_IMPLEMENT_FPU
				IMPLEMENT_FPU=1,
`else
				IMPLEMENT_FPU=0,
`endif
				IMPLEMENT_LOCK=1,
		localparam	// Derived parameters
				PHYSICAL_ADDRESS_WIDTH=ADDRESS_WIDTH,
				PAW=ADDRESS_WIDTH,
`ifdef	OPT_MMU
				VIRTUAL_ADDRESS_WIDTH=30,
`else
				VIRTUAL_ADDRESS_WIDTH=PAW,
`endif
				LGTLBSZ = 6,
				VAW=VIRTUAL_ADDRESS_WIDTH,
		localparam	AW=ADDRESS_WIDTH
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Wishbone master interface from the CPU
		// {{{
		output	wire		o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire	[(PAW-1):0]	o_wb_addr,
		output	wire	[31:0]	o_wb_data,
		output	wire	[3:0]	o_wb_sel,
		input	wire		i_wb_stall, i_wb_ack,
		input	wire	[31:0]	i_wb_data,
		input	wire		i_wb_err,
		// }}}
		// Incoming interrupts
		input	wire		i_ext_int,
		// Outgoing interrupt
		output	wire		o_ext_int,
		// Wishbone slave interface for debugging purposes
		// {{{
		input	wire		i_dbg_cyc, i_dbg_stb, i_dbg_we,
		input	wire	[5:0]	i_dbg_addr,
		input	wire	[31:0]	i_dbg_data,
		input	wire	[3:0]	i_dbg_sel,
		output	wire		o_dbg_stall,
		output	wire		o_dbg_ack,
		output	wire	[31:0]	o_dbg_data
		// }}}
`ifdef	DEBUG_SCOPE
		, output wire	[31:0]	o_cpu_debug
`endif
		// }}}
	);

	// Declarations
	// {{{
	wire		dbg_cyc, dbg_stb, dbg_we, dbg_stall;
	wire	[5:0]	dbg_addr;
	wire	[31:0]	dbg_idata;
	reg	[31:0]	dbg_odata;
	reg		dbg_ack;
	wire		cpu_break, dbg_cmd_write;
	reg		cmd_reset, cmd_halt, cmd_step, cmd_clear_cache,
			cmd_write;
	reg	[4:0]	cmd_waddr;
	reg	[31:0]	cmd_wdata;
	wire	[2:0]	cpu_dbg_cc;
	wire		cpu_reset, cpu_halt, cpu_dbg_stall;
	wire		cpu_lcl_cyc, cpu_lcl_stb, 
			cpu_dbg_we,
			cpu_op_stall, cpu_pf_stall, cpu_i_count;
	wire	[31:0]	cpu_dbg_data;
	wire	[31:0]	cmd_data;
	reg		dbg_pre_addr, dbg_pre_ack;
	reg	[31:0]	dbg_cmd_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The external debug interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	dbg_cyc     = i_dbg_cyc;
	assign	dbg_stb     = i_dbg_stb;
	assign	dbg_we      = i_dbg_we;
	assign	dbg_addr    = i_dbg_addr;
	assign	dbg_idata   = i_dbg_data;
	assign	o_dbg_ack   = dbg_ack;
	assign	o_dbg_stall = dbg_stall;
	assign	o_dbg_data  = dbg_odata;
	//
	// We offer only a limited interface here, requiring a pre-register
	// write to set the local address.  This interface allows access to
	// the Zip System on a debug basis only, and not to the rest of the
	// wishbone bus.  Further, to access these registers, the control
	// register must first be accessed to both stop the CPU and to
	// set the following address in question.  Hence all accesses require
	// two accesses: write the address to the control register (and halt
	// the CPU if not halted), then read/write the data from the data
	// register.
	//
	assign	dbg_cmd_write = (dbg_stb)&&(dbg_we)&&(dbg_addr[5]);

	// cmd_reset
	// {{{
	// Always start us off with an initial reset
	initial	cmd_reset = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		cmd_reset <= 1'b1;
	else if (cpu_break && !START_HALTED)
		cmd_reset <= 1'b1;
	else
		cmd_reset <= ((dbg_cmd_write)&&(dbg_idata[`RESET_BIT]));
	// }}}

	// cmd_halt
	// {{{
	initial	cmd_halt  = START_HALTED;
	always @(posedge i_clk)
	if (i_reset)
		cmd_halt <= START_HALTED;
	else if (cmd_reset)
		cmd_halt <= START_HALTED;
	else begin
		// {{{
		// When shall we release from a halt?  Only if we have come
		// to a full and complete stop.  Even then, we only release if
		// we aren't being given a command to step the CPU.
		//
		if (!cmd_write && !cpu_dbg_stall && dbg_cmd_write
			&& (!dbg_idata[`HALT_BIT] || dbg_idata[`STEP_BIT]))
			cmd_halt <= 1'b0;

		// Reasons to halt

		// 1. Halt on any unhandled CPU exception.  The cause of the
		//	exception must be cured before we can (re)start.
		//	If the CPU is configured to start immediately on power
		//	up, we leave it to reset on any exception instead.
		if (cpu_break && START_HALTED)
			cmd_halt <= 1'b1;

		// 2. Halt on any user request to halt.  (Only valid if the
		//	STEP bit isn't also set)
		if (dbg_cmd_write && dbg_idata[`HALT_BIT]
						&& !dbg_idata[`STEP_BIT])
			cmd_halt <= 1'b1;

		// 3. Halt on any user request to write to a CPU register
		if (i_dbg_stb && dbg_we && !dbg_addr[5])
			cmd_halt <= 1'b1;

		// 4. Halt following any step command
		if (cmd_step)
			cmd_halt <= 1'b1;

		// 4. Halt following any clear cache
		if (cmd_clear_cache)
			cmd_halt <= 1'b1;

		// 5. Halt on any clear cache bit--independent of any step bit
		if (dbg_cmd_write && dbg_idata[`CLEAR_CACHE_BIT])
			cmd_halt <= 1'b1;
		// }}}
	end
	// }}}

	// cmd_clear_cache
	// {{{
	initial	cmd_clear_cache = 1'b0;
	always @(posedge i_clk)
	if (i_reset || cpu_reset)
		cmd_clear_cache <= 1'b0;
	else if (cmd_halt && dbg_cmd_write
			&& dbg_idata[`CLEAR_CACHE_BIT] && dbg_idata[`HALT_BIT])
		cmd_clear_cache <= 1'b1;
	else if (cmd_halt && !cpu_dbg_stall)
		cmd_clear_cache <= 1'b0;
	// }}}

	// cmd_step
	// {{{
	initial	cmd_step  = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cmd_step <= 1'b0;
	else if (dbg_cmd_write && dbg_idata[`STEP_BIT])
		cmd_step <= 1'b1;
	else if (!cpu_dbg_stall)
		cmd_step <= 1'b0;
	// }}}

	assign	cpu_reset = (cmd_reset);

	assign	cpu_halt = (cmd_halt);
	// Values:
	//	0x0003f -> cmd_addr mask
	//	0x00040 -> reset
	//	0x00080 -> PIC interrrupt pending
	//	0x00100 -> cmd_step
	//	0x00200 -> cmd_stall
	//	0x00400 -> cmd_halt
	//	0x00800 -> cmd_clear_cache
	//	0x01000 -> cc.sleep
	//	0x02000 -> cc.gie
	//	0x10000 -> External interrupt line is high
	assign	cmd_data = { 7'h00, 8'h00, i_ext_int,
			cpu_break, cpu_dbg_cc,
			1'b0, cmd_halt, (!cpu_dbg_stall), 1'b0,
			i_ext_int, cpu_reset, 6'h0 };

	initial	cmd_write = 0;
	always @(posedge i_clk)
	if (i_reset || cpu_reset)
		cmd_write <= 1'b0;
	else if (!cmd_write || !cpu_dbg_stall)
		cmd_write <= dbg_stb && dbg_we && !dbg_addr[5] && (|i_dbg_sel);

	always @(posedge i_clk)
	if ((!cmd_write || !cpu_dbg_stall)&&(dbg_stb && dbg_we && !dbg_addr[5]))
	begin
		cmd_waddr <= dbg_addr[4:0];
		cmd_wdata <= dbg_idata;
	end

	//
	// The CPU itself
	// {{{
	assign cpu_dbg_we = ((dbg_stb)&&(dbg_we)&&(!dbg_addr[5]));
`ifdef	FORMAL
	(* anyseq *)	reg	f_cpu_halted, f_cpu_data, f_cpu_stall,
				f_cpu_break;
	(* anyseq *) reg [2:0]	f_cpu_dbg_cc;
	(* anyseq *) reg [31:0]	f_cpu_dbg_data;

	assign	cpu_dbg_stall = f_cpu_stall;
	assign	cpu_break = f_cpu_break;
	assign	cpu_dbg_cc = f_cpu_dbg_cc;
	assign	cpu_dbg_data = f_cpu_dbg_data;

	fdebug #(
		// {{{
		.OPT_DISTRIBUTED_RAM(1'b1)
		// }}}
	) fdbg (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_cpu_reset(cpu_reset),
		.i_halt(cpu_halt),
		.i_halted(f_cpu_halted),
		.i_clear_cache(cmd_clear_cache),
		.i_dbg_we(cmd_write),
		.i_dbg_reg(cmd_waddr),
		.i_dbg_data(cmd_wdata),
		.i_dbg_stall(cpu_dbg_stall),
		.i_dbg_break(cpu_break),
		.i_dbg_cc(cpu_dbg_cc)
		// }}}
	);
`else
	zipwb	#(
		// {{{
		.RESET_ADDRESS(RESET_ADDRESS),
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.LGICACHE(LGICACHE),
		.OPT_LGDCACHE(LGDCACHE),
		.WITH_LOCAL_BUS(0)
		// }}}
	) thecpu(
		// {{{
		i_clk, cpu_reset, i_ext_int,
			cpu_halt, cmd_clear_cache,
				cmd_waddr, cmd_write,
				cmd_wdata, i_dbg_addr[4:0],
				cpu_dbg_stall, cpu_dbg_data,
				cpu_dbg_cc, cpu_break,
			o_wb_cyc, o_wb_stb,
				cpu_lcl_cyc, cpu_lcl_stb,
				o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_stall, i_wb_ack, i_wb_data,
				(i_wb_err)||(cpu_lcl_cyc),
			cpu_op_stall, cpu_pf_stall, cpu_i_count
`ifdef	DEBUG_SCOPE
			, o_cpu_debug
`endif
		// }}}
	);
`endif
	// }}}

	// Return debug response values
	// {{{
	// assign	dbg_odata = (dbg_addr[5])?cmd_data :cpu_dbg_data;

	always @(posedge i_clk)
		dbg_pre_addr <= dbg_addr[5];

	always @(posedge i_clk)
		dbg_cmd_data <= cmd_data;

	initial	dbg_pre_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_dbg_cyc)
		dbg_pre_ack <= 1'b0;
	else
		dbg_pre_ack <= dbg_stb && !o_dbg_stall;

	initial dbg_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_dbg_cyc)
		dbg_ack <= 1'b0;
	else
		dbg_ack <= dbg_pre_ack;

	always @(posedge i_clk)
	if (dbg_pre_addr)
		dbg_odata <= dbg_cmd_data;
	else
		dbg_odata <= cpu_dbg_data;

	assign	dbg_stall= (!cmd_write || !cpu_dbg_stall) && dbg_we && !dbg_addr[5];
	// }}}
	// }}}
	assign	o_ext_int = (cmd_halt) && (!i_wb_stall);

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, dbg_cyc, cpu_lcl_stb, cpu_op_stall,
			cpu_pf_stall, cpu_i_count };
	// verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = 3;

	reg	[F_LGDEPTH-1:0]	fwb_nreqs, fwb_nacks, fwb_outstanding;

	fwb_slave #(
		.AW(6), .DW(32), .F_LGDEPTH(F_LGDEPTH)
	) fwb(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(i_dbg_cyc), .i_wb_stb(i_dbg_stb),
		.i_wb_we(i_dbg_we), .i_wb_addr(i_dbg_addr),
		.i_wb_data(i_dbg_data),
		.i_wb_ack(o_dbg_ack), .i_wb_stall(o_dbg_stall),
		.i_wb_idata(o_dbg_data), .i_wb_err(1'b0),
		.f_nreqs(fwb_nreqs), .f_nacks(fwb_nacks),
		.f_outstanding(fwb_outstanding)
		// }}}
	);

	always @(*)
	if (i_dbg_cyc)
		assert(fwb_outstanding == dbg_pre_ack + o_dbg_ack);

	always @(posedge i_clk)
	if ($past(i_dbg_cyc && cpu_dbg_we))
		assume(i_dbg_cyc);
`endif
// }}}
endmodule
