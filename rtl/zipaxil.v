////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipaxil.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A potential top level module holding the core of the Zip CPU
//		together--this one with AXI-lite instruction, data, and debug
//	interfaces.  In general, the Zip CPU is designed to be as simple as
//	possible.  (actual implementation aside ...)  The instruction set is
//	about as RISC as you can get, with only 26 instruction types currently
//	supported.  (There are still 8-instruction Op-Codes reserved for
//	floating point, and 5 which can be used for transactions not requiring
//	registers.) Please see the accompanying spec.pdf file for a description
//	of these instructions.
//
//	This version is bus width agnostic for both instruction and data buses,
//	although the debug bus must still be 32-bits.  Instruction and data
//	buses must be at least 32-bits wide.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	zipaxil #(
		// {{{
		parameter	C_DBG_ADDR_WIDTH = 8,
		parameter	ADDRESS_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	OPT_LGICACHE = 0,
		parameter	OPT_LGDCACHE = 0,
		parameter	[0:0]	OPT_PIPELINED = 1'b1,
		parameter [ADDRESS_WIDTH-1:0] RESET_ADDRESS={(ADDRESS_WIDTH){1'b0}},
		parameter [0:0]	START_HALTED = 1'b0,
		parameter [0:0]	SWAP_WSTRB = 1'b1,
		parameter 	OPT_MPY    = 3,
		parameter [0:0]	OPT_DIV    = 1'b1,
		parameter [0:0]	OPT_SHIFTS = 1'b1,
		parameter [0:0]	OPT_LOCK   = 1'b1,
		parameter [0:0]	OPT_FPU = 0,
		parameter [0:0]	OPT_EARLY_BRANCHING = 1,
		parameter [0:0]	OPT_CIS = 1'b1,
		parameter [0:0]	OPT_LOWPOWER   = 1'b0,
		parameter [0:0]	OPT_DISTRIBUTED_REGS = 1'b1,
		parameter [0:0]	OPT_DBGPORT    = START_HALTED,
		parameter [0:0]	OPT_TRACE_PORT = 1'b0,
		parameter [0:0]	OPT_PROFILER   = 1'b0,
		parameter [0:0]	OPT_USERMODE   = 1'b1,
		parameter	RESET_DURATION = 10,
		// localparam [0:0]	WITH_LOCAL_BUS = 1'b0,
`ifdef	VERILATOR
		parameter	[0:0]	OPT_SIM = 1'b1,
		parameter	[0:0]	OPT_CLKGATE = OPT_LOWPOWER
`else
		parameter	[0:0]	OPT_SIM = 1'b0,
		parameter	[0:0]	OPT_CLKGATE = 1'b0
`endif
`ifdef	FORMAL
		, parameter	F_LGDEPTH=8
`endif
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
					i_interrupt, i_cpu_reset,
		// Debug interface
		// {{{
		// Debug interface -- inputs
//		input	wire		i_halt, i_clear_cache,
//		input	wire	[4:0]	i_dbg_wreg,
//		input	wire		i_dbg_we,
//		input	wire	[31:0]	i_dbg_data,
//		input	wire	[4:0]	i_dbg_rreg,
		// Debug interface -- outputs
//		output	wire		cpu_dbg_stall,
//		output	reg	[31:0]	o_dbg_reg,
//		output	reg	[2:0]	o_dbg_cc,
//		output	wire		o_break,
		input	wire		S_DBG_AWVALID,
		output	wire		S_DBG_AWREADY,
		input	wire	[C_DBG_ADDR_WIDTH-1:0]	S_DBG_AWADDR,
		// Verilator coverage_off
		input	wire	[2:0]	S_DBG_AWPROT,
		// Verilator coverage_on
		//
		input	wire		S_DBG_WVALID,
		output	wire		S_DBG_WREADY,
		input	wire	[31:0]	S_DBG_WDATA,
		input	wire	[3:0]	S_DBG_WSTRB,
		//
		output	reg		S_DBG_BVALID,
		input	wire		S_DBG_BREADY,
		// Verilator coverage_off
		output	wire	[1:0]	S_DBG_BRESP,
		// Verilator coverage_on
		//
		input	wire		S_DBG_ARVALID,
		output	wire		S_DBG_ARREADY,
		input	wire	[7:0]	S_DBG_ARADDR,
		// Verilator coverage_off
		input	wire	[2:0]	S_DBG_ARPROT,
		// Verilator coverage_on
		//
		output	reg		S_DBG_RVALID,
		input	wire		S_DBG_RREADY,
		output	reg	[31:0]	S_DBG_RDATA,
		// Verilator coverage_off
		output	wire	[1:0]	S_DBG_RRESP,
		// Verilator coverage_on
		//
		// }}}
		// Instruction bus (master)
		// {{{
		// Verilator coverage_off
		output	wire				M_INSN_AWVALID,
		input	wire				M_INSN_AWREADY,
		output	wire	[ADDRESS_WIDTH-1:0]	M_INSN_AWADDR,
		output	wire	[2:0]			M_INSN_AWPROT,
		//
		output	wire				M_INSN_WVALID,
		input	wire				M_INSN_WREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_INSN_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_INSN_WSTRB,
		//
		input	wire				M_INSN_BVALID,
		output	wire				M_INSN_BREADY,
		input	wire	[1:0]			M_INSN_BRESP,
		// Verilator coverage_on
		//
		output	wire				M_INSN_ARVALID,
		input	wire				M_INSN_ARREADY,
		output	wire	[ADDRESS_WIDTH-1:0]	M_INSN_ARADDR,
		output	wire	[2:0]			M_INSN_ARPROT,
		//
		input	wire				M_INSN_RVALID,
		output	wire				M_INSN_RREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_INSN_RDATA,
		input	wire	[1:0]			M_INSN_RRESP,
		// }}}
		// Data bus (master)
		// {{{
		output	wire				M_DATA_AWVALID,
		input	wire				M_DATA_AWREADY,
		output	wire [ADDRESS_WIDTH-1:0]	M_DATA_AWADDR,
		// Verilator coverage_off
		output	wire	[2:0]			M_DATA_AWPROT,
		// Verilator coverage_on
		//
		output	wire				M_DATA_WVALID,
		input	wire				M_DATA_WREADY,
		output	wire [C_AXI_DATA_WIDTH-1:0]	M_DATA_WDATA,
		output	wire [C_AXI_DATA_WIDTH/8-1:0]	M_DATA_WSTRB,
		//
		input	wire				M_DATA_BVALID,
		output	wire				M_DATA_BREADY,
		input	wire	[1:0]			M_DATA_BRESP,
		//
		output	wire				M_DATA_ARVALID,
		input	wire				M_DATA_ARREADY,
		output	wire [ADDRESS_WIDTH-1:0]	M_DATA_ARADDR,
		// Verilator coverage_off
		output	wire	[2:0]			M_DATA_ARPROT,
		// Verilator coverage_on
		//
		input	wire				M_DATA_RVALID,
		output	wire				M_DATA_RREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_DATA_RDATA,
		input	wire	[1:0]			M_DATA_RRESP,
		// }}}
		// Accounting outputs ... to help us count stalls and usage
		output	wire		o_cmd_reset,
		output	wire		o_halted,
		output	wire		o_gie,
		output	wire		o_op_stall,
		output	wire		o_pf_stall,
		output	wire		o_i_count,
		//
		output	wire	[31:0]	o_cpu_debug,
		//
`ifdef	VBENCH_TB
		// {{{
		// output	wire			cpu_halt,
		//				cmd_reset,
		//				cmd_step,
		output	wire			early_branch,
		output	wire	[31:0]		early_branch_pc,
		output	wire	[6:0]		dcdA, dcdB,
		output	wire			new_pc,
		output	wire	[31:0]		cpu_ipc, cpu_upc, pf_pc,
		// output	wire			pf_cyc, pf_stb, pf_we,
		// output	wire	[31:0]		pf_addr,
		// output	wire			pf_ack,
		output	wire			pf_valid, pf_illegal,
		// pf_vmask, pf_r_v, pf_tagsrc, pf_tagipc, pf_tagvallst,
		// output	wire	[31:0]		pf_lastpc,
		output	wire	[31:0]		pf_instruction,
		output	wire	[31:0]		pf_instruction_pc,
		//
		output	wire			dcd_ce, dcd_stalled, dcd_gie,
						dcd_valid, dcd_illegal,
						dcd_phase, dcd_break, dcd_pipe,
		output	wire	[3:0]		dcd_opn,
		output	wire			dcd_rA, dcd_rB, dcd_wR, dcd_wF,
		output	wire	[4:0]		dcdR,
		output	wire			dcdRpc, dcdRcc,
		output	wire	[31:0]		dcd_pc,
		output	wire			dcd_M,
		//
		output	wire			op_ce, op_illegal, op_valid,
						op_valid_mem, op_valid_alu,
						op_stall, op_wR, op_wF,
						op_phase, op_gie,
		output	wire	[4:0]		op_R, op_Aid, op_Bid,
		output	wire	[31:0]		op_Av, op_Bv, op_pc,
		output	wire			master_stall,
		//
		output	wire			alu_ce, adf_ce_unconditional,
						alu_valid, alu_wR, alu_wF,
						alu_pc_valid, alu_illegal,
						alu_gie,
						set_cond, alu_phase,
		output	wire	[3:0]		alu_flags,
		output	wire	[31:0]		alu_pc,
		//
		output	wire			mem_valid, mem_pc_valid, mem_ce,
						mem_busy, mem_rdbusy,
		output	wire	[4:0]		mem_wreg,
		//
		output	wire			div_valid, div_ce, div_busy,
		//
		output	wire	[4:0]		wr_reg_id,
		output	wire			wr_reg_ce, wr_flags_ce,
		output	wire	[31:0]		wr_gpreg_vl, wr_spreg_vl,
		output	wire	[15:0]		w_iflags, w_uflags,
		//
		output	wire			cpu_sim,
						r_sleep, master_ce, op_break,
						r_gie,
		output	wire	[22:0]		cpu_sim_immv,
		output	wire	[7:0]		op_F,
		//
		//
		// ZipSystem peripherals
		output	wire	[31:0]		watchbus, watchdog, pic_data,
						wdbus_data,
		output	wire	[15:0]		int_state, alt_int_state,
		output	wire	[31:0]		timer_a,
						timer_b, timer_c, jiffies,
						utc_data, uoc_data, uic_data,
						upc_data, mtc_data, moc_data,
						mpc_data, mic_data,
		output	wire	[31:0]		mem_data, mem_addr, mem_result,
		output	wire			op_pipe,
						// op_A_alu, op_B_alu,
						// op_A_mem, op_B_mem,
		output	wire	[3:0]		op_opn,
		output	wire	[31:0]		alu_result,
		output	wire			alu_busy,
		output	wire	[4:0]		alu_reg,
		output	wire			switch_to_interrupt,
						release_from_interrupt,
						break_en,
		// }}}
`endif
		output	wire		o_prof_stb,
		output	wire [ADDRESS_WIDTH-1:0] o_prof_addr,
		output	wire	[31:0]	o_prof_ticks
	// }}}
	);

	// Declarations
	// {{{
	localparam	[0:0]	DBG_ADDR_CTRL = 1'b0,
				DBG_ADDR_CPU  = 1'b1;

	localparam	C_DBG_DATA_WIDTH = 32;
	localparam	DBGLSB = $clog2(C_DBG_DATA_WIDTH/8);
	localparam	AW=ADDRESS_WIDTH-2;
	localparam	[0:0]	OPT_PIPELINED_BUS_ACCESS = (OPT_PIPELINED)&&(OPT_LGDCACHE > 1);
	localparam	[0:0]	OPT_MEMPIPE = OPT_PIPELINED_BUS_ACCESS;
	localparam	[0:0]	OPT_DCACHE = (OPT_LGDCACHE > 4);

	localparam FETCH_LIMIT = (OPT_LGICACHE < 4) ? (1 << OPT_LGICACHE) : 16;

	// Debug bit allocations
	// {{{
	//	DBGCTRL
	//		 5 DBG Catch -- Catch exceptions/fautls w/ debugger
	//		 4 Clear cache
	//		 3 RESET_FLAG
	//		 2 STEP	(W=1 steps, and returns to halted)
	//		 1 HALT(ED)
	//		 0 HALT
	//	DBGDATA
	//		read/writes internal registers
	//
	localparam	HALT_BIT = 0,
			STEP_BIT = 2,
			RESET_BIT = 3,
			CLEAR_CACHE_BIT = 4,
			CATCH_BIT = 5;
	// }}}
	localparam [0:0]	OPT_ALIGNMENT_ERR = 1'b0;
	localparam [0:0]	SWAP_ENDIANNESS = 1'b0;

	// AXI-lite signal handling
	// {{{
	wire		awskd_valid, wskd_valid, arskd_valid;
	wire		dbg_write_ready, dbg_read_ready;
	wire	[C_DBG_ADDR_WIDTH-DBGLSB-1:0]	awskd_addr, arskd_addr;
	wire	[31:0]	wskd_data;
	wire	[3:0]	wskd_strb;
	reg		dbg_write_valid, dbg_read_valid;
	wire		dbg_blkram_stall;
	reg	[4:0]	dbg_write_reg;
	wire	[4:0]	dbg_read_reg;
	reg	[31:0]	dbg_write_data;
	wire	[31:0]	dbg_read_data;
	wire		cpu_dbg_stall, cpu_break, dbg_write_stall;
	wire	[2:0]	cpu_dbg_cc;
	// }}}

	wire	reset_hold, halt_on_fault, dbg_catch;
	wire	cpu_clken, cpu_clock, clk_gate;
	wire	reset_request, release_request, halt_request, step_request,
		clear_cache_request;
	wire	cpu_has_halted;


	// CPU control registers
	// {{{
	reg		cmd_halt, cmd_reset, cmd_step, cmd_clear_cache;
	wire	[31:0]	cpu_status;
	wire		dbg_cmd_write, dbg_cpu_write;
	wire	[31:0]	dbg_cmd_data;
	wire	[3:0]	dbg_cmd_strb;
	// }}}

	// Fetch
	// {{{
	wire		pf_new_pc, clear_icache, pf_ready;
	wire [AW+1:0]	pf_request_address;
`ifndef	VBENCH_TB
	wire	[31:0]	pf_instruction;
	wire [AW+1:0]	pf_instruction_pc;
	wire		pf_valid, pf_illegal;
`endif
	// }}}
	// Memory
	// {{{
	wire		clear_dcache, bus_lock;
	wire	[2:0]	mem_op;
	wire	[31:0]	mem_cpu_addr;
	wire	[AW+1:0]	mem_lock_pc;
	wire	[31:0]	mem_wdata;
	wire	[4:0]	mem_reg;
	wire		mem_pipe_stalled, mem_bus_err;
`ifndef	VBENCH_TB
	wire		mem_ce, mem_valid, mem_busy, mem_rdbusy;
	wire	[4:0]	mem_wreg;
	wire	[31:0]	mem_result;
`endif
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug signal handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write signaling
	// {{{
	skidbuffer #(
		// {{{
		.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_DBG_ADDR_WIDTH-DBGLSB)
		// }}}
	) dbgawskd(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_DBG_AWVALID),
		.o_ready(S_DBG_AWREADY),
		.i_data(S_DBG_AWADDR[C_DBG_ADDR_WIDTH-1:DBGLSB]),
		.o_valid(awskd_valid), .i_ready(dbg_write_ready),
			.o_data(awskd_addr)
		// }}}
	);

	skidbuffer #(
		// {{{
		.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_DBG_DATA_WIDTH+C_DBG_DATA_WIDTH/8)
		// }}}
	) dbgwskd(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_DBG_WVALID),
		.o_ready(S_DBG_WREADY),
		.i_data({ S_DBG_WSTRB, S_DBG_WDATA }),
		.o_valid(wskd_valid), .i_ready(dbg_write_ready),
			.o_data({ wskd_strb, wskd_data })
		// }}}
	);

	assign	dbg_write_ready = awskd_valid && wskd_valid
			&& ((wskd_strb==0) || awskd_addr[5] != DBG_ADDR_CPU
			   || !dbg_write_stall)
			&& (!S_DBG_BVALID || S_DBG_BREADY);

	// dbg_write_valid
	// {{{
	initial	dbg_write_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !OPT_DBGPORT)
		dbg_write_valid <= 1'b0;
	else if (!dbg_write_stall)
		dbg_write_valid <= dbg_cpu_write;
	// }}}

	// dbg_write_reg
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!dbg_write_stall)
	begin
		dbg_write_reg <= awskd_addr[4:0];
		if (OPT_LOWPOWER && !dbg_cpu_write)
			dbg_write_reg <= 0;
	end
	// }}}

	// dbg_write_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!dbg_write_stall)
	begin
		dbg_write_data <= wskd_data;
		if (OPT_LOWPOWER && !dbg_cpu_write)
			dbg_write_data <= 0;
	end
	// }}}

	// S_DBG_BVALID
	//  {{{
	initial	S_DBG_BVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_DBG_BVALID <= 1'b0;
	else if (dbg_write_ready)
		S_DBG_BVALID <= 1'b1;
	else if (S_DBG_BREADY)
		S_DBG_BVALID <= 1'b0;
	// }}}

	// S_DBG_BRESP
	// {{{
	assign	S_DBG_BRESP = 2'b00;
	// }}}

	// }}}

	//
	// Read signaling
	// {{{

	skidbuffer #(
		// {{{
		.OPT_OUTREG(0),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.DW(C_DBG_ADDR_WIDTH-DBGLSB)
		// }}}
	) dbgarskd(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_DBG_ARVALID),
		.o_ready(S_DBG_ARREADY),
		.i_data(S_DBG_ARADDR[C_DBG_ADDR_WIDTH-1:DBGLSB]),
		.o_valid(arskd_valid), .i_ready(dbg_read_ready),
			.o_data(arskd_addr)
		// }}}
	);

	assign	dbg_read_ready = arskd_valid && !dbg_blkram_stall
				&& (!S_DBG_RVALID || S_DBG_RREADY);

	assign	dbg_read_reg = (OPT_LOWPOWER && !dbg_read_ready)
					? 5'h0 : arskd_addr[4:0];

	// dbg_read_valid
	// {{{
	reg	[1:0]	r_blkram_stall;

	initial	r_blkram_stall = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !OPT_DBGPORT)
		r_blkram_stall <= 0;
	else if (dbg_read_ready && arskd_addr[5] == DBG_ADDR_CPU)
		r_blkram_stall <= 2 + (OPT_DISTRIBUTED_REGS ? 0:1);
	else if (r_blkram_stall > 0)
		r_blkram_stall <= r_blkram_stall - 1;

	initial	dbg_read_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !OPT_DBGPORT)
		dbg_read_valid <= 0;
	else
		dbg_read_valid <= (r_blkram_stall == 1);

	assign	dbg_blkram_stall = (r_blkram_stall != 0);
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && (dbg_read_valid || dbg_blkram_stall))
		assert(!S_DBG_RVALID);
`endif
	// }}}

	// S_DBG_RVALID
	// {{{
	initial	S_DBG_RVALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_DBG_RVALID <= 0;
	else if (!S_DBG_RVALID || S_DBG_RREADY)
		S_DBG_RVALID <= (dbg_read_ready
			  && (!OPT_DBGPORT || arskd_addr[5] == DBG_ADDR_CTRL))
			|| dbg_read_valid;
	// }}}

	// S_DBG_RDATA
	// {{{
	initial	S_DBG_RDATA = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		S_DBG_RDATA <= 0;
	else if (!S_DBG_RVALID || S_DBG_RREADY)
	begin
		// {{{
		if (OPT_DBGPORT && dbg_read_valid)
			S_DBG_RDATA <= dbg_read_data;
		else
			S_DBG_RDATA <= cpu_status;

		if (OPT_LOWPOWER && (!OPT_DBGPORT || !dbg_read_valid)
						&& !dbg_read_ready)
			S_DBG_RDATA <= 0;
		// }}}
	end
	// }}}

	assign	S_DBG_RRESP = 2'b00;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset, halt, clear-cache, and step controls
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	dbg_cpu_write = OPT_DBGPORT && dbg_write_ready
				&& awskd_addr[5] == DBG_ADDR_CPU
				&& wskd_strb == 4'hf;
	assign	dbg_cmd_write = dbg_write_ready && awskd_addr[5] == DBG_ADDR_CTRL;
	assign	dbg_cmd_data = wskd_data;
	assign	dbg_cmd_strb = wskd_strb;

	assign	reset_request = dbg_cmd_write && dbg_cmd_strb[RESET_BIT/8]
						&& dbg_cmd_data[RESET_BIT];
	assign	release_request = dbg_cmd_write && dbg_cmd_strb[HALT_BIT/8]
						&& !dbg_cmd_data[HALT_BIT];
	assign	halt_request = dbg_cmd_write && dbg_cmd_strb[HALT_BIT/8]
						&& dbg_cmd_data[HALT_BIT];
	assign	step_request = dbg_cmd_write && dbg_cmd_strb[STEP_BIT/8]
						&& dbg_cmd_data[STEP_BIT];
	assign	clear_cache_request = dbg_cmd_write
					&& dbg_cmd_strb[CLEAR_CACHE_BIT/8]
					&& dbg_cmd_data[CLEAR_CACHE_BIT];

	//
	// reset_hold: Always start us off with an initial reset
	// {{{
	generate if (RESET_DURATION > 0)
	begin : INITIAL_RESET_HOLD
		// {{{
		reg	[$clog2(RESET_DURATION)-1:0]	reset_counter;
		reg					r_reset_hold;

		initial	reset_counter = RESET_DURATION;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || i_cpu_reset)
			reset_counter <= RESET_DURATION;
		else if (reset_counter > 0)
			reset_counter <= reset_counter - 1;

		initial	r_reset_hold = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || i_cpu_reset)
			r_reset_hold <= 1;
		else
			r_reset_hold <= (reset_counter > 1);

		assign	reset_hold = r_reset_hold;
`ifdef	FORMAL
		always @(*)
			assert(reset_hold == (reset_counter != 0));
`endif
		// }}}
	end else begin : NO_RESET_HOLD

		assign reset_hold = 0;

	end endgenerate
	// }}}

	assign	halt_on_fault = dbg_catch;

	// cmd_reset
	// {{{
	// Always start us off with an initial reset
	initial	cmd_reset = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_cpu_reset)
		cmd_reset <= 1'b1;
	else if (reset_hold)
		cmd_reset <= 1'b1;
	else if (cpu_break && !halt_on_fault)
		cmd_reset <= 1'b1;
	else
		cmd_reset <= reset_request;
	// }}}

	// cmd_halt
	// {{{
	initial	cmd_halt  = START_HALTED;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cmd_halt <= START_HALTED;
	else if (i_cpu_reset && !dbg_write_ready && !dbg_write_stall)
		cmd_halt <= START_HALTED;
	else if (cmd_reset && START_HALTED)
		cmd_halt <= START_HALTED;
	else begin
		// {{{
		// When shall we release from a halt?  Only if we have
		// come to a full and complete stop.  Even then, we only
		// release if we aren't being given a command to step the CPU.
		//
		if (!dbg_write_valid && cpu_has_halted && dbg_cmd_write
				&& (release_request || step_request))
			cmd_halt <= 1'b0;

		// Reasons to halt

		// 1. Halt on any unhandled CPU exception.  The cause of the
		//	exception must be cured before we can (re)start.
		//	If the CPU is configured to start immediately on power
		//	up, we leave it to reset on any exception instead.
		if (cpu_break && halt_on_fault)
			cmd_halt <= 1'b1;

		// 2. Halt on any user request to halt.  (Only valid if the
		//	STEP bit isn't also set)
		if (dbg_cmd_write && halt_request && !step_request)
			cmd_halt <= 1'b1;

		// 3. Halt on any user request to write to a CPU register
		if (dbg_cpu_write)
			cmd_halt <= 1'b1;

		// 4. Halt following any step command
		if (cmd_step && !step_request)
			cmd_halt <= 1'b1;

		// 5. Halt following any clear cache
		if (cmd_clear_cache)
			cmd_halt <= 1'b1;

		// 6. Halt on any clear cache bit--independent of any step bit
		if (clear_cache_request)
			cmd_halt <= 1'b1;
		// }}}
	end
	// }}}

	// cmd_clear_cache
	// {{{
	initial	cmd_clear_cache = 1'b0;
	always @(posedge  S_AXI_ACLK)
	if (!S_AXI_ARESETN || cmd_reset)
		cmd_clear_cache <= 1'b0;
	else if (dbg_cmd_write && clear_cache_request && halt_request)
		cmd_clear_cache <= 1'b1;
	else if (cmd_halt && !cpu_dbg_stall)
		cmd_clear_cache <= 1'b0;
	// }}}

	// cmd_step
	// {{{
	initial	cmd_step = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_cpu_reset)
		cmd_step <= 1'b0;
	else if (cmd_reset || cpu_break
			|| reset_request
			|| clear_cache_request || cmd_clear_cache
			|| halt_request || dbg_cpu_write)
		cmd_step <= 1'b0;
	else if (!dbg_write_valid && cpu_has_halted && step_request)
		cmd_step <= 1'b1;
	else // if (cpu_dbg_stall)
		cmd_step <= 1'b0;
`ifdef	FORMAL
	// While STEP is true, we can't halt
	always @(*)
	if (S_AXI_ARESETN && cmd_step)
		assert(!cmd_halt);
`endif
	// }}}

	// dbg_catch
	// {{{
	generate if (!OPT_DBGPORT)
	begin : NO_DBG_CATCH
		assign	dbg_catch = START_HALTED;
	end else begin : GEN_DBG_CATCH
		reg	r_dbg_catch;

		initial	r_dbg_catch = START_HALTED;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_dbg_catch <= START_HALTED;
		else if (dbg_cmd_write && dbg_cmd_strb[CATCH_BIT/8])
			r_dbg_catch <= dbg_cmd_data[CATCH_BIT];

		assign	dbg_catch = r_dbg_catch;
	end endgenerate
	// }}}

	// cpu_status
	// {{{
	//	0xffff_f000 -> (Unused / reserved)
	//
	//	0x0000_0800 -> cpu_break
	//	0x0000_0400 -> Interrupt pending
	//	0x0000_0200 -> User mode
	//	0x0000_0100 -> Sleep (CPU is sleeping)
	//
	//	0x0000_00c0 -> (Unused/reserved)
	//	0x0000_0020 -> dbg_catch
	//	0x0000_0010 -> cmd_clear_cache
	//
	//	0x0000_0008 -> Reset
	//	0x0000_0004 -> Step (auto clearing, write only)
	//	0x0000_0002 -> Halt (status)
	//	0x0000_0001 -> Halt (request)
	assign	cpu_status = { 16'h0, 4'h0,
			cpu_break, i_interrupt, cpu_dbg_cc[1:0],
			2'h0, dbg_catch, 1'b0,
			cmd_reset, 1'b0, !cpu_dbg_stall, cmd_halt
		};
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The ZipCPU Core
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	FORMAL
	// {{{
	(* anyseq *)	reg	f_cpu_halted, f_cpu_data, f_cpu_stall,
				f_cpu_break;
	(* anyseq *) reg [2:0]	f_cpu_dbg_cc;
	(* anyseq *) reg [2:0]	f_cpu_dbg_read_data;

	assign	cpu_dbg_stall = f_cpu_stall && !f_cpu_halted;
	assign	cpu_break	= f_cpu_break;
	assign	cpu_dbg_cc	= f_cpu_dbg_cc;
	assign	dbg_read_data	= f_cpu_dbg_read_data;

	fdebug #(
		// {{{
		.OPT_START_HALTED(START_HALTED),
		.OPT_DISTRIBUTED_RAM(OPT_DISTRIBUTED_REGS)
		// }}}
	) fdbg (
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_reset(!S_AXI_ARESETN),
		.i_cpu_reset(cmd_reset || i_cpu_reset),
		.i_halt(cmd_halt),
		.i_halted(f_cpu_halted),
		.i_clear_cache(cmd_clear_cache),
		.i_dbg_we(dbg_write_valid),
		.i_dbg_reg(dbg_write_reg),
		.i_dbg_data(dbg_write_data),
		.i_dbg_stall(cpu_dbg_stall),
		.i_dbg_break(cpu_break),
		.i_dbg_cc(cpu_dbg_cc)
		// }}}
	);
	// }}}
`else
	zipcore #(
		// {{{
		.RESET_ADDRESS({ {(32-ADDRESS_WIDTH){1'b0}}, RESET_ADDRESS }),
		.ADDRESS_WIDTH(ADDRESS_WIDTH-2),
		.OPT_PIPELINED(OPT_PIPELINED),
		.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
		.OPT_DCACHE(OPT_DCACHE),
		.OPT_MPY(OPT_MPY),
		.OPT_DIV(OPT_DIV),
		.OPT_SHIFTS(OPT_SHIFTS),
		.IMPLEMENT_FPU(OPT_FPU),
		.OPT_CIS(OPT_CIS),
		.OPT_LOCK(OPT_LOCK),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_START_HALTED(START_HALTED),
		.OPT_SIM(OPT_SIM),
		.OPT_PIPELINED_BUS_ACCESS(OPT_MEMPIPE),
		// localparam	[0:0]	OPT_MEMPIPE = OPT_PIPELINED_BUS_ACCESS;
		.OPT_DBGPORT(OPT_DBGPORT),
		.OPT_TRACE_PORT(OPT_TRACE_PORT),
		.OPT_PROFILER(OPT_PROFILER),
		.OPT_CLKGATE(OPT_CLKGATE),
		.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
		.OPT_USERMODE(OPT_USERMODE)
`ifdef	FORMAL
		, .F_LGDEPTH(F_LGDEPTH)
`endif
		// }}}
	) core (
		// {{{
		.i_clk(cpu_clock), .i_reset(cmd_reset),
			.i_interrupt(i_interrupt),
		.o_clken(cpu_clken),
		// Debug interface
		// {{{
		.i_halt(cmd_halt), .i_clear_cache(cmd_clear_cache),
			.i_dbg_wreg(dbg_write_reg), .i_dbg_we(dbg_write_valid),
			.i_dbg_data(dbg_write_data),.i_dbg_rreg(dbg_read_reg),
			.o_dbg_stall(cpu_dbg_stall),.o_dbg_reg(dbg_read_data),
			.o_dbg_cc(cpu_dbg_cc), .o_break(cpu_break),
		// }}}
		// Instruction fetch interface
		// {{{
		.o_pf_new_pc(pf_new_pc), .o_clear_icache(clear_icache),
			.o_pf_ready(pf_ready),
			.o_pf_request_address(pf_request_address),
		.i_pf_valid(pf_valid),
			.i_pf_illegal(pf_illegal),
			.i_pf_instruction(pf_instruction),
			.i_pf_instruction_pc(pf_instruction_pc),
		// }}}
		// Memory unit interface
		// {{{
		.o_clear_dcache(clear_dcache), .o_mem_ce(mem_ce),
			.o_bus_lock(bus_lock),
			.o_mem_op(mem_op), .o_mem_addr(mem_cpu_addr),
			.o_mem_data(mem_wdata),
			.o_mem_lock_pc(mem_lock_pc),
			.o_mem_reg(mem_reg),
			.i_mem_busy(mem_busy),
			.i_mem_rdbusy(mem_rdbusy),
			.i_mem_pipe_stalled(mem_pipe_stalled),
		.i_mem_valid(mem_valid),
			.i_bus_err(mem_bus_err),
			.i_mem_wreg(mem_wreg),
			.i_mem_result(mem_result),
		// }}}
		// Accounting/CPU usage interface
		.o_op_stall(o_op_stall), .o_pf_stall(o_pf_stall),
		.o_i_count(o_i_count),
		//
		.o_debug(o_cpu_debug),
		//
		.o_prof_stb(  o_prof_stb),
		.o_prof_addr( o_prof_addr),
		.o_prof_ticks(o_prof_ticks)
		// }}}
	);
`endif
	assign	o_cmd_reset	= cmd_reset;
	assign	o_gie		= cpu_dbg_cc[1];
	assign	dbg_write_stall	= dbg_write_valid && cpu_dbg_stall;
	assign	cpu_has_halted  = !cpu_dbg_stall;
	assign	o_halted	= cpu_has_halted;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Instruction Fetch
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

`ifndef	FORMAL

		axilfetch #(
			// {{{
			.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.FETCH_LIMIT(FETCH_LIMIT),
			.SWAP_ENDIANNESS(SWAP_ENDIANNESS)
			// }}}
		) pf (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			// CPU signals
			// {{{
			.i_cpu_reset(cmd_reset),
			.i_new_pc(pf_new_pc),
			.i_clear_cache(clear_icache),
			.i_ready(pf_ready && clk_gate),
			.i_pc(pf_request_address),
			.o_insn(pf_instruction),
			.o_pc(pf_instruction_pc),
			.o_valid(pf_valid),
			.o_illegal(pf_illegal),
			// }}}
			// AXI-lite bus signals
			// {{{
			.M_AXI_ARVALID(M_INSN_ARVALID),
			.M_AXI_ARREADY(M_INSN_ARREADY),
			.M_AXI_ARADDR(M_INSN_ARADDR),
			.M_AXI_ARPROT(M_INSN_ARPROT),
			//
			.M_AXI_RVALID(M_INSN_RVALID),
			.M_AXI_RREADY(M_INSN_RREADY),
			.M_AXI_RDATA(M_INSN_RDATA),
			.M_AXI_RRESP(M_INSN_RRESP)
			// }}}
			// }}}
		);

`endif

	// Assign values to the (unused) M_INSN_* write ports
	// {{{
	assign	M_INSN_AWVALID = 0;
	assign	M_INSN_AWVALID = 0;
	assign	M_INSN_AWADDR  = 0;
	assign	M_INSN_AWPROT  = 0;
	//
	assign	M_INSN_WVALID = 0;
	assign	M_INSN_WDATA  = 0;
	assign	M_INSN_WSTRB  = 0;
	//
	assign	M_INSN_BREADY = 1'b1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory Unit
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
`ifndef	FORMAL
	wire	[C_AXI_DATA_WIDTH-1:0]	i_bus_data, o_bus_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	o_bus_strb;

	generate if (SWAP_WSTRB && C_AXI_DATA_WIDTH > 32 && !OPT_DCACHE)
	begin : SWAP_BUS_WORD_ORDER
		genvar	gk;

		for(gk=0; gk<C_AXI_DATA_WIDTH/32; gk=gk+1)
		begin
			assign	i_bus_data[(C_AXI_DATA_WIDTH-32-gk*32) +: 32]
						= M_DATA_RDATA[gk*32 +: 32];
			assign	M_DATA_WDATA[gk*32 +: 32]
				= o_bus_data[(C_AXI_DATA_WIDTH-32-gk*32) +: 32];
			assign	M_DATA_WSTRB[gk* 4 +:  4]
				= o_bus_strb[(C_AXI_DATA_WIDTH/8-4-gk*4) +: 4];
		end

	end else begin : KEEP_BUS_WORD_ORDER
		// {{{
		assign	i_bus_data = M_DATA_RDATA;
		assign	M_DATA_WDATA = o_bus_data;
		assign	M_DATA_WSTRB = o_bus_strb;
		// }}}
	end endgenerate

	generate if (OPT_PIPELINED_BUS_ACCESS)
	begin : PIPELINED_MEM

		axilpipe #(
			// {{{
			.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.OPT_ALIGNMENT_ERR(OPT_ALIGNMENT_ERR),
			.SWAP_WSTRB(SWAP_WSTRB),
			.OPT_LOWPOWER(OPT_LOWPOWER)
			// .OPT_SIGN_EXTEND(OPT_SIGN_EXTEND)
			// }}}
		) domem(
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			.i_cpu_reset(cmd_reset),
			// CPU interface
			// {{{
			.i_stb(mem_ce),
			.i_lock(bus_lock),
			.i_op(mem_op),
			.i_addr(mem_cpu_addr),
			.i_data(mem_wdata),
			.i_oreg(mem_reg),
			.o_busy(mem_busy),
			.o_pipe_stalled(mem_pipe_stalled),
			.o_rdbusy(mem_rdbusy),
			.o_valid(mem_valid),
			.o_err(mem_bus_err),
			.o_wreg(mem_wreg),
			.o_result(mem_result),
			// }}}
			// AXI-lite
			// Write interface
			// {{{
			.M_AXI_AWVALID(M_DATA_AWVALID),
			.M_AXI_AWREADY(M_DATA_AWREADY),
			.M_AXI_AWADDR( M_DATA_AWADDR),
			.M_AXI_AWPROT( M_DATA_AWPROT),
			//
			.M_AXI_WVALID(M_DATA_WVALID),
			.M_AXI_WREADY(M_DATA_WREADY),
			.M_AXI_WDATA(o_bus_data),
			.M_AXI_WSTRB(o_bus_strb),
			//
			.M_AXI_BVALID(M_DATA_BVALID),
			.M_AXI_BREADY(M_DATA_BREADY),
			.M_AXI_BRESP( M_DATA_BRESP),
			// }}}
			// Read interface
			// {{{
			.M_AXI_ARVALID(M_DATA_ARVALID),
			.M_AXI_ARREADY(M_DATA_ARREADY),
			.M_AXI_ARADDR( M_DATA_ARADDR),
			.M_AXI_ARPROT( M_DATA_ARPROT),
			//
			.M_AXI_RVALID(M_DATA_RVALID),
			.M_AXI_RREADY(M_DATA_RREADY),
			.M_AXI_RDATA( i_bus_data),
			.M_AXI_RRESP( M_DATA_RRESP)
			// }}}
			// }}}
		);

	end else begin : BARE_MEM

		axilops	#(
			// {{{
			.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.SWAP_ENDIANNESS(SWAP_ENDIANNESS),
			.SWAP_WSTRB(SWAP_WSTRB),
			.OPT_ALIGNMENT_ERR(OPT_ALIGNMENT_ERR),
			.OPT_LOWPOWER(OPT_LOWPOWER)
			// }}}
		) domem(
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
			.i_cpu_reset(cmd_reset),
			// CPU interface
			// {{{
			.i_stb(mem_ce),
			.i_lock(bus_lock),
			.i_op(mem_op),
			.i_addr(mem_cpu_addr[ADDRESS_WIDTH-1:0]),
			.i_data(mem_wdata),
			.i_oreg(mem_reg),
			.o_busy(mem_busy),
			.o_rdbusy(mem_rdbusy),
			.o_valid(mem_valid),
			.o_err(mem_bus_err),
			.o_wreg(mem_wreg),
			.o_result(mem_result),
			// }}}
			// AXI-lite
			// Write interface
			// {{{
			.M_AXI_AWVALID(M_DATA_AWVALID),
			.M_AXI_AWREADY(M_DATA_AWREADY),
			.M_AXI_AWADDR( M_DATA_AWADDR),
			.M_AXI_AWPROT( M_DATA_AWPROT),
			//
			.M_AXI_WVALID(M_DATA_WVALID),
			.M_AXI_WREADY(M_DATA_WREADY),
			.M_AXI_WDATA(o_bus_data),
			.M_AXI_WSTRB(o_bus_strb),
			//
			.M_AXI_BVALID(M_DATA_BVALID),
			.M_AXI_BREADY(M_DATA_BREADY),
			.M_AXI_BRESP( M_DATA_BRESP),
			// }}}
			// Read interface
			// {{{
			.M_AXI_ARVALID(M_DATA_ARVALID),
			.M_AXI_ARREADY(M_DATA_ARREADY),
			.M_AXI_ARADDR( M_DATA_ARADDR),
			.M_AXI_ARPROT( M_DATA_ARPROT),
			//
			.M_AXI_RVALID(M_DATA_RVALID),
			.M_AXI_RREADY(M_DATA_RREADY),
			.M_AXI_RDATA( i_bus_data),
			.M_AXI_RRESP( M_DATA_RRESP)
			// }}}
			// }}}
		);

		assign	mem_pipe_stalled = mem_busy;
	end endgenerate
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Clock gate
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_CLKGATE)
	begin : GATE_CPU_CLOCK

		reg	gatep;
		reg	gaten /* verilator clock_enable */;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			gatep <= 1'b1;
		else
			gatep <= cpu_clken || arskd_valid || dbg_write_valid
						|| dbg_blkram_stall;

		always @(negedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			gaten <= 1'b1;
		else
			gaten <= gatep;

		assign	cpu_clock = S_AXI_ACLK && gaten;
		assign	clk_gate = gatep;

	end else begin : NO_CLOCK_GATE

		assign	cpu_clock = S_AXI_ACLK;
		assign	clk_gate = 1'b1;

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Simulation only accesses, to make the simulation display work
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	VBENCH_TB
	assign	early_branch = core.dcd_early_branch;
	assign	early_branch_pc = core.dcd_branch_pc;

	assign	dcdA = core.dcd_full_A;
	assign	dcdB = core.dcd_full_B;

	assign	new_pc = core.new_pc;
	assign	cpu_ipc= core.ipc;
	assign	cpu_upc= core.upc;
	assign	pf_pc  = core.pf_pc;

	// assign	pf_cyc = thecpu.pf_cyc;
	// assign	pf_stb = thecpu.pf_stb;
	// assign	pf_we  = thecpu.pf_we;
	// assign	pf_addr= { thecpu.pf_addr, 2'b00 };
	// assign	pf_ack = thecpu.pf_ack;
	// assign	pf_valid = core.i_pf_valid;
	// assign	pf_illegal = core.i_pf_illegal;
	// assign	cpu_idata  = core.i_wb_data;
	// assign	pf_instruction = core.i_pf_instruction;
	// assign	pf_instruction_pc = core.i_pf_instruction_pc;
	//
	// Peeking into the decode stage
	// {{{
	assign	dcd_ce      = core.dcd_ce;
	assign	dcd_stalled = core.dcd_stalled;
	assign	dcd_gie     = core.dcd_gie;
	assign	dcd_valid   = core.dcd_valid;
	assign	dcd_illegal = core.dcd_illegal;
	assign	dcd_phase   = core.dcd_phase;
	assign	dcd_break   = core.dcd_break;
	assign	dcd_pipe    = core.dcd_pipe;
		//
	assign	dcd_opn     = core.dcd_opn;
	assign	dcd_rA      = core.dcd_rA;
	assign	dcd_rB      = core.dcd_rB;
	assign	dcd_wR      = core.dcd_wR;
	assign	dcd_wF      = core.dcd_wF;
	assign	dcdR        = core.instruction_decoder.w_dcdR;
	assign	dcdRpc      = core.instruction_decoder.w_dcdR_pc;
	assign	dcdRcc      = core.instruction_decoder.w_dcdR_cc;
	assign	dcd_pc      = core.dcd_pc;
	assign	dcd_M       = core.dcd_M;
	// }}}
	// Peeking into the op stage
	// {{{
	assign	op_ce        = core.op_ce;
	assign	op_illegal   = core.op_illegal;
	assign	op_valid     = core.op_valid;
	assign	op_valid_mem = core.op_valid_mem;
	assign	op_valid_alu = core.op_valid_alu;
	assign	op_stall     = core.op_stall;
	assign	op_wR        = core.op_wR;
	assign	op_wF        = core.op_wF;
	assign	op_phase     = core.op_phase;
	assign	op_gie       = core.op_gie;
	assign	op_pipe      = core.op_pipe;
	assign	op_R         = core.op_R;
	assign	op_Aid       = core.op_Aid;
	assign	op_Bid       = core.op_Bid;
	assign	op_Av        = core.op_Av;
	assign	op_Bv        = core.op_Bv;
	assign	op_pc        = core.op_pc;
	assign	master_stall = core.master_stall;

	assign	op_F         = core.op_F;
	assign	op_pipe      = core.op_pipe;
	assign	op_opn       = core.op_opn;
	// }}}
	// Peeking into the ALU stage
	// {{{
	assign	alu_ce   = core.alu_ce;
	assign	adf_ce_unconditional   = core.adf_ce_unconditional;
	assign	alu_valid      = core.alu_valid;
	assign	alu_wR         = core.alu_wR;
	assign	alu_wF         = core.alu_wF;
	assign	alu_pc_valid   = core.alu_pc_valid;
	assign	alu_illegal    = core.alu_illegal;
	assign	alu_gie        = core.alu_gie;
	assign	set_cond       = core.set_cond;
	assign	alu_phase      = core.alu_phase;
	assign	alu_flags      = core.alu_flags;
	assign	alu_pc         = core.alu_pc;

	assign	alu_result     = core.alu_result;
	assign	alu_busy       = core.alu_busy;
	assign	alu_reg        = core.alu_reg;
	// }}}
	// Peeking into the MEM stage
	// {{{
	//
	// assign	mem_valid    = core.i_mem_valid;
	assign	mem_pc_valid = core.mem_pc_valid;
	// assign	mem_ce       = core.o_mem_ce;
	// assign	mem_busy     = core.i_mem_busy;
	// assign	mem_rdbusy   = core.i_mem_rdbusy;
	// assign	mem_wreg     = core.i_mem_wreg;
	// }}}
	// Peeking into the divide stage
	// {{{
	assign	div_valid = core.div_valid;
	assign	div_ce    = core.div_ce;
	assign	div_busy  = core.div_busy;
	// }}}
	// Writeback stage
	// {{{
	assign	wr_reg_id = core.wr_reg_id;
	assign	wr_reg_ce = core.wr_reg_ce;
	assign	wr_flags_ce = core.wr_flags_ce;
	assign	wr_gpreg_vl = core.wr_gpreg_vl;
	assign	wr_spreg_vl = core.wr_spreg_vl;
	assign	w_iflags    = core.w_iflags;
	assign	w_uflags    = core.w_uflags;
	// }}}
	// Miscellaneous
	// {{{
	assign	cpu_sim      = core.cpu_sim;
	assign	cpu_sim_immv = core.op_sim_immv;
	assign	r_sleep      = core.sleep;
	assign	master_ce    = core.master_ce;
	assign	op_break     = core.op_break;
	assign	r_gie        = core.gie;
	// }}}
	//
	// ZipSystem peripherals
	// {{{
	assign	watchbus = 32'h0;
	assign	watchdog = 32'h0;
	assign	timer_a = 32'h0;
	assign	timer_b = 32'h0;
	assign	timer_c = 32'h0;
	assign	jiffies = 32'h0;
	assign	wdbus_data = 32'h0;
	assign	pic_data = 32'h0;
	assign	utc_data = 32'h0;
	assign	uoc_data = 32'h0;
	assign	upc_data = 32'h0;
	assign	uic_data = 32'h0;
	assign	mtc_data = 32'h0;
	assign	moc_data = 32'h0;
	assign	mpc_data = 32'h0;
	assign	mic_data = 32'h0;
	//
	assign	int_state = 16'h0;
	assign	alt_int_state = 16'h0;
	// assign	wb_cyc_gbl = mem_cyc_gbl;
	// assign	wb_stb_gbl = mem_stb_gbl;
	// assign	wb_cyc_lcl = mem_cyc_lcl;
	// assign	wb_stb_lcl = mem_stb_lcl;
	// assign	mem_stb_gbl = mem_stb_gbl;
	// assign	mem_stb_lcl = mem_stb_lcl;
	// assign	mem_we     = mem_we;
	// assign	mem_ack    = mem_ack;
	// assign	mem_stall  = mem_stall;
	assign	mem_data   = mem_wdata;
	assign	mem_addr   = { core.o_mem_addr };
	// assign	mem_result = core.i_mem_result;
	assign	switch_to_interrupt = core.w_switch_to_interrupt;
	assign	release_from_interrupt = core.w_release_from_interrupt;
	assign	break_en = core.break_en;
	// }}}
`endif
	// }}}
	// Make Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, cpu_clken, cpu_dbg_cc[2],
			S_DBG_AWADDR[DBGLSB-1:0],
			mem_lock_pc, clear_dcache,
			S_DBG_ARADDR[DBGLSB-1:0],
			S_DBG_ARPROT, S_DBG_AWPROT,
			M_INSN_AWREADY, M_INSN_WREADY,
			M_INSN_BVALID, M_INSN_BRESP
		};
	generate if (32 > ADDRESS_WIDTH)
	begin : GEN_UNUSED_ADDR
		wire	unused_addr;
		assign	unused_addr = &{ 1'b0, mem_cpu_addr[31:ADDRESS_WIDTH] };
	end endgenerate
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
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
	wire	[F_LGDEPTH-1:0]	faxil_rd_outstanding,
				faxil_wr_outstanding, faxil_awr_outstanding;

	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite debug interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_DBG_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_DBG_ADDR_WIDTH),
		.F_LGDEPTH(F_LGDEPTH),
		.F_AXI_MAXWAIT(0),
		.F_AXI_MAXDELAY(0)
		// }}}
	) faxil (
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		// AXI-lite debug writes
		// {{{
		.i_axi_awvalid(S_DBG_AWVALID),
		.i_axi_awready(S_DBG_AWREADY),
		.i_axi_awaddr(S_DBG_AWADDR),
		.i_axi_awprot(S_DBG_AWPROT),
		//
		.i_axi_wvalid(S_DBG_WVALID),
		.i_axi_wready(S_DBG_WREADY),
		.i_axi_wdata(S_DBG_WDATA),
		.i_axi_wstrb(S_DBG_WSTRB),
		//
		.i_axi_bvalid(S_DBG_BVALID),
		.i_axi_bready(S_DBG_BREADY),
		.i_axi_bresp(S_DBG_BRESP),
		// }}}
		// AXI-lite debug reads
		// {{{
		.i_axi_arvalid(S_DBG_ARVALID),
		.i_axi_arready(S_DBG_ARREADY),
		.i_axi_araddr(S_DBG_ARADDR),
		.i_axi_arprot(S_DBG_ARPROT),
		//
		.i_axi_rvalid(S_DBG_RVALID),
		.i_axi_rready(S_DBG_RREADY),
		.i_axi_rdata(S_DBG_RDATA),
		.i_axi_rresp(S_DBG_RRESP),
		// }}}
		// Induction
		// {{{
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(faxil_rd_outstanding == (S_DBG_ARREADY ? 0:1)
				+(dbg_read_valid ? 1:0) + (S_DBG_RVALID ? 1:0));

		assert(!dbg_read_valid || !S_DBG_RVALID);

		assert(faxil_wr_outstanding == (S_DBG_WREADY ? 0:1)
				+(S_DBG_BVALID ? 1:0));

		assert(faxil_awr_outstanding == (S_DBG_AWREADY ? 0:1)
				+(S_DBG_BVALID ? 1:0));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CPU's debug interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Captured above

	// }}}
`endif
// }}}
endmodule
