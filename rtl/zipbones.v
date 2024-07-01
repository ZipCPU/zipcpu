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
module	zipbones #(
		// {{{
		parameter	RESET_ADDRESS=32'h1000_0000,
				ADDRESS_WIDTH=32,
		parameter	BUS_WIDTH=32,	// Bus data width
		// CPU options
		// {{{
		parameter [0:0]	OPT_PIPELINED=1,
		parameter [0:0]	OPT_EARLY_BRANCHING=OPT_PIPELINED,
		// OPT_LGICACHE
		// {{{
		parameter	OPT_LGICACHE = 2,
		// }}}
		// OPT_LGDCACHE
		// {{{
		// Set to zero for no data cache
		parameter	OPT_LGDCACHE = 0,
		// }}}
		parameter [0:0]	START_HALTED=1,
		parameter [0:0]	OPT_DISTRIBUTED_REGS=1,
		// OPT_MPY
		// {{{
		parameter	OPT_MPY = 3,
		// }}}
		// OPT_DIV
		// {{{
		parameter [0:0]	OPT_DIV=1,
		// }}}
		// OPT_SHIFTS
		// {{{
		parameter [0:0]	OPT_SHIFTS = 1,
		// }}}
		// OPT_FPU
		// {{{
		parameter [0:0]	OPT_FPU = 0,
		// }}}
		parameter [0:0]	OPT_CIS=1,
		parameter [0:0]	OPT_LOCK=1,
		parameter [0:0]	OPT_USERMODE=1,
		parameter [0:0]	OPT_DBGPORT=START_HALTED,
		parameter [0:0]	OPT_TRACE_PORT=1,
		parameter [0:0]	OPT_PROFILER=0,
		parameter [0:0]	OPT_LOWPOWER=0,
`ifdef	VERILATOR
		parameter [0:0]	OPT_SIM=1'b1,
		parameter [0:0]	OPT_CLKGATE = OPT_LOWPOWER,
`else
		parameter [0:0]	OPT_SIM=1'b0,
		parameter [0:0]	OPT_CLKGATE = 1'b0,
`endif
		// }}}
		parameter	RESET_DURATION = 10,
		// Short-cut names
		// {{{
		// localparam	AW=ADDRESS_WIDTH,
		localparam	DBG_WIDTH=32,	// Debug bus data width
		localparam	// Derived parameters
				// PHYSICAL_ADDRESS_WIDTH=ADDRESS_WIDTH,
				PAW=ADDRESS_WIDTH-$clog2(BUS_WIDTH/8)
`ifdef	OPT_MMU
				// VIRTUAL_ADDRESS_WIDTH=30,
`else
				// VIRTUAL_ADDRESS_WIDTH=PAW,
`endif
				// LGTLBSZ = 6,
				// VAW=VIRTUAL_ADDRESS_WIDTH,

		// }}}
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Wishbone master interface from the CPU
		// {{{
		output	wire			o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire [PAW-1:0]		o_wb_addr,
		output	wire [BUS_WIDTH-1:0]	o_wb_data,
		output	wire [BUS_WIDTH/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall, i_wb_ack,
		input	wire [BUS_WIDTH-1:0]	i_wb_data,
		input	wire			i_wb_err,
		// }}}
		// Incoming interrupts
		input	wire			i_ext_int,
		// Our one outgoing interrupt
		output	wire			o_ext_int,
		// Wishbone slave interface for debugging purposes
		// {{{
		input	wire			i_dbg_cyc, i_dbg_stb, i_dbg_we,
		input	wire	[5:0]		i_dbg_addr,
		input	wire [DBG_WIDTH-1:0]	i_dbg_data,
		input	wire [DBG_WIDTH/8-1:0]	i_dbg_sel,
		output	wire			o_dbg_stall,
		output	wire			o_dbg_ack,
		output	wire [DBG_WIDTH-1:0]	o_dbg_data,
		// }}}
		output	wire	[31:0]		o_cpu_debug,
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
		output	wire			pf_cyc, pf_stb, pf_we,
		output	wire	[31:0]		pf_addr,
		output	wire			pf_ack,
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
		output	wire			wb_cyc_gbl, wb_cyc_lcl,
						wb_stb_gbl, wb_stb_lcl,
						mem_stb_gbl, mem_stb_lcl,
						mem_we, mem_ack, mem_stall,
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
		output	wire			pformem_owner,
		// }}}
`endif
		output	wire			o_prof_stb,
		output wire [ADDRESS_WIDTH-1:0]	o_prof_addr,
		output	wire	[31:0]		o_prof_ticks
		// }}}
	);

	// Declarations
	// {{{
	localparam	[0:0]	DBG_ADDR_CTRL = 1'b0,
				DBG_ADDR_CPU  = 1'b1;

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

	wire			cpu_clken;
	wire			dbg_cyc, dbg_stb, dbg_we, dbg_stall;
	wire	[5:0]		dbg_addr;
	wire	[DBG_WIDTH-1:0]	dbg_idata;
	wire [DBG_WIDTH/8-1:0]	dbg_sel;
	reg	[DBG_WIDTH-1:0]	dbg_odata;
	reg			dbg_ack;
	wire			cpu_break, dbg_cmd_write,
				dbg_cpu_write, dbg_cpu_read;
	wire			reset_hold, halt_on_fault, dbg_catch;
	wire			reset_request, release_request, halt_request,
				step_request, clear_cache_request;
	reg			cmd_reset, cmd_halt, cmd_step, cmd_clear_cache,
				cmd_write, cmd_read;
	reg	[2:0]		cmd_read_ack;

	reg	[4:0]		cmd_waddr;
	reg	[DBG_WIDTH-1:0]	cmd_wdata;
	wire	[2:0]		cpu_dbg_cc;

	wire			cpu_reset, cpu_halt, cpu_dbg_stall,
				cpu_has_halted;
	wire			cpu_lcl_cyc, cpu_lcl_stb,
				cpu_op_stall, cpu_pf_stall, cpu_i_count;
	wire	[DBG_WIDTH-1:0]	cpu_dbg_data;
	wire	[DBG_WIDTH-1:0]	cpu_status;

	wire	[DBG_WIDTH-1:0]	dbg_cmd_data;
	wire [DBG_WIDTH/8-1:0]	dbg_cmd_strb;
	reg			dbg_pre_ack;
	reg	[DBG_WIDTH-1:0]	dbg_cpu_status;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug bus signal renaming
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	dbg_cyc     = i_dbg_cyc;
	assign	dbg_stb     = i_dbg_stb;
	assign	dbg_we      = i_dbg_we;
	assign	dbg_addr    = i_dbg_addr;
	assign	dbg_idata   = i_dbg_data;
	assign	dbg_sel     = i_dbg_sel;
	assign	o_dbg_ack   = dbg_ack;
	assign	o_dbg_stall = dbg_stall;
	assign	o_dbg_data  = dbg_odata;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The external debug interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	dbg_cpu_write = OPT_DBGPORT && (dbg_stb && !dbg_stall && dbg_we)
				&& (dbg_addr[5] == DBG_ADDR_CPU)
				&& dbg_sel == 4'hf;
	assign	dbg_cpu_read = (dbg_stb && !dbg_stall && !dbg_we
				&& dbg_addr[5] == DBG_ADDR_CPU);
	assign	dbg_cmd_write = (dbg_stb && !dbg_stall && dbg_we)
					&&(dbg_addr[5] == DBG_ADDR_CTRL);
	assign	dbg_cmd_data = dbg_idata;
	assign	dbg_cmd_strb = dbg_sel;


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
		always @(posedge i_clk)
		if (i_reset)
			reset_counter <= RESET_DURATION;
		else if (reset_counter > 0)
			reset_counter <= reset_counter - 1;

		initial	r_reset_hold = 1;
		always @(posedge i_clk)
		if (i_reset)
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
	always @(posedge i_clk)
	if (i_reset)
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
	always @(posedge i_clk)
	if (i_reset)
		cmd_halt <= START_HALTED;
	else if (cmd_reset && START_HALTED)
		cmd_halt <= START_HALTED;
	else begin
		// {{{
		// When shall we release from a halt?  Only if we have
		// come to a full and complete stop.  Even then, we only
		// release if we aren't being given a command to step the CPU.
		//
		if (!cmd_write && cpu_has_halted && dbg_cmd_write
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
	always @(posedge i_clk)
	if (i_reset || cpu_reset)
		cmd_clear_cache <= 1'b0;
	else if (dbg_cmd_write && clear_cache_request && halt_request)
		cmd_clear_cache <= 1'b1;
	else if (cmd_halt && !cpu_dbg_stall)
		cmd_clear_cache <= 1'b0;
	// }}}

	// cmd_step
	// {{{
	initial	cmd_step = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cmd_step <= 1'b0;
	else if (cmd_reset || cpu_break
			|| reset_request
			|| clear_cache_request || cmd_clear_cache
			|| halt_request || dbg_cpu_write)
		cmd_step <= 1'b0;
	else if (!cmd_write && cpu_has_halted && step_request)
		cmd_step <= 1'b1;
	else // if (cpu_dbg_stall)
		cmd_step <= 1'b0;
`ifdef	FORMAL
	// While STEP is true, we can't halt
	always @(*)
	if (!i_reset && cmd_step)
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
		always @(posedge i_clk)
		if (i_reset)
			r_dbg_catch <= START_HALTED;
		else if (dbg_cmd_write && dbg_cmd_strb[CATCH_BIT/8])
			r_dbg_catch <= dbg_cmd_data[CATCH_BIT];

		assign	dbg_catch = r_dbg_catch;
	end endgenerate
	// }}}

	assign	cpu_reset = (cmd_reset);
	assign	cpu_halt = (cmd_halt);

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
			cpu_break, i_ext_int, cpu_dbg_cc[1:0],
			2'h0, dbg_catch, 1'b0,
			cmd_reset, 1'b0, !cpu_dbg_stall, cmd_halt
		};

	// }}}

	// cmd_write
	// {{{
	initial	cmd_write = 0;
	always @(posedge i_clk)
	if (i_reset || cpu_reset)
		cmd_write <= 1'b0;
	else if (!cmd_write || cpu_has_halted)
		cmd_write <= dbg_cpu_write;
	// }}}

	// cmd_read
	// {{{
	initial	cmd_read = 0;
	always @(posedge i_clk)
	if (i_reset || !dbg_cyc || !OPT_DBGPORT)
		cmd_read <= 1'b0;
	else if (dbg_cpu_read)
		cmd_read <= 1'b1;
	else if (cmd_read_ack == 1)
		cmd_read <= 1'b0;

	initial	cmd_read_ack = 0;
	always @(posedge i_clk)
	if (i_reset || !dbg_cyc || !OPT_DBGPORT)
		cmd_read_ack <= 0;
	else if (dbg_cpu_read)
		cmd_read_ack <= 2 + (OPT_DISTRIBUTED_REGS ? 0:1);
	else if (cmd_read_ack > 0)
		cmd_read_ack <= cmd_read_ack - 1;
	// }}}

	// cmd_waddr, cmd_wdata
	// {{{
	always @(posedge i_clk)
	if ((!cmd_write || cpu_has_halted) && dbg_cpu_write)
	begin
		cmd_waddr <= dbg_addr[4:0];
		cmd_wdata <= dbg_idata;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The CPU itself
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	cpu_clken = cmd_write || cmd_read || dbg_cyc;
`ifdef	FORMAL
	// {{{
	(* anyseq *)	reg	f_cpu_halted, f_cpu_data, f_cpu_stall,
				f_cpu_break;
	(* anyseq *) reg [2:0]	f_cpu_dbg_cc;
	(* anyseq *) reg [31:0]	f_cpu_dbg_data;

	assign	cpu_dbg_stall = f_cpu_stall && !f_cpu_halted;
	assign	cpu_break     = f_cpu_break;
	assign	cpu_dbg_cc    = f_cpu_dbg_cc;
	assign	cpu_dbg_data  = f_cpu_dbg_data;
	assign	cpu_has_halted= f_cpu_halted;

	fdebug #(
		// {{{
		.OPT_START_HALTED(START_HALTED),
		.OPT_DISTRIBUTED_RAM(OPT_DISTRIBUTED_REGS)
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
	// }}}
`else
	zipwb	#(
		// {{{
		.RESET_ADDRESS(RESET_ADDRESS),
		.ADDRESS_WIDTH(ADDRESS_WIDTH-$clog2(BUS_WIDTH/8)),
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_PIPELINED(OPT_PIPELINED),
		.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
		.OPT_LGICACHE(OPT_LGICACHE),
		.OPT_LGDCACHE(OPT_LGDCACHE),
		.OPT_MPY(OPT_MPY),
		.OPT_DIV(OPT_DIV),
		.OPT_SHIFTS(OPT_SHIFTS),
		.IMPLEMENT_FPU(OPT_FPU),
		.OPT_CIS(OPT_CIS),
		.OPT_LOCK(OPT_LOCK),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_START_HALTED(START_HALTED),
		.OPT_SIM(OPT_SIM),
		.OPT_DBGPORT(OPT_DBGPORT),
		.OPT_TRACE_PORT(OPT_TRACE_PORT),
		.OPT_PROFILER(OPT_PROFILER),
		.OPT_CLKGATE(OPT_CLKGATE),
		.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
		.OPT_USERMODE(OPT_USERMODE),
		.WITH_LOCAL_BUS(0)
		// }}}
	) thecpu(
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset), .i_interrupt(i_ext_int),
			.i_cpu_clken(cpu_clken),
		// Debug interface
		// {{{
		.i_halt(cpu_halt), .i_clear_cache(cmd_clear_cache),
				.i_dbg_wreg(cmd_waddr), .i_dbg_we(cmd_write),
				.i_dbg_data(cmd_wdata),
				.i_dbg_rreg(dbg_addr[4:0]),
			.o_dbg_stall(cpu_dbg_stall),
			.o_halted(cpu_has_halted),
			.o_dbg_reg(cpu_dbg_data),
			.o_dbg_cc(cpu_dbg_cc),
			.o_break(cpu_break),
		// }}}
		// Wishbone bus interface
		// {{{
		.o_wb_gbl_cyc(o_wb_cyc), .o_wb_gbl_stb(o_wb_stb),
			.o_wb_lcl_cyc(cpu_lcl_cyc),
			.o_wb_lcl_stb(cpu_lcl_stb),
			.o_wb_we(o_wb_we), .o_wb_addr(o_wb_addr),
			.o_wb_data(o_wb_data), .o_wb_sel(o_wb_sel),
		// Return values from the Wishbone bus
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
				.i_wb_data(i_wb_data),
				.i_wb_err((i_wb_err)||(cpu_lcl_cyc)),
		// }}}
			.o_op_stall(cpu_op_stall), .o_pf_stall(cpu_pf_stall),
				.o_i_count(cpu_i_count),
		.o_debug(o_cpu_debug),
		//
		.o_prof_stb(o_prof_stb),
		.o_prof_addr(o_prof_addr),
		.o_prof_ticks(o_prof_ticks)
		// }}}
	);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Return debug response values
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// always @(posedge i_clk)
	//	dbg_pre_addr <= dbg_addr[5];

	always @(posedge i_clk)
		dbg_cpu_status <= cpu_status;

	initial	dbg_pre_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_dbg_cyc)
		dbg_pre_ack <= 1'b0;
	else
		dbg_pre_ack <= dbg_stb && !dbg_stall && !dbg_cpu_read;

	initial dbg_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_dbg_cyc)
		dbg_ack <= 1'b0;
	else
		dbg_ack <= dbg_pre_ack || (cmd_read_ack == 1);

	always @(posedge i_clk)
	if (!OPT_LOWPOWER || dbg_pre_ack || cmd_read)
	begin
		if (cmd_read)
			dbg_odata <= cpu_dbg_data;
		else
			dbg_odata <= dbg_cpu_status;
	end

	assign	dbg_stall = cmd_read || (cmd_write && cpu_dbg_stall
			&& dbg_addr[5] == DBG_ADDR_CPU);
	// }}}

	assign	o_ext_int = (cmd_halt) && (!i_wb_stall);
	////////////////////////////////////////////////////////////////////////
	//
	// Simulation only accesses, to make the simulation display work
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	VBENCH_TB
	assign	early_branch = thecpu.core.dcd_early_branch;
	assign	early_branch_pc = thecpu.core.dcd_branch_pc;

	assign	dcdA = thecpu.core.dcd_full_A;
	assign	dcdB = thecpu.core.dcd_full_B;

	assign	new_pc = thecpu.core.new_pc;
	assign	cpu_ipc= thecpu.core.ipc;
	assign	cpu_upc= thecpu.core.upc;
	assign	pf_pc  = thecpu.core.pf_pc;

	assign	pf_cyc = thecpu.pf_cyc;
	assign	pf_stb = thecpu.pf_stb;
	assign	pf_we  = thecpu.pf_we;
	assign	pf_addr= { thecpu.pf_addr, 2'b00 };
	assign	pf_ack = thecpu.pf_ack;
	assign	pf_valid = thecpu.pf_valid;
	assign	pf_illegal = thecpu.pf_illegal;
	// assign	cpu_idata  = thecpu.i_wb_data;
	assign	pf_instruction = thecpu.pf_instruction;
	assign	pf_instruction_pc = thecpu.pf_instruction_pc;
	generate if (OPT_PIPELINED)
	begin : GEN_PFORMEM_OWNER_DATA
		assign	pformem_owner = thecpu.PRIORITY_DATA.pformem.r_a_owner;
	end else begin : GEN_PFORMEM_OWNER_FETCH
		assign	pformem_owner = thecpu.PRIORITY_PREFETCH.pformem.r_a_owner;
	end endgenerate
	//
	// Peeking into the decode stage
	// {{{
	assign	dcd_ce      = thecpu.core.dcd_ce;
	assign	dcd_stalled = thecpu.core.dcd_stalled;
	assign	dcd_gie     = thecpu.core.dcd_gie;
	assign	dcd_valid   = thecpu.core.dcd_valid;
	assign	dcd_illegal = thecpu.core.dcd_illegal;
	assign	dcd_phase   = thecpu.core.dcd_phase;
	assign	dcd_break   = thecpu.core.dcd_break;
	assign	dcd_pipe    = thecpu.core.dcd_pipe;
		//
	assign	dcd_opn     = thecpu.core.dcd_opn;
	assign	dcd_rA      = thecpu.core.dcd_rA;
	assign	dcd_rB      = thecpu.core.dcd_rB;
	assign	dcd_wR      = thecpu.core.dcd_wR;
	assign	dcd_wF      = thecpu.core.dcd_wF;
	assign	dcdR        = thecpu.core.instruction_decoder.w_dcdR;
	assign	dcdRpc      = thecpu.core.instruction_decoder.w_dcdR_pc;
	assign	dcdRcc      = thecpu.core.instruction_decoder.w_dcdR_cc;
	assign	dcd_pc      = thecpu.core.dcd_pc;
	assign	dcd_M       = thecpu.core.dcd_M;
	// }}}
	// Peeking into the op stage
	// {{{
	assign	op_ce        = thecpu.core.op_ce;
	assign	op_illegal   = thecpu.core.op_illegal;
	assign	op_valid     = thecpu.core.op_valid;
	assign	op_valid_mem = thecpu.core.op_valid_mem;
	assign	op_valid_alu = thecpu.core.op_valid_alu;
	assign	op_stall     = thecpu.core.op_stall;
	assign	op_wR        = thecpu.core.op_wR;
	assign	op_wF        = thecpu.core.op_wF;
	assign	op_phase     = thecpu.core.op_phase;
	assign	op_gie       = thecpu.core.op_gie;
	assign	op_pipe      = thecpu.core.op_pipe;
	assign	op_R         = thecpu.core.op_R;
	assign	op_Aid       = thecpu.core.op_Aid;
	assign	op_Bid       = thecpu.core.op_Bid;
	assign	op_Av        = thecpu.core.op_Av;
	assign	op_Bv        = thecpu.core.op_Bv;
	assign	op_pc        = thecpu.core.op_pc;
	assign	master_stall = thecpu.core.master_stall;

	assign	op_F         = thecpu.core.op_F;
	assign	op_pipe      = thecpu.core.op_pipe;
	assign	op_opn       = thecpu.core.op_opn;
	// }}}
	// Peeking into the ALU stage
	// {{{
	assign	alu_ce   = thecpu.core.alu_ce;
	assign	adf_ce_unconditional   = thecpu.core.adf_ce_unconditional;
	assign	alu_valid   = thecpu.core.alu_valid;
	assign	alu_wR   = thecpu.core.alu_wR;
	assign	alu_wF   = thecpu.core.alu_wF;
	assign	alu_pc_valid   = thecpu.core.alu_pc_valid;
	assign	alu_illegal    = thecpu.core.alu_illegal;
	assign	alu_gie        = thecpu.core.alu_gie;
	assign	set_cond       = thecpu.core.set_cond;
	assign	alu_phase      = thecpu.core.alu_phase;
	assign	alu_flags      = thecpu.core.alu_flags;
	assign	alu_pc         = thecpu.core.alu_pc;

	assign	alu_result     = thecpu.core.alu_result;
	assign	alu_busy       = thecpu.core.alu_busy;
	assign	alu_reg        = thecpu.core.alu_reg;
	// }}}
	// Peeking into the MEM stage
	// {{{
	//
	assign	mem_valid    = thecpu.mem_valid;
	assign	mem_pc_valid = thecpu.core.mem_pc_valid;
	assign	mem_ce       = thecpu.core.o_mem_ce;
	assign	mem_busy     = thecpu.core.i_mem_busy;
	assign	mem_rdbusy   = thecpu.core.i_mem_rdbusy;
	assign	mem_wreg     = thecpu.core.i_mem_wreg;
	// }}}
	// Peeking into the divide stage
	// {{{
	assign	div_valid = thecpu.core.div_valid;
	assign	div_ce    = thecpu.core.div_ce;
	assign	div_busy  = thecpu.core.div_busy;
	// }}}
	// Writeback stage
	// {{{
	assign	wr_reg_id = thecpu.core.wr_reg_id;
	assign	wr_reg_ce = thecpu.core.wr_reg_ce;
	assign	wr_flags_ce = thecpu.core.wr_flags_ce;
	assign	wr_gpreg_vl = thecpu.core.wr_gpreg_vl;
	assign	wr_spreg_vl = thecpu.core.wr_spreg_vl;
	assign	w_iflags    = thecpu.core.w_iflags;
	assign	w_uflags    = thecpu.core.w_uflags;
	// }}}
	// Miscellaneous
	// {{{
	assign	cpu_sim      = thecpu.core.cpu_sim;
	assign	cpu_sim_immv = thecpu.core.op_sim_immv;
	assign	r_sleep      = thecpu.core.sleep;
	assign	master_ce    = thecpu.core.master_ce;
	assign	op_break     = thecpu.core.op_break;
	assign	r_gie        = thecpu.core.gie;
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
	assign	wb_cyc_gbl = thecpu.mem_cyc_gbl;
	assign	wb_stb_gbl = thecpu.mem_stb_gbl;
	assign	wb_cyc_lcl = thecpu.mem_cyc_lcl;
	assign	wb_stb_lcl = thecpu.mem_stb_lcl;
	assign	mem_stb_gbl = thecpu.mem_stb_gbl;
	assign	mem_stb_lcl = thecpu.mem_stb_lcl;
	assign	mem_we     = thecpu.mem_we;
	assign	mem_ack    = thecpu.mem_ack;
	assign	mem_stall  = thecpu.mem_stall;
	assign	mem_data   = thecpu.mem_data;
	assign	mem_addr   = { thecpu.core.o_mem_addr };
	assign	mem_result = thecpu.mem_result;
	assign	switch_to_interrupt = thecpu.core.w_switch_to_interrupt;
	assign	release_from_interrupt = thecpu.core.w_release_from_interrupt;
	assign	break_en = thecpu.core.break_en;
	// }}}
`endif
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, dbg_cyc, cpu_lcl_stb, cpu_op_stall,
			cpu_dbg_cc[2], cpu_pf_stall, cpu_i_count };
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
	wire			cpu_dbg_we;

	assign cpu_dbg_we = (dbg_stb && !dbg_stall && dbg_we
					&&(dbg_addr[5] == DBG_ADDR_CPU));

	fwb_slave #(
		.AW(6), .DW(DBG_WIDTH), .F_LGDEPTH(F_LGDEPTH)
	) fwb(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(i_dbg_cyc), .i_wb_stb(i_dbg_stb && !o_dbg_stall),
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
	begin
		if (cmd_read_ack > 0)
		begin
			assert(!dbg_pre_ack);
			assert(fwb_outstanding == 1 + (o_dbg_ack ? 1:0));
		end else
			assert(fwb_outstanding == dbg_pre_ack + o_dbg_ack);
	end

	always @(posedge i_clk)
	if ($past(i_dbg_cyc && cpu_dbg_we))
		assume(i_dbg_cyc);
`endif
// }}}
endmodule
