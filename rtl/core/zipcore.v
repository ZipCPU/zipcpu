////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipcore.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:
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
module	zipcore #(
		// {{{
		parameter	ADDRESS_WIDTH=30,	// 32-b word addr width
		parameter [31:0] RESET_ADDRESS=32'h010_0000,
		parameter	OPT_MPY = 0,
		parameter [0:0]	OPT_SHIFTS = 1,
		parameter [0:0]	OPT_DIV = 1,
		parameter [0:0]	IMPLEMENT_FPU = 0,
		parameter [0:0]	OPT_EARLY_BRANCHING = 1,
		parameter [0:0]	OPT_CIS = 1'b1,
		parameter [0:0]	OPT_SIM = 1'b0,
		parameter [0:0]	OPT_DISTRIBUTED_REGS = 1'b1,
		parameter	[0:0]	OPT_PIPELINED = 1'b1,
		parameter	[0:0]	OPT_PIPELINED_BUS_ACCESS = (OPT_PIPELINED),
		parameter	[0:0]	OPT_LOCK=1,
		parameter	[0:0]	OPT_DCACHE = 1,
		parameter	[0:0]	OPT_USERMODE = 1'b1,
		parameter	[0:0]	OPT_LOWPOWER = 1'b0,
		parameter	[0:0]	OPT_CLKGATE = 1'b1,
		parameter	[0:0]	OPT_START_HALTED = 1'b1,
		parameter	[0:0]	OPT_DBGPORT = 1'b1,
		parameter	[0:0]	OPT_TRACE_PORT = 1'b0,
		parameter	[0:0]	OPT_PROFILER = 1'b0,

		localparam	AW=ADDRESS_WIDTH
`ifdef	FORMAL
		, parameter	F_LGDEPTH=4
`endif
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset, i_interrupt,
		output	wire		o_clken,
		// Debug interface
		// {{{
		input	wire		i_halt, i_clear_cache,
		input	wire	[4:0]	i_dbg_wreg,
		input	wire		i_dbg_we,
		input	wire	[31:0]	i_dbg_data,
		input	wire	[4:0]	i_dbg_rreg,
		//
		output	wire		o_dbg_stall,
		output	wire	[31:0]	o_dbg_reg,
		output	reg	[2:0]	o_dbg_cc,
		output	wire		o_break,
		// }}}
		// Instruction fetch interface
		// {{{
		output	wire		o_pf_new_pc,
		output	wire		o_clear_icache,
		output	wire		o_pf_ready,
		output	wire [(AW+1):0]	o_pf_request_address,
		input	wire		i_pf_valid, i_pf_illegal,
		input	wire [31:0]	i_pf_instruction,
		input	wire [(AW+1):0]	i_pf_instruction_pc,
		// }}}
		// Memory unit interface
		// {{{
		output	wire		o_clear_dcache,
		output	wire		o_mem_ce,
		output	wire		o_bus_lock,
		output	wire [2:0]	o_mem_op,
		output	wire [31:0]	o_mem_addr,
		output	wire [31:0]	o_mem_data,
		output	wire [AW+1:0]	o_mem_lock_pc,
		output	wire [4:0]	o_mem_reg,
		input	wire 		i_mem_busy, i_mem_rdbusy,
					i_mem_pipe_stalled, i_mem_valid,
		input	wire		i_bus_err,
		input	wire [4:0]	i_mem_wreg,
		input	wire [31:0]	i_mem_result,
		// }}}
		// Accounting outputs ... to help us count stalls and usage
		// {{{
		output	wire		o_op_stall,
		output	wire		o_pf_stall,
		output	wire		o_i_count,
		// }}}
		// Debug data for on-line/live tracing
		// {{{
		output	wire	[31:0]	o_debug,
		//}}}
		// (Optional) Profiler data
		// {{{
		output	wire		o_prof_stb,
		output	wire [AW+1:0]	o_prof_addr,
		output	wire [31:0]	o_prof_ticks
		// }}}
		// }}}
	);

	// Local parameter definitions
	// {{{
	// Verilator lint_off UNUSED
	localparam	[0:0]	OPT_MEMPIPE = OPT_PIPELINED_BUS_ACCESS;
	localparam [(AW-1):0]	RESET_BUS_ADDRESS = RESET_ADDRESS[AW+1:2];
	localparam	[3:0]	CPU_CC_REG = 4'he,
				CPU_PC_REG = 4'hf;
	localparam	[3:0]	CPU_SUB_OP = 4'h0,// also a compare instruction
				CPU_AND_OP = 4'h1,// also a test instruction
				CPU_BREV_OP= 4'h8,
				CPU_MOV_OP = 4'hd;
	localparam	CPU_CLRDCACHE_BIT=15, // Set to clr D-cache,auto clears
			CPU_CLRICACHE_BIT=14, // Set to clr I-cache,auto clears
			CPU_PHASE_BIT   = 13, // Set on last half of a CIS
			CPU_FPUERR_BIT  = 12, // Set on floating point error
			CPU_DIVERR_BIT  = 11, // Set on divide error
			CPU_BUSERR_BIT  = 10, // Set on bus error
			CPU_TRAP_BIT    =  9, // User TRAP has taken place
			CPU_ILL_BIT     =  8, // Illegal instruction
			CPU_BREAK_BIT   =  7,
			CPU_STEP_BIT    =  6, // Will step one (or two CIS) ins
			CPU_GIE_BIT     =  5,
			CPU_SLEEP_BIT   =  4;
	// Verilator lint_on  UNUSED
	// }}}

	// Register declarations
	// {{{
	//	The distributed RAM style comment is necessary on the
	// SPARTAN6 with XST to prevent XST from oversimplifying the register
	// set and in the process ruining everything else.  It basically
	// optimizes logic away, to where it no longer works.  The logic
	// as described herein will work, this just makes sure XST implements
	// that logic.
	//
	// (* ram_style = "distributed" *)
	reg	[31:0]	regset	[0:(OPT_USERMODE)? 31:15];

	// Condition codes
	// (BUS, TRAP,ILL,BREAKEN,STEP,GIE,SLEEP ), V, N, C, Z
	reg	[3:0]	flags, iflags;
	wire	[15:0]	w_uflags, w_iflags;
	reg		break_en, user_step, sleep, r_halted;
	wire		break_pending, trap, gie, ubreak, pending_interrupt,
			stepped;
	wire		step;
	wire		ill_err_u;
	reg		ill_err_i;
	reg		ibus_err_flag;
	wire		ubus_err_flag;
	wire		idiv_err_flag, udiv_err_flag;
	// Verilator coverage_off
	wire		ifpu_err_flag, ufpu_err_flag;
	// Verilator coverage_on
	wire		ihalt_phase, uhalt_phase;

	// The master chip enable
	wire		master_ce, master_stall;
	//

	//
	//	PIPELINE STAGE #1 :: Prefetch
	//		Variable declarations
	//
	// {{{
	reg	[(AW+1):0]	pf_pc;
	reg			new_pc;
	wire			clear_pipeline;

	reg			dcd_stalled;
	// wire			pf_cyc, pf_stb, pf_we, pf_stall, pf_ack, pf_err;
	// wire	[(AW-1):0]	pf_addr;
	// wire			pf_valid, pf_gie, pf_illegal;
	wire			pf_gie;
`ifdef	FORMAL
	wire	[31:0]		f_dcd_insn_word;
	wire			f_dcd_insn_gie;
	wire			f_dcd_insn_is_pipeable;
	reg	[31:0]		f_op_insn_word;
	reg	[31:0]		f_alu_insn_word;
`endif

	assign	clear_pipeline = new_pc;
	// }}}

	//
	//	PIPELINE STAGE #2 :: Instruction Decode
	//		Variable declarations
	//
	//
	// {{{
	wire	[3:0]	dcd_opn;
	wire		dcd_ce, dcd_phase;
	wire	[4:0]	dcd_A, dcd_B, dcd_R, dcd_preA, dcd_preB;
	wire		dcd_Acc, dcd_Bcc, dcd_Apc, dcd_Bpc, dcd_Rcc, dcd_Rpc;
	wire	[3:0]	dcd_F;
	wire		dcd_wR, dcd_rA, dcd_rB,
				dcd_ALU, dcd_M, dcd_DIV, dcd_FP,
				dcd_wF, dcd_gie, dcd_break, dcd_lock,
				dcd_pipe, dcd_ljmp;
	wire		dcd_valid;
	wire [AW+1:0]	dcd_pc /* verilator public_flat */;
	wire	[31:0]	dcd_I;
	wire		dcd_zI;	// true if dcd_I == 0
	wire		dcd_A_stall, dcd_B_stall, dcd_F_stall;

	wire		dcd_illegal;
	wire		dcd_early_branch, dcd_early_branch_stb;
	wire [(AW+1):0]	dcd_branch_pc;

	wire		dcd_sim;
	wire	[22:0]	dcd_sim_immv;
	wire		prelock_stall, last_lock_insn;
	wire		cc_invalid_for_dcd;
	wire		pending_sreg_write;
	// }}}


	//
	//
	//	PIPELINE STAGE #3 :: Read Operands
	//		Variable declarations
	//
	//
	//
	// {{{
	// Now, let's read our operands
	reg		op_valid /* verilator public_flat */,
			op_valid_mem, op_valid_alu;
	reg		op_valid_div, op_valid_fpu;
	wire		op_stall;
	wire	[3:0]	op_opn;
	wire	[4:0]	op_R;
	reg		op_Rcc;
	wire	[4:0]	op_Aid, op_Bid;
	wire		op_rA, op_rB;
	reg	[31:0]	r_op_Av, r_op_Bv;
	wire	[AW+1:0]	op_pc;
	wire	[31:0]	w_op_Av, w_op_Bv, op_Av, op_Bv;
	reg	[31:0]	w_pcB_v, w_pcA_v;
	reg	[31:0]	w_op_BnI;
	wire		op_wR;
	reg		op_wF;
	wire		op_gie;
	wire	[3:0]	op_Fl;
	reg	[6:0]	r_op_F;
	wire	[7:0]	op_F;
	wire		op_ce, op_phase, op_pipe;
	reg		r_op_break;
	wire		w_op_valid;
	wire		op_lowpower_clear;
	wire	[8:0]	w_cpu_info;
	// Some pipeline control wires
	reg	op_illegal;
	wire	op_break;
	wire	op_lock;

	wire		op_sim		/* verilator public_flat */;
	wire	[22:0]	op_sim_immv	/* verilator public_flat */;
	wire		alu_sim		/* verilator public_flat */;
	wire	[22:0]	alu_sim_immv	/* verilator public_flat */;
	// }}}


	//
	//
	//	PIPELINE STAGE #4 :: ALU / Memory
	//		Variable declarations
	//
	//
	// {{{
	wire	[(AW+1):0]	alu_pc;
	reg	[4:0]	alu_reg;
	reg		r_alu_pc_valid, mem_pc_valid;
	wire		alu_pc_valid;
	wire		alu_phase;
	wire		alu_ce /* verilator public_flat */, alu_stall;
	wire	[31:0]	alu_result;
	wire	[3:0]	alu_flags;
	wire		alu_valid, alu_busy;
	wire		set_cond;
	reg		alu_wR, alu_wF;
	wire		alu_gie, alu_illegal;


	wire			mem_ce, mem_stalled;

	wire		div_ce, div_error, div_busy, div_valid;
	wire	[31:0]	div_result;
	wire	[3:0]	div_flags;

	// Verilator coverage_off
	wire		fpu_ce, fpu_error, fpu_busy, fpu_valid;
	wire	[31:0]	fpu_result;
	wire	[3:0]	fpu_flags;
	// Verilator coverage_on
	reg		adf_ce_unconditional;


	reg		dbgv, dbg_clear_pipe;
	reg	[31:0]	dbg_val;
	reg	[31:0]	debug_pc;
	reg		r_dbg_stall;

	assign	div_ce = (op_valid_div)&&(adf_ce_unconditional)&&(set_cond);
	assign	fpu_ce = (IMPLEMENT_FPU)&&(op_valid_fpu)&&(adf_ce_unconditional)&&(set_cond);

	// }}}

	//
	//
	//	PIPELINE STAGE #5 :: Write-back
	//		Variable declarations
	//
	// {{{
	wire		wr_write_pc, wr_write_cc,
			wr_write_scc, wr_write_ucc;
	reg		wr_reg_ce, wr_flags_ce;
	reg	[3:0]	wr_flags;
	reg	[2:0]	wr_index;
	wire	[4:0]	wr_reg_id;
	reg	[31:0]	wr_gpreg_vl, wr_spreg_vl;
	wire		w_switch_to_interrupt, w_release_from_interrupt;
	reg	[(AW+1):0]	ipc;
	wire	[(AW+1):0]	upc;
	reg		last_write_to_cc;
	wire		cc_write_hold;
	reg		r_clear_icache;

	reg		pfpcset;
	reg	[2:0]	pfpcsrc;

	wire		w_clken;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// MASTER: clock enable.
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	master_ce = (!i_halt || alu_phase)
				&&(!cc_write_hold)&&(!o_break)&&(!sleep);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Calculate stall conditions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// PIPELINE STAGE #1 :: Prefetch
	//	These are calculated externally, within the prefetch module.
	//
	// PIPELINE STAGE #2 :: Instruction Decode
	// {{{
	always @(*)
	if (OPT_PIPELINED)
		dcd_stalled = (dcd_valid && op_stall);
	else
		dcd_stalled = (!master_ce)
			// Can't step forward when we need to be halted
			||(ill_err_i)||(ibus_err_flag)||(idiv_err_flag)
			||((dcd_valid || op_valid) && !dcd_early_branch)
			||(alu_busy)||(div_busy)||(fpu_busy)||(i_mem_busy);
	// }}}
	//
	// PIPELINE STAGE #3 :: Read Operands
	// {{{
	generate if (OPT_PIPELINED)
	begin : GEN_OP_STALL
		reg	r_cc_invalid_for_dcd;
		reg	r_pending_sreg_write;

		// cc_invalid_for_dcd
		// {{{
		initial	r_cc_invalid_for_dcd = 1'b0;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_cc_invalid_for_dcd <= 1'b0;
		else if ((alu_ce || mem_ce)&&(set_cond)&&(op_valid) &&((op_wF)
				||((op_wR)&&(op_R[4:0] == { op_gie, CPU_CC_REG }))))
			// If an instruction in the pipeline will write to the
			// CC register, then we can't be allowed to release
			// any instruction depending upon the CC register
			// (for other than conditional execution) into the
			// pipeline.
			r_cc_invalid_for_dcd <= 1'b1;
		else if (r_cc_invalid_for_dcd)
			// While the pipeline is busy, keep r_cc_invalid_for_dcd
			// high.
			r_cc_invalid_for_dcd <= ((alu_busy)||(i_mem_rdbusy)||(div_busy)||(fpu_busy));
		else
			r_cc_invalid_for_dcd <= 1'b0;

		assign	cc_invalid_for_dcd = r_cc_invalid_for_dcd;
		// }}}

		// pending_sreg_write
		// {{{
		// Used to determine if we need to stall for flags to be ready
		initial	r_pending_sreg_write = 1'b0;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_pending_sreg_write <= 1'b0;
		else if (((adf_ce_unconditional)||(mem_ce))
				&&(set_cond)&&(!op_illegal)
				&&(op_wR)
				&&(op_R[3:1] == 3'h7)
				&&(op_R[4:0] != { gie, 4'hf }))
			r_pending_sreg_write <= 1'b1;
		else if ((!i_mem_rdbusy)&&(!alu_busy))
			r_pending_sreg_write <= 1'b0;

		assign	pending_sreg_write = r_pending_sreg_write;
		// }}}

		assign	op_stall = (op_valid)&&(
		// {{{
			// Only stall if we're loaded w/valid insns and the
			// next stage is accepting our instruction
			(!adf_ce_unconditional)&&(!mem_ce)
			)
			||(dcd_valid)&&(
				// If we are halted, then accepting anything
				// into the Op stage might accept a register
				// that then gets modified by the debugging
				// interface so as to be invalid.
				i_halt
				// Stall if we need to wait for an operand A
				// to be ready to read
				|| (dcd_A_stall)
				// Likewise for B, also includes logic
				// regarding immediate offset (register must
				// be in register file if we need to add to
				// an immediate)
				||(dcd_B_stall)
				// Or if we need to wait on flags to work on the
				// CC register
				||(dcd_F_stall)
			);
		// }}}
		assign	op_ce = ((dcd_valid)||(dcd_illegal)||(dcd_early_branch))&&(!op_stall);

	end else begin : NO_OP_STALLS // !OPT_PIPELINED
		// {{{
		assign	op_stall = 1'b0; // (o_break)||(pending_interrupt);
		assign	op_ce = ((dcd_valid)||(dcd_early_branch))&&(!op_stall);
		assign	pending_sreg_write = 1'b0;
		assign	cc_invalid_for_dcd = 1'b0;

		// verilator coverage_off
		// Verilator lint_off UNUSED
		wire		pipe_unused;
		assign		pipe_unused = &{ 1'b0, cc_invalid_for_dcd,
					pending_sreg_write };
		// Verilator lint_on UNUSED
		// verilator coverage_on
		// }}}
	end endgenerate

	// BUT ... op_ce is too complex for many of the data operations.  So
	// let's make their circuit enable code simpler.  In particular, if
	// op_ doesn't need to be preserved, we can change it all we want
	// ... right?  The clear_pipeline code, for example, really only needs
	// to determine whether op_valid is true.
	// assign	op_change_data_ce = (!op_stall);
	// }}}
	//
	// PIPELINE STAGE #4 :: ALU / Memory
	// {{{
	// 1. Basic stall is if the previous stage is valid and the next is
	//	busy.
	// 2. Also stall if the prior stage is valid and the master clock enable
	//	is de-selected
	// 3. Stall if someone on the other end is writing the CC register,
	//	since we don't know if it'll put us to sleep or not.
	// 4. Last case: Stall if we would otherwise move a break instruction
	//	through the ALU.  Break instructions are not allowed through
	//	the ALU.
	generate if (OPT_PIPELINED)
	begin : GEN_ALU_STALL
		// alu_stall, alu_ce
		// {{{
		assign	alu_stall = (((master_stall)||(i_mem_rdbusy))&&(op_valid_alu)) //Case 1&2
			||(wr_reg_ce)&&(wr_write_cc);
		// assign // alu_ce = (master_ce)&&(op_valid_alu)&&(!alu_stall)
		//	&&(!clear_pipeline)&&(!op_illegal)
		//	&&(!pending_sreg_write)
		//	&&(!alu_sreg_stall);
		assign	alu_ce = (adf_ce_unconditional)&&(op_valid_alu);

		// verilator coverage_off
		// Verilator lint_off unused
		wire	unused_alu_stall = &{ 1'b0, alu_stall };
		// Verilator lint_on  unused
		// verilator coverage_on
		// }}}
	end else begin : NO_ALU_STALLS
		// alu_stall, alu_ce
		// {{{
		assign	alu_stall = (master_stall);
		//assign	alu_ce = (master_ce)&&(op_valid_alu)
		//			&&(!clear_pipeline)
		//			&&(!alu_stall);
		assign	alu_ce = (adf_ce_unconditional)&&(op_valid_alu);

		// verilator coverage_off
		// Verilator lint_off unused
		wire	unused_alu_stall = &{ 1'b0, alu_stall };
		// Verilator lint_on  unused
		// verilator coverage_on
		// }}}
	end endgenerate
	//

	// mem_ce
	// {{{
	// Note: if you change the conditions for mem_ce, you must also change
	// alu_pc_valid.
	//
	assign	mem_ce = (master_ce)&&(op_valid_mem)&&(!mem_stalled)
			&&(!clear_pipeline);
	// }}}

	// mem_stalled
	// {{{
	generate if (OPT_PIPELINED_BUS_ACCESS)
	begin : GEN_PIPELINE_MEM_STALL
		// {{{
		assign	mem_stalled = (master_stall)||((op_valid_mem)&&(
				(i_mem_pipe_stalled)
				||(i_bus_err)||(div_error)
				||(!op_pipe && i_mem_busy)
				// Stall waiting for flags to be valid
				// Or waiting for a write to the PC register
				// Or CC register, since that can change the
				//  PC as well
				||((wr_reg_ce)
					&&((wr_write_pc)||(wr_write_cc)))));
		// }}}
	end else if (OPT_PIPELINED)
	begin : GEN_MEM_STALL
		// {{{
		assign	mem_stalled = (master_stall)||((op_valid_mem)&&(
				(i_bus_err)||(div_error)||(i_mem_busy)
				// Stall waiting for flags to be valid
				// Or waiting for a write to the PC register
				// Or CC register, since that can change the
				//  PC as well
				||((wr_reg_ce)
					&&((wr_write_pc)||(wr_write_cc)))));
		// }}}
	end else begin : NO_MEM_STALL
		// {{{
		assign	mem_stalled = master_stall || i_mem_busy;
		// }}}
	end endgenerate
	// }}}
	// }}}

	//
	// Master stall condition
	// {{{
	assign	master_stall = (!master_ce)||(!op_valid)||(ill_err_i)
			||(step && stepped)
			||(ibus_err_flag)||(idiv_err_flag)
			||(pending_interrupt && !o_bus_lock)&&(!alu_phase)
			||(alu_busy)||(div_busy)||(fpu_busy)||(op_break)
			||((OPT_PIPELINED)&&(
				prelock_stall
				||((i_mem_busy)&&(op_illegal))
				||((i_mem_busy)&&(op_valid_div))
				||(alu_illegal)||(o_break)));
	// }}}
	//
	// (Everything but memory) stall condition
	// {{{

	// ALU, DIV, or FPU CE ... equivalent to the OR of all three of these
	always @(*)
	if (OPT_PIPELINED)
		adf_ce_unconditional =
			(!master_stall)&&(!op_valid_mem)&&(!i_mem_rdbusy)
			&&(!i_mem_busy || !op_wR
				|| op_R[4:0] != { gie, CPU_CC_REG });
	else
		adf_ce_unconditional = (!master_stall)&&(op_valid)&&(!op_valid_mem);
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PIPELINE STAGE #1 :: Instruction fetch
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	o_pf_ready = (!dcd_stalled && !dcd_phase);

	assign	o_pf_new_pc = (new_pc)||((dcd_early_branch_stb)&&(!clear_pipeline));

	assign	o_pf_request_address = ((dcd_early_branch_stb)&&(!clear_pipeline))
				? dcd_branch_pc:pf_pc;
	assign	pf_gie = gie;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PIPELINE STAGE #2 :: Instruction Decode
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign		dcd_ce =((OPT_PIPELINED)&&(!dcd_valid))||(!dcd_stalled);
	wire	[6:0]	dcd_full_R, dcd_full_A, dcd_full_B;

	idecode #(
		// {{{
		.ADDRESS_WIDTH(AW),
		.OPT_MPY((OPT_MPY!=0)? 1'b1:1'b0),
		.OPT_SHIFTS(OPT_SHIFTS),
		.OPT_PIPELINED(OPT_PIPELINED),
		.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
		.OPT_DIVIDE(OPT_DIV),
		.OPT_FPU(IMPLEMENT_FPU),
		.OPT_LOCK(OPT_LOCK),
		.OPT_OPIPE(OPT_PIPELINED_BUS_ACCESS),
		.OPT_USERMODE(OPT_USERMODE),
		.OPT_SIM(OPT_SIM),
		.OPT_CIS(OPT_CIS),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) instruction_decoder(
		// {{{
			.i_clk(i_clk),
			.i_reset(i_reset||clear_pipeline||o_clear_icache),
			.i_ce(dcd_ce),
			.i_stalled(dcd_stalled),
			.i_instruction(i_pf_instruction), .i_gie(pf_gie),
			.i_pc(i_pf_instruction_pc), .i_pf_valid(i_pf_valid),
				.i_illegal(i_pf_illegal),
			.o_valid(dcd_valid), .o_phase(dcd_phase),
			.o_illegal(dcd_illegal), .o_pc(dcd_pc),
			.o_dcdR(dcd_full_R), .o_dcdA(dcd_full_A),
				.o_dcdB(dcd_full_B),
			.o_preA(dcd_preA), .o_preB(dcd_preB),
			.o_I(dcd_I), .o_zI(dcd_zI), .o_cond(dcd_F),
			.o_wF(dcd_wF), .o_op(dcd_opn),
			.o_ALU(dcd_ALU), .o_M(dcd_M), .o_DV(dcd_DIV),
			.o_FP(dcd_FP), .o_break(dcd_break), .o_lock(dcd_lock),
			.o_wR(dcd_wR), .o_rA(dcd_rA), .o_rB(dcd_rB),
			.o_early_branch(dcd_early_branch),
			.o_early_branch_stb(dcd_early_branch_stb),
			.o_branch_pc(dcd_branch_pc), .o_ljmp(dcd_ljmp),
			.o_pipe(dcd_pipe),
			.o_sim(dcd_sim), .o_sim_immv(dcd_sim_immv)
`ifdef	FORMAL
			, .f_insn_word(f_dcd_insn_word),
			.f_insn_gie(f_dcd_insn_gie),
			.f_insn_is_pipeable(f_dcd_insn_is_pipeable)
`endif
		// }}}
	);

	assign	{ dcd_Rcc, dcd_Rpc, dcd_R } = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? dcd_full_R : 7'h0;
	assign	{ dcd_Acc, dcd_Apc, dcd_A } = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? dcd_full_A : 7'h0;
	assign	{ dcd_Bcc, dcd_Bpc, dcd_B } = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? dcd_full_B : 7'h0;
	assign	dcd_gie = pf_gie;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PIPELINE STAGE #3 :: Read Operands (Registers)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// op_pipe
	// {{{
	generate if (OPT_PIPELINED_BUS_ACCESS)
	begin : GEN_OP_PIPE // Memory pipelining
		reg		r_op_pipe;

		// To be a pipeable operation, there must be
		//	two valid adjacent instructions
		//	Both must be memory instructions
		//	Both must be writes, or both must be reads
		//	Both operations must be to the same identical address,
		//		or at least a single (one) increment above that
		//		address
		//
		// However ... we need to know this before this clock, hence
		// this is calculated in the instruction decoder.
		initial	r_op_pipe = 1'b0;
		always @(posedge i_clk)
		if ((OPT_LOWPOWER && i_reset)||(clear_pipeline)||(i_halt))
			r_op_pipe <= 1'b0;
		else if (op_ce)
			r_op_pipe <= (dcd_pipe)&&(op_valid_mem)&&(!OPT_LOWPOWER || !dcd_illegal);
		else if ((wr_reg_ce)&&(wr_reg_id == op_Bid[4:0]))
			r_op_pipe <= 1'b0;
		else if (mem_ce) // Clear us any time an op_ is clocked in
			r_op_pipe <= 1'b0;

		assign	op_pipe = r_op_pipe;
`ifdef	FORMAL
		always @(*)
		if (OPT_LOWPOWER && !op_valid_mem)
			assert(!r_op_pipe);
`endif
	end else begin : NO_OP_PIPE

		assign	op_pipe = 1'b0;

	end endgenerate
	// }}}

	// Read from our register set
	// {{{
	generate if (OPT_DISTRIBUTED_REGS)
	begin : GEN_DISTRIBUTED_REGS
		// {{{
		if (OPT_USERMODE)
		begin : GEN_FULL_REGSET

			assign	w_op_Av = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? regset[dcd_A] : 32'h0;
			assign	w_op_Bv = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? regset[dcd_B] : 32'h0;

		end else begin : GEN_NO_USERREGS
			assign	w_op_Av = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? regset[dcd_A[3:0]] : 32'h0;
			assign	w_op_Bv = (!OPT_LOWPOWER || dcd_valid || !OPT_PIPELINED) ? regset[dcd_B[3:0]] : 32'h0;
		end

		// verilator coverage_off
		// verilator lint_off UNUSED
		wire	unused_prereg_addrs;
		assign	unused_prereg_addrs = &{ 1'b0, dcd_preA, dcd_preB };
		// verilator lint_on  UNUSED
		// verilator coverage_on
		// }}}
	end else begin : GEN_BLOCKRAM
		// {{{
		reg	[31:0]	pre_rewrite_value, pre_op_Av, pre_op_Bv;
		reg		pre_rewrite_flag_A, pre_rewrite_flag_B;

		always @(posedge i_clk)
		if (dcd_ce)
		begin
			pre_rewrite_flag_A <= (wr_reg_ce)&&(dcd_preA == wr_reg_id);
			pre_rewrite_flag_B <= (wr_reg_ce)&&(dcd_preB == wr_reg_id);
			pre_rewrite_value  <= wr_gpreg_vl;
		end else if (OPT_PIPELINED && dcd_valid)
		begin
			pre_rewrite_flag_A <= (wr_reg_ce)&&(dcd_A == wr_reg_id);
			pre_rewrite_flag_B <= (wr_reg_ce)&&(dcd_B == wr_reg_id);
			pre_rewrite_value  <= wr_gpreg_vl;
		end

		if (OPT_USERMODE)
		begin : GEN_FULL_REGSET

			always @(posedge i_clk)
			if (dcd_ce || (OPT_PIPELINED && dcd_valid))
				pre_op_Av <= regset[dcd_ce ? dcd_preA : dcd_A];

			always @(posedge i_clk)
			if (dcd_ce || (OPT_PIPELINED && dcd_valid))
				pre_op_Bv <= regset[dcd_ce ? dcd_preB : dcd_B];

		end else begin : GEN_NO_USERREGS
			always @(posedge i_clk)
			if (dcd_ce || (OPT_PIPELINED && dcd_valid))
				pre_op_Av <= regset[dcd_ce ? dcd_preA[3:0] : dcd_A[3:0]];

			always @(posedge i_clk)
			if (dcd_ce || (OPT_PIPELINED && dcd_valid))
				pre_op_Bv <= regset[dcd_ce ? dcd_preB[3:0] : dcd_B[3:0]];
		end

		assign	w_op_Av = (pre_rewrite_flag_A) ? pre_rewrite_value : pre_op_Av;
		assign	w_op_Bv = (pre_rewrite_flag_B) ? pre_rewrite_value : pre_op_Bv;
		// }}}
	end endgenerate
	// }}}

	assign	w_cpu_info = {
	// {{{
	1'b1,
	(OPT_MPY    >0)? 1'b1:1'b0,
	(OPT_DIV >0)? 1'b1:1'b0,
	(IMPLEMENT_FPU    >0)? 1'b1:1'b0,
	OPT_PIPELINED,
	1'b0,
	(OPT_EARLY_BRANCHING > 0)? 1'b1:1'b0,
	OPT_PIPELINED_BUS_ACCESS,
	OPT_CIS
	};
	// }}}

	always @(*)
	begin
		w_pcA_v = 0;
		if ((!OPT_USERMODE)||(dcd_A[4] == dcd_gie))
			w_pcA_v[(AW+1):0] = { dcd_pc[AW+1:2], 2'b00 };
		else
			w_pcA_v[(AW+1):0] = { upc[(AW+1):2], uhalt_phase, 1'b0 };
	end

	// Op register addresses
	// {{{
	generate if (OPT_PIPELINED)
	begin : OP_REG_ADVANEC
		// {{{
		reg	[4:0]	r_op_R;
		reg	[4:0]	r_op_Aid, r_op_Bid;
		reg		r_op_rA, r_op_rB;

		initial	r_op_R   = 0;
		initial	r_op_Aid = 0;
		initial	r_op_Bid = 0;
		initial	r_op_rA  = 0;
		initial	r_op_rB  = 0;
		initial	op_Rcc = 0;
		always @(posedge i_clk)
		begin
			if (op_ce && (!OPT_LOWPOWER || w_op_valid))
			begin
				r_op_R   <= dcd_R;
				r_op_Aid <= dcd_A;
				if ((dcd_rB)&&(!dcd_early_branch)&&(!dcd_illegal))
					r_op_Bid <= dcd_B;
				r_op_rA  <= (dcd_rA)&&(!dcd_early_branch)&&(!dcd_illegal);
				r_op_rB  <= (dcd_rB)&&(!dcd_early_branch)&&(!dcd_illegal);
				op_Rcc <= (dcd_Rcc)&&(dcd_wR)&&(dcd_R[4]==dcd_gie);
			end

			if (op_lowpower_clear)
			begin
				r_op_rA <= 1'b0;
				r_op_rB <= 1'b0;
			end
		end

		assign	op_R   = r_op_R;
		assign	op_Aid = r_op_Aid;
		assign	op_Bid = r_op_Bid;
		assign	op_rA  = r_op_rA;
		assign	op_rB  = r_op_rB;
		// }}}
	end else begin : OP_REG_COPY
		// {{{
		assign	op_R = dcd_R;
		assign	op_Aid = dcd_A;
		assign	op_Bid = dcd_B;
		assign	op_rA  = dcd_rA;
		assign	op_rB  = dcd_rB;

		always @(*)
			op_Rcc = (dcd_Rcc)&&(dcd_wR)&&(dcd_R[4]==dcd_gie);
		// }}}
	end endgenerate
	// }}}

	// r_op_Av -- The registered value of the op A register
	// {{{
	reg [2:0]	avsrc;
	reg	[2:0]	bvsrc;
	reg	[1:0]	bisrc;

	always @(*)
	begin
		avsrc = 3'b000;
		if (!OPT_PIPELINED || op_ce)
		begin
			if (dcd_Apc)
				avsrc = 3'b101;
			else if (dcd_Acc)
				avsrc = 3'b110;
			else
				avsrc = 3'b111;
		end

		if (OPT_PIPELINED && wr_reg_ce)
		begin
			if (!op_ce && wr_reg_id == op_Aid && op_rA)
				avsrc = 3'b100;
			else if (op_ce && wr_reg_id == dcd_A)
				avsrc = 3'b100;
		end
	end

// 44313
	initial	r_op_Av = 0;
	always @(posedge i_clk)
	begin
		if (avsrc[2])
		case(avsrc[1:0])
		2'b00:	r_op_Av <= wr_gpreg_vl;
		2'b01:	r_op_Av <= w_pcA_v;
		2'b10:	r_op_Av <= { w_cpu_info, w_op_Av[22:16], (dcd_A[4])?w_uflags:w_iflags };
		2'b11:	r_op_Av <= w_op_Av;
		endcase

		if (op_lowpower_clear)
			r_op_Av <= 0;
	end
	// }}}

	// w_op_B -- The registered value of the op B register
	// {{{
	always @(*)
	begin
		w_pcB_v = 0;
		if ((!OPT_USERMODE)||(dcd_B[4] == dcd_gie))
			w_pcB_v[(AW+1):0] = { dcd_pc[AW+1:2], 2'b00 };
		else
			w_pcB_v[(AW+1):0] = { upc[(AW+1):2], uhalt_phase, 1'b0 };
	end

	always @(*)
	if (!dcd_rB)
		bisrc = 0;
	else if ((OPT_PIPELINED)&&(wr_reg_ce)&&(wr_reg_id == dcd_B))
		bisrc = 1;
	else if (dcd_Bcc)
		bisrc = 2;
	else
		bisrc = 3;

	always @(*)
	case(bisrc[1:0])
	2'b00: w_op_BnI = 0;
	2'b01: w_op_BnI = wr_gpreg_vl;
	2'b10: w_op_BnI = { w_cpu_info, w_op_Bv[22:16],
				(dcd_B[4]) ? w_uflags : w_iflags };
	2'b11: w_op_BnI = w_op_Bv;
	endcase

	always @(*)
	begin
		bvsrc = 0;
		if ((!OPT_PIPELINED)||(op_ce))
		begin
			if ((dcd_Bpc)&&(dcd_rB))
				bvsrc = 3'b100;
			else
				bvsrc = 3'b101;
		end else if ((OPT_PIPELINED)&&(op_rB)
			&&(wr_reg_ce)&&(op_Bid == wr_reg_id))
			bvsrc = 3'b110;
	end

	initial	r_op_Bv = 0;
	always @(posedge i_clk)
	begin
		if (bvsrc[2]) casez(bvsrc[1:0])
		2'b00: r_op_Bv <= w_pcB_v + { dcd_I[29:0], 2'b00 };
		2'b01: r_op_Bv <= w_op_BnI + dcd_I;
		2'b1?: r_op_Bv <= wr_gpreg_vl;
		endcase

		if (op_lowpower_clear)
			r_op_Bv <= 0;
	end
	// }}}

	// op_F
	// {{{
	// The logic here has become more complex than it should be, no thanks
	// to Xilinx's Vivado trying to help.  The conditions are supposed to
	// be two sets of four bits: the top bits specify what bits matter, the
	// bottom specify what those top bits must equal.  However, two of
	// conditions check whether bits are on, and those are the only two
	// conditions checking those bits.  Therefore, Vivado complains that
	// these two bits are redundant.  Hence the convoluted expression
	// below, arriving at what we finally want in the (now wire net)
	// op_F.
	initial	r_op_F = 7'h00;
	always @(posedge i_clk)
	begin
		if ((!OPT_PIPELINED)||(op_ce))
			// Cannot do op_change_data_ce here since op_F depends
			// upon being either correct for a valid op, or correct
			// for the last valid op
		begin // Set the flag condition codes, bit order is [3:0]=VNCZ
			case(dcd_F[2:0])
			3'h0:	r_op_F <= 7'h00;	// Always
			3'h1:	r_op_F <= 7'h11;	// Z
			3'h2:	r_op_F <= 7'h44;	// LT
			3'h3:	r_op_F <= 7'h22;	// C
			3'h4:	r_op_F <= 7'h08;	// V
			3'h5:	r_op_F <= 7'h10;	// NE
			3'h6:	r_op_F <= 7'h40;	// GE (!N)
			3'h7:	r_op_F <= 7'h20;	// NC
			endcase
		end

		if (op_lowpower_clear)
			r_op_F <= 7'h00;
	end // Bit order is { (flags_not_used), VNCZ mask, VNCZ value }
	assign	op_F = { r_op_F[3], r_op_F[6:0] };
	// }}}

	// op_valid
	// {{{
	assign	w_op_valid = (!clear_pipeline)&&(dcd_valid)
					&&(!dcd_ljmp)&&(!dcd_early_branch);

	initial	op_valid     = 1'b0;
	initial	op_valid_alu = 1'b0;
	initial	op_valid_mem = 1'b0;
	initial	op_valid_div = 1'b0;
	initial	op_valid_fpu = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(clear_pipeline))
	begin
		// {{{
		op_valid     <= 1'b0;
		op_valid_alu <= 1'b0;
		op_valid_mem <= 1'b0;
		op_valid_div <= 1'b0;
		op_valid_fpu <= 1'b0;
		// }}}
	end else if (op_ce)
	begin
		// {{{
		// Do we have a valid instruction?
		//   The decoder may vote to stall one of its
		//   instructions based upon something we currently
		//   have in our queue.  This instruction must then
		//   move forward, and get a stall cycle inserted.
		//   Hence, the test on dcd_stalled here.  If we must
		//   wait until our operands are valid, then we aren't
		//   valid yet until then.
		if (OPT_PIPELINED || !op_valid)
		begin
			op_valid     <= (w_op_valid)||(dcd_early_branch);
			op_valid_alu <= (w_op_valid)&&((dcd_ALU)||(dcd_illegal));
			op_valid_mem <= (dcd_M)&&(!dcd_illegal)
					&&(w_op_valid);
			op_valid_div <= (OPT_DIV)&&(dcd_DIV)&&(!dcd_illegal)&&(w_op_valid);
			op_valid_fpu <= (IMPLEMENT_FPU)&&(dcd_FP)&&(!dcd_illegal)&&(w_op_valid);
		end else if ((adf_ce_unconditional)||(mem_ce))
		begin
			op_valid     <= 1'b0;
			op_valid_alu <= 1'b0;
			op_valid_mem <= 1'b0;
			op_valid_div <= 1'b0;
			op_valid_fpu <= 1'b0;
		end
		// }}}
	end else if ((adf_ce_unconditional)||(mem_ce))
	begin
		// {{{
		// If nothing advances into the OP stage, yet what was in
		// the OP stage moves forward, then we need to invalidate what
		// used to be here.
		op_valid     <= 1'b0;
		op_valid_alu <= 1'b0;
		op_valid_mem <= 1'b0;
		op_valid_div <= 1'b0;
		op_valid_fpu <= 1'b0;
		// }}}
	end
	// }}}

	// op_lowpower_clear
	// {{{
	generate if (!OPT_LOWPOWER || !OPT_PIPELINED)
	begin : NO_OP_LOWPOWER_CLEAR

		assign	op_lowpower_clear = 1'b0;

	end else begin : GEN_OP_LOWPOWER_CLEAR
		reg		r_op_lowpower_clear;

		always @(*)
		if (i_reset || clear_pipeline)
			r_op_lowpower_clear = 1'b1;
		else if (op_ce && !w_op_valid)
			r_op_lowpower_clear = 1'b1;
		else if ((!op_ce || !w_op_valid)&&(adf_ce_unconditional || mem_ce))
			r_op_lowpower_clear = 1'b1;
		else
			r_op_lowpower_clear = 1'b0;

		assign	op_lowpower_clear = r_op_lowpower_clear;
	end endgenerate
	// }}}

	// op_break
	// {{{
	// Here's part of our debug interface.  When we recognize a break
	// instruction, we set the op_break flag.  That'll prevent this
	// instruction from entering the ALU, and cause an interrupt before
	// this instruction.  Thus, returning to this code will cause the
	// break to repeat and continue upon return.  To get out of this
	// condition, replace the break instruction with what it is supposed
	// to be, step through it, and then replace it back.  In this fashion,
	// a debugger can step through code.
	// assign w_op_break = (dcd_break)&&(r_dcd_I[15:0] == 16'h0001);

	initial	r_op_break = 1'b0;
	always @(posedge i_clk)
	if (clear_pipeline)
		r_op_break <= 1'b0;
	else if ((OPT_PIPELINED)&&(op_ce))
		r_op_break <= (dcd_valid)&&(dcd_break)&&(!dcd_illegal);
	else if ((!OPT_PIPELINED)&&(dcd_valid))
		r_op_break <= (dcd_break)&&(!dcd_illegal)&&(!step || !stepped);

	assign	op_break = r_op_break;
`ifdef	FORMAL
	always @(*)
	if (op_break)
		assert(op_valid || clear_pipeline);
`endif
	// }}}

	// op_lock
	// {{{
	generate if (!OPT_LOCK)
	begin : NO_OPLOCK

		assign op_lock       = 1'b0;

		// verilator coverage_off
		// Verilator lint_off UNUSED
		wire	dcd_lock_unused;
		assign	dcd_lock_unused = &{ 1'b0, dcd_lock };
		// Verilator lint_on  UNUSED
		// verilator coverage_on

	end else // if (!OPT_LOCK)
	begin : GEN_OPLOCK
		reg	r_op_lock;

		initial	r_op_lock = 1'b0;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_op_lock <= 1'b0;
		else if (op_ce)
			r_op_lock <= (dcd_valid)&&(dcd_lock)
					&&(!dcd_illegal);
		assign	op_lock = r_op_lock;

	end endgenerate
	// }}}

	// op_illegal
	// {{{
	initial	op_illegal = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(clear_pipeline))
		op_illegal <= 1'b0;
	else if (OPT_PIPELINED)
	begin
		if (op_ce)
			op_illegal <= (dcd_valid)&&(!dcd_ljmp)
				&&(!dcd_early_branch)&&(dcd_illegal);
	end else if (!OPT_PIPELINED)
	begin
		if (dcd_valid)
			op_illegal <= (!dcd_ljmp)&&(!dcd_early_branch)&&(dcd_illegal);
	end
	// }}}

	// op_wF
	// {{{
	always @(posedge i_clk)
	begin
		if ((!OPT_PIPELINED)||(op_ce))
			op_wF <= (dcd_wF)&&((!dcd_Rcc)||(!dcd_wR))
				&&(!dcd_early_branch);

		if (op_lowpower_clear)
			op_wF <= 1'b0;
	end
	// }}}

	// op_wR
	// {{{
	generate if ((OPT_PIPELINED)||(OPT_EARLY_BRANCHING))
	begin : GEN_OP_WR
		reg	r_op_wR;

		initial	r_op_wR = 1'b0;
		always @(posedge i_clk)
		begin
			if (op_ce)
				r_op_wR <= (dcd_wR)&&(!dcd_early_branch);
			if (op_lowpower_clear)
				r_op_wR <= 1'b0;
		end

		assign	op_wR = r_op_wR;
	end else begin : COPY_OP_WR

		assign	op_wR = dcd_wR;

	end endgenerate
	// }}}

	// op_sim, op_sim_immv
	// {{{
	generate if (OPT_SIM)
	begin : OP_SIM
		//
		// Only execute this if OPT_SIM is true--that is, if we
		// are running from a simulated environment.
		//
		reg		r_op_sim;
		reg	[22:0]	r_op_sim_immv;

		always @(posedge i_clk)
		if (op_ce)
		begin
			r_op_sim    <= dcd_sim && (!OPT_LOWPOWER || w_op_valid);
			r_op_sim_immv <= dcd_sim_immv;
			if (OPT_LOWPOWER && (!dcd_sim || !w_op_valid))
				r_op_sim_immv <= 0;
		end else if (adf_ce_unconditional)
		begin
			r_op_sim <= 1'b0;
			if (OPT_LOWPOWER)
				r_op_sim_immv <= 0;
		end

		assign	op_sim = r_op_sim;
		assign	op_sim_immv = r_op_sim_immv;

	end else begin : NO_OP_SIM

		assign	op_sim = 0;
		assign	op_sim_immv = 0;

		// verilator coverage_off
		// Verilator lint_off UNUSED
		wire	op_sim_unused;
		assign	op_sim_unused = &{ 1'b0, dcd_sim, dcd_sim_immv };
		// Verilator lint_on  UNUSED
		// verilator coverage_on
	end endgenerate
	// }}}

	// op_pc
	// {{{
	generate if ((OPT_PIPELINED)||(OPT_EARLY_BRANCHING))
	begin : SET_OP_PC

		reg	[AW+1:0]	r_op_pc;

		initial r_op_pc[0] = 1'b0;
		always @(posedge i_clk)
		if (op_ce)
		begin
			if (dcd_early_branch)
				// Need to retire an early branch as a NOOP,
				// to make sure our PC is properly updated
				r_op_pc <= dcd_branch_pc;
			else if (!OPT_LOWPOWER || w_op_valid)
				r_op_pc <= dcd_pc;
		end

		assign	op_pc = r_op_pc;

	end else begin : SET_OP_PC

		assign op_pc = dcd_pc;

	end endgenerate
	// }}}

	// op_opn -- the opcode of the current operation
	// {{{
	generate if (!OPT_PIPELINED)
	begin : COPY_DCD_OPN

		assign	op_opn = dcd_opn;

	end else begin : FWD_OPERATION

		reg	[3:0]	r_op_opn;

		always @(posedge i_clk)
		if (op_ce && (!OPT_LOWPOWER || w_op_valid || dcd_early_branch))
		begin
			// Which ALU operation?  Early branches are
			// unimplemented moves
			r_op_opn    <= ((dcd_early_branch)||(dcd_illegal))
					? CPU_MOV_OP : dcd_opn;
			// opM  <= dcd_M;	// Is this a memory operation?
			// What register will these results be written into?
		end

		assign	op_opn = r_op_opn;

	end endgenerate
	// }}}
	assign	op_gie = gie;

	assign	op_Fl = (op_gie)?(w_uflags[3:0]):(w_iflags[3:0]);

	// op_phase
	// {{{
	generate if (OPT_CIS)
	begin : OPT_CIS_OP_PHASE

		reg	r_op_phase;

		initial	r_op_phase = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(clear_pipeline))
			r_op_phase <= 1'b0;
		else if (op_ce)
			r_op_phase <= (dcd_phase)&&((!dcd_wR)||(!dcd_Rpc));

		assign	op_phase = r_op_phase;
	end else begin : OPT_NOCIS_OP_PHASE
		assign	op_phase = 1'b0;

		// verilator lint_off UNUSED
		wire	OPT_CIS_dcdRpc;
		assign	OPT_CIS_dcdRpc = dcd_Rpc;
		// verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// op_Av -- the combinatorial A value input to the ALU/MEM/DIV stage
	// {{{
	// This is tricky.  First, the PC and Flags registers aren't kept in
	// register set but in special registers of their own.  So step one
	// is to select the right register.  Step to is to replace that
	// register with the results of an ALU or memory operation, if such
	// results are now available.  Otherwise, we'd need to insert a wait
	// state of some type.
	//
	// The alternative approach would be to define some sort of
	// op_stall wire, which would stall any upstream stage.
	// We'll create a flag here to start our coordination.  Once we
	// define this flag to something other than just plain zero, then
	// the stalls will already be in place.
	generate if (OPT_PIPELINED)
	begin : FWD_OP_AV

		assign	op_Av = ((wr_reg_ce)&&(wr_reg_id == op_Aid))
			?  wr_gpreg_vl : r_op_Av;

	end else begin : COPY_OP_AV

		assign	op_Av = r_op_Av;

	end endgenerate
	// }}}

	// dcd_A_stall
	// {{{
	// Stall if we have decoded an instruction that will read register A
	//	AND ... something that may write a register is running
	//	AND (series of conditions here ...)
	//		The operation might set flags, and we wish to read the
	//			CC register
	//		OR ... (No other conditions)
	generate if (OPT_PIPELINED)
	begin : GEN_DCDA_STALL

		assign	dcd_A_stall = (dcd_rA) // &&(dcd_valid) is checked for elsewhere
				&&((op_valid)||(i_mem_rdbusy)
					||(div_busy)||(fpu_busy))
				&&(((op_wF)||(cc_invalid_for_dcd))&&(dcd_Acc))
			||((dcd_rA)&&(dcd_Acc)&&(cc_invalid_for_dcd));
	end else begin : NO_DCDA_STALL

		// There are no pipeline hazards, if we aren't pipelined
		assign	dcd_A_stall = 1'b0;

	end endgenerate
	// }}}

	// op_Bv
	// {{{
	assign	op_Bv = ((OPT_PIPELINED)&&(wr_reg_ce)
					&&(wr_reg_id == op_Bid)&&(op_rB))
			? wr_gpreg_vl: r_op_Bv;
	// }}}

	// dcd_B_stall, dcd_F_stall
	// {{{
	generate if (OPT_PIPELINED)
	begin : DCD_BF_STALLS
	// Stall if we have decoded an instruction that will read register B
	//	AND ... something that may write a (unknown) register is running
	//	AND (series of conditions here ...)
	//		The operation might set flags, and we wish to read the
	//			CC register
	//		OR the operation might set register B, and we still need
	//			a clock to add the offset to it
	assign	dcd_B_stall = (dcd_rB) // &&(dcd_valid) is checked for elsewhere
	// {{{
				// If the op stage isn't valid, yet something
				// is running, then it must have been valid.
				// We'll use the last values from that stage
				// (op_wR, op_wF, op_R) in our logic below.
				&&((op_valid)||(i_mem_rdbusy)
					||(div_busy)||(fpu_busy)||(alu_busy))
				&&(
				// Okay, what happens if the result register
				// from instruction 1 becomes the input for
				// instruction two, *and* there's an immediate
				// offset in instruction two?  In that case, we
				// need an extra clock between the two
				// instructions to calculate the base plus
				// offset.
				//
				// What if instruction 1 (or before) is in a
				// memory pipeline?  We may no longer know what
				// the register was!  We will then need  to
				// blindly wait.  We'll temper this only waiting
				// if we're not piping this new instruction.
				// If we were piping, the pipe logic in the
				// decode circuit has told us that the hazard
				// is clear, so we're okay then.
				//
				((!dcd_zI)&&(
					((op_R == dcd_B)&&(op_wR))
					||((i_mem_rdbusy)&&(!dcd_pipe))
					||(((alu_busy ||
						div_busy || i_mem_rdbusy))
						&&(alu_reg == dcd_B))
					||((wr_reg_ce)&&(wr_reg_id[3:1] == 3'h7))
					))
				// Stall following any instruction that will
				// set the flags, if we're going to need the
				// flags (CC) register for op_B.
				||(((op_wF)||(cc_invalid_for_dcd))&&(dcd_Bcc))
				// Stall on any ongoing memory operation that
				// will write to op_B -- captured above
				// ||((i_mem_busy)&&(!mem_we)&&(mem_last_reg==dcd_B)&&(!dcd_zI))
				)
			||((dcd_rB)&&(dcd_Bcc)&&(cc_invalid_for_dcd));
		// }}}
		assign	dcd_F_stall = ((!dcd_F[3])
		// {{{
					||((dcd_rA)&&(dcd_A[3:1]==3'h7)
						&&(dcd_A[4:0] != { gie, 4'hf}))
					||((dcd_rB)&&(dcd_B[3:1]==3'h7))
						&&(dcd_B[4:0] != { gie, 4'hf}))
					&&(((op_valid)&&(op_wR)
						&&(op_R[3:1]==3'h7)
						&&(op_R[4:0]!={gie, 4'hf}))
						||(pending_sreg_write));
				// &&(dcd_valid) is checked for elsewhere
		// }}}
	end else begin : NO_PIPELINE_NO_STALL
		// {{{
		// No stalls without pipelining, 'cause how can you have a
		// pipeline hazard without the pipeline?
		assign	dcd_B_stall = 1'b0;
		assign	dcd_F_stall = 1'b0;
		// }}}
	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PIPELINE STAGE #4 :: Apply Instruction
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The ALU itself
	cpuops	#(
		// {{{
		.OPT_MPY(OPT_MPY),
		.OPT_SHIFTS(OPT_SHIFTS),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) doalu(
	// {{{
		.i_clk(i_clk), .i_reset((i_reset)||(clear_pipeline)),
		.i_stb(alu_ce),
		.i_op((!OPT_LOWPOWER || alu_ce) ? op_opn : 4'h0),
		.i_a( (!OPT_LOWPOWER || alu_ce) ? op_Av  : 32'h0),
		.i_b( (!OPT_LOWPOWER || alu_ce) ? op_Bv  : 32'h0),
		.o_c(alu_result), .o_f(alu_flags),
		.o_valid(alu_valid),
		.o_busy(alu_busy)
	// }}}
	);

	// Divide
	// {{{
	generate if (OPT_DIV != 0)
	begin : DIVIDE
`ifdef	FORMAL
`define	DIVIDE_MODULE	abs_div
`else
`define	DIVIDE_MODULE	div
`endif
		`DIVIDE_MODULE #(
			.OPT_LOWPOWER(OPT_LOWPOWER)
		) thedivide(
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || clear_pipeline),
				.i_wr(div_ce), .i_signed(op_opn[0]),
			.i_numerator(op_Av), .i_denominator(op_Bv),
			.o_busy(div_busy), .o_valid(div_valid),
				.o_err(div_error), .o_quotient(div_result),
			.o_flags(div_flags)
			// }}}
		);

	end else begin : NO_DIVIDE
		// {{{
		assign	div_error = 1'b0; // Can't be high unless div_valid
		assign	div_busy  = 1'b0;
		assign	div_valid = 1'b0;
		assign	div_result= 32'h00;
		assign	div_flags = 4'h0;

		// Make verilator happy here
		// verilator coverage_off
		// verilator lint_off UNUSED
		wire	unused_divide;
		assign	unused_divide = &{ 1'b0, div_ce };
		// verilator lint_on  UNUSED
		// verilator coverage_on
		// }}}
	end endgenerate
	// }}}

	// (Non-existent) FPU
	// {{{
	generate if (IMPLEMENT_FPU != 0)
	begin : FPU
		//
		// sfpu thefpu(i_clk, i_reset, fpu_ce, op_opn[2:0],
		//	op_Av, op_Bv, fpu_busy, fpu_valid, fpu_err, fpu_result,
		//	fpu_flags);
		//
`ifdef	FORMAL
		abs_div thefpu(i_clk, ((i_reset)||(clear_pipeline)),
				fpu_ce, op_opn[2:0],
			op_Av, op_Bv, fpu_busy, fpu_valid, fpu_error, fpu_result,
			fpu_flags);

`else
		assign	fpu_error = 1'b0; // Must only be true if fpu_valid
		assign	fpu_busy  = 1'b0;
		assign	fpu_valid = 1'b0;
		assign	fpu_result= 32'h00;
		assign	fpu_flags = 4'h0;
`endif
	end else begin : GEN_NOFPU
		assign	fpu_error = 1'b0;
		assign	fpu_busy  = 1'b0;
		assign	fpu_valid = 1'b0;
		assign	fpu_result= 32'h00;
		assign	fpu_flags = 4'h0;
	end endgenerate
	// }}}

	// Condition handling
	// {{{
	assign	set_cond = ((op_F[7:4]&op_Fl[3:0])==op_F[3:0]);
	initial	alu_wF   = 1'b0;
	initial	alu_wR   = 1'b0;
	generate if (OPT_PIPELINED)
	begin : GEN_COND_PIPELINED
		always @(posedge i_clk)
		if (i_reset)
		begin
			alu_wR   <= 1'b0;
			alu_wF   <= 1'b0;
		end else if (alu_ce)
		begin
			// alu_reg <= op_R;
			alu_wR  <= (op_wR)&&(set_cond)&&(!op_illegal);
			alu_wF  <= (op_wF)&&(set_cond)&&(!op_illegal);
		end else if (!alu_busy)
		begin
			// These are strobe signals, so clear them if they
			// aren't going to be set for any particular clock
			alu_wR <= (r_halted)&&(OPT_DBGPORT && i_dbg_we && !o_dbg_stall);
			alu_wF <= 1'b0;
		end
	end else begin : GEN_COND_NOPIPE

		always @(posedge i_clk)
		begin
			alu_wR  <= (op_wR)&&(set_cond)&&(!op_illegal);
			alu_wF  <= (op_wF)&&(set_cond)&&(!op_illegal);
		end

	end endgenerate
	// }}}

	// alu_phase
	// {{{
	// Instruction phase (which half of the instruction we are on) tracking
	generate if (OPT_CIS)
	begin : GEN_ALU_PHASE

		reg	r_alu_phase;

		initial	r_alu_phase = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(clear_pipeline))
			r_alu_phase <= 1'b0;
		else if (((adf_ce_unconditional)||(mem_ce))&&(op_valid))
			r_alu_phase <= op_phase;
		else if ((adf_ce_unconditional)||(mem_ce))
			r_alu_phase <= 1'b0;

		assign	alu_phase = r_alu_phase;
	end else begin : NO_ALUPHASE

		assign	alu_phase = 1'b0;
	end endgenerate
	// }}}

	// alu_reg
	// {{{
	generate if (OPT_PIPELINED)
	begin : GEN_ALUREG_PIPE

		always @(posedge i_clk)
		if (alu_ce || div_ce || o_mem_ce || fpu_ce)
			alu_reg <= op_R;
		else if (OPT_DBGPORT && i_dbg_we && !o_dbg_stall)
			alu_reg <= i_dbg_wreg;

	end else begin : GEN_ALUREG_NOPIPE

		always @(posedge i_clk)
		if (OPT_DBGPORT && i_dbg_we && !o_dbg_stall)
			alu_reg <= i_dbg_wreg;
		else
			alu_reg <= op_R;
	end endgenerate
	// }}}

	// wr_index
	// {{{
	initial	wr_index = 0;
	always @(posedge i_clk)
	begin
		if ((OPT_PIPELINED && (mem_ce || adf_ce_unconditional))
			||(!OPT_PIPELINED && op_valid))
		begin
			wr_index <= 0;
			/*
			if (op_valid_mem)
				wr_index <= 3'b001;
			if (op_valid_alu)
				wr_index <= 3'b010;
			if (op_valid_div)
				wr_index <= 3'b011;
			if (op_valid_fpu)
				wr_index <= 3'b100;
			*/

			wr_index[0] <= (op_valid_mem | op_valid_div);
			wr_index[1] <= (op_valid_alu | op_valid_div);
			wr_index[2] <= (op_valid_fpu);
		end

		if (OPT_DBGPORT && i_dbg_we && !o_dbg_stall)
			wr_index <= 3'b000;

		if (!IMPLEMENT_FPU)
			wr_index[2] <= 1'b0;
	end
	// }}}

	//
	// DEBUG Register write access starts here
	//
	// {{{
	initial	dbgv = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !r_halted)
		dbgv <= 0;
	else
		dbgv <= OPT_DBGPORT && i_dbg_we && !o_dbg_stall;

	always @(posedge i_clk)
	if (!OPT_LOWPOWER || (OPT_DBGPORT && i_dbg_we))
		dbg_val <= i_dbg_data;

	// dbg_clear_pipe
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_pipeline || !r_halted)
		dbg_clear_pipe <= 0;
	else if (OPT_DBGPORT && i_dbg_we && !o_dbg_stall)
	begin
		dbg_clear_pipe <= 1'b0;

		if (!OPT_PIPELINED)
			dbg_clear_pipe <= 1'b1;
		if ((i_dbg_wreg == op_Bid)&&(op_rB))
			dbg_clear_pipe <= 1'b1;
		if (i_dbg_wreg[3:1] == 3'h7)
			dbg_clear_pipe <= 1'b1;
	end else if ((!OPT_PIPELINED)&&(i_clear_cache && !o_dbg_stall))
		dbg_clear_pipe <= 1'b1;
	else
		dbg_clear_pipe <= 1'b0;
	// }}}

	assign	alu_gie = gie;
	// }}}

	// r_alu_pc
	// {{{
	generate if (OPT_PIPELINED)
	begin : GEN_ALU_PC
		reg	[(AW+1):0]	r_alu_pc;
		initial	r_alu_pc = 0;
		always @(posedge i_clk)
		if ((adf_ce_unconditional)
				||((master_ce)&&(op_valid_mem)
					&&(!clear_pipeline)&&(!mem_stalled)))
			r_alu_pc  <= op_pc;
		assign	alu_pc = r_alu_pc;

	end else begin : GEN_ALU_PC_NOPIPE

		assign	alu_pc = op_pc;

	end endgenerate
	// }}}

	// r_alu_illegal
	// {{{
	generate if (OPT_PIPELINED)
	begin : SET_ALU_ILLEGAL
		reg		r_alu_illegal;

		initial	r_alu_illegal = 0;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_alu_illegal <= 1'b0;
		else if (adf_ce_unconditional)
			r_alu_illegal <= op_illegal;
		else
			r_alu_illegal <= 1'b0;

		assign	alu_illegal = (r_alu_illegal);
	end else begin : SET_ALU_ILLEGAL
		assign	alu_illegal = op_illegal;
	end endgenerate
	// }}}

	// r_alu_pc_valid, mem_pc_valid
	// {{{
	initial	r_alu_pc_valid = 1'b0;
	initial	mem_pc_valid = 1'b0;
	always @(posedge i_clk)
	if (clear_pipeline)
		r_alu_pc_valid <= 1'b0;
	else if ((adf_ce_unconditional)&&(!op_phase))
		r_alu_pc_valid <= 1'b1;
	else if (((!alu_busy)&&(!div_busy)&&(!fpu_busy))||(clear_pipeline))
		r_alu_pc_valid <= 1'b0;

	assign	alu_pc_valid = (r_alu_pc_valid)
			&&((!alu_busy)&&(!div_busy)&&(!fpu_busy));

	always @(posedge i_clk)
	if (i_reset)
		mem_pc_valid <= 1'b0;
	else
		mem_pc_valid <= (mem_ce);
	// }}}

	// Bus lock logic
	// {{{
	generate if (OPT_LOCK)
	begin : BUSLOCK
		reg		r_prelock_stall;
		reg	[1:0]	r_bus_lock;
		reg [AW+1:0]	r_lock_pc;

		// r_prelock_stall
		// {{{
		initial	r_prelock_stall = 1'b0;
		always @(posedge i_clk)
		if (!OPT_PIPELINED || clear_pipeline)
			r_prelock_stall <= 1'b0;
		else if (op_valid && op_lock && r_bus_lock == 2'b00
						&& adf_ce_unconditional)
			r_prelock_stall <= 1'b1;
		else if (op_valid && dcd_valid
					&& (i_pf_valid || dcd_early_branch))
			r_prelock_stall <= 1'b0;
		// }}}

		// r_lock_pc
		// {{{
		always @(posedge i_clk)
		if (op_valid && op_ce && op_lock)
			r_lock_pc <= op_pc-4;
`ifdef	FORMAL
		always @(posedge i_clk)
			cover(op_valid && op_ce && op_lock);
`endif
		// }}}

		// r_bus_lock
		// {{{
		// Count 3 cycles.  The lock will only hold solid for three
		// cycles after the LOCK instruction is received.  Count those
		// cycles here.
		initial	r_bus_lock = 2'b00;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_bus_lock <= 2'b00;
		else if (op_valid && (adf_ce_unconditional||mem_ce))
		begin
			if (r_bus_lock != 2'b00)
				r_bus_lock <= r_bus_lock - 1;
			else if (op_lock)
				r_bus_lock <= 2'b11;
		end
		// }}}

		assign	prelock_stall = OPT_PIPELINED && r_prelock_stall;
		assign	o_bus_lock    = |r_bus_lock;
		assign	o_mem_lock_pc = r_lock_pc;
		assign	last_lock_insn = (r_bus_lock <= 1);
`ifdef	FORMAL
		// {{{
		if (OPT_PIPELINED)
		begin
			(* anyconst *) reg r_nojump_lock;

			always @(*)
			if (r_nojump_lock && (r_prelock_stall || r_bus_lock))
			begin
				assume(!dcd_early_branch);
				assume(!dcd_ljmp);
			end

			always @(*)
			if (!clear_pipeline) case(r_bus_lock)
			2'b11: if (!prelock_stall && r_nojump_lock)
				begin
				assert(op_valid && dcd_valid && i_pf_valid);
				end
			2'b10:	begin
				assert(!prelock_stall);
				if (r_nojump_lock)
				begin
					assert(dcd_valid);
					assert(op_valid + dcd_valid + i_pf_valid >= 2'b10);
				end end
			2'b01: begin
				assert(!prelock_stall);
				if (r_nojump_lock && !dcd_illegal)
				begin
					assert(op_valid || dcd_valid
							|| i_pf_valid);
				end end
			2'b00: assert(!prelock_stall);
			endcase
		end else begin

			always @(*)
				assert(!prelock_stall);
		end
		// }}}
`endif
	end else begin : NO_BUSLOCK
		// {{{
		assign	prelock_stall = 1'b0;
		assign	o_bus_lock    = 1'b0;
		assign	o_mem_lock_pc = 0;
		assign	last_lock_insn= 1;
		// }}}
	end endgenerate
	// }}}

	// Memory interface
	// {{{
	// This logic is now managed outside the ZipCore
	//
	assign	o_mem_ce   = mem_ce && set_cond;
	assign	o_mem_op   = ((mem_ce && set_cond) || !OPT_LOWPOWER) ? op_opn[2:0] : 3'h0;
	assign	o_mem_data = ((mem_ce && set_cond) || !OPT_LOWPOWER) ? op_Av : 32'h0;
	assign	o_mem_addr = ((mem_ce && set_cond) || !OPT_LOWPOWER) ? op_Bv : 32'h0;
	assign	o_mem_reg  = ((mem_ce && set_cond) || !OPT_LOWPOWER) ? op_R : 5'h0;

	// }}}

	// Sim instructions, alu_sim, alu_sim_immv
	// {{{
	wire		cpu_sim;

	generate if (OPT_SIM)
	begin : ALU_SIM
		reg		r_alu_sim;
		reg	[22:0]	r_alu_sim_immv;
		wire	[4:0]	regid;

		assign	regid = { (OPT_USERMODE && gie), op_sim_immv[3:0]};

		if (OPT_USERMODE)
		begin : GEN_ALLSIM
			// {{{
			assign	cpu_sim = !i_reset && !clear_pipeline
					&& adf_ce_unconditional && set_cond
					&& op_sim && op_valid_alu
					&&(!wr_reg_ce || !wr_write_pc
						|| wr_reg_id[4] != alu_gie);

			initial	r_alu_sim = 1'b0;
			always @(posedge i_clk)
			begin
				if (cpu_sim)
				begin
				// Execute simulation only instructions
				// {{{
				if ((op_sim_immv[19:10] == 10'h0)&&(op_sim_immv[8]))
				begin // [N/S]EXIT
					// {{{
					$finish;

					// if (op_sim_immv[19:4] == 16'h0031)
						// Exit(User reg), code cpu_wr_gpreg
						// Verilog offers no support for this.
						// Veri1ator might, but it isn't
						// standard.
					// if (op_sim_immv[19:4] == 16'h0030)
						// Exit(Normal reg), code cpu_wr_gpreg
						// $finish;
					// if (op_sim_immv[19:8] == 12'h001)
						// Exit(Immediate), code cpu_wr_gpreg
						// $finish;
					// }}}
				end

				if (op_sim_immv[19:0] == 20'h2ff)
				begin
					// DUMP all registers
					// {{{
					if (!op_gie)
					begin
					$write("sR0 : %08x ", regset[0]);
					$write("sR1 : %08x ", regset[1]);
					$write("sR2 : %08x ", regset[2]);
					$write("sR3 : %08x\n",regset[3]);

					$write("sR4 : %08x ", regset[4]);
					$write("sR5 : %08x ", regset[5]);
					$write("sR6 : %08x ", regset[6]);
					$write("sR7 : %08x\n",regset[7]);

					$write("sR8 : %08x ", regset[8]);
					$write("sR9 : %08x ", regset[9]);
					$write("sR10: %08x ", regset[10]);
					$write("sR11: %08x\n",regset[11]);

					$write("sR12: %08x ", regset[12]);
					$write("sSP : %08x ", regset[13]);
					$write("sCC : %08x ", w_iflags);
					$write("sPC : %08x\n", (!op_gie) ? op_pc : ipc);
					$write("\n", (!op_gie) ? op_pc : ipc);
					end

					$write("uR0 : %08x ", regset[16]);
					$write("uR1 : %08x ", regset[17]);
					$write("uR2 : %08x ", regset[18]);
					$write("uR3 : %08x\n",regset[19]);

					$write("uR4 : %08x ", regset[20]);
					$write("uR5 : %08x ", regset[21]);
					$write("uR6 : %08x ", regset[22]);
					$write("uR7 : %08x\n",regset[23]);

					$write("uR8 : %08x ", regset[24]);
					$write("uR9 : %08x ", regset[25]);
					$write("uR10: %08x ", regset[26]);
					$write("uR11: %08x\n",regset[27]);

					$write("uR12: %08x ", regset[28]);
					$write("uSP : %08x ", regset[29]);
					$write("uCC : %08x ", w_uflags);
					$write("uPC : %08x\n", (op_gie) ? op_pc : upc);
					// }}}
				end

				if (op_sim_immv[19:4] == 16'h0020)
				begin
					// Dump a register
					// {{{
					$write("@%08x ", op_pc);
					$write("%c", (op_gie) ? "s":"u");
					$write("R[%2d] = 0x", op_sim_immv[3:0]);
					// Dump a register
					if (wr_reg_ce && wr_reg_id == regid)
						$display("%08x", wr_gpreg_vl);
					else
						$display("%08x", regset[regid]);
					// }}}
				end
				if (op_sim_immv[19:4] == 16'h0021)
				begin
					// Dump a user register
					// {{{
					$write("@%08x u", op_pc);
					$write("R[%2d] = 0x", op_sim_immv[3:0]);
					if (wr_reg_ce && wr_reg_id == { 1'b1, op_sim_immv[3:0] })
						$display("%08x\n", wr_gpreg_vl);
					else
						$display("%08x\n", regset[{ 1'b1,
								op_sim_immv[3:0]}]);
					// }}}
				end
				if (op_sim_immv[19:4] == 16'h0023)
				begin
					// SOUT(user register)
					// {{{
					if (wr_reg_ce && wr_reg_id == { 1'b1, op_sim_immv[3:0] })
						$write("%c", wr_gpreg_vl[7:0]);
					else
						$write("%c", regset[{ 1'b1, op_sim_immv[3:0]}][7:0]);
					// }}}
				end
				if (op_sim_immv[19:4] == 16'h0022)
				begin
					// SOUT(register)
					// {{{
					if (wr_reg_ce && wr_reg_id == regid)
						$write("%c", wr_gpreg_vl[7:0]);
					else
						$write("%c", regset[regid][7:0]);
					// }}}
				end

				if (op_sim_immv[19:8] == 12'h004)
				begin
					// SOUT(Immediate)
					// {{{
					$write("%c", op_sim_immv[7:0]);
					// }}}
				end

				// ELSE unrecognized SIM instruction

				// Set alu_sim either way
				r_alu_sim <= 1'b1;
				// }}}
				end else
					r_alu_sim <= 1'b0;

				if (adf_ce_unconditional)
					r_alu_sim_immv <= op_sim_immv;
			end
			// }}}
		end else begin : GEN_NO_USERSIM
			// {{{
			assign	cpu_sim = !i_reset && !clear_pipeline
					&& adf_ce_unconditional && set_cond
					&& op_sim && op_valid_alu
					&&(!wr_reg_ce || !wr_write_pc
						|| wr_reg_id[4] != alu_gie);

			initial	r_alu_sim = 1'b0;
			always @(posedge i_clk)
			begin
				if (cpu_sim)
				begin
				// Execute simulation only instructions
				// {{{
				if ((op_sim_immv[19:10] == 10'h0)&&(op_sim_immv[8]))
				begin // [N/S]EXIT
					// {{{
					$finish;

					// if (op_sim_immv[19:4] == 16'h0031)
						// Exit(User reg), code cpu_wr_gpreg
						// Verilog offers no support for this.
						// Veri1ator might, but it isn't
						// standard.
					// if (op_sim_immv[19:4] == 16'h0030)
						// Exit(Normal reg), code cpu_wr_gpreg
						// $finish;
					// if (op_sim_immv[19:8] == 12'h001)
						// Exit(Immediate), code cpu_wr_gpreg
						// $finish;
					// }}}
				end

				if (op_sim_immv[19:0] == 20'h2ff)
				begin
					// DUMP all registers
					// {{{
					if (!op_gie)
					begin
					$write(" R0 : %08x ", regset[0]);
					$write(" R1 : %08x ", regset[1]);
					$write(" R2 : %08x ", regset[2]);
					$write(" R3 : %08x\n",regset[3]);

					$write(" R4 : %08x ", regset[4]);
					$write(" R5 : %08x ", regset[5]);
					$write(" R6 : %08x ", regset[6]);
					$write(" R7 : %08x\n",regset[7]);

					$write(" R8 : %08x ", regset[8]);
					$write(" R9 : %08x ", regset[9]);
					$write(" R10: %08x ", regset[10]);
					$write(" R11: %08x\n",regset[11]);

					$write(" R12: %08x ", regset[12]);
					$write(" SP : %08x ", regset[13]);
					$write(" CC : %08x ", w_iflags);
					$write(" PC : %08x\n", op_pc);
					end

					// }}}
				end

				if (op_sim_immv[19:5] == 15'h0010)
				begin
					// Dump a register
					// {{{
					$write("@%08x ", op_pc);
					$write(" R[%2d] = 0x", op_sim_immv[3:0]);
					// Dump a register
					if (wr_reg_ce&&wr_reg_id[3:0] == regid[3:0])
						$display("%08x", wr_gpreg_vl);
					else
						$display("%08x", regset[regid[3:0]]);
					// }}}
				end
				if (op_sim_immv[19:5] == 15'h0011)
				begin
					// SOUT(user register)
					// {{{
					if (wr_reg_ce && wr_reg_id[3:0] == op_sim_immv[3:0])
						$write("%c", wr_gpreg_vl[7:0]);
					else
						$write("%c", regset[op_sim_immv[3:0]][7:0]);
					// }}}
				end

				if (op_sim_immv[19:8] == 12'h004)
				begin
					// SOUT(Immediate)
					// {{{
					$write("%c", op_sim_immv[7:0]);
					// }}}
				end

				// ELSE unrecognized SIM instruction

				// Set alu_sim either way
				r_alu_sim <= 1'b1;
				// }}}
				end else
					r_alu_sim <= 1'b0;

				if (adf_ce_unconditional)
					r_alu_sim_immv <= op_sim_immv;
			end

			// Verilator lint_off UNUSED
			wire	unused_simmv;
			assign	unused_simmv = &{ 1'b0, regid[4] };
			// Verilator lint_on  UNUSED
			// }}}
		end

		assign	alu_sim      = r_alu_sim;
		assign	alu_sim_immv = r_alu_sim_immv;

	end else begin : NO_ALU_SIM

		assign	alu_sim = 0;
		assign	alu_sim_immv = 0;
		assign	cpu_sim = 0;

	end endgenerate
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PIPELINE STAGE #5 :: Write-back results
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// This stage is not allowed to stall.  If results are ready to be
	// written back, they are written back at all cost.  Sleepy CPU's
	// won't prevent write back, nor debug modes, halting the CPU, nor
	// anything else.  Indeed, the (master_ce) bit is only as relevant
	// as knowinig something is available for writeback.

	// (was) wr_discard, wr_reg_ce
	// {{{
	//
	// Write back to our generic register set ...
	// When shall we write back?  On one of two conditions
	//	Note that the flags needed to be checked before issuing the
	//	bus instruction, so they don't need to be checked here.
	//	Further, alu_wR includes (set_cond), so we don't need to
	//	check for that here either.  It also includes alu_illegal, so
	//	again--doesn't need to be checked again here.

/*
	// 12 inputs.  This implementation is made worse by wr_index.
	always @(*)
	case(wr_index)
	3'b000: wr_reg_ce  = dbgv;
	3'b001: wr_reg_ce  = i_mem_valid;
	//3'b010: wr_reg_ce = (!clear_pipeline)&&(alu_wR && alu_valid);
	3'b011: wr_reg_ce  = (!clear_pipeline)&&(div_valid)&&(!div_error);
	3'b1??: wr_reg_ce  = (!clear_pipeline)&&(fpu_valid)&&(!fpu_error);
	default: wr_reg_ce = (!clear_pipeline)&&(alu_wR && alu_valid);
	endcase
*/
	// 7-LUT -- without FPU or wr_index (which wasn't needed)
	always @(*)
	begin
		wr_reg_ce = dbgv || i_mem_valid;
		if ((alu_wR && alu_valid)
				||(div_valid && !div_error)
				||(fpu_valid && !fpu_error))
			wr_reg_ce = wr_reg_ce || !clear_pipeline;
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset && ((alu_wR && alu_valid)
				||(div_valid && !div_error)
				||(fpu_valid && !fpu_error)))
		assert(!dbgv && !i_mem_valid);

	always @(*)
	if (!i_reset)
	casez(wr_index)
	3'b000: assert(!i_mem_valid && (!alu_wR || !alu_valid)
			&& (!div_valid || div_error)
			&& (!fpu_valid || fpu_error));
	3'b001: assert(!dbgv && (!alu_wR || !alu_valid)
			&& (!div_valid || div_error)
			&& (!fpu_valid || fpu_error));
	3'b010: assert(!dbgv && !i_mem_valid
			// && (!alu_wR || !alu_valid)
			&& (!div_valid || div_error)
			&& (!fpu_valid || fpu_error));
	3'b011: assert(!dbgv && !i_mem_valid
			&& (!alu_wR || !alu_valid)
			// && (!div_valid || div_error)
			&& (!fpu_valid || fpu_error));
	3'b100: assert(!dbgv && !i_mem_valid
			&& (!alu_wR || !alu_valid)
			&& (!div_valid || div_error));
			// && (!fpu_valid || fpu_error);
	default: assert(0);
	endcase
`endif
	// }}}

	// wr_reg_id, wr_write-cc, wr_write_scc, wr_write_ucc, wr_write_pc
	// {{{
	// Which register shall be written?
	//	COULD SIMPLIFY THIS: by adding three bits to these registers,
	//		One or PC, one for CC, and one for GIE match
	//	Note that the alu_reg is the register to write on a divide or
	//	FPU operation.
	generate if (OPT_USERMODE)
	begin : GEN_USERREG
		assign	wr_reg_id = (i_mem_valid) ? i_mem_wreg : alu_reg;
	end else begin : NO_USERREG
		assign	wr_reg_id[3:0] = (i_mem_valid)
					? i_mem_wreg[3:0] : alu_reg[3:0];

		assign	wr_reg_id[4] = 1'b0;
	end endgenerate

	// Are we writing to the CC register?
	// one 5-LUT ea
	assign	wr_write_cc = (wr_reg_id[3:0] == CPU_CC_REG);
	assign	wr_write_scc = (wr_reg_id[4:0] == {1'b0, CPU_CC_REG});
	assign	wr_write_ucc = (wr_reg_id[4:0] == {1'b1, CPU_CC_REG});
	// Are we writing to the PC?
	assign	wr_write_pc = (wr_reg_id[3:0] == CPU_PC_REG);
	// }}}

	// wr_?preg_vl: Select from among sources the value to be writtena
	// {{{
	// One 6-LUT per bit, or 32 6-LUTs w/o FPU
	always @(*)
	casez(wr_index)
	3'b000: wr_gpreg_vl = dbg_val;
	3'b001: wr_gpreg_vl = i_mem_result;
	// 3'b010: wr_gpreg_vl = alu_result;
	3'b011: wr_gpreg_vl = div_result;
	3'b1??: wr_gpreg_vl = fpu_result;
	default: wr_gpreg_vl = alu_result;
	endcase

	// One 6-LUT per bit, or 32 6-LUTs
	always @(*)
	case(wr_index[1:0])
	2'b00: wr_spreg_vl = dbg_val;
	2'b01: wr_spreg_vl = i_mem_result;
	// 3'b010: wr_gpreg_vl = alu_result;
	default: wr_spreg_vl = alu_result;
	endcase
	// }}}

	// Update the register set
	// {{{
	generate if (OPT_USERMODE)
	begin : SET_REGISTERS

		always @(posedge i_clk)
		if (wr_reg_ce)
			regset[wr_reg_id] <= wr_gpreg_vl;

	end else begin : SET_SREGISTERS

		always @(posedge i_clk)
		if (wr_reg_ce)
			regset[wr_reg_id[3:0]] <= wr_gpreg_vl;

	end endgenerate
	// }}}

	//
	// Write back to the condition codes/flags register ...

	// wr_flags_ce : should condition codes be written to?
	// {{{
	// When shall we write to our flags register?  alu_wF already
	// includes the set condition ...
	// assign	wr_flags_ce = (alu_wF)&&((alu_valid)
				// ||(div_valid)||(fpu_valid))
				// &&(!clear_pipeline)&&(!alu_illegal);
/*
	// 10 inputs
	always @(*)
	begin
		wr_flags_ce = 0;
		if (alu_wF && !clear_pipeline) // Includes !alu_illegal in wF
		case(wr_index)
		// 3'b000: wr_flags_ce = 0; // Debug
		// 3'b001: wr_flags_ce = 0; // Memory
		3'b010: wr_flags_ce = alu_valid; // ALU
		3'b011: wr_flags_ce = div_valid && !div_error; // DIV
		3'b1??: wr_flags_ce = fpu_valid && !fpu_error; // FPU
		default: wr_flags_ce = 0;
		endcase
	end
*/
	// 7-LUT -- since we don't need wr_index
	always @(*)
	begin
		wr_flags_ce = alu_valid || (div_valid && !div_error)
				|| (fpu_valid && !fpu_error);
		if (!alu_wF || clear_pipeline)
			wr_flags_ce = 1'b0;
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
	begin
		casez(wr_index)
		3'b000:	assert(wr_flags_ce == 1'b0);
		3'b001:	assert(wr_flags_ce == 1'b0);
		3'b010:	assert(wr_flags_ce == (alu_wF && !clear_pipeline && alu_valid));
		3'b011:	assert(wr_flags_ce == (alu_wF && !clear_pipeline && div_valid && !div_error));
		3'b100:	assert(IMPLEMENT_FPU && wr_flags_ce == (alu_wF && !clear_pipeline && fpu_valid && !fpu_error));
		default: assert(0);
		endcase

		if (alu_illegal)
			assert(!div_valid && !fpu_valid
				&& (!alu_wF || !alu_valid));
	end
`endif
	// }}}

	// wr_flags: what should the new condition codes be?
	// {{{
	always @(*)
	begin
		wr_flags = 0;
		casez(wr_index)
		3'b010: wr_flags = alu_flags;
		3'b011: wr_flags = div_flags;
		3'b1??: wr_flags = fpu_flags;
		default: wr_flags = 0;
		endcase
	end
	// }}}

	// w_uflags, w_iflags : Define the current CC registers
	// {{{
	assign	w_uflags = { 2'b00, uhalt_phase, ufpu_err_flag,
			udiv_err_flag, ubus_err_flag, trap, ill_err_u,
			ubreak, !gie && user_step, 1'b1, sleep,
			(wr_flags_ce &&  alu_gie) ? wr_flags :  flags };
	assign	w_iflags = { 2'b00, ihalt_phase, ifpu_err_flag,
			idiv_err_flag, ibus_err_flag, trap, ill_err_i,
			break_en, 1'b0, 1'b0, sleep,
			(wr_flags_ce && !alu_gie) ? wr_flags : iflags };
	// }}}

	// flags: The user condition codes, Z, C, N, and V
	// {{{
	// What value to write?
	always @(posedge i_clk)
	// If explicitly writing the register itself
	if (wr_reg_ce && wr_write_ucc)
		flags <= wr_gpreg_vl[3:0];
	// Otherwise if we're setting the flags from an ALU operation
	else if (wr_flags_ce && alu_gie)
		flags <= wr_flags;
	// }}}

	// iflags: The supervisor condition codes, Z, C, N, and V
	// {{{
	always @(posedge i_clk)
	if (wr_reg_ce && wr_write_scc)
		iflags <= wr_gpreg_vl[3:0];
	else if (wr_flags_ce && !alu_gie)
		iflags <= wr_flags;
	// }}}

	// break_en
	// {{{
	// The 'break' enable  bit.  This bit can only be set from supervisor
	// mode.  It controls what the CPU does upon encountering a break
	// instruction.
	//
	// The goal, upon encountering a break is that the CPU should stop and
	// not execute the break instruction, choosing instead to enter into
	// either interrupt mode or halt first.
	//	if ((break_en) AND (break_instruction)) // user mode or not
	//		HALT CPU
	//	else if (break_instruction) // only in user mode
	//		set an interrupt flag, set the user break bit,
	//		go to supervisor mode, allow supervisor to step the CPU.
	initial	break_en = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		break_en <= 1'b0;
	else if ((wr_reg_ce)&&(wr_write_scc))
		break_en <= wr_spreg_vl[CPU_BREAK_BIT];
	// }}}

	// break_pending
	// {{{
	generate if (OPT_PIPELINED)
	begin : GEN_PENDING_BREAK
		reg	r_break_pending;

		initial	r_break_pending = 1'b0;
		always @(posedge i_clk)
		if (clear_pipeline || !op_valid)
			r_break_pending <= 1'b0;
		else if (op_break && !r_break_pending)
			r_break_pending <= (!alu_busy)&&(!div_busy)
				&&(!fpu_busy)&&(!i_mem_busy)
				&&(!wr_reg_ce) && (!step || !stepped);
		// else
			// No need to clear this here.  The break will force the
			// pipeline to be cleared above, at which point we can
			// clear this register.
			// r_break_pending <= 1'b0;

		assign	break_pending = r_break_pending;
	end else begin : GEN_BREAK_NOPIPE

		assign	break_pending = op_break;

`ifdef	FORMAL
		always @(*)
		if (!gie && user_step && stepped)
			assert(!op_break);
`endif
	end endgenerate
	// }}}

	// o_break
	// {{{
	//
	// This is a 12-input equation on an output.  Can this be
	// simplified any?  What happens if o_break is set?  Will it ever
	// clear on its own, or does it require a write to the debug port?
	assign	o_break = (break_en || !op_gie)&&(break_pending)
				&&(!clear_pipeline)
			||(ill_err_i)
			||((!alu_gie)&&(i_bus_err))
			||((!alu_gie)&&(div_error))
			||((!alu_gie)&&(fpu_error))
			||((!alu_gie)&&(alu_illegal)&&(!clear_pipeline));

`ifdef	FORMAL
	// Can I assume that, if break_pending is true, that we're either
	// in supervisor mode, or that break_en is set?  If so, can I
	// simplify the calculation above?
	//
	// No, because once break_pending is set, the supervisor can then
	// adjust break_en without adjusting the external break.
	//
	// always @(*)
	// if (break_pending)
	//	assert(!op_gie || break_en);

	always @(*)
	if (!alu_gie && alu_illegal && !clear_pipeline)
		assert(!master_ce);

	// Do I need to break on the last condition above?
	always @(posedge i_clk)
	if (!i_reset && $past(!i_reset && !alu_gie && alu_illegal
						&& !clear_pipeline && !dbgv))
		assert(ill_err_i);

	always @(*)
	if (!i_reset)
		assert(!dbgv || !alu_valid);
`endif
	// }}}

	// sleep
	// {{{
	// The sleep register.  Setting the sleep register causes the CPU to
	// sleep until the next interrupt.  Setting the sleep register within
	// interrupt mode causes the processor to halt until a reset.  This is
	// a panic/fault halt.  The trick is that you cannot be allowed to
	// set the sleep bit and switch to supervisor mode in the same
	// instruction: users are not allowed to halt the CPU.
	initial	sleep = 1'b0;
	generate if (OPT_USERMODE)
	begin : GEN_SLEEP
		// {{{
		initial	sleep = 1'b0;
		always @(posedge i_clk)
		if (i_reset || w_switch_to_interrupt)
			// Wake up on any reset or any switch to supervisor mode
			sleep <= 1'b0;
		else if (wr_reg_ce && wr_write_cc)
		begin
			//
			// !GIE && SLEEP ==> halted
			//  GIE && SLEEP ==> sleep until an interrupt
			//
			if (!alu_gie)
				// In supervisor mode, we have no protections.
				// The supervisor can set the sleep bit however
				// he wants.  Well ... not quite.  Switching to
				// user mode and sleep mode should only be
				// possible if the interrupt flag isn't set.
				// Hence, if an interrupt is pending, then any
				// WAIT instruction essentially becomes a NOOP.
				//
				//	Thus: if (i_interrupt)
				//			&&(wr_spreg_vl[GIE])
				//		don't set the sleep bit
				//	otherwise however it would o.w. be set
				sleep <= (wr_spreg_vl[CPU_SLEEP_BIT])
					&&((!i_interrupt)
						||(!wr_spreg_vl[CPU_GIE_BIT]));
			else if (wr_spreg_vl[CPU_GIE_BIT])
				// In user mode, however, you can only set the
				// sleep mode while remaining in user mode.
				// You can't switch to sleep mode *and*
				// supervisor mode at the same time, lest you
				// halt the CPU.
				sleep <= wr_spreg_vl[CPU_SLEEP_BIT];
		end
		// }}}
	end else begin : GEN_NO_USERMODE_SLEEP
		// {{{
		// Even with no user mode, we still want to implement a sleep
		// instruction.  Here, we create an r_sleep_is_halt to
		// differentiate between the halt and the sleep condition
		// so that the supervisor can still cause the CPU to sleep.
		//
		reg	r_sleep_is_halt;
		initial	r_sleep_is_halt = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_sleep_is_halt <= 1'b0;
		else if (wr_reg_ce && wr_write_cc
				&&  wr_spreg_vl[CPU_SLEEP_BIT]
				&& !wr_spreg_vl[CPU_GIE_BIT])
			// Setting SLEEP and supervisor mode at the same time
			// halts the CPU.  Halts can only be set here.
			// They can only be cleared on reset.
			r_sleep_is_halt <= 1'b1;

		// Trying to switch to user mode, either via a WAIT or an RTU
		// instruction will cause the CPU to sleep until an interrupt,
		// in the NO-USERMODE build.
		always @(posedge i_clk)
		if (i_reset || (i_interrupt && !r_sleep_is_halt))
			sleep <= 1'b0;
		else if ((wr_reg_ce)&&(wr_write_cc)
				&&(wr_spreg_vl[CPU_GIE_BIT]))
			sleep <= 1'b1;
		// }}}
	end endgenerate
	// }}}

	// step : debug single-step control
	// {{{
	initial	user_step = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !OPT_USERMODE)
		user_step <= 1'b0;
	else if ((wr_reg_ce)&&(!alu_gie)&&(wr_write_ucc))
		// The supervisor can adjust whether or not we are stepping
		// the user mode process.  This bit does not automatically
		// clear, but can always be written while in supervisor mode.
		user_step <= wr_spreg_vl[CPU_STEP_BIT];

	assign	step = user_step && gie;
	// }}}

	// o_clken
	// {{{
	generate if (!OPT_CLKGATE)
	begin : NO_CLOCK_GATE

		assign	w_clken = 1'b1;
		assign	o_clken = 1'b1;

	end else begin : GEN_CLOCK_GATE
		reg	r_clken;

		// Actual clock gating signal
		//
		//	= r_clken || (i_interrupt&&!i_halt) || i_dbg_we
		//
		initial	r_clken = !OPT_START_HALTED;
		always @(posedge i_clk)
		if (i_reset)
			r_clken <= !OPT_START_HALTED;
		else if (i_halt && r_halted && (!OPT_DBGPORT || !i_dbg_we))
			r_clken <= i_mem_busy || !i_halt || o_mem_ce;
		else if (!i_halt&& (!sleep || i_interrupt || pending_interrupt))
			r_clken <= 1'b1;
		else // if (sleep || i_halt)
		begin
			r_clken <= 1'b0;

			// If we are in the middle of a lock operation, then
			// don't shut the clock off
			if (o_bus_lock)
				r_clken <= 1'b1;

			// If we are in between two compressed instructions
			// from the same word, then don't disable the clock
			if (alu_phase)
				r_clken <= 1'b1;

			// Don't shut the clock off if we are still busy with
			// any previous operation(s)
			if (i_mem_busy || o_mem_ce
					|| alu_busy || div_busy || fpu_busy
					|| wr_reg_ce ||(OPT_DBGPORT && i_dbg_we)
					|| i_bus_err)
				r_clken <= 1'b1;

			if (i_halt && !r_halted)
				r_clken <= 1'b1;

			// Should we wait for a valid PF result before halting?
			// if (!i_pf_valid) r_clken <= 1'b1;
			// if (!op_valid  && !dcd_illegal)  r_clken <= 1'b1;
			// if (!dcd_valid && !i_pf_illegal) r_clken <= 1'b1;
		end

		assign	w_clken = r_clken;

		// Wake up on interrupts, debug write requests, or the raising
		// of the halt flag if we're not sleeping.
		assign	o_clken = r_clken || (OPT_DBGPORT && i_dbg_we)
					|| i_clear_cache
					|| (!i_halt && (i_interrupt || !sleep));
	end endgenerate
	// }}}

	// gie, switch_to_interrupt, release_from_interrupt, r_user_stepped
	// {{{
	// The GIE register.  Only interrupts can disable the interrupt register
	generate if (OPT_USERMODE)
	begin : GEN_PENDING_INTERRUPT
		// {{{
		reg	r_pending_interrupt;
		reg	r_user_stepped;

		// r_user_stepped is used to make certain that we stop a
		// user task once a full instruction has been accomplished.
		initial	r_user_stepped = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !gie || !user_step)
			r_user_stepped <= 1'b0;
		// else if(w_switch_to_interrupt)
		//	While this is technically what we want, we can wait
		//	a clock cycle to speed up the CPU by not depending upon
		//	the complex w_switch_to_interrupt calculation here
		//	r_user_stepped <= 1'b0;
		else if (op_valid && !op_phase && !op_lock && last_lock_insn
				&& (adf_ce_unconditional || mem_ce))
			r_user_stepped <= 1'b1;

		initial	r_pending_interrupt = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_pending_interrupt <= 1'b0;
		else if (!gie || w_switch_to_interrupt)
			r_pending_interrupt <= 1'b0;
		else if (clear_pipeline && (!user_step || !stepped))
			r_pending_interrupt <= 1'b0;
		else begin
			if (i_interrupt)
				r_pending_interrupt <= 1'b1;

			if (break_pending)
				r_pending_interrupt <= 1'b1;

			if (adf_ce_unconditional && op_illegal)
				r_pending_interrupt <= 1'b1;

			if (((!alu_busy && !i_mem_busy && !div_busy && !fpu_busy)
				|| wr_reg_ce) && user_step && stepped)
				r_pending_interrupt <= 1'b1;
		end

		assign	pending_interrupt = r_pending_interrupt && !i_halt;


		assign	w_switch_to_interrupt = (gie)&&(
			// On interrupt (obviously)
			((pending_interrupt)
				&&(!alu_phase)&&(!o_bus_lock)&&(!i_mem_busy))
			//
			// On division by zero.  If the divide isn't
			// implemented, div_valid and div_error will be short
			// circuited and that logic will be bypassed
			||(div_error)
			//
			// Same thing on a floating point error.  Note that
			// fpu_error must *never* be set unless fpu_valid is
			// also set as well, else this will fail.
			||(fpu_error)
			//
			//
			||(i_bus_err)
			//
			// If we write to the CC register
			||((wr_reg_ce)&&(!wr_spreg_vl[CPU_GIE_BIT])
				&&(wr_reg_id[4])&&(wr_write_cc))
			);
		assign	w_release_from_interrupt = (!gie)&&(!i_interrupt)
			// Then if we write the sCC register
			&&(((wr_reg_ce)&&(wr_spreg_vl[CPU_GIE_BIT])
				&&(wr_write_scc))
			);

`ifdef	FORMAL
		always @(posedge i_clk)
		if (r_pending_interrupt && gie && !clear_pipeline)
			assert(i_interrupt || user_step || alu_illegal
					|| ill_err_u || break_pending);

		always @(posedge i_clk)
		if (f_past_valid && $past(user_step && stepped && !o_bus_lock
							&& !o_dbg_stall))
			assert(!gie || r_pending_interrupt);
`endif
		assign	stepped = r_user_stepped;
		// }}}
	end else begin : NO_PENDING_INTS
		// {{{
		assign	w_switch_to_interrupt    = 1'b0;
		assign	w_release_from_interrupt = 1'b0;
		assign	pending_interrupt = 1'b0;
		assign	stepped = 1'b0;

		// Verilator lint_off UNUSED
		wire	unused_int_signals;
		assign	unused_int_signals = &{ 1'b0, last_lock_insn };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate

	generate if (OPT_USERMODE)
	begin : SET_GIE

		reg	r_gie;

		initial	r_gie = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_gie <= 1'b0;	// Supervisor mode
		else if (w_switch_to_interrupt)
			r_gie <= 1'b0;	// Supervisor mode
		else if (w_release_from_interrupt)
			r_gie <= 1'b1;	// User mode

		assign	gie = r_gie;
	end else begin : ZERO_GIE

		assign	gie = 1'b0;

	end endgenerate
	// }}}

	// trap, ubreak
	// {{{
	generate if (OPT_USERMODE)
	begin : SET_TRAP_N_UBREAK
		// {{{

		reg	r_trap;
		reg	r_ubreak;

		// A trap is generated when the user writes to the CC
		// register to clear the GIE bit.  This is how the supervisor
		// can tell that supervisor mode was entered by a request from
		// usermode.
		initial	r_trap = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(w_release_from_interrupt))
			r_trap <= 1'b0;
		else if (wr_reg_ce && wr_write_ucc)
		begin
			if (!alu_gie)
				// The trap bit can only be cleared by the
				// supervisor.
				r_trap <= (r_trap)&&(wr_spreg_vl[CPU_TRAP_BIT]);
			else if (!wr_spreg_vl[CPU_GIE_BIT]) // && alu_gie
				// Execute a trap
				r_trap <= !dbgv;
		end

		// A user break is an indication of an exception.  Something
		// went wrong.  When entering supervisor mode, if this bit
		// is set the supervisor then knows something went wrong in
		// userspace that needs to be looked into.
		initial	r_ubreak = 1'b0;
		always @(posedge i_clk)
		if (i_reset || w_release_from_interrupt)
			r_ubreak <= 1'b0;
		else if (op_gie && break_pending && w_switch_to_interrupt)
			// Breaks are set when a BREAK instruction is accepted
			// for execution from the OP stage, *and* when in user
			// mode
			r_ubreak <= 1'b1;
		else if ((!alu_gie || dbgv)&&(wr_reg_ce)&&(wr_write_ucc))
			// Allow the supervisor or debug port to clear this
			// register--but not to set it
			r_ubreak <= (ubreak)&&(wr_spreg_vl[CPU_BREAK_BIT]);

		assign	trap = r_trap;
		assign	ubreak = r_ubreak;
		// }}}
	end else begin : NO_USERTRAP

		assign	trap   = 1'b0;
		assign	ubreak = 1'b0;

	end endgenerate
	// }}}

	// ill_err_i, ill_err_u: Illegal instruction flags
	// {{{
	initial	ill_err_i = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		ill_err_i <= 1'b0;
	else if (dbgv && wr_write_scc)
		// Only the debug interface (or a CPU reset) can clear the
		// supervisor's illegal instruction flag
		ill_err_i <= (ill_err_i)&&(wr_spreg_vl[CPU_ILL_BIT]);
	else if (!alu_gie && alu_illegal && !clear_pipeline)
		// The supervisor's illegal instruction flag is set in
		// supervisor (not user) mode, on trying to execute the illegal
		// instruction
		ill_err_i <= 1'b1;

	generate if (OPT_USERMODE)
	begin : SET_USER_ILLEGAL_INSN

		reg	r_ill_err_u;

		//
		// The user's illegal instruction exception flag.  Used and
		// cleared by the supervisor.
		//

		initial	r_ill_err_u = 1'b0;
		always @(posedge i_clk)
		// The bit is automatically cleared on release from interrupt
		// or reset
		if (i_reset || w_release_from_interrupt)
			r_ill_err_u <= 1'b0;
		else if ((!alu_gie || dbgv)&&(wr_reg_ce)&&(wr_write_ucc))
			// Either the supervisor or the debugger can clear this
			// bit.  (Neither can set it)
			r_ill_err_u <=((ill_err_u)&&(wr_spreg_vl[CPU_ILL_BIT]));
		else if (alu_gie && alu_illegal && !clear_pipeline)
			// This flag is set if the CPU ever attempts to execute
			// an illegal instruction while in user mode.
			r_ill_err_u <= 1'b1;

		assign	ill_err_u = r_ill_err_u;

	end else begin : NO_USER_ILL

		assign	ill_err_u = 1'b0;

	end endgenerate
	// }}}

	// ibus_err_flag, ubus_err_flag : Bus error flags
	// {{{
	// Supervisor/interrupt bus error flag -- this will crash the CPU if
	// ever set.
	initial	ibus_err_flag = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		ibus_err_flag <= 1'b0;
	else if ((dbgv)&&(wr_write_scc))
		ibus_err_flag <= (ibus_err_flag)&&(wr_spreg_vl[CPU_BUSERR_BIT]);
	else if ((i_bus_err)&&(!alu_gie))
		ibus_err_flag <= 1'b1;

	// User bus error flag -- if ever set, it will cause an interrupt to
	// supervisor mode.
	generate if (OPT_USERMODE)
	begin : SET_USER_BUSERR

		reg	r_ubus_err_flag;

		initial	r_ubus_err_flag = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(w_release_from_interrupt))
			r_ubus_err_flag <= 1'b0;
		else if (((!alu_gie)||(dbgv))&&(wr_reg_ce)&&(wr_write_ucc))
			r_ubus_err_flag <= (ubus_err_flag)&&(wr_spreg_vl[CPU_BUSERR_BIT]);
		else if ((i_bus_err)&&(alu_gie))
			r_ubus_err_flag <= 1'b1;

		assign	ubus_err_flag = r_ubus_err_flag;
	end else begin : NO_USER_BUSERR

		assign	ubus_err_flag = 1'b0;

	end endgenerate
	// }}}

	// idiv_err_flag, udiv_err_flag : Divide by zero error flags
	// {{{
	generate if (OPT_DIV != 0)
	begin : DIVERR
		// {{{
		reg	r_idiv_err_flag;

		// Supervisor/interrupt divide (by zero) error flag -- this will
		// crash the CPU if ever set.  This bit is thus available for us
		// to be able to tell if/why the CPU crashed.
		initial	r_idiv_err_flag = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_idiv_err_flag <= 1'b0;
		else if ((dbgv)&&(wr_write_scc))
			r_idiv_err_flag <= (r_idiv_err_flag)&&(wr_spreg_vl[CPU_DIVERR_BIT]);
		else if ((div_error)&&(!alu_gie))
			r_idiv_err_flag <= 1'b1;

		assign	idiv_err_flag = r_idiv_err_flag;

		if (OPT_USERMODE)
		begin : USER_DIVERR

			reg	r_udiv_err_flag;

			// User divide (by zero) error flag -- if ever set, it will
			// cause a sudden switch interrupt to supervisor mode.
			initial	r_udiv_err_flag = 1'b0;
			always @(posedge i_clk)
			if ((i_reset)||(w_release_from_interrupt))
				r_udiv_err_flag <= 1'b0;
			else if (((!alu_gie)||(dbgv))&&(wr_reg_ce)
					&&(wr_write_ucc))
				r_udiv_err_flag <= (r_udiv_err_flag)&&(wr_spreg_vl[CPU_DIVERR_BIT]);
			else if ((div_error)&&(alu_gie))
				r_udiv_err_flag <= 1'b1;

			assign	udiv_err_flag = r_udiv_err_flag;
		end else begin : NO_USER_DIVERR
			assign	udiv_err_flag = 1'b0;
		end
		// }}}
	end else begin : NO_DIVERR
		// {{{
		assign	idiv_err_flag = 1'b0;
		assign	udiv_err_flag = 1'b0;
		// }}}
	end endgenerate
	// }}}

	// ifpu_err_flag, ufpu_err_flag : Floating point error flag(s)
	// {{{
	generate if (IMPLEMENT_FPU !=0)
	begin : FPUERR
		// {{{
		// Supervisor/interrupt floating point error flag -- this will
		// crash the CPU if ever set.
		reg		r_ifpu_err_flag, r_ufpu_err_flag;
		initial	r_ifpu_err_flag = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_ifpu_err_flag <= 1'b0;
		else if ((dbgv)&&(wr_write_scc))
			r_ifpu_err_flag <= (r_ifpu_err_flag)&&(wr_spreg_vl[CPU_FPUERR_BIT]);
		else if ((fpu_error)&&(fpu_valid)&&(!alu_gie))
			r_ifpu_err_flag <= 1'b1;
		// User floating point error flag -- if ever set, it will cause
		// a sudden switch interrupt to supervisor mode.
		initial	r_ufpu_err_flag = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)&&(w_release_from_interrupt))
			r_ufpu_err_flag <= 1'b0;
		else if (((!alu_gie)||(dbgv))&&(wr_reg_ce)
				&&(wr_write_ucc))
			r_ufpu_err_flag <= (r_ufpu_err_flag)&&(wr_spreg_vl[CPU_FPUERR_BIT]);
		else if ((fpu_error)&&(alu_gie)&&(fpu_valid))
			r_ufpu_err_flag <= 1'b1;

		assign	ifpu_err_flag = r_ifpu_err_flag;
		assign	ufpu_err_flag = r_ufpu_err_flag;
		// }}}
	end else begin : NO_FPUERR
		// {{{
		assign	ifpu_err_flag = 1'b0;
		assign	ufpu_err_flag = 1'b0;
		// }}}
	end endgenerate
	// }}}

	// ihalt_phase, uhalt_phase : If an instruction was broken when halting
	// {{{
	generate if (OPT_CIS)
	begin : GEN_IHALT_PHASE
		reg		r_ihalt_phase;

		initial	r_ihalt_phase = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_ihalt_phase <= 1'b0;
		else if ((!alu_gie)&&(alu_pc_valid)&&(!clear_pipeline))
			r_ihalt_phase <= alu_phase;

		assign	ihalt_phase = r_ihalt_phase;
	end else begin : GEN_IHALT_PHASE

		assign	ihalt_phase = 1'b0;

	end endgenerate

	generate if ((!OPT_CIS) || (!OPT_USERMODE))
	begin : GEN_UHALT_PHASE

		assign	uhalt_phase = 1'b0;

	end else begin : GEN_UHALT_PHASE

		reg		r_uhalt_phase;

		initial	r_uhalt_phase = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(w_release_from_interrupt))
			r_uhalt_phase <= 1'b0;
		else if ((alu_gie)&&(alu_pc_valid))
			r_uhalt_phase <= alu_phase;
		else if ((!alu_gie)&&(wr_reg_ce)&&(wr_write_pc)
				&&(wr_reg_id[4]))
			r_uhalt_phase <= wr_spreg_vl[1];

		assign	uhalt_phase = r_uhalt_phase;

	end endgenerate
	// }}}

	// ipc, upc: Program counters
	// {{{
	//
	// Write backs to the PC register, and general increments of it
	//	We support two: upc and ipc.  If the instruction is normal,
	// we increment upc, if interrupt level we increment ipc.  If
	// the instruction writes the PC, we write whichever PC is appropriate.
	//
	// Do we need to all our partial results from the pipeline?
	// What happens when the pipeline has gie and !gie instructions within
	// it?  Do we clear both?  What if a gie instruction tries to clear
	// a non-gie instruction?

	// upc
	generate if (OPT_USERMODE)
	begin : SET_USER_PC
		// {{{
		reg	[(AW+1):0]	r_upc;

		always @(posedge i_clk)
		if ((wr_reg_ce)&&(wr_reg_id[4])&&(wr_write_pc))
			r_upc <= { wr_spreg_vl[(AW+1):2], 2'b00 };
		else if ((alu_gie)&&
				(((alu_pc_valid)&&(!clear_pipeline)&&(!alu_illegal))
				||(mem_pc_valid)))
			r_upc <= alu_pc;

		assign	upc = r_upc;
		// }}}
	end else begin : NO_UPC
		// {{{
		assign	upc = {(AW+2){1'b0}};
		// }}}
	end endgenerate

	// ipc
	// {{{
	initial	ipc = { RESET_BUS_ADDRESS, 2'b00 };
	always @(posedge i_clk)
	if (i_reset)
		ipc <= { RESET_BUS_ADDRESS, 2'b00 };
	else if ((wr_reg_ce)&&(!wr_reg_id[4])&&(wr_write_pc))
		ipc <= { wr_spreg_vl[(AW+1):2], 2'b00 };
	else if ((!alu_gie)&&(!alu_phase)&&
			(((alu_pc_valid)&&(!clear_pipeline)&&(!alu_illegal))
			||(mem_pc_valid)))
		ipc <= alu_pc;
	// }}}
	// }}}

	// pf_pc : the program counter used by the pre-fetch
	// {{{

	// pfpcset, pfpcsrc
	// {{{
	always @(*)
	begin
		pfpcset = 0;
		pfpcsrc = 0;
		if (i_reset)
		begin
			pfpcsrc = 0;
			pfpcset = 1;
		end else if ((dbgv)&&(wr_reg_ce)&&(wr_reg_id[4] == gie && wr_write_pc))
		begin
			pfpcsrc = 1; // spreg
			pfpcset = 1;
		end else if ((w_switch_to_interrupt)
				||((!gie)&&((o_clear_icache)||(dbg_clear_pipe))))
		begin
			pfpcsrc = 2; // ipc
			pfpcset = 1;
		end else if ((w_release_from_interrupt)||((gie)&&((o_clear_icache)||(dbg_clear_pipe))))
		begin
			pfpcsrc = 3; // upc
			pfpcset = 1;
		end else if ((wr_reg_ce)&&(wr_reg_id[4] == gie && wr_write_pc))
		begin
			pfpcsrc = 1; // spreg
			pfpcset = 1;
		end else if ((dcd_early_branch_stb)&&(!clear_pipeline))
		begin
			pfpcsrc = 4; // branch
			pfpcset = 1;
		end else if ((new_pc)||(o_pf_ready&& i_pf_valid))
		begin
			pfpcsrc = 5; // PC increment
			pfpcset = 1;
		end
	end
	// }}}

	initial pf_pc = { RESET_BUS_ADDRESS, 2'b00 };
	always @(posedge i_clk)
	if (pfpcset)
	case(pfpcsrc)
	3'b000: pf_pc <= { RESET_BUS_ADDRESS, 2'b00 };
	3'b001: pf_pc <= { wr_spreg_vl[(AW+1):2], 2'b00 };
	3'b010: pf_pc <= { ipc[(AW+1):2], 2'b00 };
	3'b011: pf_pc <= { upc[(AW+1):2], 2'b00 };
	3'b100: pf_pc <= { dcd_branch_pc[AW+1:2] + 1'b1, 2'b00 };
	3'b101: pf_pc <= { pf_pc[(AW+1):2] + 1'b1, 2'b00 };
	default: pf_pc <= { RESET_BUS_ADDRESS, 2'b00 };
	endcase
/*
	if (i_reset)
		pf_pc <= { RESET_BUS_ADDRESS, 2'b00 };
	else if ((dbg_clear_pipe)&&(wr_reg_ce)&&(wr_write_pc))
		pf_pc <= { wr_spreg_vl[(AW+1):2], 2'b00 };
	else if ((w_switch_to_interrupt)
			||((!gie)&&((o_clear_icache)||(dbg_clear_pipe))))
		pf_pc <= { ipc[(AW+1):2], 2'b00 };
	else if ((w_release_from_interrupt)||((gie)&&((o_clear_icache)||(dbg_clear_pipe))))
		pf_pc <= { upc[(AW+1):2], 2'b00 };
	else if ((wr_reg_ce)&&(wr_reg_id[4] == gie)&&(wr_write_pc))
		pf_pc <= { wr_spreg_vl[(AW+1):2], 2'b00 };
	else if ((dcd_early_branch_stb)&&(!clear_pipeline))
		pf_pc <= { dcd_branch_pc[AW+1:2] + 1'b1, 2'b00 };
	else if ((new_pc)||((!pf_stalled)&&(i_pf_valid)))
		pf_pc <= { pf_pc[(AW+1):2] + 1'b1, 2'b00 };
*/
	// }}}

	initial	last_write_to_cc = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_write_to_cc <= 1'b0;
	else
		last_write_to_cc <= (wr_reg_ce)&&(wr_write_cc);
	assign	cc_write_hold = (wr_reg_ce && wr_write_cc)||(last_write_to_cc);

	// o_clear_icache
	// {{{
	// If we aren't pipelined, or equivalently if we have no cache, these
	// instructions will get quietly (or not so quietly) ignored by the
	// optimizer.
	initial	r_clear_icache = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		r_clear_icache <= 1'b0;
	else if (i_clear_cache && !o_dbg_stall)
		r_clear_icache <= 1'b1;
	else if ((wr_reg_ce)&&(wr_write_scc))
		r_clear_icache <=  wr_spreg_vl[CPU_CLRICACHE_BIT];
	else
		r_clear_icache <= 1'b0;

	assign	o_clear_icache = r_clear_icache;
	// }}}

	// o_clear_dcache
	// {{{
	generate if (OPT_DCACHE)
	begin : CLEAR_DCACHE
		reg	r_clear_dcache;

		initial	r_clear_dcache = 1'b1;
		always @(posedge i_clk)
		if (i_reset)
			r_clear_dcache <= 1'b0;
		else if (i_clear_cache && !o_dbg_stall)
			r_clear_dcache <= 1'b1;
		else if ((wr_reg_ce)&&(wr_write_scc))
			r_clear_dcache <=  wr_spreg_vl[CPU_CLRDCACHE_BIT];
		else
			r_clear_dcache <= 1'b0;

		assign	o_clear_dcache = r_clear_dcache;
	end else begin : NOCLEAR_DCACHE

		assign	o_clear_dcache = 1'b0;

	end endgenerate
	// }}}

	// new_pc : does the Prefetch need to clear the pipeline and start over?
	// {{{
	initial	new_pc = 1'b1;
	always @(posedge i_clk)
	if ((i_reset)||(o_clear_icache)||(dbg_clear_pipe))
		new_pc <= 1'b1;
	else if (w_switch_to_interrupt)
		new_pc <= 1'b1;
	else if (w_release_from_interrupt)
		new_pc <= 1'b1;
	// else if ((wr_reg_ce)&&(wr_reg_id[4] == gie)&&(wr_write_pc))
	// Can't check for *this* PC here, since a user PC might be
	// loaded in the pipeline and hence rewritten.  Thus, while
	// I hate to do it, we'll need to clear the pipeline on any
	// PC write
	else if ((wr_reg_ce)&&(alu_gie == wr_reg_id[4])&&(wr_write_pc))
		new_pc <= 1'b1;
	else
		new_pc <= 1'b0;
	// }}}

	//
	// The debug write-back interface
	// {{{

	// debug_pc
	// {{{
	generate if (OPT_USERMODE)
	begin : DBGPC_FULL
		// {{{
		always @(*)
		begin
			debug_pc = 0;
			if (!OPT_DBGPORT)
			begin
				// Empty block--if there's no debug port, we'll
				// leave this valu at zero to reduce power
			end else if (i_dbg_rreg[4])
				// User mode
				debug_pc[(AW+1):0]
					= { upc[(AW+1):2], uhalt_phase, 1'b0 };
			else
				// Supervisor mode
				debug_pc[(AW+1):0]
					= { ipc[(AW+1):2], ihalt_phase, 1'b0 };
		end
		// }}}
	end else begin : DBGPC_NO_USER
		// {{{
		always @(*)
		begin
			debug_pc = 0;
			if (OPT_DBGPORT)
			debug_pc[(AW+1):0] = { ipc[AW+1:2], ihalt_phase, 1'b0 };
		end
		// }}}
	end endgenerate
	// }}}

	// o_dbg_reg
	// {{{
	generate if (!OPT_DBGPORT)
	begin : NO_DBGPORT

		assign	o_dbg_reg = 0;

		// verilator lint_off UNUSED
		wire	unused_dbgport;
		assign	unused_dbgport = &{ 1'b0, i_dbg_rreg, debug_pc };
		// verilator lint_on  UNUSED

	end else if (OPT_USERMODE)
	begin : SETDBG
		// {{{
		reg	[31:0]	pre_dbg_reg, r_dbg_reg;

		if (OPT_DISTRIBUTED_REGS)
		begin : GEN_DISTRIBUTED_RAM_DBG
			// {{{
			always @(*)
				pre_dbg_reg = regset[i_dbg_rreg];

			always @(posedge i_clk)
			begin
				r_dbg_reg <= pre_dbg_reg;
				if (i_dbg_rreg[3:0] == CPU_PC_REG)
					r_dbg_reg <= debug_pc;
				else if (i_dbg_rreg[3:0] == CPU_CC_REG)
				begin
					r_dbg_reg[15:0] <= (i_dbg_rreg[4])
							? w_uflags : w_iflags;
					r_dbg_reg[31:23] <= w_cpu_info;
					r_dbg_reg[CPU_GIE_BIT] <= i_dbg_rreg[4];
				end
			end

			assign	o_dbg_reg = r_dbg_reg;
			// }}}
		end else begin : GEN_BKRAM_DBG
			// {{{
			reg	[1:0]	dbg_reg_sel;
			reg	[31:0]	pre_dbg_special;

			// First clock

			always @(posedge i_clk)
			begin
				dbg_reg_sel[1] <= (i_dbg_rreg[3:1] == 3'h7);
				dbg_reg_sel[0] <= i_dbg_rreg[0];
			end

			always @(posedge i_clk)
				pre_dbg_reg <= regset[i_dbg_rreg];

			always @(posedge i_clk)
			if (i_dbg_rreg[0])
				pre_dbg_special <= debug_pc;
			else begin
				pre_dbg_special <= 0;
				pre_dbg_special[15:0] <= (i_dbg_rreg[4])
							? w_uflags : w_iflags;
				pre_dbg_special[31:23] <= w_cpu_info;
				pre_dbg_special[CPU_GIE_BIT] <= i_dbg_rreg[4];
			end

			// Second clock

			always @(posedge i_clk)
			if (!dbg_reg_sel[1])
				r_dbg_reg <= pre_dbg_reg;
			else if (dbg_reg_sel[0])
				r_dbg_reg <= pre_dbg_special;
			else begin
				r_dbg_reg <= pre_dbg_special;
				r_dbg_reg[22:16] <= pre_dbg_reg[22:16];
			end


			assign	o_dbg_reg = r_dbg_reg;
			// }}}
		end
		// }}}
	end else begin : NO_USER_SETDBG
		// {{{
		reg	[31:0]	r_dbg_reg, pre_dbg_reg;

		if (OPT_DISTRIBUTED_REGS)
		begin : GEN_DISTRIBUTED_RAM_DBG

			always @(*)
				pre_dbg_reg = regset[i_dbg_rreg[3:0]];

			always @(posedge i_clk)
			begin
				r_dbg_reg <= pre_dbg_reg;
				if (i_dbg_rreg[3:0] == CPU_PC_REG)
					r_dbg_reg <= debug_pc;
				else if (i_dbg_rreg[3:0] == CPU_CC_REG)
				begin
					r_dbg_reg[15:0] <= w_iflags;
					r_dbg_reg[31:23] <= w_cpu_info;
					r_dbg_reg[CPU_GIE_BIT] <= 1'b0;
				end
			end
		end else begin : GEN_BKRAM_DBG
			// {{{
			reg	[1:0]	dbg_reg_sel;
			reg	[31:0]	pre_dbg_special;

			// First clock

			always @(posedge i_clk)
			begin
				dbg_reg_sel[1] <= (i_dbg_rreg[3:1] == 3'h7);
				dbg_reg_sel[0] <= i_dbg_rreg[0];
			end

			always @(posedge i_clk)
				pre_dbg_reg <= regset[i_dbg_rreg[3:0]];

			always @(posedge i_clk)
			if (i_dbg_rreg[0])
				pre_dbg_special <= debug_pc;
			else begin
				pre_dbg_special <= 0;
				pre_dbg_special[15:0] <= w_iflags;
				pre_dbg_special[31:23] <= w_cpu_info;
				pre_dbg_special[CPU_GIE_BIT] <= 1'b0;
			end

			// Second clock

			always @(posedge i_clk)
			if (!dbg_reg_sel[1])
				r_dbg_reg <= pre_dbg_reg;
			else if (dbg_reg_sel[0])
				r_dbg_reg <= pre_dbg_special;
			else begin
				r_dbg_reg <= pre_dbg_special;
				r_dbg_reg[22:16] <= pre_dbg_reg[22:16];
			end

			assign	o_dbg_reg = r_dbg_reg;
			// }}}
		end

		assign	o_dbg_reg = r_dbg_reg;
		// }}}
	end endgenerate
	// }}}

	always @(posedge i_clk)
		o_dbg_cc <= { i_bus_err, gie, sleep };

	// r_halted
	// {{{
	generate if (OPT_PIPELINED)
	begin : GEN_HALT_PIPELINED
		// {{{
		initial	r_halted = OPT_START_HALTED;
		always @(posedge i_clk)
		if (i_reset)
			r_halted <= OPT_START_HALTED;
		else if (!i_halt)
			r_halted <= 1'b0;
		else if (r_halted)
			r_halted <= 1'b1;
		else
			r_halted <= (!alu_phase)&&(!o_bus_lock)&&(
				// To be halted, any long lasting instruction
				// must be completed.
				(i_pf_valid)&&(!i_mem_busy)&&(!alu_busy)
					&&(!div_busy)&&(!fpu_busy)
				// Operations must either be valid, or illegal
				&&((dcd_valid)||(dcd_illegal)));
		// }}}
	end else begin : GEN_HALT_NOPIPE
		// {{{
		initial	r_halted = OPT_START_HALTED;
		always @(posedge i_clk)
		if (i_reset)
			r_halted <= OPT_START_HALTED;
		else if (!i_halt)
			r_halted <= 1'b0;
		else if (r_halted)
			r_halted <= 1'b1;
		else
			r_halted <= (!alu_phase)
				// To be halted, any long lasting instruction
				// must be completed.
				&&(i_pf_valid)&&(!i_mem_busy)&&(!alu_busy)
					&&(!div_busy)&&(!fpu_busy);
		// }}}
	end endgenerate
	// }}}

	// o_dbg_stall
	// {{{
	initial	r_dbg_stall = 1'b1;

	always @(posedge i_clk)
	if (i_reset)
		r_dbg_stall <= 1'b1;
	else if (!r_halted || (wr_reg_ce && wr_reg_id[3:1] == 3'h7))
		r_dbg_stall <= 1'b1;
	else
		r_dbg_stall <= (OPT_DBGPORT && i_dbg_we && !o_dbg_stall);

	assign	o_dbg_stall = OPT_DBGPORT && (!r_halted || r_dbg_stall);
	// }}}
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Accounting outputs
	// {{{

	//
	//
	// Produce accounting outputs: Account for any CPU stalls, so we can
	// later evaluate how well we are doing.
	//
	//
	assign	o_op_stall = (master_ce)&&(op_stall);
	assign	o_pf_stall = (master_ce)&&(!i_pf_valid);
	assign	o_i_count  = (alu_pc_valid)&&(!clear_pipeline);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The debug scope output
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_TRACE_PORT)
	begin : GEN_DEBUG_PORT
		localparam [1:0]
				DBGSRC_FLAGS	= 2'b00,
				DBGSRC_WRITEBACK = 2'b01,
				DBGSRC_JUMP	= 2'b10;

		reg	[31:0]	r_debug;
		reg		debug_trigger, dbg_mem_we;
		wire	[27:0]	debug_flags;
		reg	[1:0]	dbgsrc;
		// Verilator lint_off UNUSED
		wire	[27:0]	dbg_pc, dbg_wb_addr;
		// Verilator lint_on  UNUSED


		initial	debug_trigger = 1'b0;
		always @(posedge i_clk)
			debug_trigger <= (!i_halt)&&(o_break);

		always @(posedge i_clk)
		if (o_mem_ce)
			dbg_mem_we <= o_mem_op[0];

		assign debug_flags = { master_ce, i_halt, o_break, sleep,
				gie, ibus_err_flag, trap, ill_err_i,
				o_clear_icache, i_pf_valid, i_pf_illegal, dcd_ce,
				dcd_valid, dcd_stalled, op_ce, op_valid,
				op_pipe, alu_ce, alu_busy, alu_wR,
				alu_illegal, alu_wF, mem_ce, dbg_mem_we,
				i_mem_busy, i_mem_pipe_stalled, (new_pc), (dcd_early_branch) };

		if (AW-1 < 27)
		begin : GEN_SHORT_DBGPC
			assign	dbg_pc[(AW-1):0] = pf_pc[(AW+1):2];
			assign	dbg_pc[27:AW] = 0;

			assign	dbg_wb_addr[(AW-1):0] = 0;
			assign	dbg_wb_addr[27:AW] = 0;
		end else // if (AW-1 >= 27)
		begin : GEN_WIDE_DBGPC
			assign	dbg_pc[27:0] = pf_pc[29:2];
			assign	dbg_wb_addr = 0;
		end

		always @(posedge i_clk)
		begin
			dbgsrc <= 0;
			if ((i_halt)||(!master_ce)||(debug_trigger)||(o_break))
				dbgsrc <= DBGSRC_FLAGS;
			else if ((i_mem_valid)||((!clear_pipeline)&&(!alu_illegal)
					&&(((alu_wR)&&(alu_valid))
						||(div_valid)||(fpu_valid))))
				dbgsrc <= DBGSRC_WRITEBACK;
			else if (clear_pipeline)
				dbgsrc <= DBGSRC_JUMP;
			else
				dbgsrc <= DBGSRC_FLAGS;
		end

		always @(posedge i_clk)
		casez(dbgsrc)
		DBGSRC_FLAGS:
			r_debug <= { debug_trigger, 3'b101,
				debug_flags };
		DBGSRC_WRITEBACK:
			r_debug <= { debug_trigger, 1'b0,
				wr_reg_id[3:0], wr_gpreg_vl[25:0]};
		DBGSRC_JUMP: r_debug <= { debug_trigger, 3'b100,
				dbg_pc };
		default: r_debug <= 32'h0;
		endcase

		assign	o_debug = r_debug;

	end else begin : NO_TRACE_PORT

		assign	o_debug = 32'h0;

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Hardware profiler support
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_PROFILER)
	begin : GEN_PROFILER
		reg			prof_stb;
		reg	[AW+1:0]	prof_addr;
		reg	[31:0]		prof_ticks;

		initial	prof_stb = 1'b0;
		always @(posedge i_clk)
		if (i_reset || clear_pipeline)
			prof_stb <= 1'b0;
		else
			prof_stb <= (alu_pc_valid || mem_pc_valid);

		initial	prof_addr = 0;
		always @(posedge i_clk)
		if (i_reset || clear_pipeline)
			prof_addr <= RESET_ADDRESS[AW+1:0];
		else if (alu_pc_valid || mem_pc_valid)
			prof_addr <= alu_pc;

		initial	prof_ticks = 0;
		always @(posedge i_clk)
		if (i_reset)
			prof_ticks <= 0;
		else if (!i_halt)
			prof_ticks <= prof_ticks + 1;

		assign	o_prof_stb   = prof_stb;
		assign	o_prof_addr  = prof_addr;
		assign	o_prof_ticks = prof_ticks;
	end else begin : NO_PROFILER
		assign	o_prof_stb = 1'b0;
		assign	o_prof_addr = 0;
		assign	o_prof_ticks = 0;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Verilator $display simulation dumping support
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The following is somewhat useful for debugging under Icarus Verilog.
	// In that case, the VCD file can tell you what's going on at any
	// specific moment, but it doesn't put the register set into the VCD
	// file, nor does it give you any insight into the current contents of
	// the memory, or how they got that way.  The following is intended to
	// be a first step towards that end.
	//
	// As currently envisioned, we track values written to the registers,
	// and values read and written to memory.  The program counter offered
	// is typically off by 4 from the actual instruction address being
	// completed.  It may be off by more in the case of memory instructions.
	// I haven't (yet) tried to make the PC given match the instruction
	// address--so that may be an item to do later.
	//
	// You can activate (or de-activate) these instructions via the
	// OPT_SIM_DEBUG flag below.  If set to one, the simulation debuggin
	// statements will be output as the CPU executes.
	localparam	OPT_SIM_DEBUG = 1'b0;
	generate if (OPT_SIM_DEBUG)
	begin : GEN_SIM_DEBUG

		reg [31:0]	nstime;

		initial	nstime = 0;
		always @(posedge i_clk)
			nstime <= nstime + 10;

		always @(posedge i_clk)
		if (!i_reset && o_mem_ce)
		begin
			if (o_mem_reg[4] && !o_mem_op[0])
			begin
				case(o_mem_op[2:1])
				// 3'b000: 
				// 3'b001: 
				2'b01: $display("MEM: %8d LW uR%1d         <- @%08x", nstime, o_mem_reg[3:0], o_mem_addr);
				2'b10: $display("MEM: %8d LH uR%1d         <- @%08x", nstime, o_mem_reg[3:0], o_mem_addr);
				2'b11: $display("MEM: %8d LB uR%1d         <- @%08x", nstime, o_mem_reg[3:0], o_mem_addr);
				default: $display("MEM: %8d Unknown MEM op: %d\n", nstime, o_mem_op);
			endcase
			end else case(o_mem_op[2:0])
			// 3'b000: 
			// 3'b001: 
			3'b010: $display("MEM: %8d LW sR%1d         <- @%08x", nstime, o_mem_reg, o_mem_addr);
			3'b011: $display("MEM: %8d SW 0x%08x -> @%08x", nstime, o_mem_data, o_mem_addr);
			3'b100: $display("MEM: %8d LH sR%1d         <- @%08x", nstime, o_mem_reg, o_mem_addr);
			3'b101: $display("MEM: %8d SH 0x%08x -> @%04x", nstime, o_mem_data[15:0], o_mem_addr);
			3'b110: $display("MEM: %8d LB sR%1d         <- @%08x", nstime, o_mem_reg, o_mem_addr);
			3'b111: $display("MEM: %8d SB 0x%08x -> @%02x", nstime, o_mem_data[7:0], o_mem_addr);
			default: $display("MEM: %8d Unknown MEM op: %d\n", nstime, o_mem_op);
			endcase
		end

		always @(posedge i_clk)
		if (!i_reset && i_bus_err)
		begin
			$display("MEM: %8d BUS ERROR!!", nstime);
		end

		always @(posedge i_clk)
		if (!i_reset && wr_reg_ce)
		begin
			if (i_mem_valid)
			begin
				if (i_mem_wreg[4])
					$display("MEM: %8d Load 0x%08x -> uR%1d", nstime, i_mem_result, i_mem_wreg[3:0]);
				else
					$display("MEM: %8d Load 0x%08x -> sR%1d", nstime, i_mem_result, i_mem_wreg[3:0]);
			end

			if (wr_reg_id[4] && OPT_USERMODE)
			begin
				if (wr_reg_id[3:0] == CPU_PC_REG)
					$display("REG: %8d   uPC          <- 0x%08x [0x%08x]", nstime, wr_spreg_vl, (gie) ? upc : ipc);
				else if (wr_reg_id[3:0] == CPU_CC_REG)
					$display("REG: %8d   uCC          <- 0x%08x [0x%08x]", nstime, wr_spreg_vl, (gie) ? upc : ipc);
				else if (wr_reg_id == 4'hd)
					$display("REG: %8d   uSP          <- 0x%08x [0x%08x]", nstime, wr_gpreg_vl, (gie) ? upc : ipc);
				else
					$display("REG: %8d   uR%1x          <- 0x%08x [0x%08x]", nstime, wr_reg_id[3:0], wr_gpreg_vl, (gie) ? upc : ipc);
			end else begin

				if (wr_reg_id[3:0] == CPU_PC_REG)
					$display("REG: %8d   sPC          <- 0x%08x [0x%08x]", nstime, wr_spreg_vl, ipc);
				else if (wr_reg_id[3:0] == CPU_CC_REG)
					$display("REG: %8d   sCC          <- 0x%08x [0x%08x]", nstime, wr_spreg_vl, ipc);
				else if (wr_reg_id[3:0] == 4'hd)
					$display("REG: %8d   sSP          <- 0x%08x [0x%08x]", nstime, wr_gpreg_vl, ipc);
				else
					$display("REG: %8d   sR%1x          <- 0x%08x [0x%08x]", nstime, wr_reg_id[3:0], wr_gpreg_vl, ipc);
			end
		end
	end endgenerate
	// }}}

	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, fpu_ce, wr_spreg_vl[1:0],
		ipc[1:0], upc[1:0], pf_pc[1:0],
		dcd_rA, dcd_pipe, dcd_zI,
		dcd_A_stall, dcd_B_stall, dcd_F_stall,
		op_Rcc, op_pipe, op_lock, i_mem_pipe_stalled, prelock_stall,
		dcd_F, w_clken };
	generate if (AW+2 < 32)
	begin : UNUSED_AW
		wire	generic_ignore;
		assign	generic_ignore = &{ 1'b0, wr_spreg_vl[31:(AW+2)] };
	end if (!OPT_USERMODE)
	begin : UNUSED_USERMODE
		wire	unused_usermode;
		assign	unused_usermode = &{ 1'b0, alu_reg[4], i_mem_wreg[4],
				i_dbg_rreg[4] };
	end endgenerate
	// verilator lint_on  UNUSED
	// verilator coverage_on
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
	// Declarations
	// {{{
`ifdef	ZIPCPU
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
`define	ASSERT	assert
//
//

	wire	[1+1+4+15+6+4+13+AW+1+32+4+23-1:0]	f_dcd_data;
	wire		fc_op_prepipe;
	wire	[6:0]	fc_alu_Aid;
	wire		fc_alu_wR, fc_alu_M, fc_alu_prepipe;
	reg		f_alu_phase;

	reg		f_past_valid;

	reg	[2:0]	f_dbg_pc_seq, f_dbg_cc_seq, f_dbg_reg_seq;

	wire		fc_op_illegal, fc_op_wF, fc_op_ALU, fc_op_M,
			fc_op_DV, fc_op_FP, fc_op_break,
			fc_op_lock, fc_op_wR, fc_op_rA, fc_op_rB,
			fc_op_sim;
	wire	[6:0]	fc_op_Rid, fc_op_Aid, fc_op_Bid;
	wire	[31:0]	fc_op_I;
	wire	[3:0]	fc_op_cond;
	wire	[3:0]	fc_op_op;
	wire	[22:0]	fc_op_sim_immv;
	wire		f_op_insn; //f_alu_insn,f_wb_insn
	reg		f_op_phase, f_op_early_branch;
	reg		f_op_zI;
	reg	f_op_branch;

	wire	[31:0]	f_Bv;
	reg	[31:0]	f_Av, f_pre_Bv;

	reg	f_alu_branch;

	wire	[31:0]	f_dcd_mem_addr;
	wire	[AW-1:0]	f_next_mem, f_op_mem_addr;
	wire	[4+AW+2+7+4-1:0]	f_op_data;

	wire		fc_alu_illegal, fc_alu_wF, fc_alu_ALU, fc_alu_DV,
			fc_alu_FP, fc_alu_break, fc_alu_lock,
			fc_alu_rA, fc_alu_rB, fc_alu_sim;
	wire	[6:0]	fc_alu_Rid, fc_alu_Bid;
	wire	[31:0]	fc_alu_I;
	wire	[3:0]	fc_alu_cond;
	wire	[3:0]	fc_alu_op;
	wire	[22:0]	fc_alu_sim_immv;

	wire	[F_LGDEPTH-1:0]	f_mem_outstanding;
	wire			f_mem_gie, f_mem_pc, f_read_cycle,
				f_exwrite_cycle;
	wire	[4:0]		f_last_reg, f_addr_reg;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

`ifndef	VERIFIC
	initial	assume(i_reset);
`endif
	always @(posedge i_clk)
	if (!f_past_valid)
		assume(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The debugging interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	fdebug #(
		.OPT_START_HALTED(OPT_START_HALTED),
		.OPT_DISTRIBUTED_RAM(OPT_DISTRIBUTED_REGS)
	) fdbg (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_cpu_reset(i_reset),
		.i_halt(i_halt),
		.i_halted(r_halted),
		.i_clear_cache(i_clear_cache),
		.i_dbg_we(i_dbg_we),
		.i_dbg_reg(i_dbg_wreg),
		.i_dbg_data(i_dbg_data),
		.i_dbg_stall(o_dbg_stall),
		.i_dbg_break(o_break),
		.i_dbg_cc(o_dbg_cc)
		// , .i_dbg_rreg(i_dbg_rreg),
		// .i_dbg_rdata(o_dbg_rdata),
		// }}}
	);

	always @(*)
	if (i_halt && r_halted)
	begin
		`ASSERT(!alu_ce);
		`ASSERT(!alu_phase);
		`ASSERT(!div_ce);
		`ASSERT(!o_mem_ce);
		`ASSERT(f_mem_outstanding == 0);
	end

	initial	f_dbg_pc_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_dbg_pc_seq <= 0;
	else begin
		f_dbg_pc_seq[0] <= i_dbg_we && !o_dbg_stall
				&& (i_dbg_wreg == { gie, CPU_PC_REG });
		f_dbg_pc_seq[2:1] <= f_dbg_pc_seq[1:0];
	end

	always @(posedge i_clk)
	begin
		if (f_dbg_pc_seq[0])
		begin
			`ASSERT(dbgv && alu_reg == { gie, CPU_PC_REG });
		end

		if (f_dbg_pc_seq[1])
		begin
			`ASSERT(clear_pipeline);
			`ASSERT(o_pf_request_address == $past({ i_dbg_data[31:2], 2'b00 },2));
		end
	end

	initial	f_dbg_cc_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_dbg_cc_seq <= 0;
	else begin
		f_dbg_cc_seq[0] <= i_dbg_we && !o_dbg_stall
				&& (i_dbg_wreg == { gie, CPU_CC_REG });
		f_dbg_cc_seq[2:1] <= f_dbg_cc_seq[1:0];
	end

	always @(posedge i_clk)
	if (f_dbg_cc_seq[0])
	begin
		`ASSERT(wr_reg_ce);
		`ASSERT(wr_reg_id == $past(i_dbg_wreg));
		`ASSERT(wr_spreg_vl == $past(i_dbg_data));
	end

	initial	f_dbg_reg_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_dbg_reg_seq <= 0;
	else begin
		f_dbg_reg_seq[0] <= i_dbg_we && !o_dbg_stall
				&& (i_dbg_rreg[3:1] != 3'h7 );
		f_dbg_reg_seq[2:1] <= f_dbg_reg_seq[1:0];
	end

	always @(posedge i_clk)
	begin
		if (f_dbg_reg_seq[0] && !i_reset)
		begin
			`ASSERT(dbgv && alu_reg == $past(i_dbg_wreg));
			`ASSERT($past(i_dbg_rreg[3:1]) != 3'h7);
			`ASSERT(dbg_val == $past(i_dbg_data));

			`ASSERT(wr_reg_ce);
			`ASSERT(wr_gpreg_vl == $past(i_dbg_data));
			`ASSERT(wr_reg_id == $past(i_dbg_wreg));
		end

		// if (f_dbg_reg_seq[1])
		// begin
		// end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		// Initial assertions
		`ASSERT(!i_pf_valid);
		`ASSERT(!dcd_phase);
		`ASSERT(!op_phase);
		`ASSERT(!alu_phase);
		//
		`ASSERT(!i_pf_valid);
		`ASSERT(!dcd_valid);
		`ASSERT(!op_valid);
		`ASSERT(!op_valid_mem);
		`ASSERT(!op_valid_div);
		`ASSERT(!op_valid_alu);
		`ASSERT(!op_valid_fpu);
		//
		`ASSERT(!alu_valid);
		`ASSERT(!alu_busy);
		//
		`ASSERT(!i_mem_valid);
		`ASSERT(!i_mem_rdbusy);
		`ASSERT(!i_bus_err);
		//
		`ASSERT(!div_valid);
		`ASSERT(!div_busy);
		`ASSERT(!div_error);
		//
		`ASSERT(!fpu_valid);
		`ASSERT(!fpu_busy);
		`ASSERT(!fpu_error);
		//
		`ASSERT(!ill_err_i);
		`ASSERT(!ill_err_u);
		`ASSERT(!idiv_err_flag);
		`ASSERT(!udiv_err_flag);
		`ASSERT(!ibus_err_flag);
		`ASSERT(!ubus_err_flag);
		`ASSERT(!ifpu_err_flag);
		`ASSERT(!ufpu_err_flag);
		`ASSERT(!ihalt_phase);
		`ASSERT(!uhalt_phase);
	end

	always @(*)
	begin
		if (i_pf_valid)		`ASSERT(f_past_valid);
		if (dcd_valid)		`ASSERT(f_past_valid);
		if (alu_pc_valid)	`ASSERT(f_past_valid);
		if (i_mem_valid)	`ASSERT(f_past_valid);
		if (div_valid)		`ASSERT(f_past_valid);
		if (fpu_valid)		`ASSERT(f_past_valid);
		if (w_op_valid)		`ASSERT(f_past_valid);
		// if (i_mem_busy)	`ASSERT(f_past_valid);
		if (i_mem_rdbusy)	`ASSERT(f_past_valid);
		if (div_busy)		`ASSERT(f_past_valid);
		if (fpu_busy)		`ASSERT(f_past_valid);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pipeline signaling check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (clear_pipeline)
	begin
		// `ASSERT(!alu_ce);
		`ASSERT(!mem_ce);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(clear_pipeline)))
	begin
		`ASSERT(!alu_busy);
		`ASSERT(!div_busy);
		`ASSERT(!i_mem_rdbusy);
		`ASSERT(!fpu_busy);
		//
		`ASSERT(!alu_valid);
		`ASSERT(!div_valid);
		`ASSERT(!fpu_valid);
	end

	always @(*)
	if (dcd_ce)
		`ASSERT((op_ce)||(!dcd_valid));

	always @(*)
	if ((op_ce)&&(!clear_pipeline))
		`ASSERT((adf_ce_unconditional)||(mem_ce)||(!op_valid));

	//
	// Make sure the dcd stage is never permanently stalled
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(alu_wR))&&(!$past(alu_wF))
		&&($past(f_past_valid,2))&&(!$past(alu_wR,2))&&(!$past(alu_wF))
		&&(!op_valid)&&(master_ce)
		&&(!clear_pipeline)&&(!i_reset)
		&&(!div_busy)&&(!div_valid)
		&&(!i_mem_busy)&&(!i_mem_valid)&&(!i_bus_err)
		&&(!alu_busy)&&(!alu_pc_valid)&&(!alu_valid)
		&&(!fpu_busy)&&(!fpu_valid)&&(!fpu_error)
		&&(!op_break)&&(!o_break)
		&&(!w_switch_to_interrupt)
		&&(!ibus_err_flag)&&(!ill_err_i)&&(!idiv_err_flag))
	begin
		if (OPT_PIPELINED)
			`ASSERT(dcd_ce || cc_invalid_for_dcd || i_halt);
		if (!dcd_valid)
			`ASSERT(dcd_ce);
	end

	always @(posedge i_clk)
	if (OPT_PIPELINED && !i_halt && !i_reset && (wr_flags_ce
			|| (wr_reg_ce && wr_reg_id == { op_gie, CPU_CC_REG })))
		`ASSERT(cc_invalid_for_dcd);

	always @(posedge i_clk)
	if (!f_past_valid || !OPT_PIPELINED)
	begin
		`ASSERT(!cc_invalid_for_dcd);
	end else if (alu_busy)
	begin
		`ASSERT(cc_invalid_for_dcd == (alu_wF || alu_reg == { gie, CPU_CC_REG }));
	end else if (i_mem_rdbusy || i_bus_err)
	begin
		`ASSERT(i_bus_err || f_exwrite_cycle
			|| cc_invalid_for_dcd == (alu_reg == { gie, CPU_CC_REG }));
	end else if (!clear_pipeline && cc_invalid_for_dcd)
	begin
		`ASSERT(alu_illegal || wr_flags_ce
			|| ((i_mem_valid || i_bus_err)
				&& ($past(i_mem_rdbusy
					&& f_last_reg == { gie, CPU_CC_REG })))
			|| (wr_flags_ce || (wr_reg_ce && wr_reg_id == { op_gie, CPU_CC_REG }))
			|| ($past(wr_flags_ce)
				|| $past(wr_reg_ce && wr_reg_id == { op_gie, CPU_CC_REG })));
	end

	//
	// Make sure the ops stage is never permanently stalled
	always @(*)
	if ((op_valid)&&(master_ce)&&(!clear_pipeline)&&(!i_reset)
		&&(!div_busy)&&(!div_valid)
		&&(!i_mem_busy)&&(!i_mem_valid)&&(!i_bus_err)
		&&(!alu_busy)&&(!alu_pc_valid)
		&&(!fpu_busy)&&(!fpu_valid)&&(!fpu_error)
		&&(!op_break)&&(!o_break)
		&&(!w_switch_to_interrupt)
		&&(!alu_illegal) && (!prelock_stall)
		&&(!step || !stepped)
		&&(!ibus_err_flag)&&(!ill_err_i)&&(!idiv_err_flag))
		`ASSERT(adf_ce_unconditional | mem_ce);

	// always @(posedge i_clk)
	// if (f_past_valid&& $past(op_valid && dcd_valid && i_pf_valid
	//			&& !op_ce))
	//	`ASSERT(!prelock_stall);

	//
	// Make sure that, following an op_ce && op_valid, op_valid is only
	// true if dcd_valid was as well
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(op_ce && op_valid && !dcd_valid)))
	begin
		if ($past(dcd_early_branch))
		begin
			`ASSERT(!dcd_early_branch);
		end else
			`ASSERT(!op_valid);
	end

	//
	// Same for the next step
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(op_valid && (mem_ce ||adf_ce_unconditional)))
			&&(!$past(dcd_valid)))
	begin
		if ($past(dcd_early_branch))
		begin
			`ASSERT(!dcd_early_branch);
		end else
			`ASSERT(!op_valid);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the Program counter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (i_pf_valid)
		`ASSERT(i_pf_instruction_pc[1:0]==2'b00);

	always @(*)
	if ((dcd_valid)&&(!dcd_illegal))
		`ASSERT((!dcd_pc[1])||(dcd_phase));

	always @(*)
		`ASSERT(!op_pc[0]);

	always @(*)
		`ASSERT(!alu_pc[0]);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the prefetch (output) stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if ((!clear_pipeline)&&(i_pf_valid))
		`ASSERT(pf_gie == gie);

	always @(*)
	if ((i_pf_valid)&&(!clear_pipeline))
		`ASSERT(pf_gie == gie);

	ffetch #(.ADDRESS_WIDTH(ADDRESS_WIDTH), .OPT_CONTRACT(1'b0),
		.OPT_ALIGNED(1'b1))
	chkifetch(
		.i_clk(i_clk), .i_reset(i_reset),
		.cpu_new_pc(o_pf_new_pc),
		.cpu_clear_cache(o_clear_icache),
		.cpu_pc(o_pf_request_address), .pf_valid(i_pf_valid),
		.cpu_ready(o_pf_ready), .pf_pc(i_pf_instruction_pc),
		.pf_insn(i_pf_instruction), .pf_illegal(i_pf_illegal));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the decode stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	f_dcd_data = {
			dcd_phase,
			dcd_opn, dcd_A, dcd_B, dcd_R,	// 4+15
			dcd_Acc, dcd_Bcc, dcd_Apc, dcd_Bpc, dcd_Rcc, dcd_Rpc,//6
			dcd_F,		// 4
			dcd_wR, dcd_rA, dcd_rB,
				dcd_ALU, dcd_M, dcd_DIV, dcd_FP,
				dcd_wF, dcd_gie, dcd_break, dcd_lock,
				dcd_pipe, dcd_ljmp,
			dcd_pc, 	// AW+1
			dcd_I,		// 32
			dcd_zI,	// true if dcd_I == 0
			dcd_illegal,
			dcd_early_branch,
			dcd_sim, dcd_sim_immv
		};

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(clear_pipeline))
			&&(!$past(o_clear_icache))
			&&($past(dcd_valid))&&($past(dcd_stalled))
			&&(!clear_pipeline))
	begin
		`ASSERT((!OPT_PIPELINED)||(dcd_valid));
		`ASSERT((!dcd_valid && OPT_LOWPOWER) || $stable(f_dcd_data));
		`ASSERT((!dcd_valid && OPT_LOWPOWER) || $stable(f_dcd_insn_word));
	end

	always @(*)
	if ((dcd_valid || dcd_phase)&&(!clear_pipeline))
		`ASSERT(f_dcd_insn_gie == dcd_gie);

	always @(posedge i_clk)
	if ((dcd_valid)&&(!dcd_illegal)&&(!clear_pipeline))
	begin
		`ASSERT(dcd_gie == gie);
		if ((gie)||(dcd_phase))
		begin
			`ASSERT((!dcd_wR)||(dcd_R[4]==dcd_gie));
			`ASSERT((!dcd_rA)||(dcd_A[4]==dcd_gie));
			`ASSERT((!dcd_rB)||(dcd_B[4]==dcd_gie));
		end else if ((!dcd_early_branch)&&((dcd_M)
				||(dcd_DIV)||(dcd_FP)||(!dcd_wR)))
			`ASSERT(!dcd_gie);
		if ((dcd_ALU)&&(dcd_opn==CPU_MOV_OP))
		begin
			`ASSERT(((!dcd_rA)&&(dcd_wR))
				||((!dcd_rA)&&(!dcd_rB)&&(!dcd_wR)));
		end else if (dcd_ALU)
			`ASSERT(
				(gie == dcd_R[4])
				&&(gie == dcd_A[4])
				&&((!dcd_rB)||(gie == dcd_B[4]))
				&&(dcd_gie == gie));
	end

	always @(*)
	if ((op_valid)&&(op_rA)&&(op_Aid[3:1] == 3'h7)&&(!clear_pipeline)
				&&(op_Aid[4:0] != { gie, 4'hf}))
		`ASSERT(!pending_sreg_write);

	always @(*)
	if ((op_valid)&&(op_rB)&&(op_Bid[3:1] == 3'h7)&&(!clear_pipeline)
				&&(op_Bid[4:0] != { gie, 4'hf}))
		`ASSERT(!pending_sreg_write);


	always @(*)
	if ((dcd_valid)&&(!clear_pipeline))
		`ASSERT(dcd_gie == gie);

	//
	//
	// Piped Memory assertions
	//
	//
	always @(*)
	if ((dcd_valid)&&(dcd_M)&&(dcd_pipe)&&(!dcd_illegal)&&(!alu_illegal)
			&&(!break_pending)&&(!clear_pipeline))
	begin
		if (op_valid_mem)
		begin
			`ASSERT(op_opn[0]   == dcd_opn[0]);
			`ASSERT((!dcd_rB)
				||(op_Bid[4:0] == dcd_B[4:0]));
			`ASSERT(op_rB  == dcd_rB);
		end
		`ASSERT(dcd_B[4] == dcd_gie);
	end

	always @(*)
	if (op_valid_mem && op_pipe && i_mem_busy)
		`ASSERT(f_read_cycle == !op_opn[0]);

	always @(*)
	if ((dcd_valid)&&(!dcd_M))
		`ASSERT((dcd_illegal)||(!dcd_pipe));

	assign	f_dcd_mem_addr = w_op_BnI+dcd_I;

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(dcd_early_branch))&&(!dcd_early_branch)
			&&(dcd_valid))
		`ASSERT(!dcd_pipe);
	always @(*)
	if ((dcd_valid)&&(dcd_early_branch))
		`ASSERT(!dcd_M);

	always @(*)
	if ((dcd_valid)&&(!dcd_illegal)&&(!fc_op_prepipe))
		`ASSERT(!dcd_pipe);

	always @(*)
	if ((dcd_valid)&&(dcd_pipe)&&(w_op_valid))
	begin
		// `ASSERT((dcd_A[3:1] != 3'h7)||(dcd_opn[0]));
		`ASSERT(dcd_B[3:1] != 3'h7);
		`ASSERT(dcd_rB);
		`ASSERT(dcd_M);
		`ASSERT(dcd_B == op_Bid);
		if (op_valid)
			`ASSERT((op_valid_mem)||(op_illegal));

		if (op_valid_mem)
		begin
			`ASSERT((dcd_I[AW+1:3] == 0)
				||(!alu_busy)||(!div_busy)
				||(!alu_wR)||(alu_reg != dcd_B));
			`ASSERT((!op_wR)||(op_Aid != op_Bid));
		end
	end

	//
	// Decode option processing
	//

	// OPT_CIS ... the compressed instruction set
	always @(*)
	if ((!OPT_CIS)&&(dcd_valid))
	begin
		`ASSERT(!dcd_phase);
		`ASSERT(dcd_pc[1:0] == 2'b0);
	end

	always @(*)
	if ((dcd_valid)&&(dcd_phase))
		`ASSERT(f_dcd_insn_word[31]);


	// OPT_EARLY_BRANCHING
	always @(*)
	if (!OPT_EARLY_BRANCHING)
		`ASSERT((!dcd_early_branch)
					&&(!dcd_early_branch_stb)
					&&(!dcd_ljmp));

	// OPT_DIV
	always @(*)
	if ((dcd_DIV)&&(dcd_valid)&&(!dcd_illegal))
		`ASSERT(dcd_wR);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the op stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	f_op_data = { op_valid_mem, op_valid_alu,
			op_valid_div, op_valid_fpu,
		// The Av and Bv values can change while we are stalled in the
		// op stage--that's why we are stalled there
		//	r_op_Av, r_op_Bv,	// 32 ea
			op_pc[AW+1:2],		// AW
			op_wR, op_wF,
			r_op_F,			// 7
			op_illegal, op_break,
			op_lock, op_pipe
			};


	always @(posedge i_clk)
	if ((f_past_valid)&&($past(op_valid))&&(!$past(i_reset))
			&&(!$past(clear_pipeline)))
	begin
		if (($past(op_valid_mem))&&($past(mem_stalled)))
			`ASSERT($stable(f_op_data[AW+16:1])&&(!$rose(op_pipe)));
		if (($past(op_valid_div))&&($past(div_busy)))
			`ASSERT($stable(f_op_data));
	end

	f_idecode #(
		// {{{
		.OPT_MPY((OPT_MPY!=0)? 1'b1:1'b0),
		.OPT_SHIFTS(OPT_SHIFTS),
		.OPT_DIVIDE(OPT_DIV),
		.OPT_FPU(IMPLEMENT_FPU),
		.OPT_LOCK(OPT_LOCK),
		.OPT_OPIPE(OPT_PIPELINED_BUS_ACCESS),
		.OPT_SIM(1'b0),
		.OPT_USERMODE(OPT_USERMODE),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_CIS(OPT_CIS)
		// }}}
	) f_insn_decode_op(
		// {{{
		f_op_insn_word, f_op_phase, op_gie,
		fc_op_illegal, fc_op_Rid, fc_op_Aid, fc_op_Bid,
		fc_op_I, fc_op_cond, fc_op_wF, fc_op_op, fc_op_ALU,
		fc_op_M, fc_op_DV, fc_op_FP, fc_op_break, fc_op_lock,
		fc_op_wR, fc_op_rA, fc_op_rB, fc_op_prepipe,
		fc_op_sim, fc_op_sim_immv
		// }}}
	);

	initial	f_op_early_branch = 1'b0;
	always @(posedge i_clk)
	if (op_ce && (!OPT_MEMPIPE || dcd_valid || dcd_illegal || dcd_early_branch))
	begin
		f_op_insn_word <= f_dcd_insn_word;
		f_op_phase <= dcd_phase;
		f_op_early_branch <= dcd_early_branch;
		f_op_zI <= dcd_zI;
	end

	initial	f_op_branch = 1'b0;
	always @(posedge i_clk)
	if ((i_reset)||(clear_pipeline))
		f_op_branch <= 1'b0;
	else if (op_ce)
		f_op_branch <= (dcd_early_branch)||dcd_ljmp;
	else if ((adf_ce_unconditional)||(mem_ce))
		f_op_branch <= 1'b0;

	always @(*)
	if (!OPT_EARLY_BRANCHING)
	begin
		`ASSERT(!f_op_branch);
	end else if ((f_op_early_branch)&&(op_valid))
		`ASSERT(f_op_branch);


	always @(posedge i_clk)
	if (op_valid &&(f_op_branch || !fc_op_illegal)&& !clear_pipeline)
	begin
		// {{{
		if (f_op_branch)
		begin
			// {{{
			`ASSERT(!op_valid_alu);
			`ASSERT(!op_valid_mem);
			`ASSERT(!op_valid_div);
			`ASSERT(!op_valid_fpu);
			`ASSERT(!op_illegal);
			`ASSERT(!op_rA);
			`ASSERT(!op_rB);
			`ASSERT(!op_wR);
			`ASSERT(!op_wF);
			`ASSERT(op_opn == CPU_MOV_OP);
			// }}}
		end

		if (op_illegal)
		begin
			// {{{
			`ASSERT(!op_valid_mem);
			`ASSERT(!op_valid_div);
			`ASSERT(!op_valid_fpu);
			`ASSERT( op_valid_alu);
			`ASSERT((!OPT_PIPELINED)||(!op_rA));
			`ASSERT((!OPT_PIPELINED)||(!op_rB));
			`ASSERT(!f_op_branch);
			// }}}
		end else begin
			if (!f_op_branch)
			begin
				// {{{
				`ASSERT(fc_op_ALU == op_valid_alu);
				`ASSERT(fc_op_M   == op_valid_mem);
				`ASSERT(fc_op_DV  == op_valid_div);
				`ASSERT(fc_op_FP  == op_valid_fpu);
				`ASSERT(fc_op_rA == op_rA);
				`ASSERT(fc_op_rB == op_rB);
				`ASSERT(fc_op_wF == op_wF);
				`ASSERT(fc_op_Rid[4:0] == op_R);
				`ASSERT(f_op_zI == (fc_op_I == 0));
				`ASSERT(fc_op_wF  == op_wF);
				`ASSERT(fc_op_lock == op_lock);
				if (!OPT_PIPELINED && step && stepped)
				begin
					`ASSERT(!op_break);
				end else begin
					`ASSERT(fc_op_break == op_break);
				end
				`ASSERT(fc_op_I == 0 || !i_mem_rdbusy
					|| f_exwrite_cycle
					|| !fc_op_rB
					|| (fc_op_Bid[4:0] != f_last_reg
						&& (f_mem_outstanding <= 1)
						&& (!fc_op_M || !op_pipe))
					|| fc_op_Bid[4:0] == f_addr_reg);
				if (!i_halt && !i_reset && !f_exwrite_cycle)
				`ASSERT((!wr_reg_ce)
					||(wr_reg_id != fc_op_Bid[4:0])
					||(!op_rB)||(fc_op_I == 0));

				`ASSERT(fc_op_sim == op_sim);
				`ASSERT(fc_op_sim_immv == op_sim_immv);

				case(fc_op_cond[2:0])
				3'h0:	`ASSERT(op_F == 8'h00);	// Always
				3'h1:	`ASSERT(op_F == 8'h11);	// Z
				3'h2:	`ASSERT(op_F == 8'h44);	// LT
				3'h3:	`ASSERT(op_F == 8'h22);	// C
				3'h4:	`ASSERT(op_F == 8'h88);	// V
				3'h5:	`ASSERT(op_F == 8'h10);	// NE
				3'h6:	`ASSERT(op_F == 8'h40);	// GE (!N)
				3'h7:	`ASSERT(op_F == 8'h20);	// NC
				endcase

				if ((fc_op_wR)&&(fc_op_Rid[4:0] == { gie, CPU_PC_REG}))
				begin
					`ASSERT(!op_phase);
				end else
					`ASSERT(f_op_phase == op_phase);
				// }}}
			end // Bit order is { (flags_not_used), VNCZ mask, VNCZ value }
			`ASSERT((!op_wR)||(fc_op_Rid[4:0] == op_R));
			`ASSERT(((!op_wR)&&(!op_rA))||(fc_op_Aid[4:0] == op_Aid[4:0]));
			`ASSERT((!op_rB)||(fc_op_Bid[4:0] == op_Bid));
			//
			// if ((!alu_illegal)&&(!ill_err_i)&&(!clear_pipeline))

			if (f_op_early_branch)
			begin
				// {{{
				`ASSERT(op_opn  == CPU_MOV_OP);
				`ASSERT(!op_wR);
				`ASSERT(!op_wF);
				`ASSERT(f_op_branch);
				// }}}
			end else begin
				// {{{
				`ASSERT(fc_op_op  == op_opn);
				`ASSERT(fc_op_wR == op_wR);
				// }}}
			end
		end
		if (!OPT_PIPELINED_BUS_ACCESS)
			`ASSERT((!i_mem_rdbusy)||(i_mem_wreg != fc_op_Bid)
				||(!fc_op_rB)||(fc_op_I == 0));
		// }}}
	end else if (op_valid && !clear_pipeline && fc_op_illegal)
	begin
		// {{{
		`ASSERT(op_illegal);
		`ASSERT(op_valid_alu);
		`ASSERT(!f_op_branch);
		// }}}
	end

	always @(*)
	if ((op_valid)&&(op_illegal))
	begin
		`ASSERT(!op_valid_div);
		`ASSERT(!op_valid_fpu);
		`ASSERT(!op_valid_mem);
	end

//	always @(*)
//	if (!op_valid)
//		`ASSERT(!op_break);

	always @(*)
	if ((!OPT_CIS)&&(op_valid))
	begin
		`ASSERT((!op_phase)||(op_illegal));
		`ASSERT(op_pc[1:0] == 2'b0);
	end

	always @(*)
	if ((!OPT_LOCK)&&(op_valid))
		`ASSERT((!op_lock)||(op_illegal));

	always @(*)
	if (!OPT_EARLY_BRANCHING)
		`ASSERT(!f_op_early_branch);


	always @(*)
	if (op_ce)
		`ASSERT((dcd_valid)||(dcd_illegal)||(dcd_early_branch));

	always @(*)
	if ((f_past_valid)&&(!f_op_zI)&&(i_mem_rdbusy)&&(op_valid)&&(op_rB))
		`ASSERT((!OPT_DCACHE)||(OPT_MEMPIPE)
			||(i_mem_wreg != op_Bid));

	always @(posedge i_clk)
	if ((op_valid)&&(op_rB)&&(!f_op_zI)&&((i_mem_rdbusy)||(i_mem_valid))
		&&(i_mem_wreg != {gie, CPU_PC_REG}))
	begin
		if (!OPT_MEMPIPE)
		begin
			`ASSERT(fc_alu_Aid[4:0] == i_mem_wreg);
			`ASSERT(i_mem_wreg        != op_Bid);
		end
	end

	always @(posedge i_clk)
	if (i_mem_rdbusy)
	begin
		`ASSERT(fc_alu_M);
		`ASSERT(!OPT_PIPELINED||fc_alu_wR || (OPT_LOCK && f_mem_pc));
	end

	always @(*)
	if ((op_valid)&&(!clear_pipeline))
		`ASSERT(op_gie == gie);

	always @(*)
	if ((op_valid_alu)&&(!op_illegal))
	begin
		if ((op_opn != CPU_SUB_OP)
			&&(op_opn != CPU_AND_OP)
			&&(op_opn != CPU_MOV_OP))
		begin
			`ASSERT(op_wR);
		end
		if ((op_opn != CPU_MOV_OP)&&(op_opn != CPU_BREV_OP))
			`ASSERT(op_rA);
	end


	always @(posedge i_clk)
	if ((op_valid)&&(!op_illegal)
			&&(!alu_illegal)&&(!ill_err_i)&&(!clear_pipeline))
	begin
		`ASSERT(op_gie == gie);
		if ((gie)||(op_phase))
		begin
			`ASSERT((!op_wR)||(op_R[4] == gie));
			`ASSERT((!op_rA)||(op_Aid[4] == gie));
			`ASSERT((!op_rB)||(op_Bid[4] == gie));
		end else if (((op_valid_mem)
				||(op_valid_div)||(op_valid_fpu)
				||((op_valid_alu)&&(op_opn!=CPU_MOV_OP))))
		begin
			`ASSERT((!op_wR)||(op_R[4] == gie));
			`ASSERT((!op_rA)||(op_Aid[4] == gie));
			`ASSERT((!op_rB)||(op_Bid[4] == gie));
		end
	end

	always @(posedge i_clk)
	if ((!op_valid)&&(!$past(op_illegal))
			&&(!clear_pipeline)&&(!pending_interrupt))
		`ASSERT(!op_illegal);

	always @(*)
	begin
		if (alu_ce)
			`ASSERT(adf_ce_unconditional);
		if (div_ce)
			`ASSERT(adf_ce_unconditional);
		if (fpu_ce)
			`ASSERT(adf_ce_unconditional);

		if ((op_valid)&&(op_illegal))
			`ASSERT(op_valid_alu);
	end

	always @(*)
	if (mem_ce)
		`ASSERT((op_valid)&&(op_valid_mem)&&(!op_illegal));

	always @(*)
	if (div_ce)
		`ASSERT(op_valid_div);


	always @(*)
	if ((ibus_err_flag)||(ill_err_i)||(idiv_err_flag))
	begin
		`ASSERT(master_stall);
		`ASSERT(!mem_ce);
		`ASSERT(!alu_ce);
		`ASSERT(!div_ce);
		`ASSERT(!adf_ce_unconditional);
	end

	always @(posedge i_clk)
	if ((adf_ce_unconditional)||(mem_ce))
		`ASSERT(op_valid);

	always @(*)
	if ((op_valid_alu)&&(!adf_ce_unconditional)&&(!clear_pipeline))
		`ASSERT(!op_ce);

	always @(*)
	if ((op_valid_div)&&(!adf_ce_unconditional))
		`ASSERT(!op_ce);

	always @(posedge i_clk)
	if (alu_stall)
		`ASSERT(!alu_ce);
	always @(posedge i_clk)
	if (mem_stalled)
		`ASSERT(!o_mem_ce);
	always @(posedge i_clk)
	if (div_busy)
		`ASSERT(!div_ce);

	always @(*)
	if ((!i_reset)&&(break_pending)&&(!clear_pipeline))
		`ASSERT((op_valid)&&(op_break));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Op: Memory pipeline assertions
	//

	assign	f_next_mem    = o_mem_addr + 1'b1;
	assign	f_op_mem_addr = op_Bv[AW+1:2];

	fmem #(
		// {{{
		.OPT_LOCK(OPT_LOCK),
		.F_LGDEPTH(F_LGDEPTH),
		.OPT_MAXDEPTH((OPT_PIPELINED && OPT_PIPELINED_BUS_ACCESS)
					? 14:1),
		.OPT_AXI_LOCK(2)	// Let the solver pick
		// }}}
	) chkmemops(
		// {{{
		.i_clk(i_clk), .i_sys_reset(i_reset), .i_cpu_reset(i_reset),
		//
		.i_stb(o_mem_ce),
		.i_pipe_stalled(i_mem_pipe_stalled),
		.i_clear_cache(o_clear_dcache),
		.i_lock(o_bus_lock),
		.i_op(o_mem_op), .i_data(o_mem_data), .i_addr(o_mem_addr),
			.i_oreg(o_mem_reg), .i_areg(op_Bid),
		.i_busy(i_mem_busy),.i_rdbusy(i_mem_rdbusy),
		.i_valid(i_mem_valid), .i_err(i_bus_err), .i_wreg(i_mem_wreg),
		.i_result(i_mem_result),
		.f_outstanding(f_mem_outstanding),
		.f_pc(f_mem_pc), .f_gie(f_mem_gie),
		.f_read_cycle(f_read_cycle),
		.f_axi_write_cycle(f_exwrite_cycle),
		.f_last_reg(f_last_reg), .f_addr_reg(f_addr_reg)
		// }}}
	);

	always @(*)
	if ((op_valid)&&(!fc_alu_prepipe))
		`ASSERT((!op_valid_mem)||(!op_pipe));

	// Validate op_opn and (some of) op_Bid
	// {{{
	always @(*)
	if ((op_valid_mem)&&(op_pipe))
	begin
		// {{{
		if (i_mem_rdbusy)
			`ASSERT(op_opn[0] == f_exwrite_cycle);
		if (f_mem_outstanding > ((i_bus_err || i_mem_valid) ? 1:0))
			`ASSERT(op_opn[0] != fc_alu_wR);

		// if ((i_mem_busy)&&(!i_mem_rdbusy && !i_mem_valid))
		//	`ASSERT(!o_mem_ce || op_opn[0] == 1'b1);

		if (i_mem_rdbusy)
		begin
			if (OPT_PIPELINED_BUS_ACCESS)
			begin end
			else if (OPT_DCACHE)
				`ASSERT(!i_mem_valid || i_mem_wreg != op_Bid);
		end
		// }}}
	end
	// }}}

	always @(posedge i_clk)
	if (op_valid_mem && op_pipe)
	begin
		// {{{
		if ((i_mem_busy)&&(!OPT_DCACHE))
			`ASSERT((f_op_mem_addr == o_mem_addr)
				||(f_op_mem_addr == f_next_mem));
		if (i_mem_valid)
			`ASSERT(op_Bid != i_mem_wreg);

		if (alu_busy||alu_valid)
			`ASSERT((!alu_wR)||(op_Bid != alu_reg));

		if (f_past_valid)
		begin
			if ((i_mem_busy)&&(!OPT_DCACHE))
			`ASSERT((op_Bv[(AW+1):2]==o_mem_addr[(AW-1):0])
				||(op_Bv[(AW+1):2]==o_mem_addr[(AW-1):0]+1'b1));

			if ($past(mem_ce))
				`ASSERT(op_Bid == $past(op_Bid));
		end

		`ASSERT(op_Bid[3:1] != 3'h7);

		if ((i_mem_rdbusy||i_mem_valid) && !f_exwrite_cycle)
		begin
			if (!OPT_MEMPIPE)
			begin
				// {{{
				`ASSERT(fc_alu_Aid[4:0] == i_mem_wreg);
				`ASSERT(i_mem_wreg     != op_Bid);
				// }}}
			end else if (OPT_DCACHE)
			begin
				// {{{
				`ASSERT(fc_alu_Aid[4:0] != op_Bid);
				// }}}
			end else // if (!OPT_DCACHE)
			begin
				// {{{
				if ((i_mem_valid)
					||($past(i_mem_rdbusy)))
					`ASSERT(i_mem_wreg != op_Bid);
				// }}}
			end
		end
		// }}}
	end

	always @(*)
	if ((dcd_valid)&&(dcd_pipe))
		`ASSERT((op_Aid[3:1] != 3'h7)||(op_opn[0]));

	always @(*)
	if ((op_valid)&(!op_valid_mem))
		`ASSERT((op_illegal)||(!op_pipe));

	// Check f_addr_reg and f_last_reg
	// {{{
	always @(*)
	if (OPT_MEMPIPE && (op_valid && op_rB) && !f_exwrite_cycle
			&&(!f_op_zI)&&(i_mem_rdbusy || i_mem_valid))
		`ASSERT(f_last_reg != op_Bid);

	always @(*)
	if (i_mem_rdbusy && !f_exwrite_cycle)
		`ASSERT(f_last_reg == alu_reg);

	always @(*)
	if ((op_valid_mem)&&(op_pipe) && i_mem_valid)
		`ASSERT(op_Bid != i_mem_wreg);

	always @(*)
	if ((op_valid_mem)&&(op_pipe) && (i_mem_rdbusy || i_mem_valid))
		`ASSERT(op_Bid == f_addr_reg);

	always @(*)
	if (i_mem_rdbusy)
	begin
		if (op_valid_mem && op_pipe)
		begin
			`ASSERT(op_Bid == f_addr_reg);
			`ASSERT(op_Bid != f_last_reg);
			if (dcd_M && dcd_pipe && !dcd_illegal
							&& !dcd_early_branch)
				`ASSERT(op_Bid == dcd_B[4:0]);
		end else if (!op_valid_mem && dcd_M && dcd_pipe
					&& !dcd_illegal && !dcd_early_branch)
			`ASSERT(dcd_B[4:0] == f_addr_reg);
	end
	// }}}

	always @(*)
	if (op_valid && !f_op_zI && i_mem_rdbusy && (f_last_reg != { gie, CPU_PC_REG }))
		`ASSERT(!op_rB || fc_op_Bid[4:0] == f_addr_reg
			||((f_mem_outstanding == 1) && (fc_op_Bid[4:0] != f_last_reg)));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the ALU stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if ((alu_ce)&&(!clear_pipeline))
		`ASSERT((op_valid_alu)&&(op_gie == gie));
	always @(*)
	if ((mem_ce)&&(!clear_pipeline))
		`ASSERT((op_valid_mem)&&(op_gie == gie));
	always @(*)
	if ((div_ce)&&(!clear_pipeline))
		`ASSERT((op_valid_div)&&(op_gie == gie));

	always @(*)
	if ((!clear_pipeline)&&((i_mem_valid)||(div_valid)||(div_busy)
					||(i_mem_rdbusy)||(alu_valid)))
		`ASSERT(alu_gie == gie);
	always @(*)
	if ((!OPT_CIS)&&(alu_pc_valid))
		`ASSERT(alu_pc[1:0] == 2'b0);
	always @(*)
	if (!OPT_LOCK)
		`ASSERT((!o_bus_lock)&&(!prelock_stall));
	always @(*)
	if (!OPT_DIV)
		`ASSERT((!dcd_DIV)&&(!op_valid_div)&&(!div_busy)&&(!div_valid)&&(!div_ce));
	always @(*)
	if (OPT_MPY == 0)
		`ASSERT(alu_busy == 1'b0);


	always @(*)
	if (!clear_pipeline)
	begin
		if ((alu_valid)||(alu_illegal))
			`ASSERT(alu_gie == gie);
		if (div_valid)
			`ASSERT(alu_gie == gie);
	end

	always @(*)
	if (alu_busy)
	begin
		`ASSERT(!i_mem_rdbusy);
		`ASSERT(!div_busy);
		`ASSERT(!fpu_busy);
	end else if (i_mem_rdbusy)
	begin
		`ASSERT(!div_busy);
		`ASSERT(!fpu_busy);
	end else if (div_busy)
		`ASSERT(!fpu_busy);

	always @(posedge i_clk)
	if ((div_valid)||(div_busy))
		`ASSERT(alu_reg[3:1] != 3'h7);

	always @(posedge i_clk)
	if ((f_past_valid)&&(wr_reg_ce)
			&&((!$past(r_halted))||(!$past(i_dbg_we))))
		`ASSERT(alu_gie == gie);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking : A operand
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		f_Av = regset[fc_op_Aid[4:0]];
		if (fc_op_Aid[3:0] == CPU_PC_REG)
		begin
			if ((wr_reg_ce)&&(wr_reg_id == fc_op_Aid[4:0]))
				f_Av = wr_spreg_vl;
			else if (fc_op_Aid[4] == op_gie)
				f_Av = op_pc; // f_next_addr;
			else if (fc_op_Aid[3:0] == { 1'b1, CPU_PC_REG })
			begin
				f_Av[31:(AW+1)] = 0;
				f_Av[(AW+1):0] = { upc, uhalt_phase, 1'b0 };
			end
		end else if (fc_op_Aid[4:0] == { 1'b0, CPU_CC_REG })
		begin
			f_Av = { w_cpu_info, regset[fc_op_Aid[4:0]][22:16], w_iflags };
			if ((wr_reg_ce)&&(wr_reg_id == fc_op_Aid[4:0]))
				f_Av[22:16] = wr_spreg_vl[22:16];
		end else if (fc_op_Aid[4:0] == { 1'b1, CPU_CC_REG })
		begin
			f_Av = { w_cpu_info, regset[fc_op_Aid[4:0]][22:16], w_uflags };
			if ((wr_reg_ce)&&(wr_reg_id == fc_op_Aid[4:0]))
				f_Av[22:16] = wr_spreg_vl[22:16];
		end else if ((wr_reg_ce)&&(wr_reg_id == fc_op_Aid[4:0]))
			f_Av = wr_gpreg_vl;
		else
			f_Av = regset[fc_op_Aid[4:0]];
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking : B operand
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The PRE-logic
	always @(*)
	begin
		f_pre_Bv = regset[fc_op_Bid[4:0]];
		//
		if (fc_op_Bid[3:0] == CPU_PC_REG)
		begin
			// Can always read your own address
			if (fc_op_Bid[4] == op_gie)
				f_pre_Bv = { {(30-AW){1'b0}}, op_pc[(AW+1):2], 2'b00 }; // f_next_addr;
			else // if (fc_op_Bid[4])
				// Supervisor or user may read the users PC reg
			begin
				f_pre_Bv = 0;
				f_pre_Bv[(AW+1):0] = { upc[(AW+1):2], uhalt_phase, 1'b0 };
				if ((wr_reg_ce)&&(wr_reg_id == fc_op_Bid[4:0]))
					f_pre_Bv = wr_spreg_vl;
			end
		end else if (fc_op_Bid[3:0] == CPU_CC_REG)
		begin
			f_pre_Bv = { w_cpu_info, regset[fc_op_Bid[4:0]][22:16],
					w_uflags };
			// if ((fc_op_Bid[4] == op_gie)&&(!fc_op_Bid[4]))
			f_pre_Bv[15:0] = (gie || fc_op_Bid[4]) ? w_uflags : w_iflags;

			if ((wr_reg_ce)&&(wr_reg_id == fc_op_Bid[4:0]))
				f_pre_Bv[22:16] = wr_spreg_vl[22:16];

		end else if ((wr_reg_ce)&&(wr_reg_id == fc_op_Bid[4:0]))
			f_pre_Bv = wr_gpreg_vl;
		else
			f_pre_Bv = regset[fc_op_Bid[4:0]];
	end


	// The actual calculation of B
	assign	f_Bv = (fc_op_rB)
			? ((fc_op_Bid[5])
				? ( { f_pre_Bv }+{ fc_op_I[29:0],2'b00 })
				: (f_pre_Bv + fc_op_I))
			: fc_op_I;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CONTRACT: The operands to an ALU/MEM/DIV operation must be valid.
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (!i_reset && op_valid && !op_illegal
		&& (!clear_pipeline && !dbg_clear_pipe)
		&& (!i_halt || !dbgv)
		&&((!wr_reg_ce)||(wr_reg_id!= { gie, CPU_PC_REG }))
		&&(!f_op_branch))
	begin
		if ((fc_op_rA)&&(fc_op_Aid[3:1] != 3'h7))
			`ASSERT(f_Av == op_Av);

		if (!fc_op_rB || fc_op_Bid[4:0] != { gie, CPU_CC_REG }
				|| !OPT_PIPELINED)
		begin
			`ASSERT(f_Bv == op_Bv);
		end else if (f_op_zI)
			`ASSERT(((f_Bv ^ op_Bv) & 32'hffff_c0ff) == 0);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the ALU stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// alu_valid
	// alu_ce
	// alu_stall
	// ALU stage assertions

	always @(posedge i_clk)
	if ((alu_ce)||(mem_ce)||(div_ce)||(fpu_ce))
	begin
		f_alu_insn_word <= f_op_insn_word;
		f_alu_phase  <= f_op_phase;
	end

	initial	f_alu_branch = 1'b0;
	always @(posedge i_clk)
	if ((adf_ce_unconditional)||(mem_ce))
		f_alu_branch <= f_op_branch;
	else
		f_alu_branch <= 1'b0;

	f_idecode #(
		// {{{
		.OPT_MPY((OPT_MPY!=0)? 1'b1:1'b0),
		.OPT_SHIFTS(OPT_SHIFTS),
		.OPT_DIVIDE(OPT_DIV),
		.OPT_FPU(IMPLEMENT_FPU),
		.OPT_LOCK(OPT_LOCK),
		.OPT_OPIPE(OPT_PIPELINED_BUS_ACCESS),
		.OPT_SIM(1'b0),
		.OPT_USERMODE(OPT_USERMODE),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_CIS(OPT_CIS)
		// }}}
	) f_insn_decode_alu(
		// {{{
		f_alu_insn_word, f_alu_phase, alu_gie,
			fc_alu_illegal, fc_alu_Rid, fc_alu_Aid, fc_alu_Bid,
			fc_alu_I, fc_alu_cond, fc_alu_wF, fc_alu_op, fc_alu_ALU,
			fc_alu_M, fc_alu_DV, fc_alu_FP, fc_alu_break,
			fc_alu_lock, fc_alu_wR, fc_alu_rA, fc_alu_rB,
			fc_alu_prepipe, fc_alu_sim, fc_alu_sim_immv
		// }}}
	);

	always @(posedge i_clk)
	if (!wr_reg_ce)
	begin
		if (f_alu_branch)
		begin
			`ASSERT((!div_valid)&&(!div_busy));
			`ASSERT((!fpu_valid)&&(!fpu_busy));
			`ASSERT(!i_mem_rdbusy);
			`ASSERT(!alu_busy);
		end else begin
			`ASSERT(fc_alu_sim == alu_sim);
			`ASSERT(fc_alu_sim_immv == alu_sim_immv);

			if (!fc_alu_DV)
				`ASSERT((!div_valid)&&(!div_busy)&&(!div_error));
			if (!fc_alu_M)
				`ASSERT(!i_mem_rdbusy);
			if (!fc_alu_ALU)
				`ASSERT(!alu_busy);
			if (!fc_alu_FP)
				`ASSERT((!fpu_busy)&&(!fpu_error));
			if (alu_busy)
				`ASSERT((fc_alu_op[3:1] == 3'h5)
					||(fc_alu_op[3:0] == 4'hc));
			if ((alu_busy)||(div_busy)||(fpu_busy))
			begin
				`ASSERT(!i_mem_rdbusy);
				`ASSERT((clear_pipeline)
					||(fc_alu_Rid[4:0] == alu_reg));
				if (alu_busy)
					`ASSERT(fc_alu_wF == alu_wF);
				if ((fc_alu_Rid[3:1] == 3'h7)&&(alu_wR)
					&&(fc_alu_Rid[4:0] != { gie, 4'hf }))
					`ASSERT(pending_sreg_write);
			end else if (i_mem_rdbusy)
			begin
				if ($past(i_mem_rdbusy))
					`ASSERT(fc_alu_Rid[4] == f_mem_gie);
			end

			//if ((div_busy)||(fpu_busy))
			//	`ASSERT(alu_wR);
			//else
			if ((alu_busy)&&(alu_wR))
				`ASSERT(fc_alu_wR);

			if (alu_busy || i_mem_rdbusy || div_busy)
			begin
				if ((fc_alu_wR)&&(fc_alu_Rid[4:0] == { gie, CPU_PC_REG}))
				begin
					`ASSERT(!alu_phase);
				end else
					`ASSERT(f_alu_phase == alu_phase);
			end
		end

	end else if (!dbgv) // && wr_reg_ce
	begin
		`ASSERT(fc_alu_DV || (!div_valid)&&(!div_error));
		`ASSERT(fc_alu_ALU|| !alu_valid);
		`ASSERT(fc_alu_M  || !i_mem_valid);
		`ASSERT(fc_alu_FP || (!fpu_valid)&&(!fpu_error));
		`ASSERT((!alu_busy)&&(!div_busy)&&(!fpu_busy));

		if ((!alu_illegal)&&(fc_alu_cond[3])&&(fc_alu_wR)&&(fc_alu_ALU))
			`ASSERT(alu_wR);
		if (!i_mem_valid)
			`ASSERT(fc_alu_Rid[4:0] == alu_reg);
		if (f_exwrite_cycle)
		begin
			`ASSERT(!alu_wR);
		end else
			`ASSERT((!alu_wR)||(fc_alu_wR  == alu_wR));
		if (alu_valid)
			`ASSERT(fc_alu_wF == alu_wF);
		if (!fc_alu_wF)
			`ASSERT(!wr_flags_ce);

		`ASSERT(!f_alu_branch);
	end

	always @(posedge i_clk)
	if (f_mem_pc && i_mem_rdbusy)
	begin
		// {{{
		`ASSERT(!OPT_PIPELINED || cc_invalid_for_dcd || !fc_alu_wR
			|| fc_alu_Rid[4:0] != { gie, CPU_CC_REG });
		`ASSERT(!mem_ce);

		if (OPT_PIPELINED && fc_alu_Rid[4:0] != { gie, CPU_PC_REG }
				&& (!OPT_LOCK || fc_alu_wR))
			`ASSERT(pending_sreg_write);
		if ((!OPT_DCACHE)||(!OPT_MEMPIPE))
		begin
			`ASSERT(!fc_alu_prepipe);
		end else if ((i_mem_rdbusy && !f_exwrite_cycle)
				&&(!$past(mem_ce))&&(!$past(mem_ce,2)))
			`ASSERT(!fc_alu_prepipe);
		// }}}
	end else if (i_mem_rdbusy)
	begin
		`ASSERT(!pending_sreg_write);
		// assert(!cc_invalid_for_dcd);
	end

	// Ongoing memory operation check
	// {{{
	always @(posedge i_clk)
	if (i_mem_rdbusy)
	begin
		// In pipelined mode, this is an ongoing load operation
		// Otherwise, mem_rdbusy == i_mem_busy and we have no idea
		// what type of operation we are in
		`ASSERT(!fc_alu_illegal);
		`ASSERT(fc_alu_M);
		`ASSERT(gie == alu_reg[4]);
		if (fc_alu_rB)
			`ASSERT(fc_alu_Bid[4:0] == f_addr_reg);

		if (!f_exwrite_cycle)
		begin
			`ASSERT(alu_reg == f_last_reg);
			if (alu_reg == f_addr_reg)
				`ASSERT(!op_pipe);
		end
		if (fc_alu_cond[3])
			`ASSERT(fc_alu_Rid[4:0] == alu_reg);

		if ((fc_alu_wR)&&(fc_alu_Rid[4:0] == { gie, CPU_PC_REG}))
		begin
			`ASSERT(!alu_phase);
		end else
			`ASSERT(f_alu_phase == alu_phase);

		if (f_exwrite_cycle)
		begin
			`ASSERT(!fc_alu_wR);
		end else
			`ASSERT(fc_alu_wR);
	end else if ((i_mem_busy)&&(fc_alu_M)
		&&(f_mem_outstanding > ((i_mem_valid || i_bus_err) ? 1:0))
		&&(!i_bus_err))
	begin // Ongoing store operation
		// {{{
		`ASSERT(!fc_alu_illegal);
		`ASSERT(fc_alu_M);
		`ASSERT(!fc_alu_wR);
		// }}}
	end
	// }}}

	always @(*)
	if (!fc_alu_wR && i_mem_rdbusy)
	begin
		`ASSERT(OPT_LOCK);
		`ASSERT(f_mem_outstanding == 1);
		`ASSERT(f_mem_pc);
		`ASSERT(!f_read_cycle);
		`ASSERT(!cc_invalid_for_dcd);
		`ASSERT(f_exwrite_cycle);
		// `ASSERT(i_mem_wreg[3:0] == 4'hf);
		`ASSERT(fc_alu_M);
		`ASSERT(!pending_sreg_write);
		`ASSERT(!alu_wR);
	end else if (i_mem_rdbusy)
	begin
		`ASSERT(fc_alu_wR);
		`ASSERT(!f_exwrite_cycle);
		`ASSERT(f_read_cycle);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about the writeback stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset))&&($past(gie) != gie))
		`ASSERT(clear_pipeline);

	always @(*)
	if (!IMPLEMENT_FPU)
	begin
		`ASSERT(!ifpu_err_flag);
		`ASSERT(!ufpu_err_flag);
	end

	always @(posedge i_clk)
	if (dbgv)
	begin
		`ASSERT(wr_index == 3'h0);
		`ASSERT(wr_gpreg_vl == $past(i_dbg_data));
		`ASSERT(wr_spreg_vl == $past(i_dbg_data));
	end

	always @(*)
	if (i_mem_rdbusy || i_mem_valid)
	begin
		`ASSERT(wr_index == 3'h1);
		if (i_mem_valid)
			`ASSERT(wr_gpreg_vl == i_mem_result);
	end

	always @(*)
	if (alu_busy || alu_valid)
	begin
		`ASSERT(wr_index == 3'h2);
		if (alu_valid)
		begin
			`ASSERT(wr_gpreg_vl == alu_result);
			`ASSERT(wr_spreg_vl == alu_result);
		end
	end

	always @(*)
	if (div_busy || div_valid || div_error)
	begin
		`ASSERT(wr_index == 3'h3);
		if (div_valid)
			`ASSERT(wr_gpreg_vl == div_result);
	end

	always @(*)
	if (fpu_busy || fpu_valid || fpu_error)
	begin
		`ASSERT(wr_index == 3'h4);
		if (fpu_valid)
			`ASSERT(wr_gpreg_vl == fpu_result);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(r_halted))
	begin
		`ASSERT(!div_busy);
		`ASSERT(!i_mem_rdbusy);
		`ASSERT(!alu_busy);
		`ASSERT(!div_valid);
		`ASSERT(!i_mem_valid);
		`ASSERT(!alu_valid);
	end

	always @(*)
	if (((wr_reg_ce)||(wr_flags_ce))&&(!dbgv))
		`ASSERT(!alu_illegal);

	always @(*)
	if (!fc_alu_wR && (!OPT_LOCK || !f_mem_pc))
		`ASSERT(!i_mem_rdbusy);

	always @(*)
	if (alu_illegal)
		`ASSERT(!i_mem_rdbusy);

	always @(posedge i_clk)
	if (wr_reg_ce && !$past(i_dbg_we))
	begin
		if (!fc_alu_wR)
			`ASSERT(OPT_LOCK && f_exwrite_cycle);

		// Since writes are asynchronous, they can create errors later
		`ASSERT((!i_bus_err)||(!i_mem_valid));
		`ASSERT(!fpu_error);
		`ASSERT(!div_error);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock enable checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!OPT_CLKGATE)
	begin
		assert(w_clken);
		assert(o_clken);
	end else if (!f_past_valid)
	begin end // clken can be anything on the first clock
	else if ($past(i_reset))
	begin
		assert(w_clken != OPT_START_HALTED);
	end else if ($past((!i_halt || !r_halted) && (!sleep || i_interrupt)))
	begin
		assert(w_clken);
	end else if ($past((i_mem_busy && f_mem_outstanding > 0) || o_mem_ce))
	begin
		assert(w_clken);
	end else if (i_mem_busy || div_busy || alu_busy || fpu_busy)
	begin
		assert(o_clken);
	end else if ($past((i_interrupt || pending_interrupt) && !i_halt))
	begin
		assert(o_clken);
	end else if (!sleep && !r_halted)
	begin
		assert(o_clken);
	end

	// always @(posedge i_clk)
	// if (f_past_valid && i_mem_busy)
	//	assert(!r_halted);

	always @(posedge i_clk)
	if (!OPT_CLKGATE)
	begin
		assert(o_clken);
	end else if (!f_past_valid)
	begin
	end else if (i_dbg_we || i_clear_cache || f_mem_outstanding > 0)
	begin
		assert(o_clken);
	end else if (!i_halt && (i_interrupt || !sleep))
		assert(o_clken);


	always @(posedge i_clk)
	if (!i_reset && sleep)
	begin
		assert(!wr_reg_ce || dbgv);
		assert(!i_mem_rdbusy);
	end

	always @(posedge i_clk)
	if (!i_reset && r_halted)
		assert(!i_mem_rdbusy);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Low power checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// In low power mode, *nothing* should change unless we are doing
	// something.

	generate if (OPT_LOWPOWER && OPT_PIPELINED)
	begin : F_OPT_LOWPOWER_CHECK
		wire	[70:0]	op_state;

		//
		// OP* registers can only be expected to hold steady if
		// pipelined.  If not pipelined, many of these registers
		// become aliases for the decode registers which will
		// (of course) change from one clock to the next.
		//
		assign	op_state = { op_valid_mem, op_valid_div, op_valid_alu,
				op_valid_fpu,
				op_opn, op_R, op_Rcc, op_Aid,
				op_Bid, op_pc,
				r_op_break, op_illegal };

		always @(posedge i_clk)
		if (f_past_valid && !$past(i_reset) && !$past(clear_pipeline)
			&& ($past(op_valid && !adf_ce_unconditional && !mem_ce)
				||($past(!op_valid && !dcd_ljmp) && !op_valid)))
		begin
			assert($stable(op_state));
		end

		always @(posedge i_clk)
		if (f_past_valid && !op_valid)
		begin
			assert(r_op_F == 7'h00);
			assert(!op_wR);
			assert(!op_wF);
			assert(!op_rA);
			assert(!op_rB);

			assert(r_op_Av == 0);
			assert(r_op_Bv == 0);
		end

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (f_past_valid && !i_reset && $past(!gie))
		assert(!stepped);

	always @(posedge i_clk)
	if (f_past_valid && step && stepped)
	begin
		assert(!break_pending);
		assert(!o_bus_lock);
	end

	always @(posedge i_clk)
	if (f_past_valid && !i_reset && !o_bus_lock && !$past(o_bus_lock)
			&& !$past(o_dbg_stall) && !o_dbg_stall)
	begin
		if (step && !stepped)
		begin
			`ASSERT(!i_mem_rdbusy);
			`ASSERT(!div_busy);
			`ASSERT(!alu_busy);
			`ASSERT(!fpu_busy);
		end

		if (wr_reg_ce || wr_flags_ce)
			`ASSERT(!step || stepped);
	end

	always @(posedge i_clk)
	if (!i_reset &&(i_mem_rdbusy|| div_busy|| alu_busy || fpu_busy))
		assert(!r_halted);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && i_mem_busy)
		assert(!$rose(r_halted));

	always @(posedge i_clk)
	if (step && stepped)
	begin
		assert(!adf_ce_unconditional);
		assert(!div_ce);
		assert(!mem_ce);
		assert(!fpu_ce);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Ad-hoc (unsorted) properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_mem_rdbusy))
			&&(!$past(i_mem_valid)
					||($past(i_mem_wreg[3:1] != 3'h7))))
		`ASSERT(!i_mem_valid || i_mem_wreg[4] == alu_gie);

	always @(posedge i_clk)
	if (i_mem_valid)
		`ASSERT(i_mem_wreg[4] == alu_gie);

	always @(posedge i_clk)
	if (i_mem_rdbusy)
		`ASSERT(alu_gie == f_mem_gie);

	always @(posedge i_clk)
	if (f_mem_outstanding > 0)
		`ASSERT(alu_gie == f_mem_gie);



	// Break instructions are not allowed to move past the op stage
	always @(*)
	if ((break_pending)||(op_break))
		`ASSERT((!alu_ce)&&(!mem_ce)&&(!div_ce)&&(!fpu_ce));

	always @(*)
	if (op_break)
		`ASSERT((!alu_ce)&&(!mem_ce)&&(!div_ce)&&(!fpu_ce));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(break_pending))&&(!break_pending))
		`ASSERT((clear_pipeline)||($past(clear_pipeline)));

	always @(*)
	if ((o_break)||((alu_valid)&&(alu_illegal)))
	begin
		`ASSERT(!alu_ce);
		`ASSERT(!mem_ce);
		`ASSERT(!div_ce);
		`ASSERT(!fpu_ce);
		`ASSERT(!i_mem_rdbusy);
		// The following two shouldn't be true, but will be true
		// following a bus error
		if (!i_bus_err)
		begin
			`ASSERT(!alu_busy);
			`ASSERT(!div_busy);
			`ASSERT(!fpu_busy);
		end
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(clear_pipeline))&&
			($past(div_busy))&&(!clear_pipeline))
	begin
		`ASSERT($stable(alu_reg));
		`ASSERT(alu_reg[4] == alu_gie);
		`ASSERT($stable(alu_pc));
		`ASSERT($stable(alu_phase));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!i_reset)
			&&(!$past(clear_pipeline))&&(!clear_pipeline)
			&&(($past(div_busy))||($past(i_mem_rdbusy))))
		`ASSERT($stable(alu_gie));

	always @(posedge i_clk)
	if (i_mem_rdbusy && f_mem_outstanding > 0)
		`ASSERT(!new_pc);

	always @(posedge i_clk)
	if ((wr_reg_ce)&&((wr_write_cc)||(wr_write_pc)))
		`ASSERT(wr_spreg_vl == wr_gpreg_vl);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(clear_pipeline))&&(!$past(i_reset))
		&&($past(op_valid))&&($past(op_illegal))&&(!op_illegal))
		`ASSERT(alu_illegal);

	always @(*)
	if ((OPT_PIPELINED)&&(alu_valid)&&(alu_wR)&&(!clear_pipeline)
			&&(alu_reg[3:1] == 3'h7)
			&&(alu_reg[4:0] != { gie, CPU_PC_REG }))
		`ASSERT(pending_sreg_write);

	always @(posedge i_clk)
	if ((OPT_PIPELINED)&&(i_mem_valid || i_mem_rdbusy)
			&&(f_last_reg[3:1] == 3'h7)
			&&(!f_exwrite_cycle
				&& f_last_reg[4:0] != { gie, CPU_PC_REG }))
	begin
		`ASSERT(pending_sreg_write);
	end else if ((OPT_PIPELINED)&&(OPT_DCACHE)
			&& i_mem_valid
			&&($past(i_mem_rdbusy))
			&&($past(i_mem_rdbusy,2)))
		`ASSERT((i_mem_wreg[3:1] != 3'h7)
			||f_exwrite_cycle
			||(i_mem_wreg == { gie, CPU_PC_REG})
				||(pending_sreg_write));

	always @(*)
	if ((op_valid_alu)||(op_valid_div)||(op_valid_mem)||(op_valid_fpu))
		`ASSERT(op_valid);

	always @(*)
	if (!OPT_PIPELINED)
	begin
		if (op_valid)
		begin
			`ASSERT(!dcd_valid);
			`ASSERT(!i_mem_busy || f_mem_outstanding == 0);
			`ASSERT(!alu_busy);
			`ASSERT(!div_busy);
			`ASSERT((!wr_reg_ce)||(dbgv));
			`ASSERT(!wr_flags_ce);
		end
	end

	always @(posedge i_clk)
	if ((!OPT_PIPELINED)&&(f_past_valid))
	begin
		if (op_valid)
			`ASSERT($stable(f_dcd_insn_word));
	end

	always @(posedge i_clk)
	if ((alu_ce)||(div_ce)||(fpu_ce))
		`ASSERT(adf_ce_unconditional);

	always @(posedge i_clk)
	if ((!clear_pipeline)&&(master_ce)&&(op_ce)&&(op_valid))
	begin
		if (op_valid_mem)
		begin
			`ASSERT((mem_ce)||(!set_cond));
		end else begin
			`ASSERT(!master_stall);
			if ((set_cond)&&(op_valid_div))
				`ASSERT(div_ce||pending_sreg_write);
			if (!op_valid_alu)
				`ASSERT(!alu_ce);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug port read properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	generate if (OPT_DBGPORT)
	begin : CHK_DBGPORT_READS
		reg	[31:0]	f_dbg_check;

		// o_dbg_reg -- Reading from the debugging interface
		if (OPT_DISTRIBUTED_REGS)
		begin : F_CHK_DISTRIBUTED_RAM
			// {{{
			always @(posedge i_clk)
			if ((f_past_valid)&&($past(i_halt))&&(!$past(i_dbg_we)))
			begin
				if ($past(i_dbg_rreg[3:1]) != 3'h7)
					`ASSERT(o_dbg_reg == $past(regset[i_dbg_rreg]));
				if ($past(i_dbg_rreg[4:0]) == 5'h0f)
					`ASSERT(o_dbg_reg[AW+1:0] == $past({ ipc[(AW+1):2], ihalt_phase, 1'b0}));
				if ($past(i_dbg_rreg[4:0]) == 5'h1f)
					`ASSERT(o_dbg_reg[AW+1:0] == $past({ upc[(AW+1):2], uhalt_phase, 1'b0}));
				if ($past(i_dbg_rreg[4:0]) == 5'h0e)
				begin
					`ASSERT(o_dbg_reg[15:6] == $past(w_iflags[15:6]));
					`ASSERT(o_dbg_reg[ 4:0] == $past(w_iflags[ 4:0]));
				end

				if ($past(i_dbg_rreg[4:0]) == 5'h1e)
				begin
					`ASSERT(o_dbg_reg[15:6] == $past(w_uflags[15:6]));
					`ASSERT(o_dbg_reg[ 4:0] == $past(w_uflags[ 4:0]));
				end

				if ($past(i_dbg_rreg[3:0]) == 4'he)
				begin
					`ASSERT(o_dbg_reg[15] == 1'b0);
					`ASSERT(o_dbg_reg[31:23] == w_cpu_info);
					`ASSERT(o_dbg_reg[CPU_GIE_BIT] == $past(i_dbg_rreg[4]));
				end
			end
			// }}}
		end else begin : F_CHK_NO_DISTRIBUTED_RAM
			// {{{
			always @(posedge i_clk)
			if (f_past_valid&&$past(f_past_valid)
					&& $past(i_halt)&&$past(i_halt,2)
					&&(!$past(i_dbg_we)))
			begin
				if ($past(i_dbg_rreg[3:1],2) != 3'h7)
					`ASSERT(o_dbg_reg
						== $past(regset[i_dbg_rreg],2));
			end
			// }}}
		end


		if (OPT_USERMODE)
		begin : CHK_USER
			always @(*)
			begin
				f_dbg_check = regset[i_dbg_rreg];
				case(i_dbg_rreg)
				5'h0e: begin
					f_dbg_check[15:0] = w_iflags;
					f_dbg_check[31:23] = w_cpu_info;
					f_dbg_check[CPU_GIE_BIT] <= 1'b0;
					end
				5'h0f: f_dbg_check[(AW+1):0]
						= { ipc[(AW+1):2], ihalt_phase, 1'b0 };
				5'h1e: begin
					f_dbg_check[15:0] = w_uflags;
					f_dbg_check[31:23] = w_cpu_info;
					f_dbg_check[CPU_GIE_BIT] <= 1'b1;
					end
				5'h1f: f_dbg_check[(AW+1):0]
						= { upc[(AW+1):2], uhalt_phase, 1'b0 };
				default:
					f_dbg_check = regset[i_dbg_rreg];
				endcase
			end
		end else begin : NO_USER
			always @(*)
			begin
				if (OPT_DISTRIBUTED_REGS)
					f_dbg_check = regset[i_dbg_rreg];
				else
					f_dbg_check = 0;
				case(i_dbg_rreg[3:0])
				4'h0e: begin
					f_dbg_check[15:0] = w_iflags;
					f_dbg_check[31:23] = w_cpu_info;
					f_dbg_check[CPU_GIE_BIT] <= 1'b0;
					end
				4'h0f: f_dbg_check[(AW+1):0]
						= { ipc[(AW+1):2], ihalt_phase, 1'b0 };
				default:
					f_dbg_check = regset[i_dbg_rreg[3:0]];
				endcase
			end
		end

		if (OPT_DISTRIBUTED_REGS)
		begin
			always @(posedge i_clk)
			if (!i_reset && !$past(i_reset))
				assert(o_dbg_reg == $past(f_dbg_check));
		end else begin
			always @(posedge i_clk)
			if (!i_reset && !$past(i_reset) && !$past(i_reset,2))
				assert(o_dbg_reg == $past(f_dbg_check,2));
		end

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover statements
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	always @(posedge i_clk)
	begin
		cover(!i_reset);
		cover(!i_halt);	
		cover(!i_reset && !i_halt);
	end

	always @(posedge i_clk)
	if (!i_halt && !i_reset)
	begin
		cover(i_pf_valid &&  i_pf_illegal);
		cover(i_pf_valid && !i_pf_illegal);

		cover(dcd_valid &&  dcd_illegal);
		cover(dcd_valid && !dcd_illegal);

		cover(op_valid && !op_illegal);
		cover(op_valid &&  op_illegal);
		cover(op_valid && !op_illegal && op_ce);
		cover(op_valid &&  op_illegal && op_ce);

		cover(alu_valid);
		cover(div_valid);
		cover(o_mem_ce);
		cover(i_mem_valid);

		cover(wr_reg_ce);

		cover(gie);
	end

	always @(posedge i_clk)
	if (!i_halt && !i_reset && !$past(i_reset))
	begin
		cover(i_interrupt && !alu_phase && !o_bus_lock);
		cover(alu_illegal);
		cover( gie && w_switch_to_interrupt);
		cover(!gie && w_release_from_interrupt);

		// Cover an illegal instruction
		cover(alu_illegal);
		cover(alu_illegal && !clear_pipeline);


		// Cover a break instruction
		cover((master_ce)&&(break_pending)&&(!break_en));
		cover(o_break);
//		if (master_ce && (break_en || break_pending))
//			`ASSERT(!wr_reg_ce);


		cover(gie);
		cover(step);
		cover(step && w_switch_to_interrupt);
		cover(step && w_switch_to_interrupt && !i_interrupt);
	end

	always @(posedge i_clk)
	if (!i_halt && !i_reset && !$past(i_reset))
	begin
		cover(step);
		cover(step && wr_reg_ce);
		cover($fell(step) && $stable(!i_reset && !i_halt));
		cover($past(step && !i_reset && !i_halt));
		cover($past(step && !i_reset && !i_halt,2));
		cover(!o_bus_lock && alu_ce && step);
		cover(user_step && !gie);
		cover(user_step &&  gie);
		cover(user_step &&  gie && wr_reg_ce);

		// Cover a division by zero
		cover(!OPT_DIV || div_busy);
		cover(!OPT_DIV || div_error);
		cover(!OPT_DIV || div_valid);
	end

	generate if (OPT_DIV)
	begin : F_DIVIDE
		always @(posedge i_clk)
		if (!i_halt && !i_reset && !$past(i_reset))
		begin
			// Cover a division by zero
			cover(div_busy);
			cover(div_error);
			cover(div_valid);
		end
	end endgenerate

	generate if (OPT_LOCK)
	begin : F_CVR_LOCK

		always @(posedge i_clk)
		if (f_past_valid && !i_reset
				&& !$past(i_reset || clear_pipeline))
		begin
			cover($rose(o_bus_lock));
			cover($fell(o_bus_lock));
			cover($fell(o_bus_lock)
				&& !$past(i_bus_err || div_error || alu_illegal));
		end

	end else begin

		always @(*)
			`ASSERT(!o_bus_lock);

	end endgenerate

	always @(posedge i_clk)
	if (!i_halt && !i_reset && !$past(i_reset) && wr_reg_ce)
	begin
		`ASSERT(!alu_illegal);
	end

	always @(posedge i_clk)
	if (!i_halt && !i_reset && wr_reg_ce)
	begin
		cover(o_bus_lock);

		// Cover the switch to interrupt
		cover(i_interrupt);
		cover(i_interrupt && !alu_phase);
		cover(i_interrupt && !o_bus_lock);
		cover((i_interrupt)&&(!alu_phase)&&(!o_bus_lock));

		// Cover a "step" instruction
		//
		cover(((alu_pc_valid)||(mem_pc_valid))
				&&(step)&&(!alu_phase)&&(!o_bus_lock));
		// `ASSERT(!(((alu_pc_valid)||(mem_pc_valid))
		//		&&(step)&&(!alu_phase)&&(!o_bus_lock)));

		// Cover a bus error
		cover(i_bus_err);

		// Cover a TRAP instruction to the CC register
		cover(!alu_gie && !wr_spreg_vl[CPU_GIE_BIT]
				&&(wr_reg_id[4])&&(wr_write_cc));

		// Cover an AXI lock return branch
		cover(i_mem_valid && f_exwrite_cycle && !f_read_cycle);
	end

	// Cover all the various reasons to switch to an interrupt
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid && !i_reset && !$past(i_reset) && !i_halt) && gie)
	begin
		cover((pending_interrupt)
				&&(!alu_phase)&&(!o_bus_lock)&&(!i_mem_busy));

		cover(div_error);
		// cover(fpu_error);
		cover(i_bus_err);
		cover(wr_reg_ce && !wr_spreg_vl[CPU_GIE_BIT]
			&& wr_reg_id[4] && wr_write_cc);

		if (!clear_pipeline && !w_switch_to_interrupt)
		begin
			cover(pending_interrupt);

			cover(i_interrupt);

			cover(mem_ce && step);
			cover(break_pending && !adf_ce_unconditional);
			cover(adf_ce_unconditional && op_illegal);
			cover(adf_ce_unconditional && step);
		end

		`ASSERT(!adf_ce_unconditional || !break_pending);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Once asserted, an interrupt will stay asserted while the CPU is
	// in user mode
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_interrupt && (gie || !i_mem_busy))))
		assume(i_interrupt);
	// }}}
`endif	// FORMAL
// }}}
endmodule
