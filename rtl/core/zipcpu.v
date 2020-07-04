////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipwb.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//{{{
// Purpose:	This is the top level module holding the core of the Zip CPU
//		together.  The Zip CPU is designed to be as simple as possible.
//	(actual implementation aside ...)  The instruction set is about as
//	RISC as you can get, with only 26 instruction types currently supported.
//	(There are still 8-instruction Op-Codes reserved for floating point,
//	and 5 which can be used for transactions not requiring registers.)
//	Please see the accompanying spec.pdf file for a description of these
//	instructions.
//
//	All instructions are 32-bits wide.  All bus accesses, both address and
//	data, are 32-bits over a wishbone bus.
//
//	The Zip CPU is fully pipelined with the following pipeline stages:
//
//		1. Prefetch, returns the instruction from memory.
//
//		2. Instruction Decode
//
//		3. Read Operands
//
//		4. Apply Instruction
//
//		4. Write-back Results
//
//	Further information about the inner workings of this CPU, such as
//	what causes pipeline stalls, may be found in the spec.pdf file.  (The
//	documentation within this file had become out of date and out of sync
//	with the spec.pdf, so look to the spec.pdf for accurate and up to date
//	information.)
//
//
//	In general, the pipelining is controlled by three pieces of logic
//	per stage: _ce, _stall, and _valid.  _valid means that the stage
//	holds a valid instruction.  _ce means that the instruction from the
//	previous stage is to move into this one, and _stall means that the
//	instruction from the previous stage may not move into this one.
//	The difference between these control signals allows individual stages
//	to propagate instructions independently.  In general, the logic works
//	as:
//
//
//	assign	(n)_ce = (n-1)_valid && (!(n)_stall)
//
//
//	always @(posedge i_clk)
//		if ((i_reset)||(clear_pipeline))
//			(n)_valid = 0
//		else if (n)_ce
//			(n)_valid = 1
//		else if (n+1)_ce
//			(n)_valid = 0
//
//	assign (n)_stall = (  (n-1)_valid && ( pipeline hazard detection )  )
//			|| (  (n)_valid && (n+1)_stall );
//
//	and ...
//
//	always @(posedge i_clk)
//		if (n)_ce
//			(n)_variable = ... whatever logic for this stage
//
//	Note that a stage can stall even if no instruction is loaded into
//	it.
//
//}}}
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
//{{{
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
//}}}
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
`define	CPU_SUB_OP	4'h0 // also a compare instruction
`define	CPU_AND_OP	4'h1 // also a test instruction
`define	CPU_BREV_OP	4'h8
`define	CPU_MOV_OP	4'hd
//
`define	CPU_CC_REG	4'he
`define	CPU_PC_REG	4'hf
`define	CPU_CLRDCACHE_BIT 15	// Set to clear the D-cache,automatically clears
`define	CPU_CLRICACHE_BIT 14	// Set to clear the I-cache,automatically clears
`define	CPU_PHASE_BIT	13	// Set if we are executing the latter half of a CIS
`define	CPU_FPUERR_BIT	12	// Floating point error flag, set on error
`define	CPU_DIVERR_BIT	11	// Divide error flag, set on divide by zero
`define	CPU_BUSERR_BIT	10	// Bus error flag, set on error
`define	CPU_TRAP_BIT	9	// User TRAP has taken place
`define	CPU_ILL_BIT	8	// Illegal instruction
`define	CPU_BREAK_BIT	7
`define	CPU_STEP_BIT	6	// Will step one (or two CIS) instructions
`define	CPU_GIE_BIT	5
`define	CPU_SLEEP_BIT	4
// Compile time defines
//
`include "cpudefs.v"
//
//
module	zipwb #(
	//{{{
		parameter [31:0] RESET_ADDRESS=32'h010_0000,
		parameter	ADDRESS_WIDTH=30,
				LGICACHE=12,
`ifdef	OPT_MULTIPLY
		parameter	IMPLEMENT_MPY = `OPT_MULTIPLY,
`else
		parameter	IMPLEMENT_MPY = 0,
`endif
`ifdef	OPT_DIVIDE
		parameter [0:0]	IMPLEMENT_DIVIDE = 1,
`else
		parameter [0:0]	IMPLEMENT_DIVIDE = 0,
`endif
`ifdef	OPT_IMPLEMENT_FPU
		parameter [0:0]	IMPLEMENT_FPU = 1,
`else
		parameter [0:0]	IMPLEMENT_FPU = 0,
`endif
`ifdef	OPT_EARLY_BRANCHING
		parameter [0:0]	EARLY_BRANCHING = 1,
`else
		parameter [0:0]	EARLY_BRANCHING = 0,
`endif
`ifdef	OPT_CIS
		parameter [0:0]	OPT_CIS = 1'b1,
`else
		parameter [0:0]	OPT_CIS = 1'b0,
`endif
`ifdef	OPT_NO_USERMODE
		localparam	[0:0]	OPT_NO_USERMODE = 1'b1,
`else
		localparam	[0:0]	OPT_NO_USERMODE = 1'b0,
`endif
`ifdef	OPT_PIPELINED
		parameter	[0:0]	OPT_PIPELINED = 1'b1,
`else
		parameter	[0:0]	OPT_PIPELINED = 1'b0,
`endif
`ifdef	OPT_PIPELINED_BUS_ACCESS
		localparam	[0:0]	OPT_PIPELINED_BUS_ACCESS = (OPT_PIPELINED),
`else
		localparam	[0:0]	OPT_PIPELINED_BUS_ACCESS = 1'b0,
`endif
		localparam	[0:0]	OPT_MEMPIPE = OPT_PIPELINED_BUS_ACCESS,
		parameter	[0:0]	IMPLEMENT_LOCK=1,
		localparam	[0:0]	OPT_LOCK=(IMPLEMENT_LOCK)&&(OPT_PIPELINED),
`ifdef	OPT_DCACHE
		parameter		OPT_LGDCACHE = 10,
`else
		parameter		OPT_LGDCACHE = 0,
`endif
		localparam	[0:0]	OPT_DCACHE = (OPT_LGDCACHE > 0),

		parameter [0:0]	WITH_LOCAL_BUS = 1'b1,
		localparam	AW=ADDRESS_WIDTH,
		localparam	[(AW-1):0]	RESET_BUS_ADDRESS = RESET_ADDRESS[(AW+1):2],
		parameter	F_LGDEPTH=8
	// }}}
	) (
	// I/O declarations
	//{{{
	input	wire		i_clk, i_reset, i_interrupt,
	// Debug interface -- inputs
	input	wire		i_halt, i_clear_pf_cache,
	input	wire	[4:0]	i_dbg_reg,
	input	wire		i_dbg_we,
	input	wire	[31:0]	i_dbg_data,
	// Debug interface -- outputs
	output	wire		o_dbg_stall,
	output	reg	[31:0]	o_dbg_reg,
	output	reg	[3:0]	o_dbg_cc,
	output	wire		o_break,
	// CPU interface to the wishbone bus
	// Wishbone interface -- outputs
	output	wire		o_wb_gbl_cyc, o_wb_gbl_stb,
	output	wire		o_wb_lcl_cyc, o_wb_lcl_stb, o_wb_we,
	output	wire	[(AW-1):0]	o_wb_addr,
	output	wire	[31:0]	o_wb_data,
	output	wire	[3:0]	o_wb_sel,
	// Wishbone interface -- inputs
	input	wire		i_wb_stall, i_wb_ack,
	input	wire	[31:0]	i_wb_data,
	input	wire		i_wb_err,
	// Accounting outputs ... to help us count stalls and usage
	output	wire		o_op_stall,
	output	wire		o_pf_stall,
	output	wire		o_i_count,
	//
`ifdef	DEBUG_SCOPE
	, output	reg	[31:0]	o_debug
	// output	wire	[31:0]	o_dcache_debug;
`endif
	//}}}
	);



	zipcore #(
		.RESET_ADDRESS(RESET_ADDRESS),
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.IMPLEMENT_MPY(IMPLEMENT_MPY),
		.IMPLEMENT_DIVIDE(IMPLEMENT_DIVIDE),
		.IMPLEMENT_FPU(IMPLEMENT_FPU),
		.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
		.OPT_CIS(OPT_CIS),
		.OPT_NO_USERMODE(OPT_NO_USERMODE),
		.OPT_PIPELINED(OPT_PIPELINED),
		.OPT_PIPELINED_BUS_ACCESS(OPT_PIPELINED_BUS_ACCESS),
		// localparam	[0:0]	OPT_MEMPIPE = OPT_PIPELINED_BUS_ACCESS;
		.IMPLEMENT_LOCK(IMPLEMENT_LOCK),
		// localparam	[0:0]	OPT_LOCK=(IMPLEMENT_LOCK)&&(OPT_PIPELINED);
		// parameter [0:0]	WITH_LOCAL_BUS = 1'b1;
		// localparam	AW=ADDRESS_WIDTH;
		// localparam	[(AW-1):0]	RESET_BUS_ADDRESS = RESET_ADDRESS[(AW+1):2];
		.F_LGDEPTH(F_LGDEPTH)
	) core (i_clk, i_reset, i_interrupt,
		// Debug interface
		i_halt, i_clear_pf_cache, i_dbg_reg, i_dbg_we, i_dbg_data,
			o_dbg_stall, o_dbg_reg, o_dbg_cc,
			o_break,
		// CPU interface to the instruction fetch unit
		o_pf_new_pc, o_clear_icache, o_pf_ready,
				o_pf_request_address,
			i_pf_instruction, i_pf_instruction_pc, i_pf_valid,
				i_pf_illegal,
		// CPU interface to the memory unit
		o_clear_dcache, o_mem_ce, o_bus_lock,
			o_mem_op, o_mem_data, o_mem_addr, o_mem_reg,
			i_mem_busy, i_mem_pipe_stalled,
				i_mem_valid, i_bus_err, i_mem_wreg, i_mem_result,
		// Accounting/CPU usage interface
		o_op_stall, o_pf_stall, o_i_count
`ifdef	DEBUG_SCOPE
		, o_debug // , o_dcache_debug
`endif
		);


	




	// Condition codes
	// (BUS, TRAP,ILL,BREAKEN,STEP,GIE,SLEEP ), V, N, C, Z
	reg	[3:0]	flags, iflags;
	wire	[15:0]	w_uflags, w_iflags;
	reg		break_en, step, sleep, r_halted;
	wire		break_pending, trap, gie, ubreak, pending_interrupt;
	wire		w_clear_icache, w_clear_dcache, ill_err_u;
	reg		ill_err_i;
	reg		ibus_err_flag;
	wire		ubus_err_flag;
	wire		idiv_err_flag, udiv_err_flag;
	wire		ifpu_err_flag, ufpu_err_flag;
	wire		ihalt_phase, uhalt_phase;

	// The master chip enable
	wire		master_ce, master_stall;

	//
	//
	//	PIPELINE STAGE #1 :: Prefetch
	//		Variable declarations
	//
	//{{{
	reg	[(AW+1):0]	pf_pc;
	wire	[(AW+1):0]	pf_request_address, pf_instruction_pc;
	reg	new_pc;
	wire	clear_pipeline;

	reg			dcd_stalled;
	wire			pf_cyc, pf_stb, pf_we, pf_stall, pf_ack, pf_err;
	wire	[(AW-1):0]	pf_addr;
	wire	[31:0]		pf_data;
	wire	[31:0]		pf_instruction;
	wire			pf_valid, pf_gie, pf_illegal;
	wire			pf_stalled;
	wire			pf_new_pc;
`ifdef	FORMAL
	wire	[31:0]		f_dcd_insn_word;
	wire			f_dcd_insn_gie;
	reg	[31:0]		f_op_insn_word;
	reg	[31:0]		f_alu_insn_word;
`endif

	assign	clear_pipeline = new_pc;
	//}}}

	//
	//
	//	PIPELINE STAGE #2 :: Instruction Decode
	//		Variable declarations
	//
	//
	//{{{
	reg		op_valid /* verilator public_flat */,
			op_valid_mem, op_valid_alu;
	reg		op_valid_div, op_valid_fpu;
	wire		op_stall, dcd_ce, dcd_phase;
	wire	[3:0]	dcd_opn;
	wire	[4:0]	dcd_A, dcd_B, dcd_R, dcd_preA, dcd_preB;
	wire		dcd_Acc, dcd_Bcc, dcd_Apc, dcd_Bpc, dcd_Rcc, dcd_Rpc;
	wire	[3:0]	dcd_F;
	wire		dcd_wR, dcd_rA, dcd_rB,
				dcd_ALU, dcd_M, dcd_DIV, dcd_FP,
				dcd_wF, dcd_gie, dcd_break, dcd_lock,
				dcd_pipe, dcd_ljmp;
	wire		dcd_valid;
	wire	[AW+1:0]	dcd_pc /* verilator public_flat */;
	wire	[31:0]	dcd_I;
	wire		dcd_zI;	// true if dcd_I == 0
	wire	dcd_A_stall, dcd_B_stall, dcd_F_stall;

	wire	dcd_illegal;
	wire			dcd_early_branch, dcd_early_branch_stb;
	wire	[(AW+1):0]	dcd_branch_pc;

	wire		dcd_sim;
	wire	[22:0]	dcd_sim_immv;
	wire		prelock_stall;
	wire		cc_invalid_for_dcd;
	wire		pending_sreg_write;
	//}}}


	//
	//
	//	PIPELINE STAGE #3 :: Read Operands
	//		Variable declarations
	//
	//
	//
	//{{{
	// Now, let's read our operands
	reg	[4:0]	alu_reg;
	wire	[3:0]	op_opn;
	reg	[4:0]	op_R;
	reg		op_Rcc;
	reg	[4:0]	op_Aid, op_Bid;
	reg		op_rA, op_rB;
	reg	[31:0]	r_op_Av, r_op_Bv;
	reg	[(AW+1):0]	op_pc;
	wire	[31:0]	w_op_Av, w_op_Bv, op_Av, op_Bv;
	reg	[31:0]	w_pcB_v, w_pcA_v;
	reg	[31:0]	w_op_BnI;
	reg		op_wR, op_wF;
	wire		op_gie;
	wire	[3:0]	op_Fl;
	reg	[6:0]	r_op_F;
	wire	[7:0]	op_F;
	wire		op_ce, op_phase, op_pipe;
	reg		r_op_break;
	reg	[3:0]	r_op_opn;
	wire	w_op_valid;
	wire	[8:0]	w_cpu_info;
	// Some pipeline control wires
	reg	op_illegal;
	wire	op_break;
	wire	op_lock;

`ifdef	VERILATOR
	reg		op_sim		/* verilator public_flat */;
	reg	[22:0]	op_sim_immv	/* verilator public_flat */;
	reg		alu_sim		/* verilator public_flat */;
	reg	[22:0]	alu_sim_immv	/* verilator public_flat */;
`else
	wire	op_sim = 1'b0;
`endif
	//}}}


	//
	//
	//	PIPELINE STAGE #4 :: ALU / Memory
	//		Variable declarations
	//
	//
	//{{{
	wire	[(AW+1):0]	alu_pc;
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
	wire			mem_pipe_stalled;
	wire			mem_valid, mem_stall, mem_ack, mem_err, bus_err,
				mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl, mem_we;
	wire	[4:0]		mem_wreg;

	wire			mem_busy, mem_rdbusy;
	wire	[(AW-1):0]	mem_addr;
	wire	[31:0]		mem_data, mem_result;
	wire	[3:0]		mem_sel;

	wire		div_ce, div_error, div_busy, div_valid;
	wire	[31:0]	div_result;
	wire	[3:0]	div_flags;

	wire		fpu_ce, fpu_error, fpu_busy, fpu_valid;
	wire	[31:0]	fpu_result;
	wire	[3:0]	fpu_flags;
	reg		adf_ce_unconditional;

	wire		bus_lock;

	reg		dbgv, dbg_clear_pipe;
	reg	[31:0]	dbg_val;

	assign	div_ce = (op_valid_div)&&(adf_ce_unconditional)&&(set_cond);
	assign	fpu_ce = (IMPLEMENT_FPU)&&(op_valid_fpu)&&(adf_ce_unconditional)&&(set_cond);

	//}}}

	//
	//
	//	PIPELINE STAGE #5 :: Write-back
	//		Variable declarations
	//
	//{{{
	wire		wr_discard, wr_write_pc, wr_write_cc,
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
	reg		r_clear_icache, r_clear_dcache;
	//}}}

`ifdef	FORMAL
	wire	[F_LGDEPTH-1:0]
		f_gbl_arb_nreqs, f_gbl_arb_nacks, f_gbl_arb_outstanding,
		f_lcl_arb_nreqs, f_lcl_arb_nacks, f_lcl_arb_outstanding,
		f_gbl_mem_nreqs, f_gbl_mem_nacks, f_gbl_mem_outstanding,
		f_lcl_mem_nreqs, f_lcl_mem_nacks, f_lcl_mem_outstanding,
		f_gbl_pf_nreqs, f_gbl_pf_nacks, f_gbl_pf_outstanding,
		f_lcl_pf_nreqs, f_lcl_pf_nacks, f_lcl_pf_outstanding,
		f_mem_nreqs, f_mem_nacks, f_mem_outstanding;
	reg	f_pf_nreqs, f_pf_nacks, f_pf_outstanding;
	wire	f_mem_pc;
`endif


	//
	//	MASTER: clock enable.
	//
	assign	master_ce = ((!i_halt)||(alu_phase))
				&&(!cc_write_hold)&&(!o_break)&&(!sleep);


	//
	//	PIPELINE STAGE #1 :: Prefetch
	//		Calculate stall conditions
	//
	//	These are calculated externally, within the prefetch module.
	//

	//
	//	PIPELINE STAGE #2 :: Instruction Decode
	//		Calculate stall conditions

	always @(*)
	if (OPT_PIPELINED)
		dcd_stalled = (dcd_valid)&&(op_stall);
	else
		dcd_stalled = (!master_ce)||(ill_err_i)||(dcd_valid)||(op_valid)
			||(ibus_err_flag)||(idiv_err_flag)
			||(alu_busy)||(div_busy)||(fpu_busy)||(mem_busy);
	//
	//	PIPELINE STAGE #3 :: Read Operands
	//		Calculate stall conditions
	//{{{
	generate if (OPT_PIPELINED)
	begin : GEN_OP_STALL
		reg	r_cc_invalid_for_dcd;
		always @(posedge i_clk)
			r_cc_invalid_for_dcd <=
				(set_cond)&&(op_valid)
					&&((op_wF)||((op_wR)&&(op_R[4:0] == { op_gie, `CPU_CC_REG })))
				||((r_cc_invalid_for_dcd)
					&&((alu_busy)||(mem_rdbusy)||(div_busy)||(fpu_busy)));

		assign	cc_invalid_for_dcd = r_cc_invalid_for_dcd;

		reg	r_pending_sreg_write;
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
		else if ((!mem_rdbusy)&&(!alu_busy))
			r_pending_sreg_write <= 1'b0;

		assign	pending_sreg_write = r_pending_sreg_write;

		assign	op_stall = (op_valid)&&(
		//{{{
			// Only stall if we're loaded w/validins and the
			// next stage is accepting our instruction
			(!adf_ce_unconditional)&&(!mem_ce)
			)
			||(dcd_valid)&&(
				// Stall if we need to wait for an operand A
				// to be ready to read
				(dcd_A_stall)
				// Likewise for B, also includes logic
				// regarding immediate offset (register must
				// be in register file if we need to add to
				// an immediate)
				||(dcd_B_stall)
				// Or if we need to wait on flags to work on the
				// CC register
				||(dcd_F_stall)
			);
		//}}}
		assign	op_ce = ((dcd_valid)||(dcd_illegal)||(dcd_early_branch))&&(!op_stall);

	end else begin // !OPT_PIPELINED

		assign	op_stall = 1'b0; // (o_break)||(pending_interrupt);
		assign	op_ce = ((dcd_valid)||(dcd_early_branch))&&(!op_stall);
		assign	pending_sreg_write = 1'b0;
		assign	cc_invalid_for_dcd = 1'b0;

		// Verilator lint_off UNUSED
		wire	[1:0]	pipe_unused;
		assign		pipe_unused = { cc_invalid_for_dcd,
					pending_sreg_write };
		// Verilator lint_on UNUSED
	end endgenerate

	// BUT ... op_ce is too complex for many of the data operations.  So
	// let's make their circuit enable code simpler.  In particular, if
	// op_ doesn't need to be preserved, we can change it all we want
	// ... right?  The clear_pipeline code, for example, really only needs
	// to determine whether op_valid is true.
	// assign	op_change_data_ce = (!op_stall);
	//}}}

	//
	//	PIPELINE STAGE #4 :: ALU / Memory
	//		Calculate stall conditions
	//
	//{{{
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
		assign	alu_stall = (((master_stall)||(mem_rdbusy))&&(op_valid_alu)) //Case 1&2
			||(wr_reg_ce)&&(wr_write_cc);
		// assign // alu_ce = (master_ce)&&(op_valid_alu)&&(!alu_stall)
		//	&&(!clear_pipeline)&&(!op_illegal)
		//	&&(!pending_sreg_write)
		//	&&(!alu_sreg_stall);
		assign	alu_ce = (adf_ce_unconditional)&&(op_valid_alu);

		// Verilator lint_off unused
		wire	unused_alu_stall = alu_stall;
		// Verilator lint_on  unused
	end else begin

		assign	alu_stall = (master_stall);
		//assign	alu_ce = (master_ce)&&(op_valid_alu)
		//			&&(!clear_pipeline)
		//			&&(!alu_stall);
		assign	alu_ce = (adf_ce_unconditional)&&(op_valid_alu);

		// Verilator lint_off unused
		wire	unused_alu_stall = alu_stall;
		// Verilator lint_on  unused
	end endgenerate
	//

	//
	// Note: if you change the conditions for mem_ce, you must also change
	// alu_pc_valid.
	//
	assign	mem_ce = (master_ce)&&(op_valid_mem)&&(!mem_stalled)
			&&(!clear_pipeline);

	generate if (OPT_PIPELINED_BUS_ACCESS)
	begin

		assign	mem_stalled = (master_stall)||((op_valid_mem)&&(
				(mem_pipe_stalled)
				||(bus_err)||(div_error)
				||((!op_pipe)&&(mem_busy))
				// Stall waiting for flags to be valid
				// Or waiting for a write to the PC register
				// Or CC register, since that can change the
				//  PC as well
				||((wr_reg_ce)
					&&((wr_write_pc)||(wr_write_cc)))));
	end else if (OPT_PIPELINED)
	begin
		assign	mem_stalled = (master_stall)||((op_valid_mem)&&(
				(bus_err)||(div_error)||(mem_busy)
				// Stall waiting for flags to be valid
				// Or waiting for a write to the PC register
				// Or CC register, since that can change the
				//  PC as well
				||((wr_reg_ce)
					&&((wr_write_pc)||(wr_write_cc)))));
	end else begin

		assign	mem_stalled = (master_stall);

	end endgenerate
	//}}}

	assign	master_stall = (!master_ce)||(!op_valid)||(ill_err_i)
			||(ibus_err_flag)||(idiv_err_flag)
			||(pending_interrupt)&&(!alu_phase)
			||(alu_busy)||(div_busy)||(fpu_busy)||(op_break)
			||((OPT_PIPELINED)&&(
				((OPT_LOCK)&&(prelock_stall))
				||((mem_busy)&&(op_illegal))
				||((mem_busy)&&(op_valid_div))
				||(alu_illegal)||(o_break)));


	// ALU, DIV, or FPU CE ... equivalent to the OR of all three of these
	always @(*)
	if (OPT_PIPELINED)
		adf_ce_unconditional =
			(!master_stall)&&(!op_valid_mem)&&(!mem_rdbusy)
			&&((!mem_busy)||(!op_wR)||(op_R[4:1] != { gie, 3'h7}));
	else
		adf_ce_unconditional = (!master_stall)&&(op_valid)&&(!op_valid_mem);

	//
	//
	//	PIPELINE STAGE #1 :: Prefetch
	//
	//
	//{{{
//	assign	pf_stalled = (dcd_stalled)||(dcd_phase);
//
//	assign	pf_new_pc = (new_pc)||((dcd_early_branch_stb)&&(!clear_pipeline));
//
//	assign	pf_request_address = ((dcd_early_branch_stb)&&(!clear_pipeline))
//				? dcd_branch_pc:pf_pc;
//	assign	pf_gie = gie;
`ifdef	OPT_SINGLE_FETCH
	prefetch	#(ADDRESS_WIDTH)
	//{{{
			pf(i_clk, (i_reset), pf_new_pc, w_clear_icache,
				(!pf_stalled),
				pf_request_address,
				pf_instruction, pf_instruction_pc,
					pf_valid, pf_illegal,
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
				pf_stall, pf_ack, pf_err, i_wb_data);
	//}}}
`else
`ifdef	OPT_DOUBLE_FETCH

	dblfetch #(ADDRESS_WIDTH)
	//{{{
		pf(i_clk, i_reset, pf_new_pc, w_clear_icache,
				(!pf_stalled),
				pf_request_address,
				pf_instruction, pf_instruction_pc,
					pf_valid,
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
					pf_stall, pf_ack, pf_err, i_wb_data,
				pf_illegal);
	//}}}

`else // Not single fetch and not double fetch

	pfcache #(LGICACHE, ADDRESS_WIDTH)
	//{{{
		pf(i_clk, i_reset, pf_new_pc, w_clear_icache,
				// dcd_pc,
				(!pf_stalled),
				pf_request_address,
				pf_instruction, pf_instruction_pc, pf_valid,
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
					pf_stall, pf_ack, pf_err, i_wb_data,
				pf_illegal);
	//}}}
`endif	// OPT_DOUBLE_FETCH
`endif	// OPT_SINGLE_FETCH
	//}}}







/*
	generate if ((!OPT_PIPELINED)||(!OPT_LOCK))
	begin

		assign op_lock       = 1'b0;

		// Verilator lint_off UNUSED
		wire	dcd_lock_unused;
		assign	dcd_lock_unused = dcd_lock;
		// Verilator lint_on  UNUSED

	end else // if (IMPLEMENT_LOCK != 0)
	begin : OPLOCK
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
*/


/*
	// Bus lock logic
	//{{{
	generate
	if ((OPT_PIPELINED)&&(!OPT_LOCK))
	begin : BUSLOCK
		reg	r_prelock_stall;

		initial	r_prelock_stall = 1'b0;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_prelock_stall <= 1'b0;
		else if ((op_valid)&&(op_lock)&&(op_ce))
			r_prelock_stall <= 1'b1;
		else if ((op_valid)&&(dcd_valid)&&(pf_valid))
			r_prelock_stall <= 1'b0;

		assign	prelock_stall = r_prelock_stall;

		reg	r_prelock_primed;
		initial	r_prelock_primed = 1'b0;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_prelock_primed <= 1'b0;
		else if (r_prelock_stall)
			r_prelock_primed <= 1'b1;
		else if ((adf_ce_unconditional)||(mem_ce))
			r_prelock_primed <= 1'b0;

		reg	[1:0]	r_bus_lock;
		initial	r_bus_lock = 2'b00;
		always @(posedge i_clk)
		if (clear_pipeline)
			r_bus_lock <= 2'b00;
		else if ((op_valid)&&((adf_ce_unconditional)||(mem_ce)))
		begin
			if (r_prelock_primed)
				r_bus_lock <= 2'b10;
			else if (r_bus_lock != 2'h0)
				r_bus_lock <= r_bus_lock + 2'b11;
		end

		assign	bus_lock = |r_bus_lock;
	end else begin
		assign	prelock_stall = 1'b0;
		assign	bus_lock = 1'b0;
	end endgenerate
	//}}}
*/

	// Memory interface
	//{{{
	generate if (OPT_DCACHE)
	begin : MEM_DCACHE

		dcache #(.LGCACHELEN(OPT_LGDCACHE), .ADDRESS_WIDTH(AW),
			.LGNLINES(OPT_LGDCACHE-3), .OPT_LOCAL_BUS(WITH_LOCAL_BUS),
			.OPT_PIPE(OPT_MEMPIPE),
			.OPT_LOCK(OPT_LOCK)
`ifdef	FORMAL
			, .OPT_FIFO_DEPTH(2)
			, .F_LGDEPTH(F_LGDEPTH)
`endif
			) docache(i_clk, i_reset, w_clear_dcache,
		///{{{
				(mem_ce)&&(set_cond), bus_lock,
				(op_opn[2:0]), op_Bv, op_Av, op_R,
				mem_busy, mem_pipe_stalled,
				mem_valid, bus_err, mem_wreg, mem_result,
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err, i_wb_data
`ifdef	FORMAL
			, f_mem_nreqs, f_mem_nacks, f_mem_outstanding, f_mem_pc
`endif
				// , o_dcache_debug
			);
		///}}}
	end else begin : NO_CACHE

		// Verilator lint_off UNUSED
		wire	unused_clear_dcache = w_clear_dcache;
		// Verilator lint_on UNUSED
	if (OPT_PIPELINED_BUS_ACCESS)
	begin : MEM

		pipemem	#(.ADDRESS_WIDTH(AW),
			.IMPLEMENT_LOCK(OPT_LOCK),
			.WITH_LOCAL_BUS(WITH_LOCAL_BUS)
`ifdef	FORMAL
			, .OPT_MAXDEPTH(4'h3),
			.F_LGDEPTH(F_LGDEPTH)
`endif
			) domem(i_clk,i_reset,
		///{{{
			(mem_ce)&&(set_cond), bus_lock,
				(op_opn[2:0]), op_Bv, op_Av, op_R,
				mem_busy, mem_pipe_stalled,
				mem_valid, bus_err, mem_wreg, mem_result,
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err, i_wb_data
`ifdef	FORMAL
			, f_mem_nreqs, f_mem_nacks, f_mem_outstanding, f_mem_pc
`endif
			);
		//}}}
	end else begin : MEM

		memops	#(.ADDRESS_WIDTH(AW),
			.IMPLEMENT_LOCK(OPT_LOCK),
			.WITH_LOCAL_BUS(WITH_LOCAL_BUS)
`ifdef	FORMAL
			, .F_LGDEPTH(F_LGDEPTH)
`endif	// F_LGDEPTH
			) domem(i_clk,i_reset,
		//{{{
			(mem_ce)&&(set_cond), bus_lock,
				(op_opn[2:0]), op_Bv, op_Av, op_R,
				mem_busy,
				mem_valid, bus_err, mem_wreg, mem_result,
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err, i_wb_data
`ifdef	FORMAL
			, f_mem_nreqs, f_mem_nacks, f_mem_outstanding
`endif
			);
`ifdef	FORMAL
		assign	f_mem_pc = 1'b0;
`endif
		//}}}
		assign	mem_pipe_stalled = 1'b0;
	end end endgenerate

	assign	mem_rdbusy = (mem_busy)&&((!OPT_PIPELINED)||(!mem_we));

	// Either the prefetch or the instruction gets the memory bus, but
	// never both.
	generate if (OPT_PIPELINED)
	begin : PRIORITY_DATA

		wbdblpriarb	#(.DW(32),.AW(AW)
`ifdef	FORMAL
			,.F_LGDEPTH(F_LGDEPTH), .F_MAX_STALL(2),
			.F_MAX_ACK_DELAY(2)
`endif // FORMAL
			) pformem(i_clk, i_reset,
		//{{{
		// Memory access to the arbiter, priority position
		mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl,
			mem_we, mem_addr, mem_data, mem_sel,
			mem_stall, mem_ack, mem_err,
		// Prefetch access to the arbiter
		//
		// At a first glance, we might want something like:
		//
		// pf_cyc, 1'b0, pf_stb, 1'b0, pf_we, pf_addr, pf_data, 4'hf,
		//
		// However, we know that the prefetch will not generate any
		// writes.  Therefore, the write specific lines (mem_data and
		// mem_sel) can be shared with the memory in order to ease
		// timing and LUT usage.
		pf_cyc,1'b0,pf_stb, 1'b0, pf_we, pf_addr, mem_data, mem_sel,
			pf_stall, pf_ack, pf_err,
		// Common wires, in and out, of the arbiter
		o_wb_gbl_cyc, o_wb_lcl_cyc, o_wb_gbl_stb, o_wb_lcl_stb,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_stall, i_wb_ack, i_wb_err
`ifdef	FORMAL
		,f_gbl_arb_nreqs, f_gbl_arb_nacks, f_gbl_arb_outstanding,
		f_lcl_arb_nreqs, f_lcl_arb_nacks, f_lcl_arb_outstanding,
		f_gbl_mem_nreqs, f_gbl_mem_nacks, f_gbl_mem_outstanding,
		f_lcl_mem_nreqs, f_lcl_mem_nacks, f_lcl_mem_outstanding,
		f_gbl_pf_nreqs, f_gbl_pf_nacks, f_gbl_pf_outstanding,
		f_lcl_pf_nreqs, f_lcl_pf_nacks, f_lcl_pf_outstanding
`endif
		);
		//}}}

	end else begin : PRIORITY_PREFETCH

		wbdblpriarb	#(.DW(32),.AW(AW)
`ifdef	FORMAL
			,.F_LGDEPTH(F_LGDEPTH), .F_MAX_STALL(2),
			.F_MAX_ACK_DELAY(2)
`endif // FORMAL
			) pformem(i_clk, i_reset,
		//{{{
		// Prefetch access to the arbiter, priority position
		//
		// At a first glance, we might want something like:
		//
		// pf_cyc, 1'b0, pf_stb, 1'b0, pf_we, pf_addr, pf_data, 4'hf,
		//
		// However, we know that the prefetch will not generate any
		// writes.  Therefore, the write specific lines (mem_data and
		// mem_sel) can be shared with the memory in order to ease
		// timing and LUT usage.
		pf_cyc,1'b0,pf_stb, 1'b0, pf_we, pf_addr, mem_data, mem_sel,
			pf_stall, pf_ack, pf_err,
		// Memory access to the arbiter
		mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl,
			mem_we, mem_addr, mem_data, mem_sel,
			mem_stall, mem_ack, mem_err,
		// Common wires, in and out, of the arbiter
		o_wb_gbl_cyc, o_wb_lcl_cyc, o_wb_gbl_stb, o_wb_lcl_stb,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_stall, i_wb_ack, i_wb_err
`ifdef	FORMAL
		,f_gbl_arb_nreqs, f_gbl_arb_nacks, f_gbl_arb_outstanding,
		f_lcl_arb_nreqs, f_lcl_arb_nacks, f_lcl_arb_outstanding,
		f_gbl_pf_nreqs, f_gbl_pf_nacks, f_gbl_pf_outstanding,
		f_lcl_pf_nreqs, f_lcl_pf_nacks, f_lcl_pf_outstanding,
		f_gbl_mem_nreqs, f_gbl_mem_nacks, f_gbl_mem_outstanding,
		f_lcl_mem_nreqs, f_lcl_mem_nacks, f_lcl_mem_outstanding
`endif
		);
		//}}}
	end endgenerate

	//}}}
	//}}}
endmodule
