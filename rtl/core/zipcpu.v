///////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipcpu.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
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
//	assign	(n)_ce = (n-1)_valid && (~(n)_stall)
//
//
//	always @(posedge i_clk)
//		if ((i_rst)||(clear_pipeline))
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
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////////
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
///////////////////////////////////////////////////////////////////////////////
//
// We can either pipeline our fetches, or issue one fetch at a time.  Pipelined
// fetches are more complicated and therefore use more FPGA resources, while
// single fetches will cause the CPU to stall for about 5 stalls each 
// instruction cycle, effectively reducing the instruction count per clock to
// about 0.2.  However, the area cost may be worth it.  Consider:
//
//	Slice LUTs		ZipSystem	ZipCPU
//	Single Fetching		2521		1734
//	Pipelined fetching	2796		2046
//
//
//
`define	CPU_CC_REG	4'he
`define	CPU_PC_REG	4'hf
`define	CPU_CLRCACHE_BIT 14	// Set to clear the I-cache, automatically clears
`define	CPU_PHASE_BIT	13	// Set if we are executing the latter half of a VLIW
`define	CPU_FPUERR_BIT	12	// Floating point error flag, set on error
`define	CPU_DIVERR_BIT	11	// Divide error flag, set on divide by zero
`define	CPU_BUSERR_BIT	10	// Bus error flag, set on error
`define	CPU_TRAP_BIT	9	// User TRAP has taken place
`define	CPU_ILL_BIT	8	// Illegal instruction
`define	CPU_BREAK_BIT	7
`define	CPU_STEP_BIT	6	// Will step one or two (VLIW) instructions
`define	CPU_GIE_BIT	5
`define	CPU_SLEEP_BIT	4
// Compile time defines
//
`include "cpudefs.v"
//
//
module	zipcpu(i_clk, i_rst, i_interrupt,
		// Debug interface
		i_halt, i_clear_pf_cache, i_dbg_reg, i_dbg_we, i_dbg_data,
			o_dbg_stall, o_dbg_reg, o_dbg_cc,
			o_break,
		// CPU interface to the wishbone bus
		o_wb_gbl_cyc, o_wb_gbl_stb,
			o_wb_lcl_cyc, o_wb_lcl_stb,
			o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_data,
			i_wb_err,
		// Accounting/CPU usage interface
		o_op_stall, o_pf_stall, o_i_count
`ifdef	DEBUG_SCOPE
		, o_debug
`endif
		);
	parameter	RESET_ADDRESS=32'h0100000, ADDRESS_WIDTH=32,
			LGICACHE=8;
`ifdef	OPT_MULTIPLY
	parameter	IMPLEMENT_MPY = `OPT_MULTIPLY;
`else
	parameter	IMPLEMENT_MPY = 0;
`endif
`ifdef	OPT_DIVIDE
	parameter	IMPLEMENT_DIVIDE = 1;
`else
	parameter	IMPLEMENT_DIVIDE = 0;
`endif
`ifdef	OPT_IMPLEMENT_FPU
	parameter	IMPLEMENT_FPU = 1,
`else
	parameter	IMPLEMENT_FPU = 0,
`endif
			IMPLEMENT_LOCK=1;
`ifdef	OPT_EARLY_BRANCHING
	parameter	EARLY_BRANCHING = 1;
`else
	parameter	EARLY_BRANCHING = 0;
`endif
	localparam	AW=ADDRESS_WIDTH;
	input			i_clk, i_rst, i_interrupt;
	// Debug interface -- inputs
	input			i_halt, i_clear_pf_cache;
	input		[4:0]	i_dbg_reg;
	input			i_dbg_we;
	input		[31:0]	i_dbg_data;
	// Debug interface -- outputs
	output	wire		o_dbg_stall;
	output	reg	[31:0]	o_dbg_reg;
	output	reg	[3:0]	o_dbg_cc;
	output	wire		o_break;
	// Wishbone interface -- outputs
	output	wire		o_wb_gbl_cyc, o_wb_gbl_stb;
	output	wire		o_wb_lcl_cyc, o_wb_lcl_stb, o_wb_we;
	output	wire	[(AW-1):0]	o_wb_addr;
	output	wire	[31:0]	o_wb_data;
	// Wishbone interface -- inputs
	input			i_wb_ack, i_wb_stall;
	input		[31:0]	i_wb_data;
	input			i_wb_err;
	// Accounting outputs ... to help us count stalls and usage
	output	wire		o_op_stall;
	output	wire		o_pf_stall;
	output	wire		o_i_count;
	//
`ifdef	DEBUG_SCOPE
	output	reg	[31:0]	o_debug;
`endif


	// Registers
	//
	//	The distributed RAM style comment is necessary on the
	// SPARTAN6 with XST to prevent XST from oversimplifying the register
	// set and in the process ruining everything else.  It basically
	// optimizes logic away, to where it no longer works.  The logic
	// as described herein will work, this just makes sure XST implements
	// that logic.
	//
	(* ram_style = "distributed" *)
`ifdef	OPT_NO_USERMODE
	reg	[31:0]	regset [0:15];
`else
	reg	[31:0]	regset [0:31];
`endif

	// Condition codes
	// (BUS, TRAP,ILL,BREAKEN,STEP,GIE,SLEEP ), V, N, C, Z
	reg	[3:0]	flags, iflags;
	wire	[14:0]	w_uflags, w_iflags;
	reg		break_en, step, sleep, r_halted;
	wire		break_pending, trap, gie, ubreak;
	wire		w_clear_icache, ill_err_u;
`ifdef	OPT_ILLEGAL_INSTRUCTION
	reg		ill_err_i;
`else
	wire		ill_err_i;
`endif
	reg		ibus_err_flag;
	wire		ubus_err_flag;
	wire		idiv_err_flag, udiv_err_flag;
	wire		ifpu_err_flag, ufpu_err_flag;
	wire		ihalt_phase, uhalt_phase;

	// The master chip enable
	wire		master_ce;

	//
	//
	//	PIPELINE STAGE #1 :: Prefetch
	//		Variable declarations
	//
	reg	[(AW-1):0]	pf_pc;
	reg	new_pc;
	wire	clear_pipeline;
	assign	clear_pipeline = new_pc;

	wire		dcd_stalled;
	wire		pf_cyc, pf_stb, pf_we, pf_busy, pf_ack, pf_stall, pf_err;
	wire	[(AW-1):0]	pf_addr;
	wire	[31:0]		pf_data;
	wire	[31:0]		instruction;
	wire	[(AW-1):0]	instruction_pc;
	wire	pf_valid, instruction_gie, pf_illegal;

	//
	//
	//	PIPELINE STAGE #2 :: Instruction Decode
	//		Variable declarations
	//
	//
	reg		opvalid, opvalid_mem, opvalid_alu;
	reg		opvalid_div, opvalid_fpu;
	wire		op_stall, dcd_ce, dcd_phase;
	wire	[3:0]	dcdOp;
	wire	[4:0]	dcdA, dcdB, dcdR;
	wire		dcdA_cc, dcdB_cc, dcdA_pc, dcdB_pc, dcdR_cc, dcdR_pc;
	wire	[3:0]	dcdF;
	wire		dcdR_wr, dcdA_rd, dcdB_rd,
				dcdALU, dcdM, dcdDV, dcdFP,
				dcdF_wr, dcd_gie, dcd_break, dcd_lock,
				dcd_pipe, dcd_ljmp;
	reg		r_dcdvalid;
	wire		dcdvalid;
	wire	[(AW-1):0]	dcd_pc;
	wire	[31:0]	dcdI;
	wire		dcd_zI;	// true if dcdI == 0
	wire	dcdA_stall, dcdB_stall, dcdF_stall;

	wire	dcd_illegal;
	wire			dcd_early_branch;
	wire	[(AW-1):0]	dcd_branch_pc;


	//
	//
	//	PIPELINE STAGE #3 :: Read Operands
	//		Variable declarations
	//
	//
	//
	// Now, let's read our operands
	reg	[4:0]	alu_reg;
	wire	[3:0]	opn;
	wire	[4:0]	opR;
	reg	[31:0]	r_opA, r_opB;
	reg	[(AW-1):0]	op_pc;
	wire	[31:0]	w_opA, w_opB;
	wire	[31:0]	opA_nowait, opB_nowait, opA, opB;
	reg		opR_wr, opF_wr;
	wire		op_gie, opR_cc;
	wire	[14:0]	opFl;
	reg	[6:0]	r_opF;
	wire	[7:0]	opF;
	wire		op_ce, op_phase, op_pipe, op_change_data_ce;
	// Some pipeline control wires
`ifdef	OPT_PIPELINED
	reg	opA_alu, opA_mem;
	reg	opB_alu, opB_mem;
`endif
`ifdef	OPT_ILLEGAL_INSTRUCTION
	reg	op_illegal;
`else
	wire	op_illegal;
	assign	op_illegal = 1'b0;
`endif
	wire	op_break;
	wire	op_lock;


	//
	//
	//	PIPELINE STAGE #4 :: ALU / Memory
	//		Variable declarations
	//
	//
	wire	[(AW-1):0]	alu_pc;
	reg		r_alu_pc_valid, mem_pc_valid;
	wire		alu_pc_valid;
	wire		alu_phase;
	wire		alu_ce, alu_stall;
	wire	[31:0]	alu_result;
	wire	[3:0]	alu_flags;
	wire		alu_valid, alu_busy;
	wire		set_cond;
	reg		alu_wr, alF_wr;
	wire		alu_gie, alu_illegal;



	wire	mem_ce, mem_stalled;
	wire	mem_pipe_stalled;
	wire	mem_valid, mem_ack, mem_stall, mem_err, bus_err,
		mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl, mem_we;
	wire	[4:0]		mem_wreg;

	wire			mem_busy, mem_rdbusy;
	wire	[(AW-1):0]	mem_addr;
	wire	[31:0]		mem_data, mem_result;

	wire	div_ce, div_error, div_busy, div_valid;
	wire	[31:0]	div_result;
	wire	[3:0]	div_flags;

	assign	div_ce = (master_ce)&&(~clear_pipeline)&&(opvalid_div)
				&&(~mem_rdbusy)&&(~div_busy)&&(~fpu_busy)
				&&(set_cond);

	wire	fpu_ce, fpu_error, fpu_busy, fpu_valid;
	wire	[31:0]	fpu_result;
	wire	[3:0]	fpu_flags;

	assign	fpu_ce = (master_ce)&&(~clear_pipeline)&&(opvalid_fpu)
				&&(~mem_rdbusy)&&(~div_busy)&&(~fpu_busy)
				&&(set_cond);

	wire	adf_ce_unconditional;

	//
	//
	//	PIPELINE STAGE #5 :: Write-back
	//		Variable declarations
	//
	wire		wr_reg_ce, wr_flags_ce, wr_write_pc, wr_write_cc,
			wr_write_scc, wr_write_ucc;
	wire	[4:0]	wr_reg_id;
	wire	[31:0]	wr_gpreg_vl, wr_spreg_vl;
	wire	w_switch_to_interrupt, w_release_from_interrupt;
	reg	[(AW-1):0]	ipc;
	wire	[(AW-1):0]	upc;



	//
	//	MASTER: clock enable.
	//
	assign	master_ce = (~i_halt)&&(~o_break)&&(~sleep);


	//
	//	PIPELINE STAGE #1 :: Prefetch
	//		Calculate stall conditions
	//
	//	These are calculated externally, within the prefetch module.
	//

	//
	//	PIPELINE STAGE #2 :: Instruction Decode
	//		Calculate stall conditions
	assign		dcd_ce = ((~dcdvalid)||(~dcd_stalled))&&(~clear_pipeline);

`ifdef	OPT_PIPELINED
	assign		dcd_stalled = (dcdvalid)&&(op_stall);
`else
	// If not pipelined, there will be no opvalid_ anything, and the
	// op_stall will be false, dcdX_stall will be false, thus we can simply
	// do a ...
	assign		dcd_stalled = 1'b0;
`endif
	//
	//	PIPELINE STAGE #3 :: Read Operands
	//		Calculate stall conditions
	wire	op_lock_stall;
`ifdef	OPT_PIPELINED
	reg	cc_invalid_for_dcd;
	always @(posedge i_clk)
		cc_invalid_for_dcd <= (wr_flags_ce)
			||(wr_reg_ce)&&(wr_reg_id[3:0] == `CPU_CC_REG)
			||(opvalid)&&((opF_wr)||((opR_wr)&&(opR[3:0] == `CPU_CC_REG)))
			||((alF_wr)||((alu_wr)&&(alu_reg[3:0] == `CPU_CC_REG)))
			||(mem_busy)||(div_busy)||(fpu_busy);

	assign	op_stall = (opvalid)&&( // Only stall if we're loaded w/validins
			// Stall if we're stopped, and not allowed to execute
			// an instruction
			// (~master_ce)		// Already captured in alu_stall
			//
			// Stall if going into the ALU and the ALU is stalled
			//	i.e. if the memory is busy, or we are single
			//	stepping.  This also includes our stalls for
			//	op_break and op_lock, so we don't need to
			//	include those as well here.
			// This also includes whether or not the divide or
			// floating point units are busy.
			(alu_stall)
			//
			// Stall if we are going into memory with an operation
			//	that cannot be pipelined, and the memory is
			//	already busy
			||(mem_stalled) // &&(opvalid_mem) part of mem_stalled
			||(opR_cc)
			)
			||(dcdvalid)&&(
				// Stall if we need to wait for an operand A
				// to be ready to read
				(dcdA_stall)
				// Likewise for B, also includes logic
				// regarding immediate offset (register must
				// be in register file if we need to add to
				// an immediate)
				||(dcdB_stall)
				// Or if we need to wait on flags to work on the
				// CC register
				||(dcdF_stall)
			);
	assign	op_ce = ((dcdvalid)||(dcd_illegal)||(dcd_early_branch))&&(~op_stall)&&(~clear_pipeline);


	// BUT ... op_ce is too complex for many of the data operations.  So
	// let's make their circuit enable code simpler.  In particular, if
	// op_ doesn't need to be preserved, we can change it all we want
	// ... right?  The clear_pipeline code, for example, really only needs
	// to determine whether opvalid is true.
	assign	op_change_data_ce = (~op_stall);
`else
	assign	op_stall = (opvalid)&&(~master_ce);
	assign	op_ce = ((dcdvalid)||(dcd_illegal)||(dcd_early_branch))&&(~clear_pipeline);
	assign	op_change_data_ce = 1'b1;
`endif

	//
	//	PIPELINE STAGE #4 :: ALU / Memory
	//		Calculate stall conditions
	//
	// 1. Basic stall is if the previous stage is valid and the next is
	//	busy.  
	// 2. Also stall if the prior stage is valid and the master clock enable
	//	is de-selected
	// 3. Stall if someone on the other end is writing the CC register,
	//	since we don't know if it'll put us to sleep or not.
	// 4. Last case: Stall if we would otherwise move a break instruction
	//	through the ALU.  Break instructions are not allowed through
	//	the ALU.
`ifdef	OPT_PIPELINED
	assign	alu_stall = (((~master_ce)||(mem_rdbusy)||(alu_busy))&&(opvalid_alu)) //Case 1&2
			||((opvalid)&&(op_lock)&&(op_lock_stall))
			||((opvalid)&&(op_break))
			||(wr_reg_ce)&&(wr_write_cc)
			||(div_busy)||(fpu_busy);
	assign	alu_ce = (master_ce)&&(opvalid_alu)&&(~alu_stall)
				&&(~clear_pipeline);
`else
	assign	alu_stall = (opvalid_alu)&&((~master_ce)||(op_break));
	assign	alu_ce = (master_ce)&&(opvalid_alu)&&(~alu_stall)&&(~clear_pipeline);
`endif
	//

	//
	// Note: if you change the conditions for mem_ce, you must also change
	// alu_pc_valid.
	//
`ifdef	OPT_PIPELINED
	assign	mem_ce = (master_ce)&&(opvalid_mem)&&(~mem_stalled)
			&&(~clear_pipeline);
`else
	// If we aren't pipelined, then no one will be changing what's in the
	// pipeline (i.e. clear_pipeline), while our only instruction goes
	// through the ... pipeline.
	//
	// However, in hind sight this logic didn't work.  What happens when
	// something gets in the pipeline and then (due to interrupt or some
	// such) needs to be voided?  Thus we avoid simplification and keep
	// what worked here.
	assign	mem_ce = (master_ce)&&(opvalid_mem)&&(~mem_stalled)
			&&(~clear_pipeline);
`endif
`ifdef	OPT_PIPELINED_BUS_ACCESS
	assign	mem_stalled = (~master_ce)||(alu_busy)||((opvalid_mem)&&(
				(mem_pipe_stalled)
				||((~op_pipe)&&(mem_busy))
				||(div_busy)
				||(fpu_busy)
				// Stall waiting for flags to be valid
				// Or waiting for a write to the PC register
				// Or CC register, since that can change the
				//  PC as well
				||((wr_reg_ce)&&(wr_reg_id[4] == op_gie)
					&&((wr_write_pc)||(wr_write_cc)))));
`else
`ifdef	OPT_PIPELINED
	assign	mem_stalled = (mem_busy)||((opvalid_mem)&&(
				(~master_ce)
				// Stall waiting for flags to be valid
				// Or waiting for a write to the PC register
				// Or CC register, since that can change the
				//  PC as well
				||((wr_reg_ce)&&(wr_reg_id[4] == op_gie)&&((wr_write_pc)||(wr_write_cc)))));
`else
	assign	mem_stalled = (opvalid_mem)&&(~master_ce);
`endif
`endif

	// ALU, DIV, or FPU CE ... equivalent to the OR of all three of these
	assign	adf_ce_unconditional = (master_ce)&&(~clear_pipeline)&&(opvalid)
				&&(~opvalid_mem)&&(~mem_rdbusy)
				&&((~opvalid_alu)||(~alu_stall))&&(~op_break)
				&&(~div_busy)&&(~fpu_busy)&&(~clear_pipeline);

	//
	//
	//	PIPELINE STAGE #1 :: Prefetch
	//
	//
`ifdef	OPT_SINGLE_FETCH
	wire		pf_ce;

	assign		pf_ce = (~pf_valid)&&(~dcdvalid)&&(~opvalid)&&(~alu_busy)&&(~mem_busy)&&(~alu_pc_valid)&&(~mem_pc_valid);
	prefetch	#(ADDRESS_WIDTH)
			pf(i_clk, (i_rst), (pf_ce), (~dcd_stalled), pf_pc, gie,
				instruction, instruction_pc, instruction_gie,
					pf_valid, pf_illegal,
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
				pf_ack, pf_stall, pf_err, i_wb_data);

	initial	r_dcdvalid = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline))
			r_dcdvalid <= 1'b0;
		else if (dcd_ce)
			r_dcdvalid <= (pf_valid)||(pf_illegal);
		else if (op_ce)
			r_dcdvalid <= 1'b0;
	assign	dcdvalid = r_dcdvalid;

`else // Pipe fetch

`ifdef	OPT_TRADITIONAL_PFCACHE
	pfcache #(LGICACHE, ADDRESS_WIDTH)
		pf(i_clk, i_rst, (new_pc)||((dcd_early_branch)&&(~clear_pipeline)),
					w_clear_icache,
				// dcd_pc,
				~dcd_stalled,
				((dcd_early_branch)&&(~clear_pipeline))
					? dcd_branch_pc:pf_pc,
				instruction, instruction_pc, pf_valid,
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
					pf_ack, pf_stall, pf_err, i_wb_data,
				pf_illegal);
`else
	pipefetch	#(RESET_ADDRESS, LGICACHE, ADDRESS_WIDTH)
			pf(i_clk, i_rst, (new_pc)||(dcd_early_branch),
					w_clear_icache, ~dcd_stalled,
					(new_pc)?pf_pc:dcd_branch_pc,
					instruction, instruction_pc, pf_valid,
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
					pf_ack, pf_stall, pf_err, i_wb_data,
//`ifdef	OPT_PRECLEAR_BUS
				//((dcd_clear_bus)&&(dcdvalid))
				//||((op_clear_bus)&&(opvalid))
				//||
//`endif
				(mem_cyc_lcl)||(mem_cyc_gbl),
				pf_illegal);
`endif
`ifdef	OPT_NO_USERMODE
	assign	instruction_gie = 1'b0;
`else
	assign	instruction_gie = gie;
`endif

	initial	r_dcdvalid = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline)||(w_clear_icache))
			r_dcdvalid <= 1'b0;
		else if (dcd_ce)
			r_dcdvalid <= (pf_valid)&&(~dcd_ljmp)&&(~dcd_early_branch);
		else if (op_ce)
			r_dcdvalid <= 1'b0;
	assign	dcdvalid = r_dcdvalid;
`endif


	// If not pipelined, there will be no opvalid_ anything, and the
	idecode #(AW, IMPLEMENT_MPY, EARLY_BRANCHING, IMPLEMENT_DIVIDE,
			IMPLEMENT_FPU)
		instruction_decoder(i_clk, (i_rst)||(clear_pipeline),
			(~dcdvalid)||(~op_stall), dcd_stalled, instruction, instruction_gie,
			instruction_pc, pf_valid, pf_illegal, dcd_phase,
			dcd_illegal, dcd_pc, dcd_gie, 
			{ dcdR_cc, dcdR_pc, dcdR },
			{ dcdA_cc, dcdA_pc, dcdA },
			{ dcdB_cc, dcdB_pc, dcdB },
			dcdI, dcd_zI, dcdF, dcdF_wr, dcdOp,
			dcdALU, dcdM, dcdDV, dcdFP, dcd_break, dcd_lock,
			dcdR_wr,dcdA_rd, dcdB_rd,
			dcd_early_branch,
			dcd_branch_pc, dcd_ljmp,
			dcd_pipe);

`ifdef	OPT_PIPELINED_BUS_ACCESS
	reg		r_op_pipe;

	initial	r_op_pipe = 1'b0;
	// To be a pipeable operation, there must be 
	//	two valid adjacent instructions
	//	Both must be memory instructions
	//	Both must be writes, or both must be reads
	//	Both operations must be to the same identical address,
	//		or at least a single (one) increment above that address
	//
	// However ... we need to know this before this clock, hence this is
	// calculated in the instruction decoder.
	always @(posedge i_clk)
		if (op_ce)
			r_op_pipe <= dcd_pipe;
		else if (mem_ce) // Clear us any time an op_ is clocked in
			r_op_pipe <= 1'b0;
	assign	op_pipe = r_op_pipe;
`else
	assign	op_pipe = 1'b0;
`endif

	//
	//
	//	PIPELINE STAGE #3 :: Read Operands (Registers)
	//
	//
`ifdef	OPT_NO_USERMODE
	assign	w_opA = regset[dcdA[3:0]];
	assign	w_opB = regset[dcdB[3:0]];
`else
	assign	w_opA = regset[dcdA];
	assign	w_opB = regset[dcdB];
`endif

	wire	[8:0]	w_cpu_info;
	assign	w_cpu_info = {
`ifdef	OPT_ILLEGAL_INSTRUCTION
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_MULTIPLY
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_DIVIDE
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_IMPLEMENT_FPU
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_PIPELINED
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_TRADITIONAL_CACHE
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_EARLY_BRANCHING
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_PIPELINED_BUS_ACCESS
	1'b1,
`else
	1'b0,
`endif
`ifdef	OPT_VLIW
	1'b1
`else
	1'b0
`endif
	};

	wire	[31:0]	w_pcA_v;
	generate
	if (AW < 32)
		assign	w_pcA_v = {{(32-AW){1'b0}}, (dcdA[4] == dcd_gie)?dcd_pc:upc };
	else
		assign	w_pcA_v = (dcdA[4] == dcd_gie)?dcd_pc:upc;
	endgenerate

`ifdef	OPT_PIPELINED
	reg	[4:0]	opA_id, opB_id;
	reg		opA_rd, opB_rd;
	always @(posedge i_clk)
		if (op_ce)
		begin
			opA_id <= dcdA;
			opB_id <= dcdB;
			opA_rd <= dcdA_rd;
			opB_rd <= dcdB_rd;
		end
`endif

	always @(posedge i_clk)
`ifdef	OPT_PIPELINED
		if (op_change_data_ce)
`endif
		begin
`ifdef	OPT_PIPELINED
			if ((wr_reg_ce)&&(wr_reg_id == dcdA))
				r_opA <= wr_gpreg_vl;
			else
`endif
			if (dcdA_pc)
				r_opA <= w_pcA_v;
			else if (dcdA_cc)
				r_opA <= { w_cpu_info, w_opA[22:16], 1'b0, (dcdA[4])?w_uflags:w_iflags };
			else
				r_opA <= w_opA;
`ifdef	OPT_PIPELINED
		end else
		begin // We were going to pick these up when they became valid,
			// but for some reason we're stuck here as they became
			// valid.  Pick them up now anyway
			// if (((opA_alu)&&(alu_wr))||((opA_mem)&&(mem_valid)))
				// r_opA <= wr_gpreg_vl;
			if ((wr_reg_ce)&&(wr_reg_id == opA_id)&&(opA_rd))
				r_opA <= wr_gpreg_vl;
`endif
		end

	wire	[31:0]	w_opBnI, w_pcB_v;
	generate
	if (AW < 32)
		assign	w_pcB_v = {{(32-AW){1'b0}}, (dcdB[4] == dcd_gie)?dcd_pc:upc };
	else
		assign	w_pcB_v = (dcdB[4] == dcd_gie)?dcd_pc:upc;
	endgenerate

	assign	w_opBnI = (~dcdB_rd) ? 32'h00
`ifdef	OPT_PIPELINED
		: ((wr_reg_ce)&&(wr_reg_id == dcdB)) ? wr_gpreg_vl
`endif
		: ((dcdB_pc) ? w_pcB_v
		: ((dcdB_cc) ? { w_cpu_info, w_opB[22:16], // w_opB[31:14],
			1'b0, (dcdB[4])?w_uflags:w_iflags}
		: w_opB));

	always @(posedge i_clk)
`ifdef	OPT_PIPELINED
		if (op_change_data_ce)
			r_opB <= w_opBnI + dcdI;
		else if ((wr_reg_ce)&&(opB_id == wr_reg_id)&&(opB_rd))
			r_opB <= wr_gpreg_vl;
`else
		r_opB <= w_opBnI + dcdI;
`endif

	// The logic here has become more complex than it should be, no thanks
	// to Xilinx's Vivado trying to help.  The conditions are supposed to
	// be two sets of four bits: the top bits specify what bits matter, the
	// bottom specify what those top bits must equal.  However, two of
	// conditions check whether bits are on, and those are the only two
	// conditions checking those bits.  Therefore, Vivado complains that
	// these two bits are redundant.  Hence the convoluted expression
	// below, arriving at what we finally want in the (now wire net)
	// opF.
	always @(posedge i_clk)
`ifdef	OPT_PIPELINED
		if (op_ce) // Cannot do op_change_data_ce here since opF depends
			// upon being either correct for a valid op, or correct
			// for the last valid op
`endif
		begin // Set the flag condition codes, bit order is [3:0]=VNCZ
			case(dcdF[2:0])
			3'h0:	r_opF <= 7'h00;	// Always
			3'h1:	r_opF <= 7'h44;	// LT
			3'h2:	r_opF <= 7'h11;	// Z
			3'h3:	r_opF <= 7'h10;	// NE
			3'h4:	r_opF <= 7'h50;	// GT (!N&!Z)
`ifdef	OPT_NEW_CONDITION_CODE
			3'h5:	r_opF <= 7'h20;	// NC
`else
			3'h5:	r_opF <= 7'h40;	// GE (!N)
`endif
			3'h6:	r_opF <= 7'h02;	// C
			3'h7:	r_opF <= 7'h08;	// V
			endcase
		end // Bit order is { (flags_not_used), VNCZ mask, VNCZ value }
	assign	opF = { r_opF[3], r_opF[6:0] };

	wire	w_opvalid;
	assign	w_opvalid = (~clear_pipeline)&&(dcdvalid)&&(~dcd_ljmp)&&(!dcd_early_branch);
	initial	opvalid     = 1'b0;
	initial	opvalid_alu = 1'b0;
	initial	opvalid_mem = 1'b0;
	initial	opvalid_div = 1'b0;
	initial	opvalid_fpu = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline))
		begin
			opvalid     <= 1'b0;
			opvalid_alu <= 1'b0;
			opvalid_mem <= 1'b0;
			opvalid_div <= 1'b0;
			opvalid_fpu <= 1'b0;
		end else if (op_ce)
		begin
			// Do we have a valid instruction?
			//   The decoder may vote to stall one of its
			//   instructions based upon something we currently
			//   have in our queue.  This instruction must then
			//   move forward, and get a stall cycle inserted.
			//   Hence, the test on dcd_stalled here.  If we must
			//   wait until our operands are valid, then we aren't
			//   valid yet until then.
			opvalid<= (w_opvalid)||(dcd_illegal)&&(dcdvalid)||(dcd_early_branch);
`ifdef	OPT_ILLEGAL_INSTRUCTION
			opvalid_alu <= (w_opvalid)&&((dcdALU)||(dcd_illegal)
					||(dcd_early_branch));
			opvalid_mem <= (dcdM)&&(~dcd_illegal)&&(w_opvalid);
			opvalid_div <= (dcdDV)&&(~dcd_illegal)&&(w_opvalid);
			opvalid_fpu <= (dcdFP)&&(~dcd_illegal)&&(w_opvalid);
`else
			opvalid_alu <= (dcdALU)&&(w_opvalid)||(dcd_early_branch);
			opvalid_mem <= (dcdM)&&(w_opvalid);
			opvalid_div <= (dcdDV)&&(w_opvalid);
			opvalid_fpu <= (dcdFP)&&(w_opvalid);
`endif
		end else if ((adf_ce_unconditional)||(mem_ce))
		begin
			opvalid     <= 1'b0;
			opvalid_alu <= 1'b0;
			opvalid_mem <= 1'b0;
			opvalid_div <= 1'b0;
			opvalid_fpu <= 1'b0;
		end

	// Here's part of our debug interface.  When we recognize a break
	// instruction, we set the op_break flag.  That'll prevent this
	// instruction from entering the ALU, and cause an interrupt before
	// this instruction.  Thus, returning to this code will cause the
	// break to repeat and continue upon return.  To get out of this
	// condition, replace the break instruction with what it is supposed
	// to be, step through it, and then replace it back.  In this fashion,
	// a debugger can step through code.
	// assign w_op_break = (dcd_break)&&(r_dcdI[15:0] == 16'h0001);
`ifdef	OPT_PIPELINED
	reg	r_op_break;

	initial	r_op_break = 1'b0;
	always @(posedge i_clk)
		if (i_rst)	r_op_break <= 1'b0;
		else if (op_ce)	r_op_break <= (dcd_break);
		else if ((clear_pipeline)||(~opvalid))
				r_op_break <= 1'b0;
	assign	op_break = r_op_break;
`else
	assign	op_break = dcd_break;
`endif

`ifdef	OPT_PIPELINED
	generate
	if (IMPLEMENT_LOCK != 0)
	begin
		reg	r_op_lock, r_op_lock_stall;

		initial	r_op_lock_stall = 1'b0;
		always @(posedge i_clk)
			if (i_rst)
				r_op_lock_stall <= 1'b0;
			else
				r_op_lock_stall <= (~opvalid)||(~op_lock)
						||(~dcdvalid)||(~pf_valid);

		assign	op_lock_stall = r_op_lock_stall;

		initial	r_op_lock = 1'b0;
		always @(posedge i_clk)
			if ((i_rst)||(clear_pipeline))
				r_op_lock <= 1'b0;
			else if (op_ce)
				r_op_lock <= (dcd_lock)&&(~clear_pipeline);
		assign	op_lock = r_op_lock;

	end else begin
		assign	op_lock_stall = 1'b0;
		assign	op_lock = 1'b0;
	end endgenerate

`else
	assign op_lock_stall = 1'b0;
	assign op_lock       = 1'b0;
`endif

`ifdef	OPT_ILLEGAL_INSTRUCTION
	initial	op_illegal = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline))
			op_illegal <= 1'b0;
		else if(op_ce)
`ifdef	OPT_PIPELINED
			op_illegal <= (dcdvalid)&&((dcd_illegal)||((dcd_lock)&&(IMPLEMENT_LOCK == 0)));
`else
			op_illegal <= (dcdvalid)&&((dcd_illegal)||(dcd_lock));
`endif
		else if(alu_ce)
			op_illegal <= 1'b0;
`endif

	// No generate on EARLY_BRANCHING here, since if EARLY_BRANCHING is not
	// set, dcd_early_branch will simply be a wire connected to zero and
	// this logic should just optimize.
`ifdef	OPT_PIPELINED
	always @(posedge i_clk)
		if (op_ce)
		begin
			opF_wr <= (dcdF_wr)&&((~dcdR_cc)||(~dcdR_wr))
				&&(~dcd_early_branch)&&(~dcd_illegal);
			opR_wr <= (dcdR_wr)&&(~dcd_early_branch)&&(~dcd_illegal);
		end
`else
	always @(posedge i_clk)
	begin
		opF_wr <= (dcdF_wr)&&((~dcdR_cc)||(~dcdR_wr))
			&&(~dcd_early_branch)&&(~dcd_illegal);
		opR_wr <= (dcdR_wr)&&(~dcd_early_branch)&&(~dcd_illegal);
	end
`endif

`ifdef	OPT_PIPELINED
	reg	[3:0]	r_opn;
	reg	[4:0]	r_opR;
	reg		r_opR_cc;
	reg		r_op_gie;
	always @(posedge i_clk)
		if (op_change_data_ce)
		begin
			// Which ALU operation?  Early branches are
			// unimplemented moves
			r_opn    <= (dcd_early_branch) ? 4'hf : dcdOp;
			// opM  <= dcdM;	// Is this a memory operation?
			// What register will these results be written into?
			r_opR    <= dcdR;
			r_opR_cc <= (dcdR_cc)&&(dcdR_wr)&&(dcdR[4]==dcd_gie);
			// User level (1), vs supervisor (0)/interrupts disabled
			r_op_gie <= dcd_gie;

			//
			op_pc  <= (dcd_early_branch)?dcd_branch_pc:dcd_pc;
		end
	assign	opn = r_opn;
	assign	opR = r_opR;
`ifdef	OPT_NO_USERMODE
	assign	op_gie = 1'b0;
`else
	assign	op_gie = r_op_gie;
`endif
	assign	opR_cc = r_opR_cc;
`else
	assign	opn = dcdOp;
	assign	opR = dcdR;
`ifdef	OPT_NO_USERMODE
	assign	op_gie = 1'b0;
`else
	assign	op_gie = dcd_gie;
`endif
	// With no pipelining, there is no early branching.  We keep it
	always @(posedge i_clk)
		op_pc <= (dcd_early_branch)?dcd_branch_pc:dcd_pc;
`endif
	assign	opFl = (op_gie)?(w_uflags):(w_iflags);

`ifdef	OPT_VLIW
	reg	r_op_phase;
	initial	r_op_phase = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline))
			r_op_phase <= 1'b0;
		else if (op_change_data_ce)
			r_op_phase <= dcd_phase;
	assign	op_phase = r_op_phase;
`else
	assign	op_phase = 1'b0;
`endif

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
`ifdef	OPT_PIPELINED
	assign	opA = ((wr_reg_ce)&&(wr_reg_id == opA_id)) // &&(opA_rd))
			?  wr_gpreg_vl : r_opA;
`else
	assign	opA = r_opA;
`endif

`ifdef	OPT_PIPELINED
	// Stall if we have decoded an instruction that will read register A
	//	AND ... something that may write a register is running
	//	AND (series of conditions here ...)
	//		The operation might set flags, and we wish to read the
	//			CC register
	//		OR ... (No other conditions)
	assign	dcdA_stall = (dcdA_rd) // &&(dcdvalid) is checked for elsewhere
				&&((opvalid)||(mem_rdbusy)
					||(div_busy)||(fpu_busy))
				&&(((opF_wr)||(cc_invalid_for_dcd))&&(dcdA_cc))
			||((dcdA_rd)&&(dcdA_cc)&&(cc_invalid_for_dcd));
`else
	// There are no pipeline hazards, if we aren't pipelined
	assign	dcdA_stall = 1'b0;
`endif

`ifdef	OPT_PIPELINED
	assign	opB = ((wr_reg_ce)&&(wr_reg_id == opB_id)&&(opB_rd))
			? wr_gpreg_vl: r_opB;
`else
	assign	opB = r_opB;
`endif

`ifdef	OPT_PIPELINED
	// Stall if we have decoded an instruction that will read register B
	//	AND ... something that may write a (unknown) register is running
	//	AND (series of conditions here ...)
	//		The operation might set flags, and we wish to read the
	//			CC register
	//		OR the operation might set register B, and we still need
	//			a clock to add the offset to it
	assign	dcdB_stall = (dcdB_rd) // &&(dcdvalid) is checked for elsewhere
				// If the op stage isn't valid, yet something
				// is running, then it must have been valid.
				// We'll use the last values from that stage
				// (opR_wr, opF_wr, opR) in our logic below.
				&&((opvalid)||(mem_rdbusy)
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
				((~dcd_zI)&&(
					((opR == dcdB)&&(opR_wr))
					||((mem_rdbusy)&&(~dcd_pipe))
					))
				// Stall following any instruction that will
				// set the flags, if we're going to need the
				// flags (CC) register for opB.
				||(((opF_wr)||(cc_invalid_for_dcd))&&(dcdB_cc))
				// Stall on any ongoing memory operation that
				// will write to opB -- captured above
				// ||((mem_busy)&&(~mem_we)&&(mem_last_reg==dcdB)&&(~dcd_zI))
				)
			||((dcdB_rd)&&(dcdB_cc)&&(cc_invalid_for_dcd));
	assign	dcdF_stall = ((~dcdF[3])
					||((dcdA_rd)&&(dcdA_cc))
					||((dcdB_rd)&&(dcdB_cc)))
					&&(opvalid)&&(opR_cc);
				// &&(dcdvalid) is checked for elsewhere
`else
	// No stalls without pipelining, 'cause how can you have a pipeline
	// hazard without the pipeline?
	assign	dcdB_stall = 1'b0;
	assign	dcdF_stall = 1'b0;
`endif
	//
	//
	//	PIPELINE STAGE #4 :: Apply Instruction
	//
	//
	cpuops	#(IMPLEMENT_MPY) doalu(i_clk, (i_rst)||(clear_pipeline),
			alu_ce, opn, opA, opB,
			alu_result, alu_flags, alu_valid, alu_busy);

	generate
	if (IMPLEMENT_DIVIDE != 0)
	begin
		div thedivide(i_clk, (i_rst)||(clear_pipeline), div_ce, opn[0],
			opA, opB, div_busy, div_valid, div_error, div_result,
			div_flags);
	end else begin
		assign	div_error = 1'b0; // Can't be high unless div_valid
		assign	div_busy  = 1'b0;
		assign	div_valid = 1'b0;
		assign	div_result= 32'h00;
		assign	div_flags = 4'h0;
	end endgenerate

	generate
	if (IMPLEMENT_FPU != 0)
	begin
		//
		// sfpu thefpu(i_clk, i_rst, fpu_ce,
		//	opA, opB, fpu_busy, fpu_valid, fpu_err, fpu_result,
		//	fpu_flags);
		//
		assign	fpu_error = 1'b0; // Must only be true if fpu_valid
		assign	fpu_busy  = 1'b0;
		assign	fpu_valid = 1'b0;
		assign	fpu_result= 32'h00;
		assign	fpu_flags = 4'h0;
	end else begin
		assign	fpu_error = 1'b0;
		assign	fpu_busy  = 1'b0;
		assign	fpu_valid = 1'b0;
		assign	fpu_result= 32'h00;
		assign	fpu_flags = 4'h0;
	end endgenerate


	assign	set_cond = ((opF[7:4]&opFl[3:0])==opF[3:0]);
	initial	alF_wr   = 1'b0;
	initial	alu_wr   = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
		begin
			alu_wr   <= 1'b0;
			alF_wr   <= 1'b0;
		end else if (alu_ce)
		begin
			// alu_reg <= opR;
			alu_wr  <= (opR_wr)&&(set_cond);
			alF_wr  <= (opF_wr)&&(set_cond);
		end else if (~alu_busy) begin
			// These are strobe signals, so clear them if not
			// set for any particular clock
			alu_wr <= (i_halt)&&(i_dbg_we);
			alF_wr <= 1'b0;
		end

`ifdef	OPT_VLIW
	reg	r_alu_phase;
	initial	r_alu_phase = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			r_alu_phase <= 1'b0;
		else if ((adf_ce_unconditional)||(mem_ce))
			r_alu_phase <= op_phase;
	assign	alu_phase = r_alu_phase;
`else
	assign	alu_phase = 1'b0;
`endif

`ifdef	OPT_PIPELINED
	always @(posedge i_clk)
		if (adf_ce_unconditional)
			alu_reg <= opR;
		else if ((i_halt)&&(i_dbg_we))
			alu_reg <= i_dbg_reg;
`else
	always @(posedge i_clk)
		if ((i_halt)&&(i_dbg_we))
			alu_reg <= i_dbg_reg;
		else
			alu_reg <= opR;
`endif

	//
	// DEBUG Register write access starts here
	//
	reg		dbgv;
	initial	dbgv = 1'b0;
	always @(posedge i_clk)
		dbgv <= (~i_rst)&&(i_halt)&&(i_dbg_we)&&(r_halted);
	reg	[31:0]	dbg_val;
	always @(posedge i_clk)
		dbg_val <= i_dbg_data;
`ifdef	OPT_NO_USERMODE
	assign	alu_gie = 1'b0;
`else
`ifdef	OPT_PIPELINED
	reg	r_alu_gie;

	always @(posedge i_clk)
		if ((adf_ce_unconditional)||(mem_ce))
			r_alu_gie  <= op_gie;
	assign	alu_gie = r_alu_gie;
`else
	assign	alu_gie = op_gie;
`endif
`endif

`ifdef	OPT_PIPELINED
	reg	[(AW-1):0]	r_alu_pc;
	always @(posedge i_clk)
		if ((adf_ce_unconditional)
			||((master_ce)&&(opvalid_mem)&&(~clear_pipeline)
				&&(~mem_stalled)))
			r_alu_pc  <= op_pc;
	assign	alu_pc = r_alu_pc;
`else
	assign	alu_pc = op_pc;
`endif

`ifdef	OPT_ILLEGAL_INSTRUCTION
	reg	r_alu_illegal;
	initial	r_alu_illegal = 0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline))
			r_alu_illegal <= 1'b0;
		else if (alu_ce)
			r_alu_illegal <= op_illegal;
		else
			r_alu_illegal <= 1'b0;
	assign	alu_illegal = (r_alu_illegal);
`else
	assign	alu_illegal = 1'b0;
`endif

	initial	r_alu_pc_valid = 1'b0;
	initial	mem_pc_valid = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			r_alu_pc_valid <= 1'b0;
		else if (adf_ce_unconditional)//Includes&&(~alu_clear_pipeline)
			r_alu_pc_valid <= 1'b1;
		else if (((~alu_busy)&&(~div_busy)&&(~fpu_busy))||(clear_pipeline))
			r_alu_pc_valid <= 1'b0;
	assign	alu_pc_valid = (r_alu_pc_valid)&&((~alu_busy)&&(~div_busy)&&(~fpu_busy));
	always @(posedge i_clk)
		if (i_rst)
			mem_pc_valid <= 1'b0;
		else
			mem_pc_valid <= (mem_ce);

	wire	bus_lock;
`ifdef	OPT_PIPELINED
	generate
	if (IMPLEMENT_LOCK != 0)
	begin
		reg	[1:0]	r_bus_lock;
		initial	r_bus_lock = 2'b00;
		always @(posedge i_clk)
			if (i_rst)
				r_bus_lock <= 2'b00;
			else if ((op_ce)&&(op_lock))
				r_bus_lock <= 2'b11;
			else if ((|r_bus_lock)&&((~opvalid_mem)||(~op_ce)))
				r_bus_lock <= r_bus_lock + 2'b11;
		assign	bus_lock = |r_bus_lock;
	end else begin
		assign	bus_lock = 1'b0;
	end endgenerate
`else
	assign	bus_lock = 1'b0;
`endif

`ifdef	OPT_PIPELINED_BUS_ACCESS
	pipemem	#(AW,IMPLEMENT_LOCK) domem(i_clk, i_rst,(mem_ce)&&(set_cond), bus_lock,
				(opn[0]), opB, opA, opR,
				mem_busy, mem_pipe_stalled,
				mem_valid, bus_err, mem_wreg, mem_result,
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_addr, mem_data,
				mem_ack, mem_stall, mem_err, i_wb_data);
			
`else // PIPELINED_BUS_ACCESS
	memops	#(AW,IMPLEMENT_LOCK) domem(i_clk, i_rst,(mem_ce)&&(set_cond), bus_lock,
				(opn[0]), opB, opA, opR,
				mem_busy,
				mem_valid, bus_err, mem_wreg, mem_result,
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_addr, mem_data,
				mem_ack, mem_stall, mem_err, i_wb_data);
	assign	mem_pipe_stalled = 1'b0;
`endif // PIPELINED_BUS_ACCESS
	assign	mem_rdbusy = ((mem_busy)&&(~mem_we));

	// Either the prefetch or the instruction gets the memory bus, but 
	// never both.
	wbdblpriarb	#(32,AW) pformem(i_clk, i_rst,
		// Memory access to the arbiter, priority position
		mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl,
			mem_we, mem_addr, mem_data, mem_ack, mem_stall, mem_err,
		// Prefetch access to the arbiter
		pf_cyc, 1'b0, pf_stb, 1'b0, pf_we, pf_addr, pf_data,
			pf_ack, pf_stall, pf_err,
		// Common wires, in and out, of the arbiter
		o_wb_gbl_cyc, o_wb_lcl_cyc, o_wb_gbl_stb, o_wb_lcl_stb, 
			o_wb_we, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err);



	//
	//
	//
	//
	//
	//
	//
	//
	//	PIPELINE STAGE #5 :: Write-back results
	//
	//
	// This stage is not allowed to stall.  If results are ready to be
	// written back, they are written back at all cost.  Sleepy CPU's
	// won't prevent write back, nor debug modes, halting the CPU, nor
	// anything else.  Indeed, the (master_ce) bit is only as relevant
	// as knowinig something is available for writeback.

	//
	// Write back to our generic register set ...
	// When shall we write back?  On one of two conditions
	//	Note that the flags needed to be checked before issuing the
	//	bus instruction, so they don't need to be checked here.
	//	Further, alu_wr includes (set_cond), so we don't need to
	//	check for that here either.
`ifdef	OPT_ILLEGAL_INSTRUCTION
	assign	wr_reg_ce = (dbgv)||(mem_valid)
				||((~clear_pipeline)&&(~alu_illegal)
					&&(((alu_wr)&&(alu_valid))
						||(div_valid)||(fpu_valid)));
`else
	assign	wr_reg_ce = (dbgv)||(mem_valid)
				||((~clear_pipeline)
					&&(((alu_wr)&&(alu_valid))
						||(div_valid)||(fpu_valid)));
`endif
	// Which register shall be written?
	//	COULD SIMPLIFY THIS: by adding three bits to these registers,
	//		One or PC, one for CC, and one for GIE match
	//	Note that the alu_reg is the register to write on a divide or
	//	FPU operation.
`ifdef	OPT_NO_USERMODE
	assign	wr_reg_id[3:0] = (alu_wr|div_valid|fpu_valid)
				? alu_reg[3:0]:mem_wreg[3:0];
	assign	wr_reg_id[4] = 1'b0;
`else
	assign	wr_reg_id = (alu_wr|div_valid|fpu_valid)?alu_reg:mem_wreg;
`endif

	// Are we writing to the CC register?
	assign	wr_write_cc = (wr_reg_id[3:0] == `CPU_CC_REG);
	assign	wr_write_scc = (wr_reg_id[4:0] == {1'b0, `CPU_CC_REG});
	assign	wr_write_ucc = (wr_reg_id[4:0] == {1'b1, `CPU_CC_REG});
	// Are we writing to the PC?
	assign	wr_write_pc = (wr_reg_id[3:0] == `CPU_PC_REG);

	// What value to write?
	assign	wr_gpreg_vl = ((mem_valid) ? mem_result
				:((div_valid|fpu_valid))
					? ((div_valid) ? div_result:fpu_result)
				:((dbgv) ? dbg_val : alu_result));
	assign	wr_spreg_vl = ((mem_valid) ? mem_result
				:((dbgv) ? dbg_val : alu_result));
	always @(posedge i_clk)
		if (wr_reg_ce)
`ifdef	OPT_NO_USERMODE
			regset[wr_reg_id[3:0]] <= wr_gpreg_vl;
`else
			regset[wr_reg_id] <= wr_gpreg_vl;
`endif

	//
	// Write back to the condition codes/flags register ...
	// When shall we write to our flags register?  alF_wr already
	// includes the set condition ...
	assign	wr_flags_ce = ((alF_wr)||(div_valid)||(fpu_valid))&&(~clear_pipeline)&&(~alu_illegal);
	assign	w_uflags = { 1'b0, uhalt_phase, ufpu_err_flag,
			udiv_err_flag, ubus_err_flag, trap, ill_err_u,
			ubreak, step, 1'b1, sleep,
			((wr_flags_ce)&&(alu_gie))?alu_flags:flags };
	assign	w_iflags = { 1'b0, ihalt_phase, ifpu_err_flag,
			idiv_err_flag, ibus_err_flag, trap, ill_err_i,
			break_en, 1'b0, 1'b0, sleep,
			((wr_flags_ce)&&(~alu_gie))?alu_flags:iflags };


	// What value to write?
	always @(posedge i_clk)
		// If explicitly writing the register itself
		if ((wr_reg_ce)&&(wr_write_ucc))
			flags <= wr_gpreg_vl[3:0];
		// Otherwise if we're setting the flags from an ALU operation
		else if ((wr_flags_ce)&&(alu_gie))
			flags <= (div_valid)?div_flags:((fpu_valid)?fpu_flags
				: alu_flags);

	always @(posedge i_clk)
		if ((wr_reg_ce)&&(wr_write_scc))
			iflags <= wr_gpreg_vl[3:0];
		else if ((wr_flags_ce)&&(~alu_gie))
			iflags <= (div_valid)?div_flags:((fpu_valid)?fpu_flags
				: alu_flags);

	// The 'break' enable  bit.  This bit can only be set from supervisor
	// mode.  It control what the CPU does upon encountering a break
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
	//	Upon a CPU halt, any break condition will be reset.  The
	//	external debugger will then need to deal with whatever
	//	condition has taken place.
	initial	break_en = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(i_halt))
			break_en <= 1'b0;
		else if ((wr_reg_ce)&&(wr_write_scc))
			break_en <= wr_spreg_vl[`CPU_BREAK_BIT];

`ifdef	OPT_PIPELINED
	reg	r_break_pending;

	initial	r_break_pending = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(clear_pipeline)||(~opvalid))
			r_break_pending <= 1'b0;
		else if (op_break)
			r_break_pending <= (~alu_busy)&&(~div_busy)&&(~fpu_busy)&&(~mem_busy)&&(!wr_reg_ce);
		else
			r_break_pending <= 1'b0;
	assign	break_pending = r_break_pending;
`else
	assign	break_pending = op_break;
`endif


	assign	o_break = ((break_en)||(~op_gie))&&(break_pending)
				&&(~clear_pipeline)
			||((~alu_gie)&&(bus_err))
			||((~alu_gie)&&(div_error))
			||((~alu_gie)&&(fpu_error))
			||((~alu_gie)&&(alu_illegal)&&(!clear_pipeline));

	// The sleep register.  Setting the sleep register causes the CPU to
	// sleep until the next interrupt.  Setting the sleep register within
	// interrupt mode causes the processor to halt until a reset.  This is
	// a panic/fault halt.  The trick is that you cannot be allowed to
	// set the sleep bit and switch to supervisor mode in the same 
	// instruction: users are not allowed to halt the CPU.
	initial	sleep = 1'b0;
`ifdef	OPT_NO_USERMODE
	reg	r_sleep_is_halt;
	initial	r_sleep_is_halt = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			r_sleep_is_halt <= 1'b0;
		else if ((wr_reg_ce)&&(wr_write_cc)
				&&(wr_spreg_vl[`CPU_SLEEP_BIT])
				&&(~wr_spreg_vl[`CPU_GIE_BIT]))
			r_sleep_is_halt <= 1'b1;

	// Trying to switch to user mode, either via a WAIT or an RTU
	// instruction will cause the CPU to sleep until an interrupt, in
	// the NO-USERMODE build.
	always @(posedge i_clk)
		if ((i_rst)||((i_interrupt)&&(!r_sleep_is_halt)))
			sleep <= 1'b0;
		else if ((wr_reg_ce)&&(wr_write_cc)
				&&(wr_spreg_vl[`CPU_GIE_BIT]))
			sleep <= 1'b1;
`else
	always @(posedge i_clk)
		if ((i_rst)||(w_switch_to_interrupt))
			sleep <= 1'b0;
		else if ((wr_reg_ce)&&(wr_write_cc)&&(~alu_gie))
			// In supervisor mode, we have no protections.  The
			// supervisor can set the sleep bit however he wants.
			// Well ... not quite.  Switching to user mode and
			// sleep mode shouold only be possible if the interrupt
			// flag isn't set.
			//	Thus: if (i_interrupt)&&(wr_spreg_vl[GIE])
			//		don't set the sleep bit
			//	otherwise however it would o.w. be set
			sleep <= (wr_spreg_vl[`CPU_SLEEP_BIT])
				&&((~i_interrupt)||(~wr_spreg_vl[`CPU_GIE_BIT]));
		else if ((wr_reg_ce)&&(wr_write_cc)&&(wr_spreg_vl[`CPU_GIE_BIT]))
			// In user mode, however, you can only set the sleep
			// mode while remaining in user mode.  You can't switch
			// to sleep mode *and* supervisor mode at the same
			// time, lest you halt the CPU.
			sleep <= wr_spreg_vl[`CPU_SLEEP_BIT];
`endif

	always @(posedge i_clk)
		if (i_rst)
			step <= 1'b0;
		else if ((wr_reg_ce)&&(~alu_gie)&&(wr_write_ucc))
			step <= wr_spreg_vl[`CPU_STEP_BIT];

	// The GIE register.  Only interrupts can disable the interrupt register
`ifdef	OPT_NO_USERMODE
	assign	w_switch_to_interrupt    = 1'b0;
	assign	w_release_from_interrupt = 1'b0;
`else
	assign	w_switch_to_interrupt = (gie)&&(
			// On interrupt (obviously)
			((i_interrupt)&&(~alu_phase)&&(~bus_lock))
			// If we are stepping the CPU
			||(((alu_pc_valid)||(mem_pc_valid))&&(step)&&(~alu_phase)&&(~bus_lock))
			// If we encounter a break instruction, if the break
			//	enable isn't set.
			||((master_ce)&&(break_pending)&&(~break_en))
`ifdef	OPT_ILLEGAL_INSTRUCTION
			// On an illegal instruction
			||((alu_illegal)&&(!clear_pipeline))
`endif
			// On division by zero.  If the divide isn't
			// implemented, div_valid and div_error will be short
			// circuited and that logic will be bypassed
			||(div_error)
			// Same thing on a floating point error.  Note that
			// fpu_error must *never* be set unless fpu_valid is
			// also set as well, else this will fail.
			||(fpu_error)
			//	
			||(bus_err)
			// If we write to the CC register
			||((wr_reg_ce)&&(~wr_spreg_vl[`CPU_GIE_BIT])
				&&(wr_reg_id[4])&&(wr_write_cc))
			);
	assign	w_release_from_interrupt = (~gie)&&(~i_interrupt)
			// Then if we write the sCC register
			&&(((wr_reg_ce)&&(wr_spreg_vl[`CPU_GIE_BIT])
				&&(wr_write_scc))
			);
`endif

`ifdef	OPT_NO_USERMODE
	assign	gie = 1'b0;
`else
	reg	r_gie;

	initial	r_gie = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			r_gie <= 1'b0;
		else if (w_switch_to_interrupt)
			r_gie <= 1'b0;
		else if (w_release_from_interrupt)
			r_gie <= 1'b1;
	assign	gie = r_gie;
`endif

`ifdef	OPT_NO_USERMODE
	assign	trap   = 1'b0;
	assign	ubreak = 1'b0;
`else
	reg	r_trap;

	initial	r_trap = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(w_release_from_interrupt))
			r_trap <= 1'b0;
		else if ((alu_gie)&&(wr_reg_ce)&&(~wr_spreg_vl[`CPU_GIE_BIT])
				&&(wr_write_ucc)) // &&(wr_reg_id[4]) implied
			r_trap <= 1'b1;
		else if ((wr_reg_ce)&&(wr_write_ucc)&&(~alu_gie))
			r_trap <= (r_trap)&&(wr_spreg_vl[`CPU_TRAP_BIT]);

	reg	r_ubreak;

	initial	r_ubreak = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(w_release_from_interrupt))
			r_ubreak <= 1'b0;
		else if ((op_gie)&&(break_pending)&&(w_switch_to_interrupt))
			r_ubreak <= 1'b1;
		else if (((~alu_gie)||(dbgv))&&(wr_reg_ce)&&(wr_write_ucc))
			r_ubreak <= (ubreak)&&(wr_spreg_vl[`CPU_BREAK_BIT]);

	assign	trap = r_trap;
	assign	ubreak = r_ubreak;
`endif


`ifdef	OPT_ILLEGAL_INSTRUCTION
	initial	ill_err_i = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			ill_err_i <= 1'b0;
		// Only the debug interface can clear this bit
		else if ((dbgv)&&(wr_write_scc))
			ill_err_i <= (ill_err_i)&&(wr_spreg_vl[`CPU_ILL_BIT]);
		else if ((alu_illegal)&&(~alu_gie)&&(!clear_pipeline))
			ill_err_i <= 1'b1;

`ifdef	OPT_NO_USERMODE
	assign	ill_err_u = 1'b0;
`else
	reg	r_ill_err_u;

	initial	r_ill_err_u = 1'b0;
	always @(posedge i_clk)
		// The bit is automatically cleared on release from interrupt
		// or reset
		if ((i_rst)||(w_release_from_interrupt))
			r_ill_err_u <= 1'b0;
		// If the supervisor (or debugger) writes to this register,
		// clearing the bit, then clear it
		else if (((~alu_gie)||(dbgv))&&(wr_reg_ce)&&(wr_write_ucc))
			r_ill_err_u <=((ill_err_u)&&(wr_spreg_vl[`CPU_ILL_BIT]));
		else if ((alu_illegal)&&(alu_gie)&&(!clear_pipeline))
			r_ill_err_u <= 1'b1;

	assign	ill_err_u = r_ill_err_u;
`endif
`else
	assign ill_err_u = 1'b0;
	assign ill_err_i = 1'b0;
`endif
	// Supervisor/interrupt bus error flag -- this will crash the CPU if
	// ever set.
	initial	ibus_err_flag = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			ibus_err_flag <= 1'b0;
		else if ((dbgv)&&(wr_write_scc))
			ibus_err_flag <= (ibus_err_flag)&&(wr_spreg_vl[`CPU_BUSERR_BIT]);
		else if ((bus_err)&&(~alu_gie))
			ibus_err_flag <= 1'b1;
	// User bus error flag -- if ever set, it will cause an interrupt to
	// supervisor mode.
`ifdef	OPT_NO_USERMODE  
	assign	ubus_err_flag = 1'b0;
`else
	reg	r_ubus_err_flag;

	initial	r_ubus_err_flag = 1'b0;
	always @(posedge i_clk)
		if ((i_rst)||(w_release_from_interrupt))
			r_ubus_err_flag <= 1'b0;
		else if (((~alu_gie)||(dbgv))&&(wr_reg_ce)&&(wr_write_ucc))
			r_ubus_err_flag <= (ubus_err_flag)&&(wr_spreg_vl[`CPU_BUSERR_BIT]);
		else if ((bus_err)&&(alu_gie))
			r_ubus_err_flag <= 1'b1;

	assign	ubus_err_flag = r_ubus_err_flag;
`endif

	generate
	if (IMPLEMENT_DIVIDE != 0)
	begin
		reg	r_idiv_err_flag, r_udiv_err_flag;

		// Supervisor/interrupt divide (by zero) error flag -- this will
		// crash the CPU if ever set.  This bit is thus available for us
		// to be able to tell if/why the CPU crashed.
		initial	r_idiv_err_flag = 1'b0;
		always @(posedge i_clk)
			if (i_rst)
				r_idiv_err_flag <= 1'b0;
			else if ((dbgv)&&(wr_write_scc))
				r_idiv_err_flag <= (r_idiv_err_flag)&&(wr_spreg_vl[`CPU_DIVERR_BIT]);
			else if ((div_error)&&(~alu_gie))
				r_idiv_err_flag <= 1'b1;

		assign	idiv_err_flag = r_idiv_err_flag;
`ifdef	OPT_NO_USERMODE
		assign	udiv_err_flag = 1'b0;
`else
		// User divide (by zero) error flag -- if ever set, it will
		// cause a sudden switch interrupt to supervisor mode.  
		initial	r_udiv_err_flag = 1'b0;
		always @(posedge i_clk)
			if ((i_rst)||(w_release_from_interrupt))
				r_udiv_err_flag <= 1'b0;
			else if (((~alu_gie)||(dbgv))&&(wr_reg_ce)
					&&(wr_write_ucc))
				r_udiv_err_flag <= (r_udiv_err_flag)&&(wr_spreg_vl[`CPU_DIVERR_BIT]);
			else if ((div_error)&&(alu_gie))
				r_udiv_err_flag <= 1'b1;

		assign	udiv_err_flag = r_udiv_err_flag;
`endif
	end else begin
		assign	idiv_err_flag = 1'b0;
		assign	udiv_err_flag = 1'b0;
	end endgenerate

	generate
	if (IMPLEMENT_FPU !=0)
	begin
		// Supervisor/interrupt floating point error flag -- this will
		// crash the CPU if ever set.
		reg		r_ifpu_err_flag, r_ufpu_err_flag;
		initial	r_ifpu_err_flag = 1'b0;
		always @(posedge i_clk)
			if (i_rst)
				r_ifpu_err_flag <= 1'b0;
			else if ((dbgv)&&(wr_write_scc))
				r_ifpu_err_flag <= (r_ifpu_err_flag)&&(wr_spreg_vl[`CPU_FPUERR_BIT]);
			else if ((fpu_error)&&(fpu_valid)&&(~alu_gie))
				r_ifpu_err_flag <= 1'b1;
		// User floating point error flag -- if ever set, it will cause
		// a sudden switch interrupt to supervisor mode.  
		initial	r_ufpu_err_flag = 1'b0;
		always @(posedge i_clk)
			if ((i_rst)&&(w_release_from_interrupt))
				r_ufpu_err_flag <= 1'b0;
			else if (((~alu_gie)||(dbgv))&&(wr_reg_ce)
					&&(wr_write_ucc))
				r_ufpu_err_flag <= (r_ufpu_err_flag)&&(wr_spreg_vl[`CPU_FPUERR_BIT]);
			else if ((fpu_error)&&(alu_gie)&&(fpu_valid))
				r_ufpu_err_flag <= 1'b1;

		assign	ifpu_err_flag = r_ifpu_err_flag;
		assign	ufpu_err_flag = r_ufpu_err_flag;
	end else begin
		assign	ifpu_err_flag = 1'b0;
		assign	ufpu_err_flag = 1'b0;
	end endgenerate

`ifdef	OPT_VLIW
	reg		r_ihalt_phase;

	initial	r_ihalt_phase = 0;
	always @(posedge i_clk)
		if (i_rst)
			r_ihalt_phase <= 1'b0;
		else if ((~alu_gie)&&(alu_pc_valid)&&(~clear_pipeline))
			r_ihalt_phase <= alu_phase;

	assign	ihalt_phase = r_ihalt_phase;

`ifdef	OPT_NO_USERMODE
	assign	uhalt_phase = 1'b0;
`else
	reg		r_uhalt_phase;

	initial	r_uhalt_phase = 0;
	always @(posedge i_clk)
		if ((i_rst)||(w_release_from_interrupt))
			r_uhalt_phase <= 1'b0;
		else if ((alu_gie)&&(alu_pc_valid))
			r_uhalt_phase <= alu_phase;
		else if ((~alu_gie)&&(wr_reg_ce)&&(wr_write_ucc))
			r_uhalt_phase <= wr_spreg_vl[`CPU_PHASE_BIT];

	assign	uhalt_phase = r_uhalt_phase;
`endif
`else
	assign	ihalt_phase = 1'b0;
	assign	uhalt_phase = 1'b0;
`endif

	//
	// Write backs to the PC register, and general increments of it
	//	We support two: upc and ipc.  If the instruction is normal,
	// we increment upc, if interrupt level we increment ipc.  If
	// the instruction writes the PC, we write whichever PC is appropriate.
	//
	// Do we need to all our partial results from the pipeline?
	// What happens when the pipeline has gie and ~gie instructions within
	// it?  Do we clear both?  What if a gie instruction tries to clear
	// a non-gie instruction?
`ifdef	OPT_NO_USERMODE
	assign	upc = {(AW){1'b0}};
`else
	reg	[(AW-1):0]	r_upc;

	always @(posedge i_clk)
		if ((wr_reg_ce)&&(wr_reg_id[4])&&(wr_write_pc))
			r_upc <= wr_spreg_vl[(AW-1):0];
		else if ((alu_gie)&&
				(((alu_pc_valid)&&(~clear_pipeline)&&(!alu_illegal))
				||(mem_pc_valid)))
			r_upc <= alu_pc;
	assign	upc = r_upc;
`endif

	always @(posedge i_clk)
		if (i_rst)
			ipc <= RESET_ADDRESS;
		else if ((wr_reg_ce)&&(~wr_reg_id[4])&&(wr_write_pc))
			ipc <= wr_spreg_vl[(AW-1):0];
		else if ((~alu_gie)&&
				(((alu_pc_valid)&&(~clear_pipeline)&&(!alu_illegal))
				||(mem_pc_valid)))
			ipc <= alu_pc;

	always @(posedge i_clk)
		if (i_rst)
			pf_pc <= RESET_ADDRESS;
		else if ((w_switch_to_interrupt)||((~gie)&&(w_clear_icache)))
			pf_pc <= ipc;
		else if ((w_release_from_interrupt)||((gie)&&(w_clear_icache)))
			pf_pc <= upc;
		else if ((wr_reg_ce)&&(wr_reg_id[4] == gie)&&(wr_write_pc))
			pf_pc <= wr_spreg_vl[(AW-1):0];
`ifdef	OPT_PIPELINED
		else if ((dcd_early_branch)&&(~clear_pipeline))
			pf_pc <= dcd_branch_pc + 1;
		else if ((new_pc)||((~dcd_stalled)&&(pf_valid)))
			pf_pc <= pf_pc + {{(AW-1){1'b0}},1'b1};
`else
		else if ((alu_gie==gie)&&(
				((alu_pc_valid)&&(~clear_pipeline))
				||(mem_pc_valid)))
			pf_pc <= alu_pc;
`endif

`ifdef	OPT_PIPELINED
	reg	r_clear_icache;
	initial	r_clear_icache = 1'b1;
	always @(posedge i_clk)
		if ((i_rst)||(i_clear_pf_cache))
			r_clear_icache <= 1'b1;
		else if ((wr_reg_ce)&&(wr_write_scc))
			r_clear_icache <=  wr_spreg_vl[`CPU_CLRCACHE_BIT];
		else
			r_clear_icache <= 1'b0;
	assign	w_clear_icache = r_clear_icache;
`else
	assign	w_clear_icache = i_clear_pf_cache;
`endif

	initial	new_pc = 1'b1;
	always @(posedge i_clk)
		if ((i_rst)||(w_clear_icache))
			new_pc <= 1'b1;
		else if (w_switch_to_interrupt)
			new_pc <= 1'b1;
		else if (w_release_from_interrupt)
			new_pc <= 1'b1;
		else if ((wr_reg_ce)&&(wr_reg_id[4] == gie)&&(wr_write_pc))
			new_pc <= 1'b1;
		else
			new_pc <= 1'b0;

	//
	// The debug interface
	wire	[31:0]	w_debug_pc;
	generate
`ifdef	OPT_NO_USERMODE
	if (AW<32)
		assign	w_debug_pc = {{(32-AW){1'b0}},ipc};
	else
		assign	w_debug_pc = ipc;
`else
	if (AW<32)
		assign	w_debug_pc = {{(32-AW){1'b0}},(i_dbg_reg[4])?upc:ipc};
	else
		assign	w_debug_pc = (i_dbg_reg[4])?upc:ipc;
`endif
	endgenerate
	
	always @(posedge i_clk)
	begin
`ifdef	OPT_NO_USERMODE
		o_dbg_reg <= regset[i_dbg_reg[3:0]];
		if (i_dbg_reg[3:0] == `CPU_PC_REG)
			o_dbg_reg <= w_debug_pc;
		else if (i_dbg_reg[3:0] == `CPU_CC_REG)
		begin
			o_dbg_reg[14:0] <= w_iflags;
			o_dbg_reg[15] <= 1'b0;
			o_dbg_reg[31:23] <= w_cpu_info;
			o_dbg_reg[`CPU_GIE_BIT] <= gie;
		end
`else
		o_dbg_reg <= regset[i_dbg_reg];
		if (i_dbg_reg[3:0] == `CPU_PC_REG)
			o_dbg_reg <= w_debug_pc;
		else if (i_dbg_reg[3:0] == `CPU_CC_REG)
		begin
			o_dbg_reg[14:0] <= (i_dbg_reg[4])?w_uflags:w_iflags;
			o_dbg_reg[15] <= 1'b0;
			o_dbg_reg[31:23] <= w_cpu_info;
			o_dbg_reg[`CPU_GIE_BIT] <= gie;
		end
`endif
	end

	always @(posedge i_clk)
		o_dbg_cc <= { o_break, bus_err, gie, sleep };

`ifdef	OPT_PIPELINED
	always @(posedge i_clk)
		r_halted <= (i_halt)&&(
			// To be halted, any long lasting instruction must
			// be completed.
			(~pf_cyc)&&(~mem_busy)&&(~alu_busy)
				&&(~div_busy)&&(~fpu_busy)
			// Operations must either be valid, or illegal
			&&((opvalid)||(i_rst)||(dcd_illegal))
			// Decode stage must be either valid, in reset, or ill
			&&((dcdvalid)||(i_rst)||(pf_illegal)));
`else
	always @(posedge i_clk)
		r_halted <= (i_halt)&&((opvalid)||(i_rst));
`endif
	assign	o_dbg_stall = ~r_halted;

	//
	//
	// Produce accounting outputs: Account for any CPU stalls, so we can
	// later evaluate how well we are doing.
	//
	//
	assign	o_op_stall = (master_ce)&&(op_stall);
	assign	o_pf_stall = (master_ce)&&(~pf_valid);
	assign	o_i_count  = (alu_pc_valid)&&(~clear_pipeline);

`ifdef	DEBUG_SCOPE
	always @(posedge i_clk)
		o_debug <= {
		/*
			o_break, i_wb_err, pf_pc[1:0],
			flags,
			pf_valid, dcdvalid, opvalid, alu_valid, mem_valid,
			op_ce, alu_ce, mem_ce,
			//
			master_ce, opvalid_alu, opvalid_mem,
			//
			alu_stall, mem_busy, op_pipe, mem_pipe_stalled,
			mem_we,
			// ((opvalid_alu)&&(alu_stall))
			// ||((opvalid_mem)&&(~op_pipe)&&(mem_busy))
			// ||((opvalid_mem)&&( op_pipe)&&(mem_pipe_stalled)));
			// opA[23:20], opA[3:0],
			gie, sleep, wr_reg_ce, wr_gpreg_vl[4:0]
		*/
		/*
			i_rst, master_ce, (new_pc),
			((dcd_early_branch)&&(dcdvalid)),
			pf_valid, pf_illegal,
			op_ce, dcd_ce, dcdvalid, dcd_stalled,
			pf_cyc, pf_stb, pf_we, pf_ack, pf_stall, pf_err,
			pf_pc[7:0], pf_addr[7:0]
		*/

			i_wb_err, gie, alu_illegal,
			      (new_pc)||((dcd_early_branch)&&(~clear_pipeline)),
			mem_busy,
				(mem_busy)?{ (o_wb_gbl_stb|o_wb_lcl_stb), o_wb_we,
					o_wb_addr[8:0] }
					: { instruction[31:21] },
			pf_valid, (pf_valid) ? alu_pc[14:0]
				:{ pf_cyc, pf_stb, pf_pc[12:0] }

		/*
			i_wb_err, gie, new_pc, dcd_early_branch,	// 4
			pf_valid, pf_cyc, pf_stb, instruction_pc[0],	// 4
			instruction[30:27],				// 4
			dcd_gie, mem_busy, o_wb_gbl_cyc, o_wb_gbl_stb,	// 4
			dcdvalid,
			((dcd_early_branch)&&(~clear_pipeline))		// 15
					? dcd_branch_pc[14:0]:pf_pc[14:0]
		*/
			};
`endif
		
endmodule
