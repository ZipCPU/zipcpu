////////////////////////////////////////////////////////////////////////////////
//
// Filename:	idecode.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This RTL file specifies how instructions are to be decoded
//		into their underlying meanings.  This is specifically a version
//	designed to support a "Next Generation", or "Version 2" instruction
//	set as (currently) activated by the OPT_NEW_INSTRUCTION_SET option
//	in cpudefs.v.
//
//	I expect to (eventually) retire the old instruction set, at which point
//	this will become the default instruction set decoder.
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
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
`define	CPU_SP_REG	4'hd
`define	CPU_CC_REG	4'he
`define	CPU_PC_REG	4'hf
//
`define	CISBIT		31
`define	CISIMMSEL	23
`define	IMMSEL		18
//
//
//
module	idecode(i_clk, i_reset, i_ce, i_stalled,
		i_instruction, i_gie, i_pc, i_pf_valid,
			i_illegal,
		o_valid,
		o_phase, o_illegal,
		o_pc, o_gie,
		o_dcdR, o_dcdA, o_dcdB, o_I, o_zI,
		o_cond, o_wF,
		o_op, o_ALU, o_M, o_DV, o_FP, o_break, o_lock,
		o_wR, o_rA, o_rB,
		o_early_branch, o_early_branch_stb, o_branch_pc, o_ljmp,
		o_pipe,
		o_sim, o_sim_immv
		);
	parameter		ADDRESS_WIDTH=24;
	parameter	[0:0]	OPT_MPY = 1'b1;
	parameter	[0:0]	OPT_EARLY_BRANCHING = 1'b1;
	parameter	[0:0]	OPT_DIVIDE = 1'b1;
	parameter	[0:0]	OPT_FPU = 1'b0;
	parameter	[0:0]	OPT_CIS = 1'b1;
	parameter	[0:0]	OPT_LOCK = 1'b1;
	parameter	[0:0]	OPT_OPIPE = 1'b1;
	localparam		AW = ADDRESS_WIDTH;
	//
	input	wire		i_clk, i_reset, i_ce, i_stalled;
	input	wire [31:0]	i_instruction;
	input	wire		i_gie;
	input	wire [(AW+1):0]	i_pc;
	input	wire		i_pf_valid, i_illegal;
	output	wire		o_valid, o_phase;
	output	reg		o_illegal;
	output	reg	[(AW+1):0]	o_pc;
	output	reg		o_gie;
	output	reg	[6:0]	o_dcdR, o_dcdA, o_dcdB;
	output	wire	[31:0]	o_I;
	output	reg		o_zI;
	output	reg	[3:0]	o_cond;
	output	reg		o_wF;
	output	reg	[3:0]	o_op;
	output	reg		o_ALU, o_M, o_DV, o_FP, o_break;
	output	reg		o_lock;
	output	reg		o_wR, o_rA, o_rB;
	output	wire		o_early_branch, o_early_branch_stb;
	output	wire	[(AW+1):0]	o_branch_pc;
	output	wire		o_ljmp;
	output	wire		o_pipe;
	output	reg		o_sim		/* verilator public_flat */;
	output	reg	[22:0]	o_sim_immv	/* verilator public_flat */;


	wire	[4:0]	w_op;
	wire		w_ldi, w_mov, w_cmptst, w_ldilo, w_ALU, w_brev,
			w_noop, w_lock, w_sim, w_break, w_special, w_add,
			w_mpy;
	wire	[4:0]	w_dcdR, w_dcdB, w_dcdA;
	wire		w_dcdR_pc, w_dcdR_cc;
	wire		w_dcdA_pc, w_dcdA_cc;
	wire		w_dcdB_pc, w_dcdB_cc;
	wire	[3:0]	w_cond;
	wire		w_wF, w_mem, w_sto, w_div, w_fpu;
	wire		w_wR, w_rA, w_rB, w_wR_n;
	wire		w_ljmp, w_ljmp_dly, w_cis_ljmp;
	wire	[31:0]	iword;
	wire		pf_valid;

	assign	pf_valid = (i_pf_valid)&&(!o_early_branch_stb);


	reg	[15:0]	r_nxt_half;

	generate if (OPT_CIS)
	begin : SET_IWORD

		assign	iword = (o_phase)
				// set second half as a NOOP ... but really
				// shouldn't matter
			? { r_nxt_half[15:0], i_instruction[15:0] }
			: i_instruction;
	end else begin : CLR_IWORD
		assign	iword = { 1'b0, i_instruction[30:0] };

		// verilator lint_off UNUSED
		wire	[15:0]	unused_nxt_half;
		assign		unused_nxt_half = r_nxt_half;
		// verilator lint_on  UNUSED
	end endgenerate

	generate
	if (OPT_EARLY_BRANCHING)
	begin
		if (OPT_CIS)
		begin : CIS_EARLY_BRANCHING

			assign	w_cis_ljmp = (iword[31:16] == 16'hfcf8);

		end else begin : NOCIS_EARLY_BRANCH

			assign	w_cis_ljmp = 1'b0;

		end

		assign	w_ljmp = (iword == 32'h7c87c000);

	end else begin : NO_EARLY_BRANCHING

		assign	w_cis_ljmp = 1'b0;
		assign	w_ljmp = 1'b0;
	end endgenerate

	reg	[4:0]	w_cis_op;

	generate if (OPT_CIS)
	begin : GEN_CIS_OP

		always @(*)
			if (!iword[`CISBIT])
				w_cis_op = iword[26:22];
			else case(iword[26:24])
			3'h0: w_cis_op = 5'h00;
			3'h1: w_cis_op = 5'h01;
			3'h2: w_cis_op = 5'h02;
			3'h3: w_cis_op = 5'h10;
			3'h4: w_cis_op = 5'h12;
			3'h5: w_cis_op = 5'h13;
			3'h6: w_cis_op = 5'h18;
			3'h7: w_cis_op = 5'h0d;
			endcase

	end else begin : GEN_NOCIS_OP

		always @(*)
			w_cis_op = w_op;

	end endgenerate

	// Decode instructions
	assign	w_op= iword[26:22];
	assign	w_mov    = (w_cis_op      == 5'h0d);
	assign	w_ldi    = (w_cis_op[4:1] == 4'hc);
	assign	w_brev   = (w_cis_op      == 5'h08);
	assign	w_mpy    = (w_cis_op[4:1] == 4'h5)||(w_cis_op[4:0]==5'h0c);
	assign	w_cmptst = (w_cis_op[4:1] == 4'h8);
	assign	w_ldilo  = (w_cis_op[4:0] == 5'h09);
	assign	w_ALU    = (!w_cis_op[4]) // anything with [4]==0, but ...
				&&(w_cis_op[3:1] != 3'h7); // not the divide
	assign	w_add    = (w_cis_op[4:0] == 5'h02);
	assign	w_mem    = (w_cis_op[4:3] == 2'b10)&&(w_cis_op[2:1] !=2'b00);
	assign	w_sto    = (w_mem)&&( w_cis_op[0]);
	assign	w_div    = (!iword[`CISBIT])&&(w_op[4:1] == 4'h7);
	assign	w_fpu    = (!iword[`CISBIT])&&(w_op[4:3] == 2'b11)
				&&(w_dcdR[3:1] != 3'h7)&&(w_op[2:1] != 2'b00)
				&&(OPT_FPU);
	// If the result register is either CC or PC, and this would otherwise
	// be a floating point instruction with floating point opcode of 0,
	// then this is a NOOP.
	assign	w_special= (!iword[`CISBIT])&&((!OPT_FPU)||(w_dcdR[3:1]==3'h7))
			&&(w_op[4:2] == 3'b111);
	assign	w_break = (w_special)&&(w_op[4:0]==5'h1c);
	assign	w_lock  = (w_special)&&(w_op[4:0]==5'h1d);
	assign	w_sim   = (w_special)&&(w_op[4:0]==5'h1e);
	assign	w_noop  = (w_special)&&(w_op[4:0]==5'h1f);


	// w_dcdR (4 LUTs)
	//
	// What register will we be placing results into (if at all)?
	//
	// Two parts to the result register: the register set, given for
	// moves in iword[18] but only for the supervisor, and the other
	// four bits encoded in the instruction.
	//
	assign	w_dcdR = { ((!iword[`CISBIT])&&(w_mov)&&(!i_gie))?iword[`IMMSEL]:i_gie,
				iword[30:27] };

	// dcdB - What register is used in the opB?
	//
	assign w_dcdB[4] = ((!iword[`CISBIT])&&(w_mov)&&(!i_gie))?iword[13]:i_gie;
	assign w_dcdB[3:0]= (iword[`CISBIT])
				? (((!iword[`CISIMMSEL])&&(iword[26:25]==2'b10))
					? `CPU_SP_REG : iword[22:19])
				: iword[17:14];

	// 0 LUTs
	assign	w_dcdA = w_dcdR;	// on ZipCPU, A is always result reg
	// 2 LUTs, 1 delay each
	assign	w_dcdR_pc = (w_dcdR == {i_gie, `CPU_PC_REG});
	assign	w_dcdR_cc = (w_dcdR == {i_gie, `CPU_CC_REG});
	// 0 LUTs
	assign	w_dcdA_pc = w_dcdR_pc;
	assign	w_dcdA_cc = w_dcdR_cc;
	// 2 LUTs, 1 delays each
	assign	w_dcdB_pc = (w_rB)&&(w_dcdB[3:0] == `CPU_PC_REG);
	assign	w_dcdB_cc = (w_rB)&&(w_dcdB[3:0] == `CPU_CC_REG);

	//
	// Under what condition will we execute this instruction?  Only the
	// load immediate instruction and the CIS instructions are completely
	// unconditional.  Well ... not quite.  The BREAK, LOCK, and SIM/NOOP
	// instructions are also unconditional.
	//
	assign	w_cond = ((w_ldi)||(w_special)||(iword[`CISBIT])) ? 4'h8 :
			{ (iword[21:19]==3'h0), iword[21:19] };

	// rA - do we need to read register A?
	assign	w_rA = // Floating point reads reg A
			(w_fpu)
			// Divide's read A
			||(w_div)
			// ALU ops read A,
			//	except for MOV's and BREV's which don't
			||((w_ALU)&&(!w_brev)&&(!w_mov))
			// STO's read A
			||(w_sto)
			// Test/compares
			||(w_cmptst);
	// rB -- do we read a register for operand B?  Specifically, do we
	// add the registers value to the immediate to create opB?
	assign	w_rB     = (w_mov)
				||((!iword[`CISBIT])&&(iword[`IMMSEL])&&(!w_ldi)&&(!w_special))
				||(( iword[`CISBIT])&&(iword[`CISIMMSEL])&&(!w_ldi))
				// If using compressed instruction sets,
				// we *always* read on memory operands.
				||(( iword[`CISBIT])&&(w_mem));

	// wR -- will we be writing our result back?
	// wR_n = !wR
	// All but STO, NOOP/BREAK/LOCK, and CMP/TST write back to w_dcdR
	assign	w_wR_n   = (w_sto)
				||(w_special)
				||(w_cmptst);
	assign	w_wR     = !w_wR_n;
	//
	// wF -- do we write flags when we are done?
	//
	assign	w_wF     = (w_cmptst)
			||((w_cond[3])&&((w_fpu)||(w_div)
				||((w_ALU)&&(!w_mov)&&(!w_ldilo)&&(!w_brev)
					&&(w_dcdR[3:1] != 3'h7))));

	// Bottom 13 bits: no LUT's
	// w_dcd[12: 0] -- no LUTs
	// w_dcd[   13] -- 2 LUTs
	// w_dcd[17:14] -- (5+i0+i1) = 3 LUTs, 1 delay
	// w_dcd[22:18] : 5 LUTs, 1 delay (assuming high bit is o/w determined)
	reg	[22:0]	r_I;
	wire	[22:0]	w_I, w_fullI;
	wire		w_Iz;

	assign	w_fullI = (w_ldi) ? { iword[22:0] } // LDI
			// MOVE immediates have one less bit
			:((w_mov) ?{ {(23-13){iword[12]}}, iword[12:0] }
			// Normal Op-B immediate ... 18 or 14 bits
			:((!iword[`IMMSEL]) ? { {(23-18){iword[17]}}, iword[17:0] }
			: { {(23-14){iword[13]}}, iword[13:0] }
			));

	generate if (OPT_CIS)
	begin : GEN_CIS_IMMEDIATE
		wire	[7:0]	w_halfbits;
		assign	w_halfbits = iword[`CISIMMSEL:16];

		wire	[7:0]	w_halfI;
		assign	w_halfI = (iword[26:24]==3'h6) ? w_halfbits[7:0] // 8'b for LDI
				:(w_halfbits[7])?
					{ {(6){w_halfbits[2]}}, w_halfbits[1:0]}
					:{ w_halfbits[6], w_halfbits[6:0] };
		assign	w_I  = (iword[`CISBIT])
				? {{(23-8){w_halfI[7]}}, w_halfI }
				: w_fullI;

	end else begin : GEN_NOCIS_IMMEDIATE

		assign	w_I  = w_fullI;

	end endgenerate

	assign	w_Iz = (w_I == 0);


	//
	// The o_phase parameter is special.  It needs to let the software
	// following know that it cannot break/interrupt on an o_phase asserted
	// instruction, lest the break take place between the first and second
	// half of a CIS instruction.  To do this, o_phase must be asserted
	// when the first instruction half is valid, but not asserted on either
	// a 32-bit instruction or the second half of a 2x16-bit instruction.
	generate if (OPT_CIS)
	begin : GEN_CIS_PHASE
		reg	r_phase;

		// Phase is '1' on the first instruction of a two-part set
		// But, due to the delay in processing, it's '1' when our
		// output is valid for that first part, but that'll be the
		// same time we are processing the second part ... so it may
		// look to us like a '1' on the second half of processing.

		// When no instruction is in the pipe, phase is zero
		initial	r_phase = 1'b0;
		always @(posedge i_clk)
		if ((i_reset)||(w_ljmp_dly))
			r_phase <= 1'b0;
		else if ((i_ce)&&(pf_valid))
		begin
			if (o_phase)
				// CIS instructions only have two parts.  On
				// the second part (o_phase is true), return
				// back to the first
				r_phase <= 0;
			else if ((i_instruction[`CISBIT])&&(w_dcdR_pc)&&(w_wR))
				// CIS instructions are unconditional.
				// Therefore, any write to the PC will affect
				// the PC, and the second half of the
				// instruction will be irrelevant and may be
				// ignored.
				r_phase <= 0;
			else
				r_phase <= (i_instruction[`CISBIT]);
		end else if (i_ce)
			r_phase <= 1'b0;

		assign	o_phase = r_phase;
	end else begin
		assign	o_phase = 1'b0;
	end endgenerate


	initial	o_illegal = 1'b0;
	always @(posedge i_clk)
		if (i_reset)
			o_illegal <= 1'b0;
		else if (i_ce)
		begin
			o_illegal <= (i_illegal);
			if ((!OPT_CIS)&&(i_instruction[`CISBIT]))
				o_illegal <= 1'b1;
			if ((!OPT_MPY)&&(w_mpy))
				o_illegal <= 1'b1;

			if ((!OPT_DIVIDE)&&(w_div))
				o_illegal <= 1'b1;
			else if ((OPT_DIVIDE)&&(w_div)&&(w_dcdR[3:1]==3'h7))
				o_illegal <= 1'b1;


			if ((!OPT_FPU)&&(w_fpu))
				o_illegal <= 1'b1;

`ifndef	VERILATOR
			// Simulation instructions on real hardware should
			// always cause an illegal instruction error
			if (w_sim)
				o_illegal <= 1'b1;
`endif

			// There are two (missing) special instructions
			// These should cause an illegal instruction error
			if ((w_dcdR[3:1]==3'h7)&&(w_cis_op[4:1]==4'b1101))
				o_illegal <= 1'b1;

			// If the lock function isn't implemented, this should
			// also cause an illegal instruction error
			if ((!OPT_LOCK)&&(w_lock))
				o_illegal <= 1'b1;
		end

	initial	o_pc = 0;
	always @(posedge i_clk)
		if (i_ce)
		begin
			o_pc[0] <= 1'b0;

			if (OPT_CIS)
			begin
				if (!o_phase)
					o_gie<= i_gie;

				if (iword[`CISBIT])
				begin
					if (o_phase)
						o_pc[AW+1:1] <= o_pc[AW+1:1] + 1'b1;
					else if (pf_valid)
						o_pc <= { i_pc[AW+1:2], 1'b1, 1'b0 };
				end else begin
					// The normal, non-CIS case
					o_pc <= { i_pc[AW+1:2] + 1'b1, 2'b00 };
				end
			end else begin
				// The normal, non-CIS case
				o_gie<= i_gie;
				o_pc <= { i_pc[AW+1:2] + 1'b1, 2'b00 };
			end

			// Under what condition will we execute this
			// instruction?  Only the load immediate instruction
			// is completely unconditional.
			o_cond <= w_cond;
			// Don't change the flags on conditional instructions,
			// UNLESS: the conditional instruction was a CMP
			// or TST instruction.
			o_wF <= w_wF;

			// Record what operation/op-code (4-bits) we are doing
			//	Note that LDI magically becomes a MOV
			// 	instruction here.  That way it's a pass through
			//	the ALU.  Likewise, the two compare instructions
			//	CMP and TST becomes SUB and AND here as well.
			// We keep only the bottom four bits, since we've
			// already done the rest of the decode necessary to
			// settle between the other instructions.  For example,
			// o_FP plus these four bits uniquely defines the FP
			// instruction, o_DV plus the bottom of these defines
			// the divide, etc.
			o_op <= ((w_ldi)||(w_noop))? 4'hd : w_cis_op[3:0];

			// Default values
			o_dcdR <= { w_dcdR_cc, w_dcdR_pc, w_dcdR};
			o_dcdA <= { w_dcdA_cc, w_dcdA_pc, w_dcdA};
			o_dcdB <= { w_dcdB_cc, w_dcdB_pc, w_dcdB};
			o_wR  <= w_wR;
			o_rA  <= w_rA;
			o_rB  <= w_rB;
			r_I    <= w_I;
			o_zI   <= w_Iz;

			// Turn a NOOP into an ALU operation--subtract in
			// particular, although it doesn't really matter as long
			// as it doesn't take longer than one clock.  Note
			// also that this depends upon not setting any registers
			// or flags, which should already be true.
			o_ALU  <=  (w_ALU)||(w_ldi)||(w_cmptst)||(w_noop);
			o_M    <=  w_mem;
			o_DV   <=  w_div;
			o_FP   <=  w_fpu;

			o_break <= w_break;
			o_lock  <= (OPT_LOCK)&&(w_lock);

			if (OPT_CIS)
				r_nxt_half <= { iword[`CISBIT], iword[14:0] };
			else
				r_nxt_half <= 0;

`ifdef	VERILATOR
			// Support the SIM instruction(s)
			o_sim <= (w_sim)||(w_noop);
`else
			o_sim <= 1'b0;
`endif
			o_sim_immv <= iword[22:0];
		end

	generate if (OPT_EARLY_BRANCHING)
	begin
		reg			r_early_branch,
					r_early_branch_stb,
					r_ljmp;
		reg	[(AW+1):0]	r_branch_pc;

		initial r_ljmp = 1'b0;
		always @(posedge i_clk)
			if (i_reset)
				r_ljmp <= 1'b0;
			else if (i_ce)
			begin
				if (o_early_branch_stb)
					r_ljmp <= 1'b0;
				else if ((OPT_CIS)&&(iword[`CISBIT]))
					r_ljmp <= w_cis_ljmp;
				else if (pf_valid)
					r_ljmp <= (w_ljmp);
			end
		assign	o_ljmp = r_ljmp;

		initial	r_early_branch     = 1'b0;
		initial	r_early_branch_stb = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			r_early_branch     <= 1'b0;
			r_early_branch_stb <= 1'b0;
		end else if ((i_ce)&&(pf_valid))
		begin
			if (r_ljmp)
			begin
				// LW (PC),PC
				r_early_branch     <= 1'b1;
				r_early_branch_stb <= 1'b1;
			end else if ((!iword[`CISBIT])&&(iword[30:27]==`CPU_PC_REG)
					&&(w_cond[3]))
			begin
				if ((w_add)&&(!iword[`IMMSEL]))
				begin
					// Add x,PC
					r_early_branch     <= 1'b1;
					r_early_branch_stb <= 1'b1;
				end else begin
					r_early_branch     <= 1'b0;
					r_early_branch_stb <= 1'b0;
				end
			// LDI #x,PC is no longer supported
			end else begin
				r_early_branch <= 1'b0;
				r_early_branch_stb <= 1'b0;
			end
		end else if (i_ce)
		begin
			r_early_branch     <= 1'b0;
			r_early_branch_stb <= 1'b0;
		end else
			r_early_branch_stb <= 1'b0;

		always @(posedge i_clk)
			if (i_ce)
			begin
				if (r_ljmp)
					r_branch_pc <= { iword[(AW+1):2],
							2'b00 };
				else begin
				// Add x,PC
				r_branch_pc[AW+1:2] <= i_pc[AW+1:2]
					+ {{(AW-15){iword[17]}},iword[16:2]}
					+ {{(AW-1){1'b0}},1'b1};
				r_branch_pc[1:0] <= 2'b00;
				end
			end

		assign	w_ljmp_dly         = r_ljmp;
		assign	o_early_branch     = r_early_branch;
		assign	o_early_branch_stb = r_early_branch_stb;
		assign	o_branch_pc        = r_branch_pc;
	end else begin
		assign	w_ljmp_dly         = 1'b0;
		assign	o_early_branch     = 1'b0;
		assign	o_early_branch_stb = 1'b0;
		assign	o_branch_pc = {(AW+2){1'b0}};
		assign	o_ljmp = 1'b0;
	end endgenerate


	// To be a pipeable operation there must be ...
	//	1. Two valid adjacent instructions
	//	2. Both must be memory operations, of the same time (both lods
	//		or both stos)
	//	3. Both must use the same register base address
	//	4. Both must be to the same address, or the address incremented
	//		by one
	// Note that we're not using iword here ... there's a lot of logic
	// taking place, and it's only valid if the new word is not compressed.
	//
	reg	r_valid;
	generate if (OPT_OPIPE)
	begin
		reg	r_pipe;

		initial	r_pipe = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_pipe <= 1'b0;
		else if (i_ce)
			r_pipe <= (r_valid)&&((pf_valid)||(o_phase))
				// Both must be memory operations
				&&(w_mem)&&(o_M)
				// Both must be writes, or both stores
				&&(o_op[0] == w_cis_op[0])
				// Both must be register ops
				&&(w_rB == o_rB)
				// Both must use the same register for B
				&&(w_dcdB[3:0] == o_dcdB[3:0])
				// But ... the result can never be B
				&&((o_op[0])
					||(w_dcdB[3:0] != o_dcdA[3:0]))
				// Needs to be to the mode, supervisor or user
				&&(i_gie == o_gie)
				// Same condition, or no condition before
				&&((w_cond[2:0]==o_cond[2:0])
					||(o_cond[2:0] == 3'h0))
				// Same or incrementing immediate
				&&(w_I[13]==r_I[13])
				&&((w_I[13:2]==r_I[13:2])
					||({1'b0, w_I[13:2]}==(r_I[13:2]+12'h1)));
		assign o_pipe = r_pipe;
	end else begin
		assign o_pipe = 1'b0;
	end endgenerate

	initial	r_valid = 1'b0;
	always @(posedge i_clk)
		if (i_reset)
			r_valid <= 1'b0;
		else if (i_ce)
			r_valid <= ((pf_valid)||(o_phase))&&(!o_ljmp);
		else if (!i_stalled)
			r_valid <= 1'b0;

	assign	o_valid = r_valid;


	assign	o_I = { {(32-22){r_I[22]}}, r_I[21:0] };

	// Make Verilator happy across all our various options
	// verilator lint_off  UNUSED
	wire	[5:0] possibly_unused;
	assign	possibly_unused = { w_lock, w_ljmp, w_ljmp_dly, w_cis_ljmp, i_pc[1:0] };
	// verilator lint_on  UNUSED
`ifdef	FORMAL
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////
	//
	//
	// Assumptions about our inputs
	//
	//
	///////////////////////////
	always @(*)
		assume(i_ce == ((!o_valid)||(!i_stalled)));

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_valid);
		assert(!o_illegal);
		assert(!o_phase);
		assert(!o_ljmp);
		assert(!o_pipe);

		assume(!i_pf_valid);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
		assume(i_gie == $past(i_gie));

`ifdef	IDECODE
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(i_ce))
		&&($past(f_past_valid))&&(!$past(i_reset,2))&&(!$past(i_ce,2)))
		restrict(i_ce);
`endif

	reg	f_new_insn, f_last_insn;

	initial	f_new_insn = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		f_new_insn <= 1'b0;
	else
		f_new_insn <= ((pf_valid)&&(!i_stalled));

	initial	f_last_insn = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		f_last_insn <= 1'b0;
	else
		f_last_insn <= (o_valid)&&(i_stalled);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(f_last_insn)))
	begin
		if (($past(pf_valid))&&(pf_valid))
		begin
			assume(i_instruction == $past(i_instruction));
			assume(i_gie == $past(i_gie));
			assume(i_pc  == $past(i_pc));
			assume(i_illegal == $past(i_illegal));
		end
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_early_branch_stb))
		assume(!pf_valid);

	wire	[4+21+32+1+4+1+4+11+AW+3+23-1:0]	f_result;
	assign	f_result = { o_valid, o_phase, o_illegal,
			o_gie, o_dcdR, o_dcdA, o_dcdB, o_I, o_zI, o_cond,
			o_wF, o_op, o_ALU, o_M, o_DV, o_FP, o_break, o_lock,
			o_wR, o_rA, o_rB, o_early_branch, o_branch_pc, o_ljmp,
			o_pipe, o_sim, o_sim_immv, o_pc };

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(f_last_insn))
		assert(f_result == $past(f_result));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(pf_valid))
			&&(!$past(o_ljmp)))
		assert(o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(f_new_insn)
			&&($past(pf_valid))&&($past(i_illegal)))
		assert(o_illegal);


	// Let's walk through some basic instructions
	// First 8-instructions, SUB - ASR
	always @(*)
	if ((!iword[`CISBIT])&&(iword[26:25]==2'b00))
	begin
		assert(!w_cmptst);
		assert(!w_div);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		assert((w_rA)&&(w_wR)&&(w_ALU));
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert((w_wF == w_cond[3])||(w_dcdA[3:1]==3'b111));
	end else if ((iword[`CISBIT])&&(iword[26:24]<3'b011))
	begin
		assert(!w_cmptst);
		assert(!w_div);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		assert((w_rA)&&(w_wR)&&(w_ALU));
		assert(w_rB == iword[`CISIMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[22:19]);

		if (iword[26:24] == 3'b000)
			assert(w_cis_op == 5'h0);
		else if (iword[26:24] == 5'h01)
			assert(w_cis_op == 5'h01);
		else // if (iword[26:24] == 3'b010)
			assert(w_cis_op == 5'h02);

		assert(w_cond == 4'h8);
		
		if (iword[`CISIMMSEL])
			assert(w_I == { {(23-3){iword[18]}}, iword[18:16] });
		else
			assert(w_I == { {(23-7){iword[22]}}, iword[22:16] });
	end else
		assert(!w_add);

	// BREV and LDILO
	always @(*)
	if ((!iword[`CISBIT])&&((w_cis_op == 5'h8)
			||(w_cis_op == 5'h09)))
	begin
		assert(!w_mpy);
		assert(!w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		if (w_cis_op == 5'h8)
		begin
			assert(w_brev);
			assert(!w_ldilo);
			assert((!w_rA)&&(w_wR)&&(w_ALU));
		end else begin// if (w_cis_op == 5'h9)
			assert(w_ldilo);
			assert(!w_brev);
			assert((w_rA)&&(w_wR)&&(w_ALU));
		end
		assert(!w_special);
		assert(!w_fpu);
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert(!w_wF);
	end else begin
		assert(!w_brev);
		assert(!w_ldilo);
	end

	//
	// Multiply instructions
	always @(*)
	if ((!iword[`CISBIT])&&((w_cis_op == 5'ha)
			||(w_cis_op == 5'h0b)
			||(w_cis_op == 5'h0c)))
	begin
		assert(w_mpy);
		assert(!w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert((w_rA)&&(w_wR)&&(w_ALU));
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert((w_wF == w_cond[3])||(w_dcdA[3:1]==3'b111));
	end else
		assert(!w_mpy);

	//
	// Move instruction
	always @(*)
	if ((!iword[`CISBIT])&&((w_cis_op == 5'hd)))
	begin
		assert(w_mov);
		assert(!w_div);
		assert(!w_mpy);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert((!w_rA)&&(w_wR)&&(w_ALU));
		assert(w_rB);
		assert(w_dcdA[4] == ((i_gie)||(iword[`IMMSEL])));
		assert(w_dcdB[4] == ((i_gie)||(iword[13])));
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert(!w_wF);
	end else if ((iword[`CISBIT])&&(iword[26:24]==3'b111))
	begin
		assert(w_mov);
		assert(!w_div);
		assert(!w_mpy);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert((!w_rA)&&(w_wR)&&(w_ALU));
		assert(w_rB);
		assert(w_dcdA[4] == (i_gie));
		assert(w_dcdB[4] == (i_gie));
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[22:19]);

		assert(w_cis_op == 5'h0d);

		assert(w_cond == 4'h8);
		assert(!w_wF);
	end else
		assert(!w_mov);

	//
	// Divide instruction
	always @(*)
	if ((!iword[`CISBIT])&&(iword[26:23]==4'b0111))
	begin
		assert(w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		assert((w_rA)&&(w_wR));
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert((w_wF == w_cond[3])||(w_dcdA[3:1]==3'b111));
	end else
		assert(!w_div);

	//
	// Comparison instructions
	always @(*)
	if ((!iword[`CISBIT])&&(iword[26:23]==4'b1000))
	begin
		assert(w_cmptst);
		assert(!w_div);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		assert((w_rA)&&(!w_wR)&&(!w_ALU));
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert(w_wF);
	end else if ((iword[`CISBIT])&&(iword[26:24]==3'b011))
	begin
		assert(w_cmptst);
		assert(!w_div);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		assert((w_rA)&&(!w_wR)&&(!w_ALU));
		assert(w_rB == iword[`CISIMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[22:19]);

		assert(w_cis_op == 5'h10);

		assert(w_cond == 4'h8);
		if (iword[`CISIMMSEL])
			assert(w_I == { {(23-3){iword[18]}}, iword[18:16] });
		else
			assert(w_I == { {(23-7){iword[22]}}, iword[22:16] });
		assert(w_wF);
	end else
		assert(!w_cmptst);

	always @(posedge i_clk)
	if ((f_new_insn)&&($past(w_cmptst)))
		assert(o_ALU);

	//
	// Memory instructions
	always @(*)
	if ((!iword[`CISBIT])&&(
		(iword[26:23]==4'b1001)		// Word
		||(iword[26:23]==4'b1010)	// Half-word, or short
		||(iword[26:23]==4'b1011)))	// Byte ops
	begin
		assert(w_mem);
		assert(w_sto == iword[22]);
		assert(!w_cmptst);
		assert(!w_div);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		if (w_sto)
			assert((w_rA)&&(!w_wR));
		else
			assert((!w_rA)&&(w_wR));
		assert(!w_ALU);
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert(!w_wF);
	end else if ((iword[`CISBIT])&&(iword[26:25]==2'b10))
	begin
		assert(w_mem);
		assert(w_sto == iword[24]);
		assert(!w_cmptst);
		assert(!w_div);
		assert(!w_ldi);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert(!w_special);
		assert(!w_fpu);
		assert(!w_mpy);
		if (w_sto)
			assert((w_rA)&&(!w_wR));
		else
			assert((!w_rA)&&(w_wR));
		assert(!w_ALU);
		assert(w_rB);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		if (iword[`CISIMMSEL])
			assert(w_dcdB[3:0] == iword[22:19]);
		else
			assert(w_dcdB[3:0] == `CPU_SP_REG);

		if (w_sto)
			assert(w_cis_op == 5'h13);
		else
			assert(w_cis_op == 5'h12);

		assert(w_cond == 4'h8);
		assert(!w_wF);
	end else begin
		assert(!w_sto);
		assert(!w_mem);
	end

	always @(*)
	if (w_sto)
		assert(w_mem);

	//
	// LDI -- Load immediate
	always @(*)
	if ((!iword[`CISBIT])&&(w_op[4:1] == 4'hc))
	begin
		assert(w_ldi);
		assert(!w_mpy);
		assert(!w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert((!w_rA)&&(w_wR)&&(!w_ALU));
		assert(!w_special);
		assert(!w_fpu);
		assert(w_rB == 1'b0);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond == 4'h8);
		assert(!w_wF);

		assert(w_Iz == (iword[22:0] == 0));
		assert(w_I[22:0] == iword[22:0]);
	end else if ((iword[`CISBIT])&&(iword[26:24] == 3'b110))
	begin
		assert(w_ldi);
		assert(!w_mpy);
		assert(!w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert((!w_rA)&&(w_wR)&&(!w_ALU));
		assert(!w_special);
		assert(!w_fpu);
		assert(w_rB == 1'b0);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);

		assert(w_cis_op[4:1] == 4'hc);

		assert(w_cond == 4'h8);
		assert(!w_wF);

		assert(w_Iz == (iword[23:16] == 0));
		assert(w_I[22:0] == { {(23-8){iword[23]}}, iword[23:16] });
	end else
		assert(!w_ldi);

	always @(posedge i_clk)
	if ((f_new_insn)&&($past(w_ldi)))
		assert(o_ALU);


	always @(*)
	if ((w_break)||(w_lock)||(w_sim)||(w_noop))
		assert(w_special);


	//
	// FPU -- Floating point instructions
	always @(*)
	if ((!iword[`CISBIT])&&(OPT_FPU)&&(
			(w_cis_op[4:1] == 4'hd)
			||(w_cis_op[4:1] == 4'he)
			||(w_cis_op[4:1] == 4'hf))
			&&(iword[30:28] != 3'h7))
	begin
		assert(w_fpu);
		assert(!w_ldi);
		assert(!w_mpy);
		assert(!w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);
		assert((w_wR)&&(!w_ALU));
		if ((w_cis_op == 5'he)||(w_cis_op == 5'hf))
			assert(!w_rA);
		else
			assert(w_rA);
		assert(!w_special);
		assert(w_rB == iword[`IMMSEL]);
		assert(w_dcdA[4] == i_gie);
		assert(w_dcdB[4] == i_gie);
		assert(w_dcdA[3:0] == iword[30:27]);
		assert(w_dcdB[3:0] == iword[17:14]);

		assert(w_cis_op == w_op);

		assert(w_cond[3] == (iword[21:19] == 3'b000));
		assert(w_cond[2:0] == iword[21:19]);
		assert((w_wF == w_cond[3])||(w_dcdA[3:1]==3'b111));
	end else
		assert(!w_fpu);

	//
	// Special instructions
	always @(*)
	if ((!iword[`CISBIT])&&(
			(w_cis_op == 5'h1c)
			||(w_cis_op == 5'h1d)
			||(w_cis_op == 5'h1e)
			||(w_cis_op == 5'h1f))
			&&((iword[30:28] == 3'h7)||(!OPT_FPU)))
	begin
		assert(w_special);
		if (w_cis_op == 5'h1c)
		begin
			assert(w_break);
			assert(!w_lock);
			assert(!w_sim);
			assert(!w_noop);
		end else if (w_cis_op == 5'h1d)
		begin
			assert(!w_break);
			assert( w_lock);
			assert(!w_sim);
			assert(!w_noop);
		end else if (w_cis_op == 5'h1e)
		begin
			assert(!w_break);
			assert(!w_lock);
			assert( w_sim);
			assert(!w_noop);
		end else begin
			assert(!w_break);
			assert(!w_lock);
			assert(!w_sim);
			assert( w_noop);
		end
		assert(!w_fpu);
		assert(!w_ldi);
		assert(!w_mpy);
		assert(!w_div);
		assert(!w_cmptst);
		assert(!w_mem);
		assert(!w_sto);
		assert(!w_mov);
		assert(!w_brev);
		assert(!w_ldilo);

		assert((!w_rA)&&(!w_rB)&&(!w_wR)&&(!w_ALU));

		assert(w_cis_op == w_op);

		assert(w_cond == 4'h8);
		assert(!w_wF);
	end else begin
		assert(!w_special);
		assert(!w_break);
		assert(!w_lock);
		assert(!w_sim);
		assert(!w_noop);
	end

	generate if (OPT_EARLY_BRANCHING)
	begin
		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_ce))&&(!$past(i_reset)))
		begin
			if ($past(pf_valid))
			begin
				if ($past(o_ljmp))
				begin
					// 2nd half of LW (PC),PC
					assert(o_early_branch);
					assert(o_early_branch_stb);
				end else if ((!$past(iword[`CISBIT]))&&($past(w_add))
					&&(!$past(w_rB))
					&&($past(w_cond[3]))
					&&(o_dcdR[4:0]=={ i_gie, 4'hf }))
				begin
					// ADD #x,PC
					assert(o_early_branch);
					assert(o_early_branch_stb);
				end else if ((!$past(iword[`CISBIT]))
					&&($past(w_cis_op == 5'h12))
					&&($past(w_rB))
					&&($past(w_cond[3]))
					&&(o_zI)
					&&(o_dcdB[4:0]=={ i_gie, 4'hf })
					&&(o_dcdR[4:0]=={ i_gie, 4'hf }))
				begin
					// LW (PC),PC
					assert(!o_early_branch);
					assert(!o_early_branch_stb);
				end else if ((OPT_CIS)&&($past(o_phase))
					&&($past(w_cis_op == 5'h12))
					&&($past(w_rB))
					&&($past(w_cond[3]))
					&&($past(w_Iz))
					&&($past(w_dcdB_pc))
					&&($past(w_dcdR_pc))
					&&(o_dcdR[4:0]=={ i_gie, 4'hf }))
				begin
					// (CIS) LW (PC),PC
					assert(!o_early_branch);
					assert(!o_early_branch_stb);
				end else begin
					assert(!o_early_branch);
				end
			end else if ((OPT_CIS)&&($past(o_phase)))
			begin
				if (($past(w_cis_op == 5'h12))
					&&($past(w_rB))
					&&($past(w_cond[3]))
					&&($past(w_Iz))
					&&($past(w_dcdB_pc))
					&&($past(w_dcdR_pc)))
				begin
				// (CIS) LW (PC),PC
				assert(!o_early_branch);
				assert(!o_early_branch_stb);
				end else begin
					assert(!o_early_branch);
					assert(!o_early_branch_stb);
				end
			end
		end else begin
			assert(!o_early_branch_stb);
		end

		always @(*)
			assume(i_instruction[31:16] != 16'hfcf8);

		always @(*)
		if ((o_valid)
				// LW
				&&(o_M)&&(o_op[2:0]==3'b010)
				// Zero immediate
				&&(o_zI)
				// Unconditional
				&&(o_cond[3])
				// From PC to PC
				&&(o_dcdR[5])&&(o_dcdB[5]))
			assert(o_ljmp);
		else if (o_valid)
			assert(!o_ljmp);

	end else begin
		always @(*)
			assert(!o_early_branch_stb);
		always @(*)
			assert(!o_early_branch);
	end endgenerate

	always @(*)
		if (o_early_branch_stb)
			assert(o_early_branch);
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_early_branch_stb))&&(!$past(pf_valid)))
		assert(!o_early_branch_stb);

	always @(*)
	if (!OPT_LOCK)
		assert(!o_lock);

	generate if (OPT_CIS)
	begin : F_OPT_CIS
		always @(*)
		if (!o_valid)
			assert(!o_phase);

		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_reset)))
		begin
			if ((o_phase)&&($past(i_ce)))
				assert((iword[30:16] == $past(i_instruction[14:0]))
					&&(iword[`CISBIT]));
			else if (!o_phase)
				assert(iword == i_instruction);

			if ((!$past(o_phase))&&($past(i_ce))
					&&($past(pf_valid))
					&&(!$past(w_ljmp_dly))
					&&($past(i_instruction[`CISBIT]))
					&&((!$past(w_dcdR_pc))
						||(!$past(w_wR))))
				assert(o_phase);
			else if (($past(o_phase))&&($past(i_ce)))
				assert(!o_phase);

			assert((!o_phase)||(!o_ljmp));
		end

		always @(posedge i_clk)
		if (f_past_valid)
		begin
			if ($past(i_reset))
				assert(o_gie == $past(i_gie));
			else if (($past(i_ce))&&(!$past(o_phase)))
				assert(o_gie == $past(i_gie));
			else
				assert(o_gie == $past(o_gie));
		end
		
		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_stalled))&&($past(pf_valid))
				&&($past(i_ce)))
		begin
			assert(o_pc[0] == 1'b0);
			if (!$past(iword[`CISBIT]))
			begin
				assert(o_pc[1:0]==2'b00);
				assert(o_pc[AW+1:2] == $past(i_pc[AW+1:2])+1'b1);
			end else if ($past(iword[`CISBIT])&&($past(o_phase)))
				assert(o_pc[(AW+1):1] == $past(o_pc[(AW+1):1]) + 1'b1);
			else if ($past(iword[`CISBIT]))
				assert(o_pc[(AW+1):1] == { $past(i_pc[(AW+1):2]), 1'b1});
		end


		always @(*)
		if (iword[`CISBIT])
		begin
			assert((!w_ldi)||(w_I == { {(23-8){iword[23]}}, iword[23:16] }));
			assert((w_ldi)||(iword[`CISIMMSEL])
				||(w_I == { {(23-7){iword[22]}}, iword[22:16] }));
			assert((w_ldi)||(!iword[`CISIMMSEL])
				||(w_I == { {(23-3){iword[18]}}, iword[18:16] }));
		end else begin
			assert((!w_ldi)||(w_I == iword[22:0]));
			assert((!w_mov)||(w_I == { {(23-13){iword[12]}}, iword[12:0] }));
			assert((w_ldi)||(w_mov)||(iword[`IMMSEL])
					||(w_I == { {(23-18){iword[17]}}, iword[17:0] }));
			assert((w_ldi)||(w_mov)||(!iword[`IMMSEL])
					||(w_I == { {(23-14){iword[13]}}, iword[13:0] }));
		end

		always @(posedge i_clk)
		if ((f_past_valid)&&(o_phase)&&($past(i_ce)))
			assert((r_nxt_half[15])
				&&(r_nxt_half[14:0]==$past(i_instruction[14:0])));
	end else begin

		always @(*)
		begin
			assert((o_phase)||(iword[30:0] == i_instruction[30:0]));
			assert(o_phase == 1'b0);
			assert(o_pc[0] == 1'b0);
		end

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_ce)))
			assert(o_pc[AW+1:2] == $past(i_pc[AW+1:2]) + 1'b1);
		else if (f_past_valid)
			assert(o_pc == $past(o_pc));

		always @(*)
			assert(o_pc[1:0] == 2'b00);

		always @(*)
			assert((!w_ldi)||(w_I == iword[22:0]));
		always @(*)
			assert((!w_mov)||(w_I == { {(23-13){iword[12]}}, iword[12:0] }));
		always @(*)
			assert((w_ldi)||(w_mov)||(iword[`IMMSEL])
					||(w_I == { {(23-18){iword[17]}}, iword[17:0] }));
		always @(*)
			assert((w_ldi)||(w_mov)||(!iword[`IMMSEL])
					||(w_I == { {(23-14){iword[13]}}, iword[13:0] }));

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_ce))&&(!$past(i_reset)))
			assert((!$past(i_instruction[`CISBIT]))
				||(!$past(pf_valid))||(o_illegal));
	end endgenerate

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_ce))&&($past(w_fpu)))
	begin
		if (OPT_FPU)
			assert(o_FP);
		else
			assert(o_illegal);
	end
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_ce))&&($past(w_lock)))
	begin
		if (OPT_LOCK)
			assert(o_lock);
		else
			assert(o_illegal);
	end

	wire	[20:0]	f_next_pipe_I, f_this_pipe_I;
	assign	f_this_pipe_I = r_I[22:2];
	assign	f_next_pipe_I = r_I[22:2]+1'b1;
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin
		if (OPT_OPIPE)
		begin
			if (($past(i_ce))
				&&(($past(pf_valid))||($past(o_phase))))
			begin
				if ((!$past(o_M))||(!o_M))
					assert(!o_pipe);
				else if ($past(o_op[0])!=o_op[0])
					assert(!o_pipe);
				else if ($past(o_rB)!=o_rB)
					assert(!o_pipe);
				else if ($past(o_dcdB) != o_dcdB)
					assert(!o_pipe);
				else if (o_wR != $past(o_wR))
					assert(!o_pipe);
				else if ((o_wR)&&($past(o_dcdR) == o_dcdB))
					assert(!o_pipe);
				else if ($past(o_gie) != $past(i_gie))
					assert(!o_pipe);
				else if (($past(o_cond) != 4'h8)
					&&($past(o_cond) != o_cond))
					assert(!o_pipe);
				else if ($past(r_I[22])!=r_I[22])
					assert(!o_pipe);
				else if (($past(r_I[22:2])!=r_I[22:2])
					&&($past(r_I[22:2])+1'b1!=r_I[22:2]))
					assert(!o_pipe);
				else if (!$past(o_valid))
					assert(!o_pipe);
				// else
					// assert(o_pipe);
			end else if ($past(i_stalled))
				assert(o_pipe == $past(o_pipe));
		end
	end

	always @(*)
		assert((OPT_OPIPE)||(!o_pipe));
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_ce)))
		assert((OPT_MPY)||(o_illegal));

	always @(*)
	if (o_valid)
		assert((!o_phase)||(!o_early_branch));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid))&&($past(o_ljmp))&&($past(!i_stalled)))
		assert(!o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_early_branch_stb)))
	begin
		assert(!o_phase);
		if (!$past(i_stalled))
			assert(!o_valid);
		assert(!o_ljmp);
	end
`endif
endmodule
