////////////////////////////////////////////////////////////////////////////////
//
// Filename:	f_idecode.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This RTL file is meant to shadow the idecode.v file, but yet
//		to require no clocks for decoding at all.  The purpose is to
//	help to verify instructions as they go through the ZipCPU pipeline,
//	and so to know what instructions are supposed to do what when.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2024, Gisselquist Technology, LLC
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
//
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	f_idecode #(
		// {{{
		parameter	[0:0]	OPT_MPY    = 1'b1,
		parameter	[0:0]	OPT_SHIFTS = 1'b1,
		parameter	[0:0]	OPT_DIVIDE = 1'b1,
		parameter	[0:0]	OPT_FPU    = 1'b0,
		parameter	[0:0]	OPT_CIS    = 1'b1,
		parameter	[0:0]	OPT_LOCK   = 1'b1,
		parameter	[0:0]	OPT_OPIPE  = 1'b1,
		parameter	[0:0]	OPT_SIM    = 1'b0,
		parameter	[0:0]	OPT_USERMODE = 1'b1,
		parameter	[0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire [31:0]	i_instruction,
		input	wire		i_phase, i_gie,
		output	reg		o_illegal,
		output	wire	[6:0]	o_dcdR, o_dcdA, o_dcdB,
		output	wire	[31:0]	o_I,
		output	wire	[3:0]	o_cond,
		output	wire		o_wF,
		output	wire	[3:0]	o_op,
		output	wire		o_ALU, o_M, o_DV, o_FP, o_break,
		output	wire		o_lock,
		output	wire		o_wR, o_rA, o_rB,
		output	wire		o_prepipe,
		output	wire		o_sim,
		output	wire	[22:0]	o_sim_immv
		// }}}
	);

	// Declarations
	// {{{
	localparam	[3:0]	CPU_SP_REG = 4'hd,
				CPU_CC_REG = 4'he,
				CPU_PC_REG = 4'hf;
	localparam		CISBIT    = 31,
				CISIMMSEL = 23,
				IMMSEL    = 18;

	wire	[4:0]	w_op;
	wire		w_ldi, w_mov, w_cmptst, w_ldilo, w_ALU, w_brev,
			w_noop, w_lock, w_sim, w_break, w_special, // w_add,
			w_mpy;
	wire	[4:0]	w_dcdR, w_dcdB, w_dcdA;
	wire		w_dcdR_pc, w_dcdR_cc;
	wire		w_dcdA_pc, w_dcdA_cc;
	wire		w_dcdB_pc, w_dcdB_cc;
	wire	[3:0]	w_cond;
	wire		w_wF, w_mem, w_sto, w_div, w_fpu;
	wire		w_wR, w_rA, w_rB, w_wR_n;
	wire		illegal_shift;
	wire	[31:0]	iword;
	// }}}

	// iword
	// {{{
	generate if (OPT_CIS)
	begin : SET_IWORD

		assign	iword = ((!i_instruction[CISBIT])||(i_phase))
			? i_instruction
			: { 1'b1, i_instruction[14:0], i_instruction[15:0] };

	end else begin : CLR_IWORD

		assign	iword = { 1'b0, i_instruction[30:0] };

	end endgenerate
	// }}}

	reg	[4:0]	w_cis_op;

	// w_cis_op : Get the opcode
	// {{{
	generate if (OPT_CIS)
	begin : GEN_CIS_OP

		always @(*)
		if (!iword[CISBIT])
			w_cis_op = iword[26:22];
		else case(iword[26:24])
		3'h0: w_cis_op = 5'h00;	// ADD
		3'h1: w_cis_op = 5'h01;	// AND
		3'h2: w_cis_op = 5'h02;	// SUB
		3'h3: w_cis_op = 5'h10;	// BREV
		3'h4: w_cis_op = 5'h12;	// LW
		3'h5: w_cis_op = 5'h13;	// SW
		3'h6: w_cis_op = 5'h18;	// LDI
		3'h7: w_cis_op = 5'h0d;	// MOV
		endcase

	end else begin : GEN_NOCIS_OP

		always @(*)
			w_cis_op = w_op;

	end endgenerate
	// }}}

	// Decode instructions
	// {{{
	assign	w_op= iword[26:22];
	assign	w_mov    = (w_cis_op      == 5'h0d);
	assign	w_ldi    = (w_cis_op[4:1] == 4'hc);
	assign	w_brev   = (w_cis_op      == 5'h08);
	assign	w_mpy    = (w_cis_op[4:1] == 4'h5)||(w_cis_op[4:0]==5'h0c);
	assign	w_cmptst = (w_cis_op[4:1] == 4'h8);
	assign	w_ldilo  = (w_cis_op[4:0] == 5'h09);
	assign	w_ALU    = (!w_cis_op[4]) // anything with [4]==0, but ...
				&&(w_cis_op[3:1] != 3'h7); // not the divide
	// assign	w_add    = (w_cis_op[4:0] == 5'h02);
	assign	w_mem    = (w_cis_op[4:3] == 2'b10)&&(w_cis_op[2:1] !=2'b00);
	assign	w_sto    = (w_mem)&&( w_cis_op[0]);
	assign	w_div    = (!iword[CISBIT])&&(w_op[4:1] == 4'h7);
	assign	w_fpu    = (!iword[CISBIT])&&(w_op[4:3] == 2'b11)
				&&(w_dcdR[3:1] != 3'h7)
				&&(w_op[2:1] != 2'b00);
	// If the result register is either CC or PC, and this would otherwise
	// be a floating point instruction with floating point opcode of 0,
	// then this is a NOOP.
	assign	w_special= (!iword[CISBIT])&&(w_dcdR[3:1]==3'h7)
			&&(w_op[4:2] == 3'b111);
	assign	w_break = (w_special)&&(w_op[4:0]==5'h1c);
	assign	w_lock  = (w_special)&&(w_op[4:0]==5'h1d);
	assign	w_sim   = (w_special)&&(w_op[4:0]==5'h1e);
	assign	w_noop  = (w_special)&&(w_op[4:1]==4'hf); // Must include w_sim
`ifdef	FORMAL
	always @(*)
		assert(!w_special || !w_fpu);
`endif
	// }}}

	// w_dcdR, w_dcdA
	// {{{
	// What register will we be placing results into (if at all)?
	//
	// Two parts to the result register: the register set, given for
	// moves in iword[18] but only for the supervisor, and the other
	// four bits encoded in the instruction.
	//
	assign	w_dcdR = { ((!iword[CISBIT])&&(OPT_USERMODE)&&(w_mov)&&(!i_gie))?iword[IMMSEL]:i_gie,
				iword[30:27] };

	assign	w_dcdA = w_dcdR;	// on ZipCPU, A is always result reg

	assign	w_dcdA_pc = w_dcdR_pc;
	assign	w_dcdA_cc = w_dcdR_cc;

	assign	w_dcdR_pc = (w_dcdR == {i_gie, CPU_PC_REG});
	assign	w_dcdR_cc = (w_dcdR == {i_gie, CPU_CC_REG});
	// }}}

	// dcdB - What register is used in the opB?
	// {{{
	assign w_dcdB[4] = ((!iword[CISBIT])&&(w_mov)&&(OPT_USERMODE)&&(!i_gie))?iword[13]:i_gie;
	assign w_dcdB[3:0]= (iword[CISBIT])
				? (((!iword[CISIMMSEL])&&(iword[26:25]==2'b10))
					? CPU_SP_REG : iword[22:19])
				: iword[17:14];

	assign	w_dcdB_pc = (w_rB)&&(w_dcdB[3:0] == CPU_PC_REG);
	assign	w_dcdB_cc = (w_rB)&&(w_dcdB[3:0] == CPU_CC_REG);
	// }}}

	// w_cond
	// {{{
	// Under what condition will we execute this instruction?  Only the
	// load immediate instruction and the CIS instructions are completely
	// unconditional.  Well ... not quite.  The BREAK, LOCK, and SIM/NOOP
	// instructions are also unconditional.
	//
	assign	w_cond = ((w_ldi)||(w_special)||(iword[CISBIT])) ? 4'h8 :
			{ (iword[21:19]==3'h0), iword[21:19] };
	// }}}

	// rA - do we need to read register A?
	// {{{
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
	// }}}

	// rB -- do we read a register for operand B?
	// {{{
	// Specifically, do we add the registers value to the immediate to
	// create opB?
	assign	w_rB     = (w_mov)
				||((!iword[CISBIT])&&(iword[IMMSEL])&&(!w_ldi)&&(!w_special))
				||(( iword[CISBIT])&&(iword[CISIMMSEL])&&(!w_ldi))
				// If using compressed instruction sets,
				// we *always* read on memory operands.
				||(( iword[CISBIT])&&(w_mem));
	// }}}

	// wR -- will we be writing our result back?
	// {{{
	// wR_n = !wR
	// All but STO, NOOP/BREAK/LOCK, and CMP/TST write back to w_dcdR
	assign	w_wR_n   = (w_sto)
				||(w_special)
				||(w_cmptst);
	assign	w_wR     = !w_wR_n;
	// }}}
	//
	// wF -- do we write flags when we are done?
	// {{{
	assign	w_wF     = (w_cmptst)
			||((w_cond[3])&&(w_fpu||w_div
				||((w_ALU)&&(!w_mov)&&(!w_ldilo)&&(!w_brev)
					&&(w_dcdR[3:1] != 3'h7))));
	// }}}

	// w_immsrc - where does the immediate value come from
	// {{{
	// Bottom 13 bits: no LUT's
	// w_dcd[12: 0] -- no LUTs
	// w_dcd[   13] -- 2 LUTs
	// w_dcd[17:14] -- (5+i0+i1) = 3 LUTs, 1 delay
	// w_dcd[22:18] : 5 LUTs, 1 delay (assuming high bit is o/w determined)
	wire	[22:0]	w_I, w_fullI;

	// w_fullI -- extracting the immediate value from the insn word
	// {{{
	assign	w_fullI = (w_ldi) ? { iword[22:0] } // LDI
			// MOVE immediates have one less bit
			:((w_mov) ?{ {(23-13){iword[12]}}, iword[12:0] }
			// Normal Op-B immediate ... 18 or 14 bits
			:((!iword[IMMSEL]) ? { {(23-18){iword[17]}}, iword[17:0] }
			: { {(23-14){iword[13]}}, iword[13:0] }
			));
	// }}}

	// w_I and w_Iz: Immediate value decoding
	// {{{
	generate if (OPT_CIS)
	begin : GEN_CIS_IMMEDIATE
		wire	[7:0]	w_halfbits;
		assign	w_halfbits = iword[CISIMMSEL:16];

		wire	[7:0]	w_halfI;
		assign	w_halfI = (iword[26:24]==3'h6) ? w_halfbits[7:0] // 8'b for LDI
				:(w_halfbits[7])?
					{ {(6){w_halfbits[2]}}, w_halfbits[1:0]}
					:{ w_halfbits[6], w_halfbits[6:0] };
		assign	w_I  = (iword[CISBIT])
				? {{(23-8){w_halfI[7]}}, w_halfI }
				: w_fullI;

	end else begin : GEN_NOCIS_IMMEDIATE

		assign	w_I  = w_fullI;

	end endgenerate

	// }}}
	// }}}

	// illegal_shift
	// {{{
	generate if (OPT_SHIFTS)
	begin
		assign	illegal_shift = 1'b0;
	end else begin
		reg	r_illegal_shift;

		always @(*)
		begin
			r_illegal_shift = 1'b1;
			if (i_instruction[CISBIT])
				r_illegal_shift = 1'b0;
			else if ((i_instruction[26:22] == 5'h5)
				||(i_instruction[26:22] == 5'h6)
				||(i_instruction[26:22] == 5'h7))
				r_illegal_shift = 1'b0;
			else if (!i_instruction[18]
					&& i_instruction[17:0] == 18'h1)
				r_illegal_shift = 1'b0;
		end

		assign	illegal_shift = r_illegal_shift;
	end endgenerate
	// }}}

	// o_illegal
	// {{{
	initial	o_illegal = 1'b0;
	always @(*)
	begin
		o_illegal = 1'b0;

		if (illegal_shift)
			o_illegal = 1'b1;

		if ((!OPT_CIS)&&(i_instruction[CISBIT]))
			o_illegal = 1'b1;
		if ((!OPT_MPY)&&(w_mpy))
			o_illegal = 1'b1;

		if ((!OPT_DIVIDE)&&(w_div))
			o_illegal = 1'b1;
		else if ((OPT_DIVIDE)&&(w_div)&&(w_dcdR[3:1]==3'h7))
			o_illegal = 1'b1;


		if (!OPT_FPU && w_fpu)
			o_illegal = 1'b1;

		if ((!OPT_SIM)&&(w_sim))
		// Simulation instructions on real hardware should
		// always cause an illegal instruction error
			o_illegal = 1'b1;

		// There are two (missing) special instructions, after
		// BREAK, LOCK, SIM, and NOOP.  These are special if their
		// (unused-result) register is either the PC or CC register.
		//
		// These should cause an illegal instruction error
		if ((w_dcdR[3:1]==3'h7)&&(w_cis_op[4:1]==4'b1101))
			o_illegal = 1'b1;

		// If the lock function isn't implemented, this should
		// also cause an illegal instruction error
		if ((!OPT_LOCK)&&(w_lock))
			o_illegal = 1'b1;
	end
	// }}}

	generate if (OPT_OPIPE)
	begin
		// o_prepipe is true if a pipelined memory instruction
		// might follow this one
		assign	o_prepipe =
				((OPT_CIS)||(!i_instruction[CISBIT]))
				&&(o_M)&&(o_rB)
				&&(o_dcdB[3:1] != 3'h7)
				&&(o_dcdR[3:1] != 3'h7)
				&&((!o_wR)||(o_dcdR != o_dcdB));
	end else begin
		assign	o_prepipe = 1'b0;
	end endgenerate

	assign	o_dcdR = { w_dcdR_cc, w_dcdR_pc, w_dcdR};
	assign	o_dcdA = { w_dcdA_cc, w_dcdA_pc, w_dcdA};
	assign	o_dcdB = { w_dcdB_cc, w_dcdB_pc, w_dcdB};
	assign	o_I = { {(32-22){w_I[22]}}, w_I[21:0] };
	assign	o_cond = w_cond;
	assign	o_wF   = w_wF;
	assign	o_op   = ((w_ldi)||(w_noop))? 4'hd : w_cis_op[3:0];
	assign	o_ALU  =  (w_ALU)||(w_ldi)||(w_cmptst)||(w_noop);
	assign	o_M    = w_mem;
	assign	o_DV   = (OPT_DIVIDE)&&(w_div);
	assign	o_FP   = (OPT_FPU)&&(w_fpu);
	assign	o_break= w_break;
	assign	o_lock = (OPT_LOCK)&&(w_lock);
	assign	o_wR   = w_wR;
	assign	o_rA   = w_rA;
	assign	o_rB   = w_rB;
	assign	o_sim      = (OPT_SIM) ? ((w_sim)||(w_noop)) : 1'b0;
	assign	o_sim_immv = (OPT_SIM && (!OPT_LOWPOWER || o_sim)) ? iword[22:0] : 0;

endmodule
