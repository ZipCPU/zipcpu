///////////////////////////////////////////////////////////////////////////////
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
//
//
`define	CPU_CC_REG	4'he
`define	CPU_PC_REG	4'hf
//
`include "cpudefs.v"
//
//
//
module	idecode(i_clk, i_rst, i_ce, i_stalled,
		i_instruction, i_gie, i_pc, i_pf_valid,
			i_illegal,
		o_phase, o_illegal,
		o_pc, o_gie,
		o_dcdR, o_dcdA, o_dcdB, o_I, o_zI,
		o_cond, o_wF,
		o_op, o_ALU, o_M, o_DV, o_FP, o_break, o_lock,
		o_wR, o_rA, o_rB,
		o_early_branch, o_branch_pc, o_ljmp,
		o_pipe
		);
	parameter	ADDRESS_WIDTH=24, IMPLEMENT_MPY=1, EARLY_BRANCHING=1,
			IMPLEMENT_DIVIDE=1, IMPLEMENT_FPU=0, AW = ADDRESS_WIDTH;
	input			i_clk, i_rst, i_ce, i_stalled;
	input	[31:0]		i_instruction;
	input			i_gie;
	input	[(AW-1):0]	i_pc;
	input			i_pf_valid, i_illegal;
	output	wire		o_phase;
	output	reg		o_illegal;
	output	reg	[(AW-1):0]	o_pc;
	output	reg		o_gie;
	output	reg	[6:0]	o_dcdR, o_dcdA, o_dcdB;
	output	wire	[31:0]	o_I;
	output	reg		o_zI;
	output	reg	[3:0]	o_cond;
	output	reg		o_wF;
	output	reg	[3:0]	o_op;
	output	reg		o_ALU, o_M, o_DV, o_FP, o_break;
	output	wire		o_lock;
	output	reg		o_wR, o_rA, o_rB;
	output	wire		o_early_branch;
	output	wire	[(AW-1):0]	o_branch_pc;
	output	wire		o_ljmp;
	output	wire		o_pipe;

	wire	dcdA_stall, dcdB_stall, dcdF_stall;
	wire			o_dcd_early_branch;
	wire	[(AW-1):0]	o_dcd_branch_pc;
	reg	o_dcdI, o_dcdIz;
`ifdef	OPT_PIPELINED
	reg	r_lock;
`endif
`ifdef	OPT_PIPELINED_BUS_ACCESS
	reg	r_pipe;
`endif


	wire	[4:0]	w_op;
	wire		w_ldi, w_mov, w_cmptst, w_ldilo, w_ALU, w_brev, w_noop;
	wire	[4:0]	w_dcdR, w_dcdB, w_dcdA;
	wire		w_dcdR_pc, w_dcdR_cc;
	wire		w_dcdA_pc, w_dcdA_cc;
	wire		w_dcdB_pc, w_dcdB_cc;
	wire	[3:0]	w_cond;
	wire		w_wF, w_dcdM, w_dcdDV, w_dcdFP;
	wire		w_wR, w_rA, w_rB, w_wR_n;
	wire		w_ljmp, w_ljmp_dly;
	wire	[31:0]	iword;


`ifdef	OPT_VLIW
	reg	[16:0]	r_nxt_half;
	assign	iword = (o_phase)
				// set second half as a NOOP ... but really 
				// shouldn't matter
			? { r_nxt_half[16:7], 1'b0, r_nxt_half[6:0], 5'b11000, 3'h7, 6'h00 }
			: i_instruction;
`else
	assign	iword = { 1'b0, i_instruction[30:0] };
`endif

	generate
	if (EARLY_BRANCHING != 0)
		assign	w_ljmp = (iword == 32'h7c87c000);
	else
		assign	w_ljmp = 1'b0;
	endgenerate


	assign	w_op= iword[26:22];
	assign	w_mov    = (w_op      == 5'h0f);
	assign	w_ldi    = (w_op[4:1] == 4'hb);
	assign	w_brev   = (w_op      == 5'hc);
	assign	w_cmptst = (w_op[4:1] == 4'h8);
	assign	w_ldilo  = (w_op[4:0] == 5'h9);
	assign	w_ALU    = (~w_op[4]);

	// 4 LUTs
	//
	// Two parts to the result register: the register set, given for
	// moves in i_word[18] but only for the supervisor, and the other
	// four bits encoded in the instruction.
	//
	assign	w_dcdR = { ((~iword[31])&&(w_mov)&&(~i_gie))?iword[18]:i_gie,
				iword[30:27] };
	// 2 LUTs
	//
	// If the result register is either CC or PC, and this would otherwise
	// be a floating point instruction with floating point opcode of 0,
	// then this is a NOOP.
	assign	w_noop   = (w_op[4:0] == 5'h18)&&(
			((IMPLEMENT_FPU>0)&&(w_dcdR[3:1] == 3'h7))
			||(IMPLEMENT_FPU==0));

	// 4 LUTs
	assign	w_dcdB = { ((~iword[31])&&(w_mov)&&(~i_gie))?iword[13]:i_gie,
				iword[17:14] };

	// 0 LUTs
	assign	w_dcdA = w_dcdR;
	// 2 LUTs, 1 delay each
	assign	w_dcdR_pc = (w_dcdR == {i_gie, `CPU_PC_REG});
	assign	w_dcdR_cc = (w_dcdR == {i_gie, `CPU_CC_REG});
	// 0 LUTs
	assign	w_dcdA_pc = w_dcdR_pc;
	assign	w_dcdA_cc = w_dcdR_cc;
	// 2 LUTs, 1 delays each
	assign	w_dcdB_pc = (w_dcdB[3:0] == `CPU_PC_REG);
	assign	w_dcdB_cc = (w_dcdB[3:0] == `CPU_CC_REG);

	// Under what condition will we execute this
	// instruction?  Only the load immediate instruction
	// is completely unconditional.
	//
	// 3+4 LUTs
	assign	w_cond = (w_ldi) ? 4'h8 :
			(iword[31])?{(iword[20:19]==2'b00),
					1'b0,iword[20:19]}
			: { (iword[21:19]==3'h0), iword[21:19] };

	// 1 LUT
	assign	w_dcdM    = (w_op[4:1] == 4'h9);
	// 1 LUT
	assign	w_dcdDV   = (w_op[4:1] == 4'ha);
	// 1 LUT
	assign	w_dcdFP   = (w_op[4:3] == 2'b11)&&(w_dcdR[3:1] != 3'h7);
	// 4 LUT's--since it depends upon FP/NOOP condition (vs 1 before)
	//	Everything reads A but ... NOOP/BREAK/LOCK, LDI, LOD, MOV
	assign	w_rA     = (w_dcdFP)
				// Divide's read A
				||(w_dcdDV)
				// ALU read's A, unless it's a MOV to A
				// This includes LDIHI/LDILO
				||((~w_op[4])&&(w_op[3:0]!=4'hf))
				// STO's read A
				||((w_dcdM)&&(w_op[0]))
				// Test/compares
				||(w_op[4:1]== 4'h8);
	// 1 LUTs -- do we read a register for operand B?  Specifically, do
	// we need to stall if the register is not (yet) ready?
	assign	w_rB     = (w_mov)||((iword[18])&&(~w_ldi));
	// 1 LUT: All but STO, NOOP/BREAK/LOCK, and CMP/TST write back to w_dcdR
	assign	w_wR_n   = ((w_dcdM)&&(w_op[0]))
				||((w_op[4:3]==2'b11)&&(w_dcdR[3:1]==3'h7))
				||(w_cmptst);
	assign	w_wR     = ~w_wR_n;
	//
	// 1-output bit (5 Opcode bits, 4 out-reg bits, 3 condition bits)
	//	
	//	This'd be 4 LUTs, save that we have the carve out for NOOPs
	//	and writes to the PC/CC register(s).
	assign	w_wF     = (w_cmptst)
			||((w_cond[3])&&((w_dcdFP)||(w_dcdDV)
				||((w_ALU)&&(~w_mov)&&(~w_ldilo)&&(~w_brev)
					&&(iword[30:28] != 3'h7))));

	// Bottom 13 bits: no LUT's
	// w_dcd[12: 0] -- no LUTs
	// w_dcd[   13] -- 2 LUTs
	// w_dcd[17:14] -- (5+i0+i1) = 3 LUTs, 1 delay
	// w_dcd[22:18] : 5 LUTs, 1 delay (assuming high bit is o/w determined)
	reg	[22:0]	r_I;
	wire	[22:0]	w_I, w_fullI;
	wire		w_Iz;

	assign	w_fullI = (w_ldi) ? { iword[22:0] } // LDI
			:((w_mov) ?{ {(23-13){iword[12]}}, iword[12:0] } // Move
			:((~iword[18]) ? { {(23-18){iword[17]}}, iword[17:0] }
			: { {(23-14){iword[13]}}, iword[13:0] }
			));

`ifdef	OPT_VLIW
	wire	[5:0]	w_halfI;
	assign	w_halfI = (w_ldi) ? iword[5:0]
				:((iword[5]) ? 6'h00 : {iword[4],iword[4:0]});
	assign	w_I  = (iword[31])? {{(23-6){w_halfI[5]}}, w_halfI }:w_fullI;
`else
	assign	w_I  = w_fullI;
`endif
	assign	w_Iz = (w_I == 0);


`ifdef	OPT_VLIW
	//
	// The o_phase parameter is special.  It needs to let the software
	// following know that it cannot break/interrupt on an o_phase asserted
	// instruction, lest the break take place between the first and second
	// half of a VLIW instruction.  To do this, o_phase must be asserted
	// when the first instruction half is valid, but not asserted on either
	// a 32-bit instruction or the second half of a 2x16-bit instruction.
	reg	r_phase;
	initial	r_phase = 1'b0;
	always @(posedge i_clk)
		if ((i_rst) // When no instruction is in the pipe, phase is zero
			||(o_early_branch)||(w_ljmp_dly))
			r_phase <= 1'b0;
		else if ((i_ce)&&(i_pf_valid))
			r_phase <= (o_phase)? 1'b0:(i_instruction[31]);
	// Phase is '1' on the first instruction of a two-part set
	// But, due to the delay in processing, it's '1' when our output is
	// valid for that first part, but that'll be the same time we
	// are processing the second part ... so it may look to us like a '1'
	// on the second half of processing.

	assign	o_phase = r_phase;
`else
	assign	o_phase = 1'b0;
`endif


	initial	o_illegal = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			o_illegal <= 1'b0;
		else if (i_ce)
		begin
`ifdef	OPT_VLIW
			o_illegal <= (i_illegal);
`else
			o_illegal <= ((i_illegal) || (i_instruction[31]));
`endif
			if ((IMPLEMENT_MPY==0)&&((w_op[4:1]==4'h5)||(w_op[4:0]==5'h08)))
				o_illegal <= 1'b1;

			if ((IMPLEMENT_DIVIDE==0)&&(w_dcdDV))
				o_illegal <= 1'b1;
			else if ((IMPLEMENT_DIVIDE!=0)&&(w_dcdDV)&&(w_dcdR[3:1]==3'h7))
				o_illegal <= 1'b1;


			if ((IMPLEMENT_FPU!=0)&&(w_dcdFP)&&(w_dcdR[3:1]==3'h7))
				o_illegal <= 1'b1;
			else if ((IMPLEMENT_FPU==0)&&(w_dcdFP))
				o_illegal <= 1'b1;

			if ((w_op[4:3]==2'b11)&&(w_dcdR[3:1]==3'h7)
				&&(
					(w_op[2:0] != 3'h1)	// BREAK
`ifdef	OPT_PIPELINED
					&&(w_op[2:0] != 3'h2)	// LOCK
`endif
					&&(w_op[2:0] != 3'h0)))	// NOOP
				o_illegal <= 1'b1;
		end


	always @(posedge i_clk)
		if (i_ce)
		begin
`ifdef	OPT_VLIW
			if (~o_phase)
			begin
				o_gie<= i_gie;
				// i.e. dcd_pc+1
				o_pc <= i_pc+{{(AW-1){1'b0}},1'b1};
			end
`else
			o_gie<= i_gie;
			o_pc <= i_pc+{{(AW-1){1'b0}},1'b1};
`endif

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
			o_op <= (w_ldi)||(w_noop)? 4'hf:w_op[3:0];

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
			o_ALU  <=  (w_ALU)||(w_ldi)||(w_cmptst)||(w_noop); // 2 LUT
			o_M    <=  w_dcdM;
			o_DV   <=  w_dcdDV;
			o_FP   <=  w_dcdFP;
	
			o_break <= (w_op[4:0]==5'b11001)&&(
				((IMPLEMENT_FPU>0)&&(w_dcdR[3:1]==3'h7))
				||(IMPLEMENT_FPU==0));
`ifdef	OPT_PIPELINED
			r_lock  <= (w_op[4:0]==5'b11010)&&(
				((IMPLEMENT_FPU>0)&&(w_dcdR[3:1]==3'h7))
				||(IMPLEMENT_FPU==0));
`endif
`ifdef	OPT_VLIW
			r_nxt_half <= { iword[31], iword[13:5],
				((iword[21])? iword[20:19] : 2'h0),
				iword[4:0] };
`endif
		end

`ifdef	OPT_PIPELINED
	assign	o_lock = r_lock;
`else
	assign	o_lock = 1'b0;
`endif

	generate
	if (EARLY_BRANCHING!=0)
	begin
		reg			r_early_branch, r_ljmp;
		reg	[(AW-1):0]	r_branch_pc;

		initial r_ljmp = 1'b0;
		always @(posedge i_clk)
			if (i_rst)
				r_ljmp <= 1'b0;
			else if ((i_ce)&&(i_pf_valid))
				r_ljmp <= (w_ljmp);
		assign	o_ljmp = r_ljmp;

		always @(posedge i_clk)
		if (i_rst)
			r_early_branch <= 1'b0;
		else if ((i_ce)&&(i_pf_valid))
		begin
			if (r_ljmp)
				// LOD (PC),PC
				r_early_branch <= 1'b1;
			else if ((~iword[31])&&(iword[30:27]==`CPU_PC_REG)&&(w_cond[3]))
			begin
				if (w_op[4:1] == 4'hb) // LDI to PC
					// LDI x,PC
					r_early_branch     <= 1'b1;
				else if ((w_op[4:0]==5'h02)&&(~iword[18]))
					// Add x,PC
					r_early_branch     <= 1'b1;
				else begin
					r_early_branch     <= 1'b0;
				end
			end else
				r_early_branch <= 1'b0;
		end else if (i_ce)
			r_early_branch <= 1'b0;

		always @(posedge i_clk)
			if (i_ce)
			begin
				if (r_ljmp)
					r_branch_pc <= iword[(AW-1):0];
				else if (w_op[4:1] == 4'hb) // LDI
					r_branch_pc <= {{(AW-23){iword[22]}},iword[22:0]};
				else // Add x,PC
				r_branch_pc <= i_pc
					+ {{(AW-17){iword[17]}},iword[16:0]}
					+ {{(AW-1){1'b0}},1'b1};
			end

		assign	w_ljmp_dly         = r_ljmp;
		assign	o_early_branch     = r_early_branch;
		assign	o_branch_pc        = r_branch_pc;
	end else begin
		assign	w_ljmp_dly         = 1'b0;
		assign	o_early_branch = 1'b0;
		assign	o_branch_pc = {(AW){1'b0}};
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
`ifdef	OPT_PIPELINED_BUS_ACCESS
	initial	r_pipe = 1'b0;
	always @(posedge i_clk)
		if (i_ce)
			r_pipe <= (r_valid)&&(i_pf_valid)&&(~i_instruction[31])
				&&(w_dcdM)&&(o_M)&&(o_op[0] ==i_instruction[22])
				&&(i_instruction[17:14] == o_dcdB[3:0])
				&&(i_instruction[17:14] != o_dcdA[3:0])
				&&(i_gie == o_gie)
				&&((i_instruction[21:19]==o_cond[2:0])
					||(o_cond[2:0] == 3'h0))
				&&((i_instruction[13:0]==r_I[13:0])
					||({1'b0, i_instruction[13:0]}==(r_I[13:0]+14'h1)));
	assign o_pipe = r_pipe;
`else
	assign o_pipe = 1'b0;
`endif

	always @(posedge i_clk)
		if (i_rst)
			r_valid <= 1'b0;
		else if ((i_ce)&&(o_ljmp))
			r_valid <= 1'b0;
		else if ((i_ce)&&(i_pf_valid))
			r_valid <= 1'b1;
		else if (~i_stalled)
			r_valid <= 1'b0;
			

	assign	o_I = { {(32-22){r_I[22]}}, r_I[21:0] };

endmodule
