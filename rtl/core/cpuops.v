///////////////////////////////////////////////////////////////////////////
//
// Filename:	cpuops.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This supports the instruction set reordering of operations
//		created by the second generation instruction set, as well as
//	the new operations of POPC (population count) and BREV (bit reversal).
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
///////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015, Gisselquist Technology, LLC
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
///////////////////////////////////////////////////////////////////////////
//
`define	LONG_MPY
module	cpuops(i_clk,i_rst, i_ce, i_valid, i_op, i_a, i_b, o_c, o_f, o_valid,
			o_illegal, o_busy);
	parameter	IMPLEMENT_MPY = 1;
	input		i_clk, i_rst, i_ce;
	input		[3:0]	i_op;
	input		[31:0]	i_a, i_b;
	input			i_valid;
	output	reg	[31:0]	o_c;
	output	wire	[3:0]	o_f;
	output	reg		o_valid;
	output	wire		o_illegal;
	output	wire		o_busy;

	// Rotate-left pre-logic
	wire	[63:0]	w_rol_tmp;
	assign	w_rol_tmp = { i_a, i_a } << i_b[4:0];
	wire	[31:0]	w_rol_result;
	assign	w_rol_result = w_rol_tmp[63:32]; // Won't set flags

	// Shift register pre-logic
	wire	[32:0]		w_lsr_result, w_asr_result, w_lsl_result;
	wire	signed	[32:0]	w_pre_asr_input, w_pre_asr_shifted;
	assign	w_pre_asr_input = { i_a, 1'b0 };
	assign	w_pre_asr_shifted = w_pre_asr_input >>> i_b[4:0];
	assign	w_asr_result = (|i_b[31:5])? {(33){i_a[31]}}
				: w_pre_asr_shifted;// ASR
	assign	w_lsr_result = ((|i_b[31:6])||(i_b[5]&&(i_b[4:0]!=0)))? 33'h00
				:((i_b[5])?{32'h0,i_a[31]}
				
				: ( { i_a, 1'b0 } >> (i_b[4:0]) ));// LSR
	assign	w_lsl_result = ((|i_b[31:6])||(i_b[5]&&(i_b[4:0]!=0)))? 33'h00
				:((i_b[5])?{i_a[0], 32'h0}
				: ({1'b0, i_a } << i_b[4:0]));	// LSL

	// Bit reversal pre-logic
	wire	[31:0]	w_brev_result;
	genvar	k;
	generate
	for(k=0; k<32; k=k+1)
	begin : bit_reversal_cpuop
		assign w_brev_result[k] = i_b[31-k];
	end endgenerate

	// Popcount pre-logic
	wire	[31:0]	w_popc_result;
	assign	w_popc_result[5:0]=
		 ({5'h0,i_b[ 0]}+{5'h0,i_b[ 1]}+{5'h0,i_b[ 2]}+{5'h0,i_b[ 3]})
		+({5'h0,i_b[ 4]}+{5'h0,i_b[ 5]}+{5'h0,i_b[ 6]}+{5'h0,i_b[ 7]})
		+({5'h0,i_b[ 8]}+{5'h0,i_b[ 9]}+{5'h0,i_b[10]}+{5'h0,i_b[11]})
		+({5'h0,i_b[12]}+{5'h0,i_b[13]}+{5'h0,i_b[14]}+{5'h0,i_b[15]})
		+({5'h0,i_b[16]}+{5'h0,i_b[17]}+{5'h0,i_b[18]}+{5'h0,i_b[19]})
		+({5'h0,i_b[20]}+{5'h0,i_b[21]}+{5'h0,i_b[22]}+{5'h0,i_b[23]})
		+({5'h0,i_b[24]}+{5'h0,i_b[25]}+{5'h0,i_b[26]}+{5'h0,i_b[27]})
		+({5'h0,i_b[28]}+{5'h0,i_b[29]}+{5'h0,i_b[30]}+{5'h0,i_b[31]});
	assign	w_popc_result[31:6] = 26'h00;

	// Prelogic for our flags registers
	wire	z, n, v;
	reg	c, pre_sign, set_ovfl;
	always @(posedge i_clk)
		if (i_ce) // 1 LUT
			set_ovfl =(((i_op==4'h0)&&(i_a[31] != i_b[31]))//SUB&CMP
				||((i_op==4'h2)&&(i_a[31] == i_b[31])) // ADD
				||(i_op == 4'h6) // LSL
				||(i_op == 4'h5)); // LSR

`ifdef	LONG_MPY
	reg	mpyhi;
	wire	mpybusy;
`endif

	// A 4-way multiplexer can be done in one 6-LUT.
	// A 16-way multiplexer can therefore be done in 4x 6-LUT's with
	//	the Xilinx multiplexer fabric that follows. 
	// Given that we wish to apply this multiplexer approach to 33-bits,
	// this will cost a minimum of 132 6-LUTs.
	generate
	if (IMPLEMENT_MPY == 0)
	begin
		always @(posedge i_clk)
		if (i_ce)
		begin
			pre_sign <= (i_a[31]);
			c <= 1'b0;
			casez(i_op)
			4'b0000:{c,o_c } <= {1'b0,i_a}-{1'b0,i_b};// CMP/SUB
			4'b0001:   o_c   <= i_a & i_b;		// BTST/And
			4'b0010:{c,o_c } <= i_a + i_b;		// Add
			4'b0011:   o_c   <= i_a | i_b;		// Or
			4'b0100:   o_c   <= i_a ^ i_b;		// Xor
			4'b0101:{o_c,c } <= w_lsr_result[32:0];	// LSR
			4'b0110:{c,o_c } <= w_lsl_result[32:0]; // LSL
			4'b0111:{o_c,c } <= w_asr_result[32:0];	// ASR
`ifndef	LONG_MPY
			4'b1000:   o_c   <= { i_b[15: 0], i_a[15:0] }; // LODIHI
`endif
			4'b1001:   o_c   <= { i_a[31:16], i_b[15:0] }; // LODILO
			// 4'h1010: The unimplemented MPYU,
			// 4'h1011: and here for the unimplemented MPYS
			4'b1100:   o_c   <= w_brev_result;	// BREV
			4'b1101:   o_c   <= w_popc_result;	// POPC
			4'b1110:   o_c   <= w_rol_result;	// ROL
			default:   o_c   <= i_b;		// MOV, LDI
			endcase
		end

		assign o_busy = 1'b0;

		reg	r_illegal;
		always @(posedge i_clk)
			r_illegal <= (i_ce)&&((i_op == 4'ha)||(i_op == 4'hb)
`ifdef	LONG_MPY
				||(i_op == 4'h8)
`endif
			);
		assign o_illegal = r_illegal;
	end else begin
		//
		// Multiply pre-logic
		//
`ifdef	LONG_MPY
		reg	[63:0]	r_mpy_result;
		if (IMPLEMENT_MPY == 1)
		begin // Our two clock option (one clock extra)
			reg	signed	[64:0]	r_mpy_a_input, r_mpy_b_input;
			reg			mpypipe, x;
			initial	mpypipe = 1'b0;
			always @(posedge i_clk)
				mpypipe <= (i_ce)&&((i_op[3:1]==3'h5)||(i_op[3:0]==4'h8));
			always @(posedge i_clk)
			if (i_ce)
			begin
				r_mpy_a_input <= {{(33){(i_a[31])&(i_op[0])}},
							i_a[31:0]};
				r_mpy_b_input <= {{(33){(i_b[31])&(i_op[0])}},
							i_b[31:0]};
			end
			always @(posedge i_clk)
				if (mpypipe)
					{x, r_mpy_result} = r_mpy_a_input
							* r_mpy_b_input;
			always @(posedge i_clk)
				if (i_ce)
					mpyhi  = i_op[1];
			assign	mpybusy = mpypipe;
		end else if (IMPLEMENT_MPY == 2)
		begin // The three clock option
			reg	[31:0]	r_mpy_a_input, r_mpy_b_input;
			reg		r_mpy_signed;
			reg	[1:0]	mpypipe;

			// First clock, latch in the inputs
			always @(posedge i_clk)
			begin
				// mpypipe indicates we have a multiply in the
				// pipeline.  In this case, the multiply
				// pipeline is a two stage pipeline, so we need 
				// two bits in the pipe.
				mpypipe[0] <= (i_ce)&&((i_op[3:1]==3'h5)
							||(i_op[3:0]==4'h8));
				mpypipe[1] <= mpypipe[0];
	
				if (i_op[0]) // i.e. if signed multiply
				begin
					r_mpy_a_input <= {(~i_a[31]),i_a[30:0]};
					r_mpy_b_input <= {(~i_b[31]),i_b[30:0]};
				end else begin
					r_mpy_a_input <= i_a[31:0];
					r_mpy_b_input <= i_b[31:0];
				end
				// The signed bit really only matters in the
				// case of 64 bit multiply.  We'll keep track
				// of it, though, and pretend in all other
				// cases.
				r_mpy_signed  <= i_op[0];

				if (i_ce)
					mpyhi  = i_op[1];
			end

			assign	mpybusy = |mpypipe;

			// Second clock, do the multiplies, get the "partial
			// products".  Here, we break our input up into two
			// halves, 
			//
			//   A  = (2^16 ah + al)
			//   B  = (2^16 bh + bl)
			//
			// and use these to compute partial products.
			//
			//   AB = (2^32 ah*bh + 2^16 (ah*bl + al*bh) + (al*bl)
			//
			// Since we're following the FOIL algorithm to get here,
			// we'll name these partial products according to FOIL.
			//
			// The trick is what happens if A or B is signed.  In
			// those cases, the real value of A will not be given by
			//	A = (2^16 ah + al)
			// but rather
			//	A = (2^16 ah[31^] + al) - 2^31
			//  (where we have flipped the sign bit of A)
			// and so ...
			//
			// AB= (2^16 ah + al - 2^31) * (2^16 bh + bl - 2^31)
			//	= 2^32(ah*bh)
			//		+2^16 (ah*bl+al*bh)
			//		+(al*bl)
			//		- 2^31 (2^16 bh+bl + 2^16 ah+al)
			//		- 2^62
			//	= 2^32(ah*bh)
			//		+2^16 (ah*bl+al*bh)
			//		+(al*bl)
			//		- 2^31 (2^16 bh+bl + 2^16 ah+al + 2^31)
			//
			reg	[31:0]	pp_f, pp_l; // F and L from FOIL
			reg	[32:0]	pp_oi; // The O and I from FOIL
			reg	[32:0]	pp_s;
			always @(posedge i_clk)
			begin
				pp_f<=r_mpy_a_input[31:16]*r_mpy_b_input[31:16];
				pp_oi<=r_mpy_a_input[31:16]*r_mpy_b_input[15: 0]
					+ r_mpy_a_input[15: 0]*r_mpy_b_input[31:16];
				pp_l<=r_mpy_a_input[15: 0]*r_mpy_b_input[15: 0];
				// And a special one for the sign
				if (r_mpy_signed)
					pp_s <= 32'h8000_0000-(
					  	r_mpy_a_input[31:0]
						+ r_mpy_b_input[31:0]);
				else
					pp_s <= 33'h0;
			end

			// Third clock, add the results and produce a product
			always @(posedge i_clk)
			begin
				r_mpy_result[15:0] <= pp_l[15:0];
				r_mpy_result[63:16] <=
				  	{ 32'h00, pp_l[31:16] }
					+ { 15'h00, pp_oi }
					+ { pp_s, 15'h00 }
					+ { pp_f, 16'h00 };
			end
		end // Fourth clock -- results are available for writeback.
`else
		wire	signed	[16:0]	w_mpy_a_input, w_mpy_b_input;
		wire		[33:0]	w_mpy_result;
		reg		[31:0]	r_mpy_result;
		assign	w_mpy_a_input ={ ((i_a[15])&(i_op[0])), i_a[15:0] };
		assign	w_mpy_b_input ={ ((i_b[15])&(i_op[0])), i_b[15:0] };
		assign	w_mpy_result   = w_mpy_a_input * w_mpy_b_input;
		always @(posedge i_clk)
			if (i_ce)
				r_mpy_result  = w_mpy_result[31:0];
`endif

		//
		// The master ALU case statement
		//
		always @(posedge i_clk)
		if (i_ce)
		begin
			pre_sign <= (i_a[31]);
			c <= 1'b0;
			casez(i_op)
			4'b0000:{c,o_c } <= {1'b0,i_a}-{1'b0,i_b};// CMP/SUB
			4'b0001:   o_c   <= i_a & i_b;		// BTST/And
			4'b0010:{c,o_c } <= i_a + i_b;		// Add
			4'b0011:   o_c   <= i_a | i_b;		// Or
			4'b0100:   o_c   <= i_a ^ i_b;		// Xor
			4'b0101:{o_c,c } <= w_lsr_result[32:0];	// LSR
			4'b0110:{c,o_c } <= w_lsl_result[32:0]; // LSL
			4'b0111:{o_c,c } <= w_asr_result[32:0];	// ASR
`ifdef	LONG_MPY
			4'b1000:   o_c   <= r_mpy_result[31:0]; // MPY
`else
			4'b1000:   o_c   <= { i_b[15: 0], i_a[15:0] }; // LODIHI
`endif
			4'b1001:   o_c   <= { i_a[31:16], i_b[15:0] }; // LODILO
`ifdef	LONG_MPY
			4'b1010:   o_c   <= r_mpy_result[63:32]; // MPYHU
			4'b1011:   o_c   <= r_mpy_result[63:32]; // MPYHS
`else
			4'b1010:   o_c   <= r_mpy_result; // MPYU
			4'b1011:   o_c   <= r_mpy_result; // MPYS
`endif
			4'b1100:   o_c   <= w_brev_result;	// BREV
			4'b1101:   o_c   <= w_popc_result;	// POPC
			4'b1110:   o_c   <= w_rol_result;	// ROL
			default:   o_c   <= i_b;		// MOV, LDI
			endcase
		end else if (r_busy)
`ifdef	LONG_MPY
			o_c <= (mpyhi)?r_mpy_result[63:32]:r_mpy_result[31:0];
`else
			o_c <= r_mpy_result;
`endif

		reg	r_busy;
		initial	r_busy = 1'b0;
		always @(posedge i_clk)
			r_busy <= (~i_rst)&&(i_ce)&&(i_valid)
`ifdef	LONG_MPY
					&&((i_op[3:1] == 3'h5)
						||(i_op[3:0] == 4'h8))||mpybusy;
`else
					&&(i_op[3:1] == 3'h5);
`endif

		assign o_busy = r_busy;

		assign o_illegal = 1'b0;
	end endgenerate

	assign	z = (o_c == 32'h0000);
	assign	n = (o_c[31]);
	assign	v = (set_ovfl)&&(pre_sign != o_c[31]);

	assign	o_f = { v, n, c, z };

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			o_valid <= 1'b0;
		else
			o_valid <= (i_ce)&&(i_valid)
`ifdef	LONG_MPY
				&&(i_op[3:1] != 3'h5)&&(i_op[3:0] != 4'h8)
				||(o_busy)&&(~mpybusy);
`else
				&&(i_op[3:1] != 3'h5)||(o_busy);
`endif
endmodule
