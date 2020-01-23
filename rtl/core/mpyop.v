////////////////////////////////////////////////////////////////////////////////
//
// Filename:	mpyop.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This code has been pulled from the cpuops.v file so as to
//		encapsulate the multiply component--the one component that
//	(can't be) formally verified well, and so must be abstracted away.
//	This separation was done to support potential future abstraction.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
module	mpyop(i_clk,i_reset, i_stb, i_op, i_a, i_b, o_valid, o_busy, o_result, o_hi);
	// The following parameter selects which multiply algorithm we use.
	// Timing performance is strictly dependent upon it.
	parameter	IMPLEMENT_MPY = 1;
	input	wire		i_clk, i_reset, i_stb;
	input	wire	[1:0]	i_op; // 2'b00=MPY, 2'b10=MPYUHI, 2'b11=MPYSHI
	input	wire	[31:0]	i_a, i_b;
	output	wire		o_valid; // True if we'll be valid on the next clock;
	output	wire		o_busy; // The multiply is busy if true
	output	wire	[63:0]	o_result; // Where we dump the multiply result
	output	reg		o_hi;	// Return the high half of the multiply


	// A 4-way multiplexer can be done in one 6-LUT.
	// A 16-way multiplexer can therefore be done in 4x 6-LUT's with
	//	the Xilinx multiplexer fabric that follows. 
	// Given that we wish to apply this multiplexer approach to 33-bits,
	// this will cost a minimum of 132 6-LUTs.

// i_stb instead of this_is_a_multiply_op
// o_result
// o_busy
// o_done
	generate
	if (IMPLEMENT_MPY == 0)
	begin : MPYNONE // No multiply support.

		assign	o_result   = 64'h00;
		assign	o_busy     = 1'b0;
		assign	o_valid    = i_stb;
		always @(*) o_hi = 1'b0; // Not needed

`ifdef	VERILATOR
		// verilator lint_off UNUSED
		wire	[32+32+5-1:0]	mpy_unused;
		assign	mpy_unused = { i_clk, i_reset, i_stb, i_op, i_a, i_b };
		// verilator lint_on  UNUSED
`endif
	end else begin : IMPY
	if (IMPLEMENT_MPY == 1)
	begin : MPY1CK // Our single clock option (no extra clocks)

		wire	signed	[63:0]	w_mpy_a_input, w_mpy_b_input;

		assign	w_mpy_a_input = {{(32){(i_a[31])&(i_op[0])}},i_a[31:0]};
		assign	w_mpy_b_input = {{(32){(i_b[31])&(i_op[0])}},i_b[31:0]};

		assign	o_result = w_mpy_a_input * w_mpy_b_input;

		assign	o_busy  = 1'b0;
		assign	o_valid = 1'b0;
		always @(*) o_hi = i_op[1];

`ifdef	VERILATOR
		// verilator lint_off UNUSED
		wire	[3:0]	mpy_unused;
		assign	mpy_unused = { i_clk, i_reset, i_stb, i_op[1] };
		// verilator lint_on  UNUSED
`endif

	end else begin: MPN1
	if (IMPLEMENT_MPY == 2)
	begin : MPY2CK // Our two clock option (ALU must pause for 1 clock)

		reg	signed	[63:0]	r_mpy_a_input, r_mpy_b_input;
		always @(posedge i_clk)
		begin
			r_mpy_a_input <={{(32){(i_a[31])&(i_op[0])}},i_a[31:0]};
			r_mpy_b_input <={{(32){(i_b[31])&(i_op[0])}},i_b[31:0]};
		end

		assign	o_result = r_mpy_a_input * r_mpy_b_input;
		assign	o_busy  = 1'b0;

		reg	mpypipe;
		initial	mpypipe = 1'b0;
		always @(posedge i_clk)
			if (i_reset)
				mpypipe <= 1'b0;
			else
				mpypipe <= (i_stb);

		assign	o_valid = mpypipe; // this_is_a_multiply_op;
		always @(posedge i_clk)
		if (i_stb)
			o_hi  <= i_op[1];

	end else begin : MPN2
	if (IMPLEMENT_MPY == 3)
	begin : MPY3CK // Our three clock option (ALU pauses for 2 clocks)
		reg	signed	[63:0]	r_smpy_result;
		reg		[63:0]	r_umpy_result;
		reg	signed	[31:0]	r_mpy_a_input, r_mpy_b_input;
		reg		[1:0]	mpypipe;
		reg		[1:0]	r_sgn;

		initial	mpypipe = 2'b0;
		always @(posedge i_clk)
			if (i_reset)
				mpypipe <= 2'b0;
			else
			mpypipe <= { mpypipe[0], i_stb };

		// First clock
		always @(posedge i_clk)
		begin
			r_mpy_a_input <= i_a[31:0];
			r_mpy_b_input <= i_b[31:0];
			r_sgn <= { r_sgn[0], i_op[0] };
		end

		// Second clock
`ifdef	VERILATOR
		wire	signed	[63:0]	s_mpy_a_input, s_mpy_b_input;
		wire		[63:0]	u_mpy_a_input, u_mpy_b_input;

		assign	s_mpy_a_input = {{(32){r_mpy_a_input[31]}},r_mpy_a_input};
		assign	s_mpy_b_input = {{(32){r_mpy_b_input[31]}},r_mpy_b_input};
		assign	u_mpy_a_input = {32'h00,r_mpy_a_input};
		assign	u_mpy_b_input = {32'h00,r_mpy_b_input};
		always @(posedge i_clk)
			r_smpy_result <= s_mpy_a_input * s_mpy_b_input;
		always @(posedge i_clk)
			r_umpy_result <= u_mpy_a_input * u_mpy_b_input;
`else

		wire		[31:0]	u_mpy_a_input, u_mpy_b_input;

		assign	u_mpy_a_input = r_mpy_a_input;
		assign	u_mpy_b_input = r_mpy_b_input;

		always @(posedge i_clk)
			r_smpy_result <= r_mpy_a_input * r_mpy_b_input;
		always @(posedge i_clk)
			r_umpy_result <= u_mpy_a_input * u_mpy_b_input;
`endif

		always @(posedge i_clk)
		if (i_stb)
			o_hi  <= i_op[1];
		assign	o_busy  = mpypipe[0];
		assign	o_result = (r_sgn[1])?r_smpy_result:r_umpy_result;
		assign	o_valid = mpypipe[1];

		// Results are then set on the third clock
	end else begin : MPN3
	if (IMPLEMENT_MPY == 4)
	begin : MPY4CK // The three clock option
		reg	[63:0]	r_mpy_result;
		reg	[31:0]	r_mpy_a_input, r_mpy_b_input;
		reg		r_mpy_signed;
		reg	[2:0]	mpypipe;

		// First clock, latch in the inputs
		initial	mpypipe = 3'b0;
		always @(posedge i_clk)
		begin
			// mpypipe indicates we have a multiply in the
			// pipeline.  In this case, the multiply
			// pipeline is a two stage pipeline, so we need 
			// two bits in the pipe.
			if (i_reset)
				mpypipe <= 3'h0;
			else begin
				mpypipe[0] <= i_stb;
				mpypipe[1] <= mpypipe[0];
				mpypipe[2] <= mpypipe[1];
			end

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

			if (i_stb)
				o_hi  <= i_op[1];
		end

		assign	o_busy  = |mpypipe[1:0];
		assign	o_valid = mpypipe[2];

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

		assign	o_result = r_mpy_result;
		// Fourth clock -- results are clocked into writeback
	end else begin : MPYSLOW

		// verilator lint_off UNUSED
		wire		unused_aux;
		wire	[65:0]	full_result;
		// verilator lint_on  UNUSED

		slowmpy #(.LGNA(6), .NA(33)) slowmpyi(i_clk, i_reset, i_stb,
			{ (i_op[0])&(i_a[31]), i_a },
			{ (i_op[0])&(i_b[31]), i_b }, 1'b0, o_busy,
				o_valid, full_result, unused_aux);

		assign	o_result = full_result[63:0];

		always @(posedge i_clk)
		if (i_stb)
			o_hi  <= i_op[1];

	end end end end end
	endgenerate // All possible multiply results have been determined

endmodule
