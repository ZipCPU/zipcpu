////////////////////////////////////////////////////////////////////////////////
//
// Filename:	memops.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU.
//
//	In the interests of code simplicity, this memory operator is
//	susceptible to unknown results should a new command be sent to it
//	before it completes the last one.  Unpredictable results might then
//	occurr.
//
//	BIG ENDIAN
//		Note that this core assumes a big endian bus, with the MSB
//		of the bus word being the least bus address
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
module	memops #(
		// {{{
		parameter	ADDRESS_WIDTH=28,
		parameter	DATA_WIDTH=32,	// CPU's register width
		parameter	BUS_WIDTH=32,
		parameter [0:0]	OPT_LOCK=1'b1,
				WITH_LOCAL_BUS=1'b1,
				OPT_ALIGNMENT_ERR=1'b1,
				OPT_LOWPOWER=1'b0,
				OPT_LITTLE_ENDIAN = 1'b0,
		localparam	AW=ADDRESS_WIDTH
`ifdef	FORMAL
		, parameter	F_LGDEPTH = 2
`endif
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// CPU interface
		// {{{
		input	wire			i_stb, i_lock,
		input	wire	[2:0]		i_op,
		input	wire	[31:0]		i_addr,
		input	wire [DATA_WIDTH-1:0]	i_data,
		input	wire	[4:0]		i_oreg,
		// CPU outputs
		output	wire			o_busy,
		output	reg			o_rdbusy,
		output	reg			o_valid,
		output	reg			o_err,
		output	reg	[4:0]		o_wreg,
		output	reg [DATA_WIDTH-1:0]	o_result,
		// }}}
		// Wishbone
		// {{{
		output	wire			o_wb_cyc_gbl,
		output	wire			o_wb_cyc_lcl,
		output	reg			o_wb_stb_gbl,
		output	reg			o_wb_stb_lcl,
		output	reg			o_wb_we,
		output	reg	[AW-1:0]	o_wb_addr,
		output	reg	[BUS_WIDTH-1:0]	o_wb_data,
		output	reg [BUS_WIDTH/8-1:0]	o_wb_sel,
		// Wishbone inputs
		input	wire			i_wb_stall, i_wb_ack, i_wb_err,
		input	wire	[BUS_WIDTH-1:0]	i_wb_data
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam	WBLSB = $clog2(BUS_WIDTH/8);
`ifdef	FORMAL
	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;
`endif

	wire		misaligned;
	reg		r_wb_cyc_gbl, r_wb_cyc_lcl;
	reg	[2+WBLSB-1:0]	r_op;
	wire		lock_gbl, lock_lcl;
	wire		lcl_bus, gbl_stb, lcl_stb;

	reg	[BUS_WIDTH/8-1:0]	oword_sel;
	wire	[BUS_WIDTH/8-1:0]	pre_sel;
	wire	[BUS_WIDTH-1:0]		pre_result;

	wire	[1:0]		oshift2;
	wire	[WBLSB-1:0]	oshift;

	// }}}

	// misaligned
	// {{{
	generate if (OPT_ALIGNMENT_ERR)
	begin : GENERATE_ALIGNMENT_ERR
		reg	r_misaligned;

		always @(*)
		casez({ i_op[2:1], i_addr[1:0] })
		4'b01?1: r_misaligned = i_stb; // Words must be halfword aligned
		4'b0110: r_misaligned = i_stb; // Words must be word aligned
		4'b10?1: r_misaligned = i_stb; // Halfwords must be aligned
		// 4'b11??: r_misaligned <= 1'b0; Byte access are never misaligned
		default: r_misaligned = 1'b0;
		endcase

		assign	misaligned = r_misaligned;
	end else begin : NO_MISALIGNMENT_ERR
		assign	misaligned = 1'b0;
	end endgenerate
	// }}}

	// lcl_stb, gbl_stb
	// {{{
	assign	lcl_bus = (WITH_LOCAL_BUS)&&(i_addr[31:24]==8'hff);
	assign	lcl_stb = (i_stb)&&( lcl_bus)&&(!misaligned);
	assign	gbl_stb = (i_stb)&&(!lcl_bus)&&(!misaligned);
	// }}}

	// r_wb_cyc_gbl, r_wb_cyc_lcl
	// {{{
	initial	r_wb_cyc_gbl = 1'b0;
	initial	r_wb_cyc_lcl = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_wb_cyc_gbl <= 1'b0;
		r_wb_cyc_lcl <= 1'b0;
	end else if ((r_wb_cyc_gbl)||(r_wb_cyc_lcl))
	begin
		if ((i_wb_ack)||(i_wb_err))
		begin
			r_wb_cyc_gbl <= 1'b0;
			r_wb_cyc_lcl <= 1'b0;
		end
	end else begin // New memory operation
		// Grab the wishbone
		r_wb_cyc_lcl <= (lcl_stb);
		r_wb_cyc_gbl <= (gbl_stb);
	end
	// }}}

	// o_wb_stb_gbl
	// {{{
	initial	o_wb_stb_gbl = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_stb_gbl <= 1'b0;
	else if ((i_wb_err)&&(r_wb_cyc_gbl))
		o_wb_stb_gbl <= 1'b0;
	else if (gbl_stb)
		o_wb_stb_gbl <= 1'b1;
	else if (o_wb_cyc_gbl)
		o_wb_stb_gbl <= (o_wb_stb_gbl)&&(i_wb_stall);
	//  }}}

	// o_wb_stb_lcl
	// {{{
	initial	o_wb_stb_lcl = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_stb_lcl <= 1'b0;
	else if ((i_wb_err)&&(r_wb_cyc_lcl))
		o_wb_stb_lcl <= 1'b0;
	else if (lcl_stb)
		o_wb_stb_lcl <= 1'b1;
	else if (o_wb_cyc_lcl)
		o_wb_stb_lcl <= (o_wb_stb_lcl)&&(i_wb_stall);
	// }}}

	// o_wb_we, o_wb_data, o_wb_sel
	// {{{
	always @(*)
	begin
		oword_sel = 0;

		casez({ OPT_LITTLE_ENDIAN, i_op[2:1], i_addr[1:0] })
		5'b00???: oword_sel[3:0] = 4'b1111;
		5'b0100?: oword_sel[3:0] = 4'b1100;
		5'b0101?: oword_sel[3:0] = 4'b0011;
		5'b01100: oword_sel[3:0] = 4'b1000;
		5'b01101: oword_sel[3:0] = 4'b0100;
		5'b01110: oword_sel[3:0] = 4'b0010;
		5'b01111: oword_sel[3:0] = 4'b0001;
		//
		// verilator coverage_off
		5'b10???: oword_sel[3:0] = 4'b1111;
		5'b1100?: oword_sel[3:0] = 4'b0011;
		5'b1101?: oword_sel[3:0] = 4'b1100;
		5'b11100: oword_sel[3:0] = 4'b0001;
		5'b11101: oword_sel[3:0] = 4'b0010;
		5'b11110: oword_sel[3:0] = 4'b0100;
		5'b11111: oword_sel[3:0] = 4'b1000;
		// verilator coverage_on
		//
		default: oword_sel[3:0] = 4'b1111;
		endcase
	end

	// pre_sel
	// {{{
	generate if (BUS_WIDTH == 32)
	begin : COPY_PRESEL
		assign	pre_sel = oword_sel;
	end else if (OPT_LITTLE_ENDIAN)
	begin : GEN_LILPRESEL
		wire	[WBLSB-3:0]	shift;

		assign	shift = i_addr[WBLSB-1:2];
		assign	pre_sel = oword_sel << (4 * i_addr[WBLSB-1:2]);
	end else begin : GEN_PRESEL
		wire	[WBLSB-3:0]	shift;

		assign	shift = {(WBLSB-2){1'b1}} ^ i_addr[WBLSB-1:2];
		assign	pre_sel = oword_sel << (4 * shift);
	end endgenerate
	// }}}

	assign	oshift  = i_addr[WBLSB-1:0];
	assign	oshift2 = i_addr[1:0];

	initial	o_wb_we   = 1'b0;
	initial	o_wb_data = 0;
	initial	o_wb_sel  = 0;
	always @(posedge i_clk)
	if (i_stb)
	begin
		o_wb_we   <= i_op[0];
		if (OPT_LOWPOWER)
		begin
			if (lcl_bus)
			begin
				// {{{
				o_wb_data <= 0;
				casez({ OPT_LITTLE_ENDIAN, i_op[2:1] })
				3'b010: o_wb_data[31:0] <= { i_data[15:0], {(16){1'b0}} } >> (8*oshift2);
				3'b011: o_wb_data[31:0] <= { i_data[ 7:0], {(24){1'b0}} } >> (8*oshift2);
				3'b00?: o_wb_data[31:0] <= i_data[31:0];
				//
				// verilator coverage_off
				3'b110: o_wb_data <= { {(BUS_WIDTH-16){1'b0}}, i_data[15:0] } << (8*oshift2);
				3'b111: o_wb_data <= { {(BUS_WIDTH-8){1'b0}},  i_data[ 7:0] } << (8*oshift2);
				3'b10?: o_wb_data <= { {(BUS_WIDTH-32){1'b0}}, i_data[31:0] } << (8*oshift2);
				// verilator coverage_on
				//
				endcase
				// }}}
			end else begin
				// {{{
				casez({ OPT_LITTLE_ENDIAN, i_op[2:1] })
				3'b010: o_wb_data <= { i_data[15:0], {(BUS_WIDTH-16){1'b0}} } >> (8*oshift);
				3'b011: o_wb_data <= { i_data[ 7:0], {(BUS_WIDTH- 8){1'b0}} } >> (8*oshift);
				3'b00?: o_wb_data <= { i_data[31:0], {(BUS_WIDTH-32){1'b0}} } >> (8*oshift);
				//
				3'b110: o_wb_data <= { {(BUS_WIDTH-16){1'b0}}, i_data[15:0] } << (8*oshift);
				3'b111: o_wb_data <= { {(BUS_WIDTH-8){1'b0}},  i_data[ 7:0] } << (8*oshift);
				3'b10?: o_wb_data <= { {(BUS_WIDTH-32){1'b0}}, i_data[31:0] } << (8*oshift);
				//
				endcase
				// }}}
			end
		end else
			casez({ i_op[2:1] })
			2'b10: o_wb_data <= { (BUS_WIDTH/16){ i_data[15:0] } };
			2'b11: o_wb_data <= { (BUS_WIDTH/ 8){ i_data[7:0] } };
			default: o_wb_data <= {(BUS_WIDTH/32){i_data}};
			endcase

		if (lcl_bus)
		begin
			o_wb_addr <= i_addr[2 +: (AW+2>32 ? (32-2) : AW)];
			o_wb_sel <= oword_sel;
		end else begin
			o_wb_addr <= i_addr[WBLSB +: (AW+WBLSB>32 ? (32-WBLSB) : AW)];
			o_wb_sel <= pre_sel;
		end

		r_op <= { i_op[2:1] , i_addr[WBLSB-1:0] };
	end else if ((OPT_LOWPOWER)&&(!o_wb_cyc_gbl)&&(!o_wb_cyc_lcl))
	begin
		o_wb_we   <= 1'b0;
		o_wb_addr <= 0;
		o_wb_data <= {(BUS_WIDTH){1'b0}};
		o_wb_sel  <= {(BUS_WIDTH/8){1'b0}};
	end
	// }}}

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_valid <= 1'b0;
	else
		o_valid <= (((o_wb_cyc_gbl)||(o_wb_cyc_lcl))
				&&(i_wb_ack)&&(!o_wb_we));
	// }}}

	// o_err
	// {{{
	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_err <= 1'b0;
	else if ((r_wb_cyc_gbl)||(r_wb_cyc_lcl))
		o_err <= i_wb_err;
	else if ((i_stb)&&(!o_busy))
		o_err <= misaligned;
	else
		o_err <= 1'b0;
	// }}}

	assign	o_busy = (r_wb_cyc_gbl)||(r_wb_cyc_lcl);

	// o_rdbusy
	// {{{
	initial	o_rdbusy = 1'b0;
	always @(posedge i_clk)
	if (i_reset|| ((o_wb_cyc_gbl || o_wb_cyc_lcl)&&(i_wb_err || i_wb_ack)))
		o_rdbusy <= 1'b0;
	else if (i_stb && !i_op[0] && !misaligned)
		o_rdbusy <= 1'b1;
	else if (o_valid)
		o_rdbusy <= 1'b0;
	// }}}

	always @(posedge i_clk)
	if (i_stb)
		o_wreg    <= i_oreg;

	// o_result
	// {{{
	generate if (OPT_LITTLE_ENDIAN)
	begin : LILEND_RESULT

		assign	pre_result = i_wb_data >> (8*r_op[$clog2(BUS_WIDTH/8)-1:0]);

	end else begin : BIGEND_RESULT

		assign	pre_result = i_wb_data << (8*r_op[$clog2(BUS_WIDTH/8)-1:0]);

	end endgenerate

	always @(posedge i_clk)
	if ((OPT_LOWPOWER)&&(!i_wb_ack))
		o_result <= 32'h0;
	else if (o_wb_cyc_lcl && (BUS_WIDTH != 32))
	begin
		// The Local bus is naturally (and only) a 32-bit bus
		casez({ OPT_LITTLE_ENDIAN, r_op[WBLSB +: 2], r_op[1:0] })
		5'b?01??: o_result <= i_wb_data[31:0];
		//
		// Big endian
		5'b0100?: o_result <= { 16'h00, i_wb_data[31:16] };
		5'b0101?: o_result <= { 16'h00, i_wb_data[15: 0] };
		5'b01100: o_result <= { 24'h00, i_wb_data[31:24] };
		5'b01101: o_result <= { 24'h00, i_wb_data[23:16] };
		5'b01110: o_result <= { 24'h00, i_wb_data[15: 8] };
		5'b01111: o_result <= { 24'h00, i_wb_data[ 7: 0] };
		//
		// Little endian : Same bus result, just grab a different bits
		//   from the bus return to send back to the CPU.
		// verilator coverage_off
		5'b1100?: o_result <= { 16'h00, i_wb_data[15: 0] };
		5'b1101?: o_result <= { 16'h00, i_wb_data[31:16] };
		5'b11100: o_result <= { 24'h00, i_wb_data[ 7: 0] };
		5'b11101: o_result <= { 24'h00, i_wb_data[15: 8] };
		5'b11110: o_result <= { 24'h00, i_wb_data[23:16] };
		5'b11111: o_result <= { 24'h00, i_wb_data[31:24] };
		// verilator coverage_on
		default: o_result <= i_wb_data[31:0];
		endcase
	end else begin
		casez({ OPT_LITTLE_ENDIAN, r_op[$clog2(BUS_WIDTH/8) +: 2] })
		// Word
		//
		// Big endian
		3'b00?: o_result <= pre_result[BUS_WIDTH-1:BUS_WIDTH-32];
		3'b010: o_result <= { 16'h00, pre_result[BUS_WIDTH-1:BUS_WIDTH-16] };
		3'b011: o_result <= { 24'h00, pre_result[BUS_WIDTH-1:BUS_WIDTH-8] };
		//
		// Little endian : Same bus result, just grab a different bits
		//   from the bus return to send back to the CPU.
		// verilator coverage_off
		3'b10?: o_result <= pre_result[31: 0];
		3'b110: o_result <= { 16'h00, pre_result[15: 0] };
		3'b111: o_result <= { 24'h00, pre_result[ 7: 0] };
		// verilator coverage_on
		//
		// Just to have an (unused) default
		// default: o_result <= pre_result[31:0]; (Messes w/ coverage)
		endcase
	end
	// }}}

	// lock_gbl and lock_lcl
	// {{{
	generate
	if (OPT_LOCK)
	begin : GEN_LOCK
		// {{{
		reg	r_lock_gbl, r_lock_lcl;

		initial	r_lock_gbl = 1'b0;
		initial	r_lock_lcl = 1'b0;

		always @(posedge i_clk)
		if (i_reset)
		begin
			r_lock_gbl <= 1'b0;
			r_lock_lcl <= 1'b0;
		end else if (((i_wb_err)&&((r_wb_cyc_gbl)||(r_wb_cyc_lcl)))
				||(misaligned))
		begin
			// Kill the lock if
			//	there's a bus error, or
			//	User requests a misaligned memory op
			r_lock_gbl <= 1'b0;
			r_lock_lcl <= 1'b0;
		end else begin
			// Kill the lock if
			//	i_lock goes down
			//	User starts on the global bus, then switches
			//	  to local or vice versa
			r_lock_gbl <= (i_lock)&&((r_wb_cyc_gbl)||(lock_gbl))
					&&(!lcl_stb);
			r_lock_lcl <= (i_lock)&&((r_wb_cyc_lcl)||(lock_lcl))
					&&(!gbl_stb);
		end

		assign	lock_gbl = r_lock_gbl;
		assign	lock_lcl = r_lock_lcl;

		assign	o_wb_cyc_gbl = (r_wb_cyc_gbl)||(lock_gbl);
		assign	o_wb_cyc_lcl = (r_wb_cyc_lcl)||(lock_lcl);
		// }}}
	end else begin : NO_LOCK
		// {{{
		assign	o_wb_cyc_gbl = (r_wb_cyc_gbl);
		assign	o_wb_cyc_lcl = (r_wb_cyc_lcl);

		assign	{ lock_gbl, lock_lcl } = 2'b00;

		// Make verilator happy
		// verilator lint_off UNUSED
		wire	[2:0]	lock_unused;
		assign	lock_unused = { i_lock, lock_gbl, lock_lcl };
		// verilator lint_on  UNUSED
		// }}}
	end endgenerate
	// }}}

`ifdef	VERILATOR
	always @(posedge i_clk)
	if ((r_wb_cyc_gbl)||(r_wb_cyc_lcl))
		assert(!i_stb);
`endif


	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, pre_result };
	generate if (AW < 22)
	begin : TOO_MANY_ADDRESS_BITS

		wire	[(21-AW):0] unused_addr;
		assign	unused_addr = i_addr[23:(AW+2)];

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
`define	ASSERT	assert
`ifdef	MEMOPS
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	reg	f_past_valid;

	reg	[2:0]		fcpu_op;
	reg	[31:0]		fcpu_addr, fcpu_data;;
	reg	[BUS_WIDTH-1:0]	fbus_data, fpre_data;
	reg [$clog2(BUS_WIDTH/8)-1:0] fcpu_shift;
	reg			fcpu_local, fcpu_misaligned;
	reg	[BUS_WIDTH/8-1:0]	fbus_sel, fpre_sel;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	`ASSUME(!i_stb);

	wire	f_cyc, f_stb;
	assign	f_cyc = (o_wb_cyc_gbl)||(o_wb_cyc_lcl);
	assign	f_stb = (o_wb_stb_gbl)||(o_wb_stb_lcl);

	fwb_master #(
		// {{{
		.AW(AW), .F_LGDEPTH(F_LGDEPTH), .DW(BUS_WIDTH),
		.F_OPT_RMW_BUS_OPTION(OPT_LOCK),
		.F_OPT_DISCONTINUOUS(OPT_LOCK)
		// }}}
	) f_wb(
		// {{{
		i_clk, i_reset,
		f_cyc, f_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
		i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
		f_nreqs, f_nacks, f_outstanding
		// }}}
	);


	// Rule: Only one of the two CYC's may be valid, never both
	always @(posedge i_clk)
		`ASSERT((!o_wb_cyc_gbl)||(!o_wb_cyc_lcl));

	// Rule: Only one of the two STB's may be valid, never both
	always @(posedge i_clk)
		`ASSERT((!o_wb_stb_gbl)||(!o_wb_stb_lcl));

	// Rule: if WITH_LOCAL_BUS is ever false, neither the local STB nor CYC
	// may be valid
	always @(*)
	if (!WITH_LOCAL_BUS)
	begin
		`ASSERT(!o_wb_cyc_lcl);
		`ASSERT(!o_wb_stb_lcl);
	end

	// Rule: If the global CYC is ever true, the LCL one cannot be true
	// on the next clock without an intervening idle of both
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(r_wb_cyc_gbl)))
		`ASSERT(!r_wb_cyc_lcl);

	// Same for if the LCL CYC is true
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(r_wb_cyc_lcl)))
		`ASSERT(!r_wb_cyc_gbl);

	// STB can never be true unless CYC is also true
	always @(posedge i_clk)
	if (o_wb_stb_gbl)
		`ASSERT(r_wb_cyc_gbl);

	always @(posedge i_clk)
	if (o_wb_stb_lcl)
		`ASSERT(r_wb_cyc_lcl);

	// This core only ever has zero or one outstanding transaction(s)
	always @(posedge i_clk)
	if ((o_wb_stb_gbl)||(o_wb_stb_lcl))
	begin
		`ASSERT(f_outstanding == 0);
	end else
		`ASSERT((f_outstanding == 0)||(f_outstanding == 1));

	// The LOCK function only allows up to two transactions (at most)
	// before CYC must be dropped.
	always @(posedge i_clk)
	if ((o_wb_stb_gbl)||(o_wb_stb_lcl))
	begin
		if (OPT_LOCK)
		begin
			`ASSERT((f_outstanding == 0)||(f_outstanding == 1));
		end else
			`ASSERT(f_nreqs <= 1);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CPU properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg				f_done;
	wire	[(F_LGDEPTH-1):0]	cpu_outstanding;
	wire				f_pc, f_rdbusy, f_gie, f_read_cycle;
	wire	[4:0]			f_last_reg;
	wire	[4:0]			f_addr_reg;
	// Verilator lint_off UNDRIVEN
	(* anyseq *)	reg	[4:0]	f_areg;
	// Verilator lint_on  UNDRIVEN

	assign	f_rdbusy = f_cyc && (f_stb || f_outstanding > 0) && !o_wb_we;

	initial	f_done = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		f_done <= 1'b0;
	else
		f_done <= ((o_wb_cyc_gbl)||(o_wb_cyc_lcl))&&(i_wb_ack);

	fmem #(
		// {{{
		.F_LGDEPTH(F_LGDEPTH),
		.OPT_LOCK(OPT_LOCK),
		.OPT_MAXDEPTH(1)
		// }}}
	) fmemi(
		// {{{
		.i_clk(i_clk),
		.i_sys_reset(i_reset),
		.i_cpu_reset(i_reset),
		.i_stb(i_stb),
		.i_pipe_stalled(o_busy),
		.i_clear_cache(1'b0),
		.i_lock(i_lock),
		.i_op(i_op), .i_addr(i_addr), .i_data(i_data), .i_oreg(i_oreg),
		.i_areg(f_areg),
		.i_busy(o_busy),
		.i_rdbusy(f_rdbusy),
		.i_valid(o_valid), .i_done(f_done), .i_err(o_err),
		.i_wreg(o_wreg), .i_result(o_result),
		.f_outstanding(cpu_outstanding),
		.f_pc(f_pc),
		.f_gie(f_gie),
		.f_read_cycle(f_read_cycle),
		.f_last_reg(f_last_reg), .f_addr_reg(f_addr_reg)
		// }}}
	);

	always @(*)
	if (!o_err)
		assert(cpu_outstanding == f_outstanding + (f_stb ? 1:0)
					+ ((f_done || o_err) ? 1:0));

	always @(*)
		assert(cpu_outstanding <= 1);

	always @(*)
	if (f_pc)
	begin
		assert(o_wreg[3:1] == 3'h7);
	end else if (f_rdbusy)
		assert(o_wreg[3:1] != 3'h7);

	always @(*)
	if (o_busy)
		assert(o_wreg[4] == f_gie);

	always @(*)
	if (!o_err)
		assert(f_rdbusy == o_rdbusy);

	always @(*)
	if (o_busy)
		assert(o_wb_we == !f_read_cycle);

	always @(*)
	if (cpu_outstanding > 0)
		assert(f_last_reg == o_wreg);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Tying the two together
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Following any i_stb request, assuming we are idle, immediately
	// begin a bus transaction
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_stb))
		&&(!$past(f_cyc))&&(!$past(i_reset)))
	begin
		if ($past(misaligned))
		begin
			`ASSERT(!f_cyc);
			`ASSERT(!o_busy);
			`ASSERT(o_err);
			`ASSERT(!o_valid);
		end else begin
			`ASSERT(f_cyc);
			`ASSERT(o_busy);
		end
	end

//	always @(posedge i_clk)
//	if (o_busy)
//		`ASSUME(!i_stb);

	always @(*)
	if (o_err || o_valid)
		`ASSERT(!o_busy);

	always @(posedge i_clk)
	if (o_wb_cyc_gbl)
		`ASSERT((o_busy)||(lock_gbl));

	always @(posedge i_clk)
	if (o_wb_cyc_lcl)
		`ASSERT((o_busy)||(lock_lcl));

	always @(posedge i_clk)
	if (f_outstanding > 0)
		`ASSERT(o_busy);

	// If a transaction ends in an error, send o_err on the output port.
	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset))
	begin
		if (($past(f_cyc))&&($past(i_wb_err)))
		begin
			`ASSERT(o_err);
		end else if ($past(misaligned))
			`ASSERT(o_err);
	end

	// Always following a successful ACK, return an O_VALID value.
	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset))
	begin
		if(($past(f_cyc))&&($past(i_wb_ack))
				&&(!$past(o_wb_we)))
		begin
			`ASSERT(o_valid);
		end else if ($past(misaligned))
		begin
			`ASSERT((!o_valid)&&(o_err));
		end else
			`ASSERT(!o_valid);
	end

	always @(posedge i_clk)
	if (i_stb)
	begin
		fcpu_op   <= i_op;
		fcpu_addr <= i_addr;
		fcpu_data <= i_data;
	end

	always @(*)
	begin
		fcpu_local = (&fcpu_addr[31:24]) && WITH_LOCAL_BUS;

		if (OPT_LITTLE_ENDIAN)
		begin
			// {{{
			casez(fcpu_op[2:1])
			2'b11: fpre_sel = { {(BUS_WIDTH/8-1){1'b0}}, 1'b1 };
			2'b10: fpre_sel = { {(BUS_WIDTH/8-2){1'b0}}, 2'b11 };
			2'b0?: fpre_sel = { {(BUS_WIDTH/8-4){1'b0}}, 4'b1111 };
			endcase

			casez(fcpu_op[2:1])
			2'b11: fpre_data = { {(BUS_WIDTH- 8){1'b0}}, fcpu_data[ 7:0] };
			2'b10: fpre_data = { {(BUS_WIDTH-16){1'b0}}, fcpu_data[15:0] };
			2'b0?: fpre_data = { {(BUS_WIDTH-32){1'b0}}, fcpu_data[31:0] };
			endcase
			// }}}
		end else if (fcpu_local)
		begin
			// {{{
			fpre_sel = 0;
			casez(fcpu_op[2:1])
			2'b11: fpre_sel[3:0] = 4'b1000;
			2'b10: fpre_sel[3:0] = 4'b1100;
			2'b0?: fpre_sel[3:0] = 4'b1111;
			endcase

			fpre_data = 0;
			casez(fcpu_op[2:1])
			2'b11: fpre_data[31:0] = { fcpu_data[ 7:0], {(24){1'b0}} };
			2'b10: fpre_data[31:0] = { fcpu_data[15:0], {(16){1'b0}} };
			2'b0?: fpre_data[31:0] = fcpu_data[31:0];
			endcase
			// }}}
		end else begin
			// {{{
			casez(fcpu_op[2:1])
			2'b11: fpre_sel = { 1'b1,    {(BUS_WIDTH/8-1){1'b0}} };
			2'b10: fpre_sel = { 2'b11,   {(BUS_WIDTH/8-2){1'b0}} };
			2'b0?: fpre_sel = { 4'b1111, {(BUS_WIDTH/8-4){1'b0}} };
			endcase

			casez(fcpu_op[2:1])
			2'b11: fpre_data = { fcpu_data[ 7:0], {(BUS_WIDTH- 8){1'b0}} };
			2'b10: fpre_data = { fcpu_data[15:0], {(BUS_WIDTH-16){1'b0}} };
			2'b0?: fpre_data = { fcpu_data[31:0], {(BUS_WIDTH-32){1'b0}} };
			endcase
			// }}}
		end


		casez({ fcpu_op[2:1], fcpu_addr[1:0] })
		4'b01?1: fcpu_misaligned = 1'b1; // Words must be halfword aligned
		4'b0110: fcpu_misaligned = 1'b1; // Words must be word aligned
		4'b10?1: fcpu_misaligned = 1'b1; // Halfwords must be aligned
		// 4'b11??: fcpu_misaligned <= 1'b0; Byte access are never misaligned
		default: fcpu_misaligned = 1'b0;
		endcase

		if (fcpu_local)
		begin
			fcpu_shift = fcpu_addr[1:0];
			if (OPT_LITTLE_ENDIAN)
			begin
				fbus_sel   = fpre_sel  << fcpu_shift;
				fbus_data  = fpre_data << (8*fcpu_shift);
			end else begin
				fbus_sel   = fpre_sel  >> (fcpu_shift + (DATA_WIDTH/8-4));
				fbus_data  = fpre_data >> (8*(fcpu_shift + (DATA_WIDTH/8-4)));
			end
		end else begin
			fcpu_shift = fcpu_addr[WBLSB-1:0];
			if (OPT_LITTLE_ENDIAN)
			begin
				fbus_sel  = fpre_sel  << fcpu_shift;
				fbus_data = fpre_data << (8*fcpu_shift);
			end else begin
				fbus_sel  = fpre_sel  >> fcpu_shift;
				fbus_data = fpre_data >> (8*fcpu_shift);
			end
		end

		if (!OPT_LOWPOWER)
		casez(fcpu_op[2:1])
		2'b11: fbus_data = {(BUS_WIDTH/ 8){fcpu_data[ 7:0] } };
		2'b10: fbus_data = {(BUS_WIDTH/16){fcpu_data[15:0] } };
		2'b0?: fbus_data = {(BUS_WIDTH/32){fcpu_data[31:0] } };
		endcase
	end

	always @(*)
	if (OPT_ALIGNMENT_ERR && fcpu_misaligned)
		assert(!o_valid && !f_cyc);

	always @(*)
	if (f_stb)
	begin
		if (fcpu_local)
		begin
			assert(o_wb_stb_lcl);
			assert(o_wb_addr == fcpu_addr[AW+1:2]);
		end else begin
			assert(o_wb_stb_gbl);
			assert(o_wb_addr == fcpu_addr[WBLSB +: AW]);
		end

		if (fcpu_op[0])
		begin
			`ASSERT(o_wb_we);
			`ASSERT(fcpu_misaligned || o_wb_sel  == fbus_sel);
			`ASSERT(fcpu_misaligned || o_wb_data == fbus_data);
		end else begin
			`ASSERT(!o_wb_we);
		end
	end

	always @(*)
	if (f_cyc)
		assert(o_wb_cyc_lcl == fcpu_local);

	initial	o_wb_we = 1'b0;
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_stb)))
	begin
		// On a write, assert o_wb_we should be true
		assert( $past(i_op[0]) == o_wb_we);
	end

	always @(posedge i_clk)
	if (o_wb_stb_lcl)
		`ASSERT(fcpu_local);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(misaligned)))
	begin
		`ASSERT(!o_wb_cyc_gbl);
		`ASSERT(!o_wb_cyc_lcl);
		`ASSERT(!o_wb_stb_gbl);
		`ASSERT(!o_wb_stb_lcl);
		`ASSERT(o_err);
	end

//	always @(posedge i_clk)
//	if ((!f_past_valid)||($past(i_reset)))
//		`ASSUME(!i_stb);

	always @(posedge i_clk)
	if ((f_past_valid)&&(OPT_LOCK)
			&&(!$past(i_reset))&&(!$past(i_wb_err))
			&&(!$past(misaligned))
			&&(!$past(lcl_stb))
			&&($past(i_lock))&&($past(lock_gbl)))
		assert(lock_gbl);

	always @(posedge i_clk)
	if ((f_past_valid)&&(OPT_LOCK)
			&&(!$past(i_reset))&&(!$past(i_wb_err))
			&&(!$past(misaligned))
			&&(!$past(lcl_stb))
			&&($past(o_wb_cyc_gbl))&&($past(i_lock))
			&&($past(lock_gbl)))
		assert(o_wb_cyc_gbl);

	always @(posedge i_clk)
	if ((f_past_valid)&&(OPT_LOCK)
			&&(!$past(i_reset))&&(!$past(i_wb_err))
			&&(!$past(misaligned))
			&&(!$past(gbl_stb))
			&&($past(o_wb_cyc_lcl))&&($past(i_lock))
			&&($past(lock_lcl)))
		assert(o_wb_cyc_lcl);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
		cover(i_wb_ack);

	// Cover a response on the same clock it is made
	always @(posedge i_clk)
		cover((o_wb_stb_gbl)&&(i_wb_ack));

	// Cover a response a clock later
	always @(posedge i_clk)
		cover((o_wb_stb_gbl)&&(i_wb_ack));

	always @(posedge i_clk)
		cover(f_done);

	always @(posedge i_clk)
		cover(f_done && !o_busy);

	generate if (WITH_LOCAL_BUS)
	begin

		// Same things on the local bus
		always @(posedge i_clk)
			cover((o_wb_cyc_lcl)&&(!o_wb_stb_lcl)&&(i_wb_ack));
		always @(posedge i_clk)
			cover((o_wb_stb_lcl)&&(i_wb_ack));

	end endgenerate
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, f_nacks, f_addr_reg };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
//
//
// Usage (from yosys):
//		(BFOR)	(!ZOI,ALIGN)	(ZOI,ALIGN)	(!ZOI,!ALIGN)
//	Cells	 230		226		281		225
//	  FDRE	 114		116		116		116
//	  LUT2	  17		 23		 76		 19
//	  LUT3	   9		 23		 17		 20
//	  LUT4	  15		  4		 11		 14
//	  LUT5	  18		 18		  7		 15
//	  LUT6	  33		 18		 54		 38
//	  MUX7	  16		 12		  		  2
//	  MUX8	   8		  1				  1
//
//
