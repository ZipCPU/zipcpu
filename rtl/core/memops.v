////////////////////////////////////////////////////////////////////////////////
//
// Filename:	memops.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU.
//
//	In the interests of code simplicity, this memory operator is 
//	susceptible to unknown results should a new command be sent to it
//	before it completes the last one.  Unpredictable results might then
//	occurr.
//
//	20150919 -- Added support for handling BUS ERR's (i.e., the WB
//		error signal).
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017, Gisselquist Technology, LLC
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
module	memops(i_clk, i_rst, i_stb, i_lock,
		i_op, i_addr, i_data, i_oreg,
			o_busy, o_valid, o_err, o_wreg, o_result,
		o_wb_cyc_gbl, o_wb_cyc_lcl,
			o_wb_stb_gbl, o_wb_stb_lcl,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
		i_wb_ack, i_wb_stall, i_wb_err, i_wb_data);
	parameter	ADDRESS_WIDTH=30;
	parameter [0:0]	IMPLEMENT_LOCK=1'b0,
			WITH_LOCAL_BUS=1'b0;
	localparam	AW=ADDRESS_WIDTH;
	input	wire		i_clk, i_rst;
	input	wire		i_stb, i_lock;
	// CPU interface
	input	wire	[2:0]	i_op;
	input	wire	[31:0]	i_addr;
	input	wire	[31:0]	i_data;
	input	wire	[4:0]	i_oreg;
	// CPU outputs
	output	wire		o_busy;
	output	reg		o_valid;
	output	reg		o_err;
	output	reg	[4:0]	o_wreg;
	output	reg	[31:0]	o_result;
	// Wishbone outputs
	output	wire		o_wb_cyc_gbl;
	output	reg		o_wb_stb_gbl;
	output	wire		o_wb_cyc_lcl;
	output	reg		o_wb_stb_lcl;
	output	reg		o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	reg	[31:0]	o_wb_data;
	output	reg	[3:0]	o_wb_sel;
	// Wishbone inputs
	input	wire		i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[31:0]	i_wb_data;

	reg	r_wb_cyc_gbl, r_wb_cyc_lcl;
	wire	gbl_stb, lcl_stb;
	assign	lcl_stb = (i_stb)&&(WITH_LOCAL_BUS!=0)&&(i_addr[31:24]==8'hff);
	assign	gbl_stb = (i_stb)&&((WITH_LOCAL_BUS==0)||(i_addr[31:24]!=8'hff));

	initial	r_wb_cyc_gbl = 1'b0;
	initial	r_wb_cyc_lcl = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
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
		end else if (i_stb) // New memory operation
		begin // Grab the wishbone
			r_wb_cyc_lcl <= lcl_stb;
			r_wb_cyc_gbl <= gbl_stb;
		end
	always @(posedge i_clk)
		if (o_wb_cyc_gbl)
			o_wb_stb_gbl <= (o_wb_stb_gbl)&&(i_wb_stall);
		else
			o_wb_stb_gbl <= gbl_stb; // Grab wishbone on new operation
	always @(posedge i_clk)
		if (o_wb_cyc_lcl)
			o_wb_stb_lcl <= (o_wb_stb_lcl)&&(i_wb_stall);
		else
			o_wb_stb_lcl  <= lcl_stb; // Grab wishbone on new operation

	reg	[3:0]	r_op;
	always @(posedge i_clk)
		if (i_stb)
		begin
			o_wb_we   <= i_op[0];
			casez({ i_op[2:1], i_addr[1:0] })
`ifdef	ZERO_ON_IDLE
			4'b100?: o_wb_data <= { i_data[15:0], 16'h00 };
			4'b101?: o_wb_data <= { 16'h00, i_data[15:0] };
			4'b1100: o_wb_data <= {         i_data[7:0], 24'h00 };
			4'b1101: o_wb_data <= {  8'h00, i_data[7:0], 16'h00 };
			4'b1110: o_wb_data <= { 16'h00, i_data[7:0],  8'h00 };
			4'b1111: o_wb_data <= { 24'h00, i_data[7:0] };
`else
			4'b10??: o_wb_data <= { (2){ i_data[15:0] } };
			4'b11??: o_wb_data <= { (4){ i_data[7:0] } };
`endif
			default: o_wb_data <= i_data;
			endcase

			o_wb_addr <= i_addr[(AW+1):2];
`ifdef	SET_SEL_ON_READ
			if (i_op[0] == 1'b0)
				o_wb_sel <= 4'hf;
			else
`endif
			casez({ i_op[2:1], i_addr[1:0] })
			4'b01??: o_wb_sel <= 4'b1111;
			4'b100?: o_wb_sel <= 4'b1100;
			4'b101?: o_wb_sel <= 4'b0011;
			4'b1100: o_wb_sel <= 4'b1000;
			4'b1101: o_wb_sel <= 4'b0100;
			4'b1110: o_wb_sel <= 4'b0010;
			4'b1111: o_wb_sel <= 4'b0001;
			default: o_wb_sel <= 4'b1111;
			endcase
			r_op <= { i_op[2:1] , i_addr[1:0] };
		end
`ifdef	ZERO_ON_IDLE
		else if ((!o_wb_cyc_gbl)&&(!o_wb_cyc_lcl))
		begin
			o_wb_we   <= 1'b0;
			o_wb_addr <= 0;
			o_wb_data <= 32'h0;
			o_wb_sel  <= 4'h0;
		end
`endif

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
		o_valid <= (!i_rst)&&((o_wb_cyc_gbl)||(o_wb_cyc_lcl))&&(i_wb_ack)&&(~o_wb_we);
	initial	o_err = 1'b0;
	always @(posedge i_clk)
		o_err <= (!i_rst)&&((o_wb_cyc_gbl)||(o_wb_cyc_lcl))&&(i_wb_err);
	assign	o_busy = (o_wb_cyc_gbl)||(o_wb_cyc_lcl);

	always @(posedge i_clk)
		if (i_stb)
			o_wreg    <= i_oreg;
	always @(posedge i_clk)
`ifdef	ZERO_ON_IDLE
		if (!i_wb_ack)
			o_result <= 32'h0;
		else
`endif
		casez(r_op)
		4'b01??: o_result <= i_wb_data;
		4'b100?: o_result <= { 16'h00, i_wb_data[31:16] };
		4'b101?: o_result <= { 16'h00, i_wb_data[15: 0] };
		4'b1100: o_result <= { 24'h00, i_wb_data[31:24] };
		4'b1101: o_result <= { 24'h00, i_wb_data[23:16] };
		4'b1110: o_result <= { 24'h00, i_wb_data[15: 8] };
		4'b1111: o_result <= { 24'h00, i_wb_data[ 7: 0] };
		default: o_result <= i_wb_data;
		endcase

	generate
	if (IMPLEMENT_LOCK != 0)
	begin
		reg	lock_gbl, lock_lcl;

		initial	lock_gbl = 1'b0;
		initial	lock_lcl = 1'b0;

		always @(posedge i_clk)
		begin
			lock_gbl <= (i_lock)&&((r_wb_cyc_gbl)||(lock_gbl));
			lock_lcl <= (i_lock)&&((r_wb_cyc_lcl)||(lock_lcl));
		end

		assign	o_wb_cyc_gbl = (r_wb_cyc_gbl)||(lock_gbl);
		assign	o_wb_cyc_lcl = (r_wb_cyc_lcl)||(lock_lcl);
	end else begin
		assign	o_wb_cyc_gbl = (r_wb_cyc_gbl);
		assign	o_wb_cyc_lcl = (r_wb_cyc_lcl);
	end endgenerate


	// Make verilator happy
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = i_lock;
	// verilator lint_on  UNUSED


endmodule
