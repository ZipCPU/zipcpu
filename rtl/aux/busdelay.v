////////////////////////////////////////////////////////////////////////////////
//
// Filename:	busdelay.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Delay any access to the wishbone bus by a single clock.
//
//	When the first Zip System would not meet the timing requirements of
//	the board it was placed upon, this bus delay was added to help out.
//	It may no longer be necessary, having cleaned some other problems up
//	first, but it will remain here as a means of alleviating timing
//	problems.
//
//	The specific problem takes place on the stall line: a wishbone master
//	*must* know on the first clock whether or not the bus will stall.
//
//
//	After a period of time, I started a new design where the timing
//	associated with this original bus clock just wasn't ... fast enough.
//	I needed to delay the stall line as well.  A new busdelay was then
//	written and debugged whcih delays the stall line.  (I know, you aren't
//	supposed to delay the stall line--but what if you *have* to in order
//	to meet timing?)  This new logic has been merged in with the old,
//	and the DELAY_STALL line can be set to non-zero to use it instead
//	of the original logic.  Don't use it if you don't need it: it will
//	consume resources and slow your bus down more, but if you do need
//	it--don't be afraid to use it.  
//
//	Both versions of the bus delay will maintain a single access per
//	clock when pipelined, they only delay the time between the strobe
//	going high and the actual command being accomplished.
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
module	busdelay(i_clk,
		// The input bus
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
		// The delayed bus
		o_dly_cyc, o_dly_stb, o_dly_we, o_dly_addr,o_dly_data,o_dly_sel,
			i_dly_ack, i_dly_stall, i_dly_data, i_dly_err);
	parameter	AW=32, DW=32, DELAY_STALL = 0;
	input	wire			i_clk;
	// Input/master bus
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[(AW-1):0]	i_wb_addr;
	input	wire	[(DW-1):0]	i_wb_data;
	input	wire	[(DW/8-1):0]	i_wb_sel;
	output	reg			o_wb_ack;
	output	wire			o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;
	output	wire			o_wb_err;
	// Delayed bus
	output	reg			o_dly_cyc, o_dly_stb, o_dly_we;
	output	reg	[(AW-1):0]	o_dly_addr;
	output	reg	[(DW-1):0]	o_dly_data;
	output	reg	[(DW/8-1):0]	o_dly_sel;
	input	wire			i_dly_ack;
	input	wire			i_dly_stall;
	input	wire	[(DW-1):0]	i_dly_data;
	input	wire			i_dly_err;

	generate
	if (DELAY_STALL != 0)
	begin
		reg	r_stb, r_we, r_rtn_stall, r_rtn_err;
		reg	[(AW-1):0]	r_addr;
		reg	[(DW-1):0]	r_data;
		reg	[(DW/8-1):0]	r_sel;

		initial	o_dly_cyc  = 1'b0;
		initial	r_rtn_stall= 1'b0;
		initial	r_stb      = 1'b0;
		always @(posedge i_clk)
		begin
			o_dly_cyc <= (i_wb_cyc);
	
			if (!i_dly_stall)
			begin
				r_we   <= i_wb_we;
				r_addr <= i_wb_addr;
				r_data <= i_wb_data;
				r_sel  <= i_wb_sel;

				if (r_stb)
				begin
					o_dly_we   <= r_we;
					o_dly_addr <= r_addr;
					o_dly_data <= r_data;
					o_dly_sel  <= r_sel;
					o_dly_stb  <= 1'b1;
				end else begin
					o_dly_we   <= i_wb_we;
					o_dly_addr <= i_wb_addr;
					o_dly_data <= i_wb_data;
					o_dly_sel  <= i_wb_sel;
					o_dly_stb  <= i_wb_stb;
				end

				r_stb <= 1'b0;
			end else if (!o_dly_stb)
			begin
				o_dly_we   <= i_wb_we;
				o_dly_addr <= i_wb_addr;
				o_dly_data <= i_wb_data;
				o_dly_sel  <= i_wb_sel;
				o_dly_stb  <= i_wb_stb;
			end else if ((!r_stb)&&(!o_wb_stall))
			begin
				r_we   <= i_wb_we;
				r_addr <= i_wb_addr;
				r_data <= i_wb_data;
				r_sel  <= i_wb_sel;
				r_stb  <= i_wb_stb;
			end

			if (!i_wb_cyc)
			begin
				o_dly_stb <= 1'b0;
				r_stb <= 1'b0;
			end

			o_wb_ack  <= (i_dly_ack)&&(i_wb_cyc)&&(o_dly_cyc);
			o_wb_data <= i_dly_data;
			r_rtn_err <= (i_dly_err)&&(i_wb_cyc)&&(o_dly_cyc);
		end

		assign	o_wb_stall = r_stb;
		assign	o_wb_err   = r_rtn_err;

	end else begin

		initial	o_dly_cyc = 1'b0;
		initial	o_dly_stb = 1'b0;

		always @(posedge i_clk)
			o_dly_cyc <= i_wb_cyc;
		// Add the i_wb_cyc criteria here, so we can simplify the
		// o_wb_stall criteria below, which would otherwise *and*
		// these two.
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_dly_stb <= ((i_wb_cyc)&&(i_wb_stb));
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_dly_we  <= i_wb_we;
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_dly_addr<= i_wb_addr;
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_dly_data <= i_wb_data;
		always @(posedge i_clk)
			if (!o_wb_stall)
				o_dly_sel <= i_wb_sel;
		always @(posedge i_clk)
			o_wb_ack  <= (i_dly_ack)&&(o_dly_cyc)&&(i_wb_cyc);
		always @(posedge i_clk)
			o_wb_data <= i_dly_data;

		// Our only non-delayed line, yet still really delayed.  Perhaps
		// there's a way to register this?
		// o_wb_stall <= (i_wb_cyc)&&(i_wb_stb) ... or some such?
		// assign o_wb_stall=((i_wb_cyc)&&(i_dly_stall)&&(o_dly_stb));//&&o_cyc
		assign	o_wb_stall = ((i_dly_stall)&&(o_dly_stb));//&&o_cyc
		assign	o_wb_err   = i_dly_err;
	end endgenerate

endmodule
