////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_s2mm.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Writes data, having gone through the realignment
//		pipeline, back to the bus.  This data will be written either
//	1, 2, or 4 bytes at a time, or at the full width of the bus.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	zipdma_s2mm #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	BUS_WIDTH = 512,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter	LGPIPE = 10,
		// Abbreviations
		localparam	DW = BUS_WIDTH,
		localparam	AW = ADDRESS_WIDTH-$clog2(DW/8)
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Configuration
		// {{{
		input	wire			i_request,
		output	reg			o_busy, o_err,
		input	wire			i_inc,
		input	wire	[1:0]		i_size,
		// input wire	[LGLENGTH:0]	i_transferlen,
		input wire [ADDRESS_WIDTH-1:0]	i_addr,	// Byte address
		// }}}
		// Incoming Stream interface
		// {{{
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[DW-1:0]	S_DATA,
		// How many bytes are valid?
		input	wire [$clog2(DW/8):0]	S_BYTES,
		input	wire			S_LAST,
		// }}}
		// Outgoing Wishbone interface
		// {{{
		output	reg			o_wr_cyc, o_wr_stb,
		output	wire			o_wr_we,
		output	reg	[AW-1:0]	o_wr_addr,
		output	reg	[DW-1:0]	o_wr_data,
		output	reg	[DW/8-1:0]	o_wr_sel,
		input	wire			i_wr_stall,
		input	wire			i_wr_ack,
		input	wire	[DW-1:0]	i_wr_data,
		input	wire			i_wr_err
		// }}}
		// }}}
	);

	// Local decalarations
	// {{{
	localparam			WBLSB = $clog2(DW/8);
	reg	[ADDRESS_WIDTH-1:0]	next_addr;
	reg	[WBLSB-1:0]		subaddr;
	reg	[2*DW-1:0]		next_data;
	reg	[DW-1:0]		r_data;
	reg	[2*DW/8-1:0]		next_sel, pre_sel;
	reg	[DW/8-1:0]		r_sel;
	reg				r_last;

	reg	[LGPIPE-1:0]		wb_outstanding;
	reg				wb_pipeline_full;
	// }}}

	assign	o_wr_we = 1'b1;

	// next_addr
	// {{{
	always @(*)
	begin
		next_addr = { o_wr_addr, subaddr };

		case(i_size)
		2'b11: begin end
		2'b10: next_addr[  0] = 0;
		2'b01: next_addr[1:0] = 0;
		2'b00: next_addr[$clog2(DW/8)-1:0] = 0;
		endcase

		if (i_inc)
		case(i_size)
		2'b11: next_addr = next_addr + 1;
		2'b10: next_addr = next_addr + 2;
		2'b01: next_addr = next_addr + 4;
		2'b00: next_addr = next_addr + { {(AW-1){1'b0}}, 1'b1,
				{($clog2(DW/8)){1'b0}} };
		endcase

		if (!o_wr_stb || i_wr_stall)
			next_addr = { o_wr_addr, subaddr };
	end
	// }}}

	// next_data
	// {{{
	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		next_data = { {(DW){1'b0}}, r_data };
		if (S_VALID && !r_last)
			next_data = next_data | ({{(DW){1'b0}}, S_DATA }
					<< (next_addr[WBLSB-1:0]*8));
	end else begin
		next_data = { r_data, {(DW){1'b0}} };
		if (S_VALID && !r_last)
			next_data = next_data | ({ S_DATA, {(DW){1'b0}} }
					>> (next_addr[WBLSB-1:0]*8));
	end
	// }}}

	// next_sel
	// {{{
	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		pre_sel = 0;
		pre_sel[DW/8-1:0] = (1 << S_BYTES)-1;
		next_sel = { {(DW/8){1'b0}}, r_sel };
		if (S_VALID && !r_last)
			next_sel = next_sel | (pre_sel
					<< (next_addr[WBLSB-1:0]));
	end else begin
		pre_sel = 0;
		pre_sel[DW/8-1:0] = (1 << S_BYTES)-1;
		pre_sel[DW/8-1:0] = pre_sel[DW/8-1:0]
				<< ({1'b1,{(WBLSB){1'b0}}} - S_BYTES);

		next_sel = { r_sel, {(DW/8){1'b0}} };
		if (S_VALID && !r_last)
			next_sel = next_sel | (pre_sel
					>> (next_addr[WBLSB-1:0]));
	end
	// }}}

	// wb_pipeline_full, wb_outstanding
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_wr_cyc || i_wr_err)
	begin
		wb_pipeline_full <= 1'b0;
		wb_outstanding   <= 0;
	end else case({ (o_wr_stb && !i_wr_stall), i_wr_ack })
	2'b10:	begin
		wb_pipeline_full <= (&wb_outstanding[LGPIPE-1:1]);
		wb_outstanding <= wb_outstanding + 1;
		end
	2'b01: begin
		wb_pipeline_full <= (&wb_outstanding[LGPIPE-1:0]);
		wb_outstanding <= wb_outstanding - 1;
		end
	default: begin end
	endcase
	// }}}

	always @(posedge i_clk)
	if (i_reset || i_reset)
	begin
		// {{{
		o_wr_cyc  <= 0;
		o_wr_stb  <= 0;
		o_wr_addr <= 0;
		o_wr_data <= 0;
		o_wr_sel  <= 0;

		o_busy <= 1'b0;
		o_err  <= 1'b0;
		{ o_wr_addr, subaddr } <= {(ADDRESS_WIDTH){1'b0}};
		{ r_data, o_wr_data  } <= {(2*DW  ){1'b0}};
		{ r_sel,  o_wr_sel   } <= {(2*DW/8){1'b0}};
		r_last <= 1'b0;
		// }}}
	end else if (!o_busy || o_err || (o_wr_cyc && i_wr_err))
	begin
		// {{{
		o_wr_cyc  <= 0;
		o_wr_stb  <= 0;
		o_wr_addr <= 0;
		o_wr_data <= 0;
		o_wr_sel  <= 0;

		o_busy <= i_request && !o_err && S_VALID && !o_busy;

		if (o_busy && o_wr_cyc && i_wr_err)
		begin
			o_err  <= 1'b1;
			o_busy <= 1'b0;
		end else if (i_request && !o_busy)
			o_err <= 1'b0;

		o_wr_addr <= i_addr[ADDRESS_WIDTH-1:WBLSB];
		subaddr   <= i_addr[WBLSB-1:0];
		{ r_data, o_wr_data } <= {(2*DW  ){1'b0}};
		{ r_sel,  o_wr_sel  } <= {(2*DW/8){1'b0}};
		r_last <= 1'b0;
		// }}}
	end else if (!o_wr_stb || !i_wr_stall)
	begin
		// {{{
		o_wr_stb <= 1'b0;

		{ o_wr_addr, subaddr } <= next_addr;

		if (OPT_LITTLE_ENDIAN)
		begin
			{ r_data, o_wr_data } <= next_data;
			{ r_sel,  o_wr_sel  } <= next_sel;
		end else begin
			{ o_wr_data, r_data } <= next_data;
			{ o_wr_sel,  r_sel  } <= next_sel;
		end

		if (!wb_pipeline_full)
		begin
			if (r_last && (|r_sel))
				// Need to flush our last result out
				{ o_wr_cyc, o_wr_stb } <= 2'b11;
			else if (S_VALID && !r_last)
				// Issue a new write request for the next value
				{ o_wr_cyc, o_wr_stb } <= 2'b11;
			else if (wb_outstanding == (i_wr_ack ? 1:0))
			begin
				// We are all done writing
				o_wr_cyc <= 1'b0;
				o_busy <= !r_last;
			end
		end

		if (S_VALID && !r_last)
			r_last <= S_LAST;
		// }}}
	end

	assign	S_READY = !r_last && o_busy && (!o_wr_stb || !i_wr_stall)
				&& !wb_pipeline_full;

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wr_data };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
