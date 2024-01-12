////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_mm2s.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Read values from memory
//
//	This is the first component of the DMA sequence.  It reads values from
//	memory, and aligns them with an outgoing data stream.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022-2023, Gisselquist Technology, LLC
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
module	zipdma_mm2s #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	BUS_WIDTH = 64,
		parameter	LGLENGTH=10,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
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
		input	wire	[LGLENGTH:0]	i_transferlen,
		input wire [ADDRESS_WIDTH-1:0]	i_addr,	// Byte address
		// }}}
		// Wishbone master interface
		// {{{
		output	reg			o_rd_cyc, o_rd_stb,
		// Verilator coverage_off
		output	wire			o_rd_we,
		// Verilator coverage_on
		output	reg	[AW-1:0]	o_rd_addr,
		// Verilator coverage_off
		output	wire	[DW-1:0]	o_rd_data,
		// Verilator coverage_on
		output	reg	[DW/8-1:0]	o_rd_sel,
		input	wire			i_rd_stall,
		input	wire			i_rd_ack,
		input	wire	[DW-1:0]	i_rd_data,
		input	wire			i_rd_err,
		// }}}
		// Outgoing Stream interface
		// {{{
		output	wire			M_VALID,
		input	wire			M_READY,	// *MUST* be 1
		output	wire	[DW-1:0]	M_DATA,
		// How many bytes are valid?
		output	wire [$clog2(DW/8):0]	M_BYTES,
		output	wire			M_LAST
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam [1:0]	SZ_BYTE = 2'b11,
				SZ_16B  = 2'b10,
				SZ_32B  = 2'b01,
				SZ_BUS  = 2'b00;
	localparam	WBLSB = $clog2(DW/8);
	reg	[WBLSB:0]	nxtstb_size, rdstb_size, rdack_size, first_size;
	reg	[ADDRESS_WIDTH-1:0]	next_addr, last_request_addr;
	reg	[WBLSB-1:0]	subaddr, rdack_subaddr;
	reg	[DW/8-1:0]	nxtstb_sel, first_sel, base_sel, ibase_sel;
	reg	[LGLENGTH:0]	wb_outstanding;

	reg	[WBLSB+1:0]	fill, next_fill;

	reg			m_valid, m_last;
	reg	[DW-1:0]	sreg;
	reg	[WBLSB:0]	m_bytes;

	reg	[LGLENGTH:0]	rdstb_len, rdack_len;

	reg	[WBLSB-1:0]	pre_shift;
	reg	[DW-1:0]	pre_shifted_data;

	reg			r_inc;
	reg	[1:0]		r_size;
	// }}}

	assign	o_rd_we = 1'b0;
	assign	o_rd_data = {(DW){1'b0}};

	// Copy the configuration whenever i_request && !o_busy
	// {{{
	always @(posedge i_clk)
	if (!o_busy && (!OPT_LOWPOWER || i_request))
	begin
		r_inc  <= i_inc;
		r_size <= i_size;
		// r_transferlen <= i_transferlen;
		// r_addr <= i_addr;
	end
	// }}}

	// nxtstb_size
	// {{{
	generate if (BUS_WIDTH > 32)
	begin : GEN_NXTSTB_SIZE
		// {{{
		always @(*)
		begin
			first_size = 0;
			case(i_size)
			SZ_BYTE: first_size = 1;
			SZ_16B:  first_size = (i_addr[0]) ? 1:2;
			// Verilator lint_off WIDTH
			SZ_32B:  first_size = 4 - i_addr[1:0];
			SZ_BUS:  first_size = (DW/8)-i_addr[WBLSB-1:0];
			endcase

			if (first_size > i_transferlen)
				first_size = i_transferlen;
		end

		always @(*)
		begin
			nxtstb_size = rdstb_size;

			case(r_size)
			SZ_BYTE: nxtstb_size = 1;
			SZ_16B: nxtstb_size = (rdstb_len == 3) ? 1 : 2;
			// Verilator lint_off WIDTH
			SZ_32B: nxtstb_size = (rdstb_len >= 4 && rdstb_len < 8)
						? (rdstb_len - 4) : 4;
			SZ_BUS: begin
				nxtstb_size = (DW/8);
				if (DW/8 > rdstb_len - rdstb_size)
					nxtstb_size =
						{ 1'b0, rdstb_len[WBLSB:0] }
						-{ 1'b0, rdstb_size[WBLSB:0]};
				// if (o_rd_stb && nxtstb_size > (DW/8)-subaddr)
				//	nxtstb_size = (DW/8)-subaddr;
				end
			// Verilator lint_on  WIDTH
			endcase
		end
		// }}}
	end else begin : STD_NXTSTB_SIZE
		// {{{
		always @(*)
		begin
			first_size = 0;
			case(i_size)
			SZ_BYTE: first_size = 1;
			SZ_16B:  first_size = (i_addr[0]) ? 1:2;
			// Verilator lint_off WIDTH
			default:
				first_size = (DW/8)-i_addr[WBLSB-1:0];
			endcase

			if (first_size > i_transferlen)
				first_size = i_transferlen;
			// Verilator lint_on  WIDTH
		end

		always @(*)
		begin
			nxtstb_size = rdstb_size;

			casez(r_size)
			SZ_BYTE: nxtstb_size = 1;
			SZ_16B: nxtstb_size = (rdstb_len == 3) ? 1 : 2;
			default: begin
				// Verilator lint_off WIDTH
				nxtstb_size = (DW/8);
				if ((rdstb_len[LGLENGTH:WBLSB+1] == 0)
					    &&(rdstb_size + DW/8 > rdstb_len[WBLSB:0]))
					nxtstb_size =
						{ 1'b0, rdstb_len[WBLSB:0] }
						-{ 1'b0, rdstb_size[WBLSB:0]};
				end
				// Verilator lint_on  WIDTH
			endcase
		end
		// }}}
	end endgenerate
	// }}}

	// next_addr
	// {{{
	always @(*)
	begin
		next_addr = { o_rd_addr, subaddr };

		if (o_rd_stb && !i_rd_stall)
			next_addr = next_addr
			+ { {(ADDRESS_WIDTH-WBLSB-1){1'b0}}, rdstb_size };
	end
	// }}}

	// o_rd_cyc, o_rd_stb, o_busy, o_err, rdstb_len, rdstb_size
	// {{{
	initial	{ o_rd_cyc, o_rd_stb } = 2'b00;
	initial	{ o_busy, o_err } = 2'b00;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_rd_cyc <= 1'b0;
		o_rd_stb <= 1'b0;
		{ o_rd_addr, subaddr } <= 0;

		rdstb_size <= 0;
		rdstb_len  <= 0;
		o_busy     <= 0;
		o_err      <= 0;
		// }}}
	end else if (o_rd_cyc && i_rd_err)
	begin
		// {{{
		o_rd_cyc <= 1'b0;
		o_rd_stb <= 1'b0;
		{ o_rd_addr, subaddr } <= 0;

		rdstb_size <= 0;
		rdstb_len  <= 0;

		o_busy <= 0;
		o_err  <= 1;
		// }}}
	end else if (!o_busy)
	begin
		// {{{
		o_rd_cyc <= i_request;
		o_rd_stb <= i_request;
		o_busy   <= i_request;
		o_err    <= 0;

		rdstb_size <= 0;
		rdstb_len  <= 0;
		if (!OPT_LOWPOWER || i_request)
		begin
			{ o_rd_addr, subaddr } <= i_addr;

			// rdstb_size
			rdstb_size <= first_size;

			// rdstb_len
			rdstb_len <= i_transferlen;
		end
		// }}}
	end else begin
		if (!i_rd_stall)
			o_rd_stb <= 1'b0;

		if (rdstb_len > { {(LGLENGTH-WBLSB){1'b0}}, rdstb_size })
			o_rd_stb <= 1'b1;

		if (o_rd_stb && !i_rd_stall)
		begin
			// {{{
			if (rdstb_len <= { {(LGLENGTH-WBLSB){1'b0}}, rdstb_size })
			begin
				rdstb_len <= 0;
			end else begin
				rdstb_len <= rdstb_len
					- { {(LGLENGTH-WBLSB){1'b0}}, rdstb_size };
				o_rd_stb <= 1'b1;
			end

			// rdstb_size
			rdstb_size <= nxtstb_size;

			{ o_rd_addr, subaddr } <= next_addr;
			// }}}
		end

		if (wb_outstanding == (i_rd_ack ? 1:0) && !o_rd_stb)
			o_rd_cyc <= 1'b0;

		if (m_valid && m_last)
			o_busy <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (!o_busy)
	begin
		assert(!m_valid);
	end else if (m_valid && m_last)
	begin
		assert(rdack_len == 0);
		assert(fill == m_bytes);
	end

	always @(*)
	if (o_busy)
		assert(rdstb_len <= rdack_len);
`endif
	// }}}

	// o_rd_sel
	// {{{

	// ibase_sel
	generate if (BUS_WIDTH > 32)
	begin : GEN_STRB
		// {{{
		always @(*)
		begin
			ibase_sel = 0;

			if (OPT_LITTLE_ENDIAN)
			begin
				// {{{
				// Verilator coverage_off
				case(i_size)
				SZ_BYTE: ibase_sel = {{(DW/8-1){1'b0}}, 1'b1} << i_addr[WBLSB-1:0];
				SZ_16B: ibase_sel = {{(DW/8-2){1'b0}}, 2'h3} << {i_addr[WBLSB-1:1], 1'b0 };
				SZ_32B: ibase_sel = {{(DW/8-4){1'b0}}, 4'b1111} << {i_addr[WBLSB-1:2], 2'b0 };
				SZ_BUS: ibase_sel = {(DW/8){1'b1}};
				endcase
				// Verilator coverage_on
				// }}}
			end else begin
				// {{{
				case(i_size)
				SZ_BYTE: ibase_sel= {1'h1, {(DW/8-1){1'b0}} } >> i_addr[WBLSB-1:0];
				SZ_16B: ibase_sel = {2'h3, {(DW/8-2){1'b0}} } >> {i_addr[WBLSB-1:1], 1'b0 };
				SZ_32B: ibase_sel = {4'hf, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
				SZ_BUS: ibase_sel = {(DW/8){1'b1}};
				endcase
				// }}}
			end
		end
		// }}}
	end else begin : MIN_STRB
		// {{{
		always @(*)
		begin
			ibase_sel = 0;

			if (OPT_LITTLE_ENDIAN)
			begin
				// {{{
				// Verilator coverage_off
				case(i_size)
				SZ_BYTE: ibase_sel = {{(DW/8-1){1'b0}}, 1'b1} << i_addr[WBLSB-1:0];
				SZ_16B: ibase_sel = {{(DW/8-2){1'b0}}, 2'h3} << {i_addr[WBLSB-1:1], 1'b0 };
				default: ibase_sel = {(DW/8){1'b1}};
				endcase
				// Verilator coverage_on
				// }}}
			end else begin
				// {{{
				case(i_size)
				SZ_BYTE: ibase_sel= {1'h1, {(DW/8-1){1'b0}} } << i_addr[WBLSB-1:0];
				SZ_16B: ibase_sel = {2'h3, {(DW/8-2){1'b0}} } << {i_addr[WBLSB-1:1], 1'b0 };
				default: ibase_sel = {(DW/8){1'b1}};
				endcase
				// }}}
			end
		end
		// }}}
	end endgenerate

	always @(posedge i_clk)
	if (i_reset || (o_rd_cyc && i_rd_err))
	begin
		// {{{
		base_sel <= 0;
		// }}}
	end else if (!o_busy)
	begin
		base_sel <= 0;
		if (i_request || !OPT_LOWPOWER)
			base_sel <= ibase_sel;
	end else if (o_rd_stb && !i_rd_stall)
		base_sel <= nxtstb_sel;

	// nxtstb_sel
	// {{{
	generate if (DW == 32)
	begin : GEN_NXTSTB_SEL
		// {{{
		always @(*)
		if (OPT_LITTLE_ENDIAN)
		begin
			case(r_size)
			SZ_BYTE: nxtstb_sel = { base_sel[DW/8-2:0], base_sel[DW/8-1] };
			SZ_16B:  nxtstb_sel = { base_sel[DW/8-3:0], base_sel[DW/8-1:DW/8-2] };
			default:
				nxtstb_sel = {(DW/8){1'b1}};
			endcase

			if (!r_inc)
				nxtstb_sel = base_sel;
		end else begin
			case(r_size)
			SZ_BYTE: nxtstb_sel = { base_sel[0:0], base_sel[DW/8-1:1] };
			SZ_16B:  nxtstb_sel = { base_sel[1:0], base_sel[DW/8-1:2] };
			default:
				nxtstb_sel = {(DW/8){1'b1}};
			endcase

			if (!r_inc)
				nxtstb_sel = base_sel;
		end
		// }}}
	end else begin : GEN_WIDE_NXTSTB_SEL
		always @(*)
		if (OPT_LITTLE_ENDIAN)
		begin
			case(r_size)
			SZ_BYTE: nxtstb_sel = { base_sel[DW/8-2:0], base_sel[DW/8-1] };
			SZ_16B:  nxtstb_sel = { base_sel[DW/8-3:0], base_sel[DW/8-1:DW/8-2] };
			SZ_32B:  nxtstb_sel = { base_sel[DW/8-5:0], base_sel[DW/8-1:DW/8-4] };
			SZ_BUS:  nxtstb_sel = {(DW/8){1'b1}};
			endcase

			if (!r_inc)
				nxtstb_sel = base_sel;
		end else begin
			case(r_size)
			SZ_BYTE: nxtstb_sel = { base_sel[0:0], base_sel[DW/8-1:1] };
			SZ_16B:  nxtstb_sel = { base_sel[1:0], base_sel[DW/8-1:2] };
			SZ_32B:  nxtstb_sel = { base_sel[3:0], base_sel[DW/8-1:4] };
			SZ_BUS:  nxtstb_sel = {(DW/8){1'b1}};
			endcase

			if (!r_inc)
				nxtstb_sel = base_sel;
		end
	end endgenerate
	// }}}

	// first_sel
	generate if (BUS_WIDTH > 32)
	begin : GEN_FIRST_SEL
		// {{{
		always @(*)
		begin
			first_sel = 0;

			if (OPT_LITTLE_ENDIAN)
			begin
				// {{{
				// Verilator coverage_off
				case(i_size)
				SZ_BYTE: first_sel = {{(DW/8-1){1'b0}}, 1'b1} << i_addr[WBLSB-1:0];
				SZ_16B: first_sel = {{(DW/8-2){1'b0}}, 1'b1,i_addr[0]} << {i_addr[WBLSB-1:1], 1'b0 };
				SZ_32B: case(i_addr[1:0])
					2'b00: first_sel = {{(DW/8-4){1'b0}}, 4'b1111} << {i_addr[WBLSB-1:2], 2'b0 };
					2'b01: first_sel = {{(DW/8-4){1'b0}}, 4'b1110} << {i_addr[WBLSB-1:2], 2'b0 };
					2'b10: first_sel = {{(DW/8-4){1'b0}}, 4'b1100} << {i_addr[WBLSB-1:2], 2'b0 };
					2'b11: first_sel = {{(DW/8-4){1'b0}}, 4'b1000} << {i_addr[WBLSB-1:2], 2'b0 };
					endcase
				SZ_BUS: first_sel = {(DW/8){1'b1}} << i_addr[WBLSB-1:0];
				endcase
				// Verilator coverage_on
				// }}}
			end else begin
				// {{{
				case(i_size)
				SZ_BYTE: first_sel = {1'b1, {(DW/8-1){1'b0}} } >> i_addr[WBLSB-1:0];
				SZ_16B: first_sel = {i_addr[0], 1'b1, {(DW/8-2){1'b0}} }
						>> {i_addr[WBLSB-1:1], 1'b0 };
				SZ_32B: case(i_addr[1:0])
					2'b00: first_sel = {4'b1111, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					2'b01: first_sel = {4'b0111, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					2'b10: first_sel = {4'b0011, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					2'b11: first_sel = {4'b0001, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					endcase
				SZ_BUS: first_sel = {(DW/8){1'b1}} >> i_addr[WBLSB-1:0];
				endcase
				// }}}
			end
		end
		// }}}
	end else begin : MIN_FIRST_SEL
		// {{{
		always @(*)
		begin
			first_sel = 0;

			if (OPT_LITTLE_ENDIAN)
			begin
				// {{{
				casez(i_size)
				SZ_BYTE: first_sel = 4'b0001 << i_addr[WBLSB-1:0];
				SZ_16B: first_sel = 4'b0011 << {i_addr[WBLSB-1:1], 1'b0 };
				default: case(i_addr[1:0])
					2'b00: first_sel = 4'b1111;
					2'b01: first_sel = 4'b1110;
					2'b10: first_sel = 4'b1100;
					2'b11: first_sel = 4'b1000;
					endcase
				endcase
				// }}}
			end else begin
				// {{{
				casez(i_size)
				SZ_BYTE: first_sel = 4'b1000 >> i_addr[WBLSB-1:0];
				SZ_16B: first_sel = 4'b1100
						>> {i_addr[WBLSB-1:1], 1'b0 };
				default: case(i_addr[1:0])
					2'b00: first_sel = 4'b1111;
					2'b01: first_sel = 4'b0111;
					2'b10: first_sel = 4'b0011;
					2'b11: first_sel = 4'b0001;
					endcase
				endcase
				// }}}
			end
		end
		// }}}
	end endgenerate

	// o_rd_sel
	always @(posedge i_clk)
	if (i_reset || (o_rd_cyc && i_rd_err))
	begin
		// {{{
		o_rd_sel   <= 0;
		// }}}
	end else if (!o_busy)
	begin
		// {{{
		o_rd_sel <= {(DW/8){1'b0}};

		if (!OPT_LOWPOWER || i_request)
			o_rd_sel <= first_sel;
		// }}}
	end else if (o_rd_stb && !i_rd_stall)
		o_rd_sel <= nxtstb_sel;
	// }}}

	// wb_outstanding
	// {{{
	initial	wb_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || !o_rd_cyc || i_rd_err)
		wb_outstanding <= 0;
		// wb_pipeline_full <= 1'b0;
	else case({ (o_rd_stb && !i_rd_stall), i_rd_ack })
	2'b10: wb_outstanding <= wb_outstanding + 1;
	2'b01: wb_outstanding <= wb_outstanding - 1;
	default: begin end
	endcase
	// }}}

	// rdack_subaddr
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
	begin
		if (!OPT_LOWPOWER || i_request)
			rdack_subaddr <= i_addr[WBLSB-1:0];
	end else if (i_rd_ack)
	begin
		// Verilator lint_off WIDTH
		if (r_inc)
			rdack_subaddr <= rdack_subaddr + rdack_size;
		else case(r_size)
		SZ_BYTE: begin end
		SZ_16B: rdack_subaddr[  0] <= 1'b0;
		SZ_32B: rdack_subaddr[1:0] <= 2'b0;
		SZ_BUS: rdack_subaddr[WBLSB-1:0] <= {(WBLSB){1'b0}};
		endcase
		// Verilator lint_on  WIDTH
	end
	// }}}

	// rdack_len
	// {{{
	// Total length remaining, from the perspective of the bus return.
	// Hence, on any bus return, we drop by the number of bytes valid
	// in that return, or minus rdack_size.
	always @(posedge i_clk)
	if (!o_busy)
	begin
		if (!OPT_LOWPOWER || i_request)
			rdack_len <= i_transferlen;
	end else if (i_rd_ack)
	begin
		rdack_len <= rdack_len-{ {(LGLENGTH-WBLSB){1'b0}}, rdack_size };
		if (rdack_len <= { {(LGLENGTH-WBLSB){1'b0}}, rdack_size })
			rdack_len <= 0;
	end
	// }}}

	// rdack_size
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
	begin
		if (!OPT_LOWPOWER || i_request)
			rdack_size <= first_size;
	end else if (i_rd_ack)
	begin
		case(r_size)
		SZ_BYTE:rdack_size <= 1;
		SZ_16B: rdack_size <= 2;
		SZ_32B: rdack_size <= 4;
		// Verilator lint_off WIDTH
		SZ_BUS: if (rdack_len > DW/8 + rdack_size)
				rdack_size <= DW/8;
			else
				rdack_size <= rdack_len - rdack_size;
		// Verilator lint_on  WIDTH
		endcase
	end
	// }}}

	// fill, next_fill (depends on rdack_size)
	// {{{
	always @(*)
	begin
		next_fill = fill;
		if (M_VALID)
			next_fill = 0; // next_fill - M_BYTES;
		if (i_rd_ack)
			next_fill = next_fill + { 1'b0, rdack_size };
	end

	always @(posedge i_clk)
	if (!o_busy)
		fill <= 0;
	else
		fill <= next_fill;
	// }}}

	// m_valid
	// {{{
	initial	m_valid = 0;
	always @(posedge i_clk)
	if (!o_busy)
		m_valid <= 1'b0;
	else begin
		// Verilator lint_off WIDTH
		m_valid <= 0;
		if ((!m_valid || !m_last) && rdack_len == 0 && fill > 0)
			m_valid <= 1;
		else if (o_rd_cyc && i_rd_ack)
			m_valid <= 1'b1; // ((next_fill >= DW/8)
			// || (rdack_len <= { {(LGLENGTH-1){1'b0}}, rdack_size }));
		// Verilator lint_on  WIDTH
	end
	// }}}

	// sreg
	// {{{
	initial	pre_shift = 0;
	always @(posedge i_clk)
	if (!o_busy)
	begin
		pre_shift <= 0;
		if (!OPT_LOWPOWER || i_request)
			pre_shift <= i_addr[WBLSB-1:0];
	end else if (o_rd_cyc && i_rd_ack)
	begin
		case(r_size)
		SZ_BYTE: pre_shift <= pre_shift + (r_inc ? 1 : 0);
		SZ_16B:  begin
			// {{{
			pre_shift <= pre_shift + (r_inc ? 2 : 0);
			pre_shift[0] <= 1'b0;
			end
			// }}}
		SZ_32B:  begin
			// {{{
			// Verilator lint_off WIDTH
			pre_shift <= pre_shift + (r_inc ? 4 : 0);
			// Verilator lint_on  WIDTH
			pre_shift[1:0] <= 2'b0;
			end
			// }}}
		SZ_BUS:  pre_shift <= 0;
		endcase
	end

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		pre_shifted_data = i_rd_data >> (8*pre_shift);
	else
		pre_shifted_data = i_rd_data << (8*pre_shift);

	initial	sreg = 0;
	always @(posedge i_clk)
	if (!o_busy)
		sreg <= 0;
	else if (o_rd_cyc && i_rd_ack)
	begin
		// {{{
		// Verilator lint_off WIDTH
		sreg <= pre_shifted_data;
		// Verilator lint_on  WIDTH
		// }}}
	end else if (m_valid)
	begin
		// {{{
		sreg <= {(DW){1'b0}};
		// }}}
	end
	// }}}

	// m_bytes
	// {{{
	initial	m_bytes = 0;
	always @(posedge i_clk)
	if (!o_busy)
	begin
		m_bytes <= 0;
	end else if (i_rd_ack)
	begin
		if (|next_fill[WBLSB+1:WBLSB]) // if next_fill >= DW/8)
			// Verilator lint_off WIDTH
			m_bytes <= DW/8;
			// Verilator lint_on  WIDTH
		else
			m_bytes <= { 1'b0, next_fill[WBLSB-1:0] };
	end else if (rdack_len == 0)
		m_bytes <= next_fill[WBLSB:0];
`ifdef	FORMAL
	always @(*)
	if (M_VALID)
		assert(M_BYTES <= DW/8);
`endif
	// }}}

	// m_last
	// {{{
	always @(*)
	begin
		last_request_addr = i_addr;
		if (r_inc)
			// Verilator lint_off WIDTH
			last_request_addr = i_addr + i_transferlen - 1;
			// Verilator lint_on  WIDTH
	end

	initial	m_last = 0;
	always @(posedge i_clk)
	if (!o_busy)
	begin
		m_last <= 1'b0;
		if (!OPT_LOWPOWER || i_request)
		case(i_size)
		SZ_BYTE: m_last <= (i_transferlen <= 1);
		SZ_16B: m_last <= (last_request_addr[ADDRESS_WIDTH-1:1] != i_addr[ADDRESS_WIDTH-1:1]);
		SZ_32B: m_last <= (last_request_addr[ADDRESS_WIDTH-1:2] != i_addr[ADDRESS_WIDTH-1:2]);
		SZ_BUS: m_last <= (last_request_addr[ADDRESS_WIDTH-1:WBLSB] != i_addr[ADDRESS_WIDTH-1:WBLSB]);
		endcase
	end else if (i_rd_ack)
	begin
		// Verilator lint_off WIDTH
		m_last <= (rdack_len <= rdack_size) && (next_fill <= DW/8);
		// Verilator lint_on  WIDTH
	end else if (rdack_len == 0)
		m_last <= 1;
	// }}}

	assign	M_VALID = m_valid;
	assign	M_DATA = sreg;
	assign	M_BYTES= m_bytes;
	assign	M_LAST = m_last;

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_READY, last_request_addr[0] };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
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
	localparam	F_LGDEPTH = LGLENGTH+1-WBLSB;
	localparam	F_LGCOUNT = LGLENGTH+1;
	reg	f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwb_nreqs, fwb_nacks, fwb_outstanding;
	(* anyconst *)	reg		f_cfg_inc;
	(* anyconst *)	reg	[1:0]	f_cfg_size;
	(* anyconst *)	reg	[ADDRESS_WIDTH-1:0]	f_cfg_addr;
	(* anyconst *)	reg	[LGLENGTH:0]		f_cfg_len;
	reg	[F_LGCOUNT-1:0]	f_rcvd, f_sent;
	reg	[WBLSB:0]	f_ack_size;
	reg	[LGLENGTH:0]	r_transferlen;
	reg	[ADDRESS_WIDTH-1:0]	r_addr;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Configuration properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset) || $past(o_err))
	begin
		assume(!i_request);
	end else if ($past(o_busy && i_request))
	begin
		assume(i_request);
		assume($stable(i_inc));
		assume($stable(i_size));
		assume($stable(i_addr));
		assume($stable(i_transferlen));
	end

	always @(posedge i_clk)
	if (!o_busy && (!OPT_LOWPOWER || i_request))
	begin
		// Shadow copy of these registers
		r_transferlen <= i_transferlen;
		r_addr <= i_addr;
	end

	always @(*)
	if (i_request && !o_busy)
	begin
		assume(i_inc  == f_cfg_inc);
		assume(i_size == f_cfg_size);
		assume(i_addr == f_cfg_addr);
		assume(i_transferlen == f_cfg_len);
	end else if (o_busy)
	begin
		assert(r_inc  == f_cfg_inc);
		assert(r_size == f_cfg_size);
		assert(r_addr == f_cfg_addr);
		assert(r_transferlen == f_cfg_len);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_master #(
		// {{{
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH),
		.F_OPT_RMW_BUS_OPTION(1'b0),
		.F_OPT_DISCONTINUOUS(1'b0),
		.F_OPT_SOURCE(1'b1)
		// }}}
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(o_rd_cyc),
		.i_wb_stb(o_rd_stb),
		.i_wb_we(o_rd_we),
		.i_wb_addr(o_rd_addr),
		.i_wb_data(o_rd_data),
		.i_wb_sel(o_rd_sel),
		//
		.i_wb_stall(i_rd_stall),
		.i_wb_ack(i_rd_ack),
		.i_wb_idata(i_rd_data),
		.i_wb_err(i_rd_err),
		//
		.f_nreqs(fwb_nreqs), .f_nacks(fwb_nacks),
		.f_outstanding(fwb_outstanding)
		// }}}
	);

	always @(*)
		assert(!o_rd_we);

	always @(*)
	if (f_past_valid && o_rd_stb)
	begin
		assert(o_rd_sel != 0);

		case(i_size)
		SZ_BYTE:assert($countones(o_rd_sel) == 1);
		SZ_16B: assert($countones(o_rd_sel) <= 2);
		SZ_32B: assert($countones(o_rd_sel) <= 4);
		default: begin end
		endcase
	end

	always @(*)
	if (f_past_valid && o_rd_cyc)
		assert(fwb_outstanding == wb_outstanding);

	// f_rcvd
	// {{{
	initial	f_rcvd = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy || o_err)
		f_rcvd <= 0;
	else if (o_rd_cyc && i_rd_ack)
	begin
		if (f_rcvd == 0)
		begin
			case(i_size)
			SZ_BYTE: f_rcvd <= f_rcvd + 1;
			SZ_16B:  f_rcvd <= f_rcvd + (2 - i_addr[  0]);
			SZ_32B:  f_rcvd <= f_rcvd + (4 - i_addr[1:0]);
			SZ_BUS:  f_rcvd <= f_rcvd + (DW/8 - i_addr[WBLSB-1:0]);
			endcase
		end else case(i_size)
		SZ_BYTE: f_rcvd <= f_rcvd + 1;
		SZ_16B:  f_rcvd <= f_rcvd + 2;
		SZ_32B:  f_rcvd <= f_rcvd + 4;
		SZ_BUS:  f_rcvd <= f_rcvd + DW/8;
		endcase
	end
	// }}}

	// f_ack_size
	// {{{
	always @(*)
	begin
		case(i_size)
		SZ_BYTE: f_ack_size = 1;
		SZ_16B:  f_ack_size = 2;
		SZ_32B:  f_ack_size = 4;
		SZ_BUS:  f_ack_size = DW/8;
		endcase

		if (f_rcvd == 0)
		case(i_size)
		SZ_BYTE: f_ack_size =   1;
		SZ_16B:  f_ack_size =  (2 - i_addr[  0]);
		SZ_32B:  f_ack_size =  (4 - i_addr[1:0]);
		SZ_BUS:  f_ack_size = (DW/8-i_addr[WBLSB-1:0]);
		endcase

		if (f_rcvd + f_ack_size > i_transferlen)
			f_ack_size = i_transferlen - f_rcvd;
	end
	// }}}

	always @(*)
	if (!i_reset && o_busy)
	begin
		assert(rdack_size == f_ack_size);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(!M_VALID);
	end

	always @(*)
	if (f_past_valid && M_VALID)
	begin
		assert(M_BYTES > 0);
		assert(M_BYTES <= (DW/8));

		if (M_LAST)
			assert(!o_rd_stb);
	end

	initial	f_sent = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_sent <= 0;
	else if (M_VALID && M_READY)
	begin
		if (M_LAST)
			f_sent <= 0;
		else
			f_sent <= f_sent + M_BYTES;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Contract" properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg			fc_check;
	(* anyconst *)	reg	[F_LGCOUNT-1:0]	fc_posn;
	(* anyconst *)	reg	[7:0]		fc_byte;

	wire		fwb_check,   fm_check;
	reg [WBLSB-1:0]	fwb_shift,   fm_shift;
	reg [DW-1:0]	fwb_shifted, fm_shifted;

	// Assume a known response from the bus
	// {{{
	assign	fwb_check = fc_check && (o_rd_cyc && i_rd_ack)
				&& (f_rcvd <= fc_posn)
				&& (fc_posn < f_rcvd + f_ack_size);

	always @(*)
	begin
		fwb_shift = f_rcvd - fc_posn;
		fwb_shift = fwb_shift + pre_shift;
	end

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		fwb_shifted = i_rd_data >> (8*fwb_shift);
	else
		fwb_shifted = i_rd_data << (8*fwb_shift);

	always @(*)
	if (fwb_check)
	begin
		if (OPT_LITTLE_ENDIAN)
			assume(fwb_shifted[7:0] == fc_byte);
		else
			assume(fwb_shifted[DW-1:DW-8] == fc_byte);
	end
	// }}}

	// Assert a specific output
	// {{{
	assign	fm_check = fc_check && M_VALID
				&& (f_sent <= fc_posn)
				&& (fc_posn < f_sent + fill);

	always @(*)
		fm_shift = fc_posn - f_sent;

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		fm_shifted = sreg >> (8*fm_shift);
	else
		fm_shifted = sreg << (8*fm_shift);

	always @(*)
	if (!i_reset && fm_check)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			assert(fm_shifted[7:0] == fc_byte);
		end else
			assert(fm_shifted[2*DW-1:2*DW-8] == fc_byte);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		cover(!i_reset && i_request);
		cover(o_busy);
		cover(o_rd_cyc);
		cover(o_rd_cyc && i_rd_ack);
	end

	always @(*)
		cover(!i_reset && fm_check);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The outgoing stream isn't quite an AXI stream master interface,
	// since WB doesn't have backpressure.  Therefore, we assume M_READY
	// is always high when we need it to be.

	always @(*)
	if (!i_reset && M_VALID)
		assume(M_READY);
	// }}}
`endif
// }}}
endmodule
