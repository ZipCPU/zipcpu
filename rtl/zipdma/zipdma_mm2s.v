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
module	zipdma_mm2s #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	BUS_WIDTH = 512,
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
		output	wire			o_rd_we,
		output	wire	[AW-1:0]	o_rd_addr,
		output	wire	[DW-1:0]	o_rd_data,
		output	wire	[DW/8-1:0]	o_rd_sel,
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
	localparam	WBLSB = $clog2(DW/8);
	reg	[WBLSB:0]	nxtstb_size, rdstb_size, rdack_size;
	reg	[ADDRESS_WIDTH-1:0]	next_addr, last_request_addr;
	reg	[WBLSB-1:0]	subaddr, rdack_subaddr;
	reg	[DW/8-1:0]	nxtstb_sel, first_sel;
	reg	[LGLENGTH:0]	wb_outstanding;

	reg	[WBLSB+1:0]	fill, next_fill;

	reg			m_valid, m_last;
	reg	[2*DW-1:0]	sreg;
	reg	[WBLSB:0]	m_bytes;

	reg	[LGLENGTH:0]	rdstb_len, rdack_len;
	// }}}

	assign	o_rd_we = 1'b0;
	assign	o_rd_data = {(DW){1'b0}};

	// nxtstb_size
	// {{{
	generate if (BUS_WIDTH > 32)
	begin : GEN_NXTSTB_SIZE
		// {{{
		always @(*)
		begin
			nxtstb_size = rdstb_size;

			case(i_size)
			2'b11: nxtstb_size = 1;
			2'b10: nxtstb_size = (rdstb_len == 3) ? 1 : 2;
			// Verilator lint_off WIDTH
			2'b01: nxtstb_size = (rdstb_len >= 4 && rdstb_len < 8)
						? (rdstb_len - 4) : 4;
			2'b00: nxtstb_size = (rdstb_len > DW/8) ? (DW/8) : rdstb_len;
			// Verilator lint_on  WIDTH
			endcase
		end
		// }}}
	end else begin
		// {{{
		always @(*)
		begin
			nxtstb_size = rdstb_size;

			casez(i_size)
			2'b11: nxtstb_size = 1;
			2'b10: nxtstb_size = (rdstb_len == 3) ? 1 : 2;
			// Verilator lint_off WIDTH
			2'b0?: nxtstb_size = (rdstb_len > 4) ? 4:rdstb_len[1:0];
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
			+ { {(ADDRESS_WIDTH-WBLSB-1){1'b0}}, nxtstb_size };
	end
	// }}}

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
			// {{{
			case(i_size)
			2'b11: rdstb_size <= 1;
			2'b10: rdstb_size <= (i_addr[0]) ? 1:2;
			// Verilator lint_off WIDTH
			2'b01: rdstb_size <= 4 - i_addr[1:0];
			2'b00: rdstb_size <= (DW/8)-i_addr[WBLSB-1:0];
			endcase
			// Verilator lint_on  WIDTH
			// }}}

			// rdstb_len
			rdstb_len <= i_transferlen;
		end
		// }}}
	end else begin
		if (!i_rd_stall)
		begin
			// {{{
			if (rdstb_len <= { {(LGLENGTH-WBLSB){1'b0}}, rdstb_size })
			begin
				rdstb_len <= 0;
				o_rd_stb  <= 1'b0;
			end else
				rdstb_len <= rdstb_len
					- { {(LGLENGTH-WBLSB){1'b0}}, rdstb_size };

			// rdstb_size
			rdstb_size <= nxtstb_size;

			// }}}
		end

		if (wb_outstanding == (i_rd_ack ? 1:0) && !o_rd_stb)
			o_rd_cyc <= 1'b0;

		if (!o_rd_cyc && !m_valid)
			o_busy <= 0;
	end

	// o_rd_sel
	// {{{

	// nxtstb_sel
	// {{{
	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		nxtstb_sel = ((1<<nxtstb_size)-1) << next_addr[WBLSB-1:0];
	end else begin
		// Verilator lint_off WIDTH
		nxtstb_sel = ( {(DW/8){1'b1}} - (1<<(DW/8-1-nxtstb_size)) )
					>> next_addr[WBLSB-1:0];
		// Verilator lint_on  WIDTH
	end
	// }}}

	// first_sel
	generate if (BUS_WIDTH > 32)
	begin : GEN_STRB
		// {{{
		always @(*)
		begin
			first_sel = 0;

			if (OPT_LITTLE_ENDIAN)
			begin
				// {{{
				case(i_size)
				2'b11: first_sel = {{(DW/8-1){1'b0}}, 1'b1} << i_addr[WBLSB-1:0];
				2'b10: first_sel = {{(DW/8-2){1'b0}}, 1'b1,i_addr[0]} << {i_addr[WBLSB-1:1], 1'b0 };
				2'b01: case(i_addr[1:0])
					2'b00: first_sel = {{(DW/8-4){1'b0}}, 4'b1111} << {i_addr[WBLSB-1:2], 2'b0 };
					2'b01: first_sel = {{(DW/8-4){1'b0}}, 4'b1110} << {i_addr[WBLSB-1:2], 2'b0 };
					2'b10: first_sel = {{(DW/8-4){1'b0}}, 4'b1100} << {i_addr[WBLSB-1:2], 2'b0 };
					2'b11: first_sel = {{(DW/8-4){1'b0}}, 4'b1000} << {i_addr[WBLSB-1:2], 2'b0 };
					endcase
				2'b00: first_sel = {(DW/8){1'b1}} << i_addr[WBLSB-1:0];
				endcase
				// }}}
			end else begin
				// {{{
				case(i_size)
				2'b11: first_sel = {1'b1, {(DW/8-1){1'b0}} } >> i_addr[WBLSB-1:0];
				2'b10: first_sel = {i_addr[0], 1'b1, {(DW/8-2){1'b0}} }
						>> {i_addr[WBLSB-1:1], 1'b0 };
				2'b01: case(i_addr[1:0])
					2'b00: first_sel = {4'b1111, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					2'b01: first_sel = {4'b0111, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					2'b10: first_sel = {4'b0011, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					2'b11: first_sel = {4'b0001, {(DW/8-4){1'b0}} } >> {i_addr[WBLSB-1:2], 2'b0 };
					endcase
				2'b00: first_sel = {(DW/8){1'b1}} >> i_addr[WBLSB-1:0];
				endcase
				// }}}
			end
		end
		// }}}
	end else begin : MIN_STRB
		// {{{
		always @(*)
		begin
			first_sel = 0;

			if (OPT_LITTLE_ENDIAN)
			begin
				// {{{
				casez(i_size)
				2'b11: first_sel = 4'b0001 << i_addr[WBLSB-1:0];
				2'b10: first_sel = 4'b0011 << {i_addr[WBLSB-1:1], 1'b0 };
				2'b0?: case(i_addr[1:0])
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
				2'b11: first_sel = 4'b1000 >> i_addr[WBLSB-1:0];
				2'b10: first_sel = 4'b1100
						>> {i_addr[WBLSB-1:1], 1'b0 };
				2'b0?: case(i_addr[1:0])
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
	end else if (!i_rd_stall)
	begin
			// {{{
			o_rd_sel <= nxtstb_sel;
			if (rdstb_len <= { {(LGLENGTH-WBLSB){1'b0}}, rdstb_size })
			begin
				o_rd_sel  <= 0;
			end
		// }}}
	end
	// }}}

	// wb_outstanding
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_rd_cyc || !i_rd_err)
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
		if (i_inc)
			rdack_subaddr <= rdack_subaddr + rdack_size;
		else case(i_size)
		2'b11: begin end
		2'b10: rdack_subaddr[  0] <= 1'b0;
		2'b01: rdack_subaddr[1:0] <= 2'b0;
		2'b00: rdack_subaddr[WBLSB-1:0] <= {(WBLSB){1'b0}};
		endcase
		// Verilator lint_on  WIDTH
	end
	// }}}

	// rdack_len
	// {{{
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
	// Verilator lint_off WIDTH
	always @(posedge i_clk)
	if (!o_busy)
	begin
		if (!OPT_LOWPOWER || i_request)
		case(i_size)
		2'b11: rdack_size <= 1;
		2'b10: rdack_size <= 2 - i_addr[0];
		2'b01: rdack_size <= 4 - i_addr[1:0];
		2'b00: rdack_size <= (1<<WBLSB) - i_addr[WBLSB-1:0];
		endcase
	end else if (i_rd_ack)
	begin
		case(i_size)
		2'b11: rdack_size <= 1;
		2'b10: rdack_size <= 2;
		2'b01: rdack_size <= 4;
		2'b00: rdack_size <= (rdack_len > DW/8) ? DW/8 : rdack_len;
		endcase
	end
	// Verilator lint_on  WIDTH
	// }}}

	// fill, next_fill (depends on rdack_size)
	// {{{
	always @(*)
	begin
		next_fill = fill;
		if (M_VALID)
			// next_fill = next_fill - (DW/8);
			next_fill[WBLSB+1:WBLSB]
					= next_fill[WBLSB+1:WBLSB] - 1;
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
	always @(posedge i_clk)
	if (!o_busy)
		m_valid <= 1'b0;
	else
		// Verilator lint_off WIDTH
		m_valid <= o_rd_cyc && i_rd_ack && ((next_fill >= DW/8)
			|| (rdack_len <= { {(LGLENGTH-1){1'b0}}, rdack_size }));
		// Verilator lint_on  WIDTH
	// }}}

	// sreg
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
		sreg <= 0;
	else if (o_rd_cyc && i_rd_ack)
	begin
		// Verilator lint_off WIDTH
		if (OPT_LITTLE_ENDIAN)
		begin
			if (m_valid)
				sreg <= { {(DW){1'b0}}, sreg[2*DW-1:DW] }
					| (i_rd_data << ((fill-DW/8)*8));
			else
				sreg <= sreg | (i_rd_data << (fill * 8));
		end else begin
			if (m_valid)
				sreg <= (sreg << DW)
					| ({ i_rd_data, {(DW){1'b0}} } >> ((fill-DW/8)*8));
			else
				sreg <= sreg | ({ i_rd_data, {(DW){1'b0}} } >> (fill * 8));
		end
		// Verilator lint_on  WIDTH
	end else if (m_valid)
	begin
		if (OPT_LITTLE_ENDIAN)
			sreg <= { {(DW){1'b0}}, sreg[2*DW-1:DW] };
		else
			sreg <= { sreg[DW-1:0], {(DW){1'b0}} };
	end
	// }}}

	// m_bytes
	// {{{
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
		m_last <= 1;
	// }}}

	// m_last
	// {{{
	always @(*)
	begin
		last_request_addr = i_addr;
		if (i_inc)
			// Verilator lint_off WIDTH
			last_request_addr = i_addr + i_transferlen - 1;
			// Verilator lint_on  WIDTH
	end

	always @(posedge i_clk)
	if (!o_busy)
	begin
		m_last <= 1'b0;
		if (!OPT_LOWPOWER || i_request)
		case(i_size)
		2'b11: m_last <= (i_transferlen <= 1);
		2'b10: m_last <= (last_request_addr[ADDRESS_WIDTH-1:1] != i_addr[ADDRESS_WIDTH-1:1]);
		2'b01: m_last <= (last_request_addr[ADDRESS_WIDTH-1:2] != i_addr[ADDRESS_WIDTH-1:2]);
		2'b00: m_last <= (last_request_addr[ADDRESS_WIDTH-1:WBLSB] != i_addr[ADDRESS_WIDTH-1:WBLSB]);
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
	assign	M_DATA = (OPT_LITTLE_ENDIAN) ? sreg[DW-1:0] : sreg[2*DW-1:DW];
	assign	M_BYTES= m_bytes;
	assign	M_LAST = m_last;

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_READY, last_request_addr[0] };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
