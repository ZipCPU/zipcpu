////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_txgears.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Unpack bus words into 1, 2, 4, or more bytes per
//		outgong word.  This is to support peripherals which require
//	1, 2, or 4 byte transfers (only), as well as peripherals like memory
//	with no such restrictions.
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
module	zipdma_txgears #(
		// {{{
		parameter	BUS_WIDTH = 512,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		// Abbreviations
		localparam	DW = BUS_WIDTH
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Configuration
		// {{{
		input	wire			i_soft_reset,
		input	wire	[1:0]		i_size,
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
		// Outgoing Stream interface
		// {{{
		output	wire			M_VALID,
		input	wire			M_READY,
		output	wire	[DW-1:0]	M_DATA,
		// How many bytes are valid?
		output	wire [$clog2(DW/8):0]	M_BYTES,
		output	wire			M_LAST
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg				m_valid, m_last, r_last, r_next;
	reg	[DW-1:0]		sreg;
	reg	[$clog2(DW/8):0]	m_bytes, fill;
	// }}}

	// sreg, fill
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
	begin
		sreg <= 0;
		fill <= 0;
	end else if (S_VALID && S_READY)
	begin
		sreg <= S_DATA;
		fill <= S_BYTES;
	end else if (M_VALID && M_READY)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			case(i_size)
			2'b11: begin sreg <= sreg >>  8; fill <= fill - 1; end
			2'b10: begin sreg <= sreg >> 16; fill <= fill - 2; end
			2'b01: begin sreg <= sreg >> 32; fill <= fill - 4; end
			2'b00: begin sreg <= 0; fill <= 0; end
			endcase
		end else begin
			case(i_size)
			2'b11: begin sreg <= sreg <<  8; fill <= fill - 1; end
			2'b10: begin sreg <= sreg << 16; fill <= fill - 2; end
			2'b01: begin sreg <= sreg << 32; fill <= fill - 4; end
			2'b00: begin sreg <= 0; fill <= 0; end
			endcase
		end
	end
	// }}}

	// m_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		m_valid <= 0;
	else if (!M_VALID || M_READY)
	begin
		if (S_VALID)
			m_valid <= 1'b1;
		else case(i_size)
		2'b11: m_valid <= (fill > 1);
		2'b10: m_valid <= (fill > 2);
		2'b01: m_valid <= (fill > 4);
		2'b00: m_valid <= 0;
		endcase
	end
	// }}}

	// m_bytes
	// {{{
	generate if (BUS_WIDTH > 32)
	begin : GEN_MBYTES
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			m_bytes <= 0;
		else if (S_VALID && S_READY)
		begin
			case(i_size)
			2'b11: m_bytes <= 1;
			2'b10: m_bytes <= (S_BYTES > 2) ? 2 : S_BYTES;
			2'b01: m_bytes <= (S_BYTES > 4) ? 4 : S_BYTES;
			2'b00: m_bytes <= S_BYTES;
			endcase
		end else if (!M_VALID || M_READY)
		begin
			case(i_size)
			2'b11: m_bytes <= 1;
			2'b10: m_bytes <= (fill > 4) ? 2 : (fill - 2);
			2'b01: m_bytes <= (fill > 8) ? 4 : (fill - 4);
			2'b00: m_bytes <= 0;
			endcase
		end
	end else begin : MIN_MBYTES

		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			m_bytes <= 0;
		else if (S_VALID && S_READY)
		begin
			casez(i_size)
			2'b11: m_bytes <= 1;
			2'b10: m_bytes <= (S_BYTES > 2) ? 2 : S_BYTES;
			2'b0?: m_bytes <= S_BYTES;
			endcase
		end else if (!M_VALID || M_READY)
		begin
			casez(i_size)
			2'b11: m_bytes <= 1;
			2'b10: m_bytes <= (fill > 0) ? (fill - 2) : 0;
			2'b0?: m_bytes <= 0;
			endcase
		end

	end endgenerate
	// }}}

	// r_next -- Are we on our last word?
	// {{{
	// Only allow S_READY if r_next is true, so r_next must be true when
	// we output the last word of the shift register.
	generate if (BUS_WIDTH > 32)
	begin : GEN_NEXT
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			r_next <= 0;
		else if (S_VALID && S_READY)
		begin
			case(i_size)
			2'b11: r_next <= (S_BYTES == 1);
			2'b10: r_next <= (S_BYTES <= 2);
			2'b01: r_next <= (S_BYTES <= 4);
			2'b00: r_next <= 1;
			endcase
		end else if (!M_VALID || M_READY)
		begin
			case(i_size)
			2'b11: r_next <= (S_BYTES <= 2);
			2'b10: r_next <= (S_BYTES <= 4);
			2'b01: r_next <= (S_BYTES <= 8);
			2'b00: r_next <= 1;
			endcase
		end
		// }}}
	end else begin : MIN_NEXT
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			r_next <= 0;
		else if (S_VALID && S_READY)
		begin
			casez(i_size)
			2'b11: r_next <= (S_BYTES == 1);
			2'b10: r_next <= (S_BYTES <= 2);
			2'b0?: r_next <= 1;
			endcase
		end else if (!M_VALID || M_READY)
		begin
			casez(i_size)
			2'b11: r_next <= (S_BYTES <= 2);
			2'b10: r_next <= (S_BYTES <= 4);
			2'b0?: r_next <= 1;
			endcase
		end
		// }}}
	end endgenerate
	// }}}

	// r_last, m_last
	// {{{
	generate if (BUS_WIDTH > 32)
	begin : GEN_LAST
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			{ r_last, m_last } <= 0;
		else if (S_VALID && S_READY)
		begin
			case(i_size)
			2'b11: { r_last, m_last } <= { (S_BYTES > 1), (S_BYTES == 1) };
			2'b10: { r_last, m_last } <= { (S_BYTES > 2), (S_BYTES == 2) };
			2'b01: { r_last, m_last } <= { (S_BYTES > 4), (S_BYTES == 4) };
			2'b00: { r_last, m_last } <= { 1'b0, S_LAST };
			endcase

			if (!S_LAST)
				{ r_last, m_last } <= 2'b00;
		end else if (!M_VALID || M_READY)
		begin
			case(i_size)
			2'b11: m_last <= r_last && (fill <= 2);
			2'b10: m_last <= r_last && (fill <= 4);
			2'b01: m_last <= r_last && (fill <= 8);
			2'b00: m_last <= 0;
			endcase
		end
		// }}}
	end else begin : MIN_LAST
		// {{{
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			{ r_last, m_last } <= 0;
		else if (S_VALID && S_READY)
		begin
			casez(i_size)
			2'b11: { r_last, m_last } <= { (S_BYTES > 1), (S_BYTES == 1) };
			2'b10: { r_last, m_last } <= { (S_BYTES > 2), (S_BYTES == 2) };
			2'b0?: { r_last, m_last } <= { (S_BYTES > 4), (S_BYTES == 4) };
			endcase

			if (!S_LAST)
				{ r_last, m_last } <= 2'b00;
		end else if (!M_VALID || M_READY)
		begin
			casez(i_size)
			2'b11: m_last <= r_last && (fill <= 2);
			2'b10: m_last <= r_last && (fill <= 4);
			2'b0?: m_last <= 0;
			endcase
		end
		// }}}
	end endgenerate
	// }}}

	assign	M_VALID = m_valid;
	assign	M_DATA  = sreg;
	assign	M_BYTES = m_bytes;
	assign	M_LAST  = m_last;

	assign	S_READY = !M_VALID || (M_READY && r_next);
endmodule
