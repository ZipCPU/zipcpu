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
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
	localparam	WBLSB = $clog2(DW/8);
	localparam [1:0]	SZ_BYTE = 2'b11,
				SZ_16B  = 2'b10,
				SZ_32B  = 2'b01,
				SZ_BUS  = 2'b00;
	reg			m_valid, m_last, r_last, r_next;
	reg	[DW-1:0]	sreg;
	reg	[WBLSB:0]	m_bytes, fill;
	// }}}

	// sreg, fill
	// {{{
	initial {sreg, fill } = 0;
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
		if (M_LAST)
			{ sreg, fill } <= 0;
		else if (OPT_LITTLE_ENDIAN)
		begin
			// Verilator coverage_off
			case(i_size)
			SZ_BYTE: begin sreg <= sreg >>  8; fill <= fill - 1; end
			SZ_16B:  begin sreg <= sreg >> 16; fill <= fill - 2; end
			SZ_32B:  begin sreg <= sreg >> 32; fill <= fill - 4; end
			SZ_BUS:  begin sreg <= 0; fill <= 0; end
			endcase
			// Verilator coverage_on
		end else begin
			case(i_size)
			SZ_BYTE: begin sreg <= sreg <<  8; fill <= fill - 1; end
			SZ_16B:  begin sreg <= sreg << 16; fill <= fill - 2; end
			SZ_32B:  begin sreg <= sreg << 32; fill <= fill - 4; end
			SZ_BUS:  begin sreg <= 0; fill <= 0; end
			endcase
		end
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
		assert(fill <= (DW/8));
`endif
	// }}}

	// m_valid
	// {{{
	initial	m_valid = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		m_valid <= 0;
	else if (!M_VALID || M_READY)
	begin
		if (S_VALID && S_READY)
			m_valid <= 1'b1;
		else case(i_size)
		SZ_BYTE: m_valid <= (fill > 1);
		SZ_16B:  m_valid <= (fill > 2);
		SZ_32B:  m_valid <= (fill > 4);
		SZ_BUS:  m_valid <= 0;
		endcase
	end
`ifdef	FORMAL
	always @(*)
	if (m_valid)
		assert(m_bytes <= fill);
`endif
	// }}}

	// m_bytes
	// {{{
	generate if (BUS_WIDTH > 32)
	begin : GEN_MBYTES
		// {{{
		initial	m_bytes = 0;
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			m_bytes <= 0;
		else if (S_VALID && S_READY)
		begin
			case(i_size)
			SZ_BYTE: m_bytes <= 1;
			SZ_16B: m_bytes <= (S_BYTES > 2) ? 2 : S_BYTES;
			SZ_32B: m_bytes <= (S_BYTES > 4) ? 4 : S_BYTES;
			SZ_BUS: m_bytes <= S_BYTES;
			endcase
		end else if (!M_VALID || M_READY)
		begin
			case(i_size)
			SZ_BYTE: m_bytes <= 1;
			SZ_16B:  m_bytes <= (fill >= 4) ? 2
						: (&fill[1:0]) ? 1 : 0;
			SZ_32B:  m_bytes <= (fill >= 8) ? 4
				: (fill[2]) ? ({ {(WBLSB-1){1'b0}}, fill[1:0] })
				: 0;
			SZ_BUS:  m_bytes <= 0;
			endcase
		end
		// }}}
	end else begin : MIN_MBYTES
		// {{{
		initial	m_bytes = 0;
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			m_bytes <= 0;
		else if (S_VALID && S_READY)
		begin
			casez(i_size)
			SZ_BYTE: m_bytes <= 1;
			SZ_16B:  m_bytes <= (S_BYTES > 2) ? 2 : S_BYTES;
			default: m_bytes <= S_BYTES;
			endcase
		end else if (!M_VALID || M_READY)
		begin
			casez(i_size)
			SZ_BYTE: m_bytes <= 1;
			SZ_16B:  m_bytes <= (fill >= 4) ? 2
						: (&fill[1:0]) ? 1 : 0;
			default: m_bytes <= 0;
			endcase
		end
		// }}}
	end endgenerate
`ifdef	FORMAL
	// {{{
	always @(*)
	if (!i_reset && M_VALID)
	begin
		assert(m_bytes > 0);
		assert(m_bytes <= fill);
		if (M_LAST)
			assert(m_bytes == fill);

		case(i_size)
		SZ_BYTE: assert(m_bytes == 1);
		SZ_16B:  begin
			assert(m_bytes <= 2);
			if (m_bytes < 2)
				assert(M_LAST && m_bytes == fill);
			end
		SZ_32B:  begin
			assert(m_bytes <= 4);
			if (m_bytes < 4)
				assert(M_LAST && m_bytes == fill);
			end
		SZ_BUS:  begin
			assert(m_bytes <= DW/8);
			if (m_bytes < (DW/8))
				assert(M_LAST && m_bytes == fill);
			end
		endcase
	end
	// }}}
`endif
	// }}}

	// r_next -- Are we on our last word?
	// {{{
	// Only allow S_READY if r_next is true, so r_next must be true when
	// we output the last word of the shift register.
	generate if (BUS_WIDTH > 32)
	begin : GEN_NEXT
		// {{{
		initial	r_next = 1;
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			r_next <= 1;
		else if (M_VALID && M_READY && M_LAST)
			r_next <= 1;
		else if (S_VALID && S_READY)
		begin
			case(i_size)
			SZ_BYTE:r_next <= (S_BYTES == 1);
			SZ_16B: r_next <= (S_BYTES <= 2);
			SZ_32B: r_next <= (S_BYTES <= 4);
			SZ_BUS: r_next <= 1;
			endcase

			if (S_LAST)
				r_next <= 0;
		end else if (M_VALID && M_READY)
		begin
			case(i_size)
			SZ_BYTE:r_next <= (fill <= 2);
			SZ_16B: r_next <= (fill <= 4);
			SZ_32B: r_next <= (fill <= 8);
			SZ_BUS: r_next <= 1;
			endcase

			if (r_last)
				r_next <= 0;
		end
		// }}}
	end else begin : MIN_NEXT
		// {{{
		initial	r_next = 1;
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			r_next <= 1;
		else if (M_VALID && M_READY && M_LAST)
			r_next <= 1;
		else if (S_VALID && S_READY)
		begin
			casez(i_size)
			SZ_BYTE: r_next <= (S_BYTES == 1);
			SZ_16B:  r_next <= (S_BYTES <= 2);
			default: r_next <= 1;
			endcase

			if (S_LAST)
				r_next <= 0;
		end else if (M_VALID && M_READY)
		begin
			casez(i_size)
			SZ_BYTE: r_next <= (fill <= 2);
			SZ_16B:  r_next <= (fill <= 4);
			default: r_next <= 1;
			endcase

			if (r_last)
				r_next <= 0;
		end
		// }}}
	end endgenerate

`ifdef	FORMAL
	// {{{
	reg	[1:0]	f_mid_packet;

	// f_mid_packet
	// {{{
	initial	f_mid_packet = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		f_mid_packet <= 0;
	else if (S_VALID && S_READY)
		f_mid_packet <= (S_LAST) ? 2'b10 : 2'b01;
	else if (M_VALID && M_READY && M_LAST)
		f_mid_packet <= 2'b00;

	always @(*)
		assert(f_mid_packet != 2'b11);
	// }}}

	always @(*)
	if (!i_reset) begin

		assert(f_mid_packet[1] == (r_last || m_last));

		if (f_mid_packet[1])
		begin
			assert(!r_next);
		end else case(i_size)
		SZ_BYTE:assert(r_next == (fill <= 1));
		SZ_16B: assert(r_next == (fill <= 2));
		SZ_32B: assert(r_next == (fill <= 4));
		SZ_BUS: assert(r_next);
		endcase
	end
	// }}}
`endif
	// }}}

	// r_last, m_last
	// {{{
	generate if (BUS_WIDTH > 32)
	begin : GEN_LAST
		// {{{
		initial { r_last, m_last } = 2'b00;
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			{ r_last, m_last } <= 0;
		else if (S_VALID && S_READY)
		begin
			case(i_size)
			SZ_BYTE: { r_last, m_last } <= { (S_BYTES > 1), (S_BYTES == 1) };
			SZ_16B:  { r_last, m_last } <= { (S_BYTES > 2), (S_BYTES <= 2) };
			SZ_32B:  { r_last, m_last } <= { (S_BYTES > 4), (S_BYTES <= 4) };
			SZ_BUS:  { r_last, m_last } <= { 1'b0, S_LAST };
			endcase

			if (!S_LAST)
				{ r_last, m_last } <= 2'b00;
		end else if (M_VALID && M_READY)
		begin
			case(i_size)
			SZ_BYTE:m_last <= r_last && (fill <= 2);
			SZ_16B: m_last <= r_last && (fill <= 4);
			SZ_32B: m_last <= r_last && (fill <= 8);
			SZ_BUS: m_last <= 0;
			endcase

			case(i_size)
			SZ_BYTE:r_last <= r_last && (fill > 2);
			SZ_16B: r_last <= r_last && (fill > 4);
			SZ_32B: r_last <= r_last && (fill > 8);
			SZ_BUS: r_last <= 0;
			endcase

			// if (M_LAST)
			//	{ r_last, m_last } <= 2'b00;
		end
		// }}}
	end else begin : MIN_LAST
		// {{{
		initial { r_last, m_last } = 2'b00;
		always @(posedge i_clk)
		if (i_reset || i_soft_reset)
			{ r_last, m_last } <= 0;
		else if (S_VALID && S_READY)
		begin
			casez(i_size)
			SZ_BYTE: { r_last, m_last } <= { (S_BYTES > 1), (S_BYTES == 1) };
			SZ_16B:  { r_last, m_last } <= { (S_BYTES > 2), (S_BYTES <= 2) };
			default: { r_last, m_last } <= { (S_BYTES > 4), (S_BYTES <= 4) };
			endcase

			if (!S_LAST)
				{ r_last, m_last } <= 2'b00;
		end else if (!M_VALID || M_READY)
		begin
			casez(i_size)
			SZ_BYTE: m_last <= r_last && (fill <= 2);
			SZ_16B:  m_last <= r_last && (fill <= 4);
			default: m_last <= 0;
			endcase

			casez(i_size)
			SZ_BYTE: r_last <= r_last && (fill > 2);
			SZ_16B:  r_last <= r_last && (fill > 4);
			default: r_last <= 0;
			endcase

			// if (M_LAST)
			//	{ r_last, m_last } <= 2'b00;
		end
		// }}}
	end endgenerate

`ifdef FORMAL
	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && M_VALID && M_READY && M_LAST))
		assert({ r_last, m_last } == 2'b00);
`endif
	// }}}

	assign	M_VALID = m_valid;
	assign	M_DATA  = sreg;
	assign	M_BYTES = m_bytes;
	assign	M_LAST  = m_last;

	assign	S_READY = !M_VALID || (M_READY && r_next);
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
	localparam	F_LGCOUNT = 16;
	reg		f_past_valid;
	(* anyconst *)	reg	[1:0]	f_cfg_size;
	reg	[F_LGCOUNT-1:0]		f_rcvd, f_sent;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
	if (!i_reset)
		assume(i_size == f_cfg_size);

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Basic stream properties
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset || i_soft_reset))
		assume(!S_VALID);
	else if ($past(S_VALID && !S_READY))
	begin
		assume(S_VALID);
		assume($stable(S_DATA));
		assume($stable(S_BYTES));
		assume($stable(S_LAST));
	end
	// }}}

	// Properties of S_BYTES: incoming words are packed
	// {{{
	always @(*)
	if (!i_reset && S_VALID)
	begin
		assume(S_BYTES > 0);
		assume(S_BYTES <= (DW/8));
		if (!S_LAST)
			assume(S_BYTES == (DW/8));
	end
	// }}}

	// f_rcvd
	// {{{
	initial	f_rcvd = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		f_rcvd = 0;
	else if (S_VALID && S_READY)
	begin
		if (S_LAST)
			f_rcvd <= 0;
		else
			f_rcvd <= f_rcvd + S_BYTES;
	end

	always @(*)
		assume(!f_rcvd[F_LGCOUNT-1]);

	always @(*)
	if (f_mid_packet == 2'b00 || f_mid_packet == 2'b10)
	begin
		assert(f_rcvd == 0);
	end else
		assert(f_rcvd > 0);
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Basic stream property
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset || i_soft_reset))
		assert(!M_VALID);
	else if ($past(M_VALID && !M_READY))
	begin
		assert(M_VALID);
		assert($stable(M_DATA));
		assert($stable(M_BYTES));
		assert($stable(M_LAST));
	end
	// }}}

	// Bounding/checking M_LAST
	// {{{
	always @(*)
	if (!i_reset && M_VALID)
	begin
		assert(M_BYTES > 0);
		assert(M_BYTES <= (DW/8));

		if (!M_LAST)
		case(f_cfg_size)
		SZ_BYTE: assert(M_BYTES == 1);
		SZ_16B: assert(M_BYTES == 2);
		SZ_32B: assert(M_BYTES == 4);
		SZ_BUS: assert(M_BYTES == (DW/8));
		endcase
		else
		case(f_cfg_size)
		SZ_BYTE: assert(M_BYTES == 1);
		SZ_16B: assert(M_BYTES <= 2);
		SZ_32B: assert(M_BYTES <= 4);
		SZ_BUS: assert(M_BYTES <= (DW/8));
		endcase
	end
	// }}}

	// Bounding/checking fill
	// {{{
	always @(*)
	if (!i_reset)
	begin
		assert(!r_last || !M_LAST);
		if (r_last || M_LAST)
			assert(M_VALID);

		if (r_last)
		case(f_cfg_size)
		SZ_BYTE: assert(fill > 1);
		SZ_16B: assert(fill > 2);
		SZ_32B: assert(fill > 4);
		SZ_BUS: assert(0);
		endcase

		if (M_LAST)
		begin
			assert(fill > 0);

			case(f_cfg_size)
			2'b11: assert(fill == 1);
			SZ_16B: assert(fill <= 2);
			SZ_32B: assert(fill <= 4);
			SZ_BUS: begin end
			endcase
		end
	end

	always @(*)
	if (!i_reset)
	begin
		assert(fill <= (DW/8));
		assert(M_VALID == (fill > 0));

		if (M_LAST)
			assert(fill == M_BYTES);

		if (!M_LAST && !r_last)
		case(f_cfg_size)
		SZ_BYTE: begin end // assert(fill > 0);
		SZ_16B: assert(fill[0] == 1'b0);
		SZ_32B: assert(fill[1:0] == 2'b00);
		SZ_BUS: assert(fill[WBLSB-1:0] == 0);
		endcase
	end
	// }}}

	// f_sent
	// {{{
	initial	f_sent = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		f_sent <= 0;
	else if (M_VALID && M_READY)
	begin
		if (M_LAST)
			f_sent <= 0;
		else
			f_sent <= f_sent + M_BYTES;
	end

	always @(*)
	begin
		assume(!f_sent[F_LGCOUNT-1]);

		if (!r_last && !m_last)
		begin
			assert(f_sent + fill == f_rcvd);
			assert(f_sent <= f_rcvd);
		end
	end

	always @(*)
	if (f_mid_packet == 2'b00)
	begin
		assert(f_sent == 0);
	end else if (f_mid_packet == 2'b10)
		assert(M_VALID || f_sent > 0);
	// }}}

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

	wire			fs_check,   fm_check;
	reg	[WBLSB-1:0]	fs_shift,   fm_shift;
	reg	[DW-1:0]	fs_shifted, fm_shifted;

	// Slave assumption
	// {{{
	assign fs_check = fc_check && S_VALID && f_rcvd <= fc_posn
				&& (fc_posn < f_rcvd + S_BYTES);

	always @(*)
		fs_shift = fc_posn - f_rcvd;

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		fs_shifted = S_DATA >> (8*fs_shift);
	else
		fs_shifted = S_DATA << (8*fs_shift);

	always @(*)
	if (!i_reset && fs_check)
	begin
		if (OPT_LITTLE_ENDIAN)
			assume(fs_shifted[7:0] == fc_byte);
		else
			assume(fs_shifted[DW-1:DW-8] == fc_byte);
	end
	// }}}

	// Master assertion
	// {{{
	assign fm_check = fc_check && f_sent <= fc_posn
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
		end else begin
			assert(fm_shifted[DW-1:DW-8] == fc_byte);
		end
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

	always @(posedge i_clk)
	if (!i_reset && M_VALID && M_READY && M_LAST)
	begin
		cover(i_size == SZ_BYTE && f_sent > DW/8);
		cover(i_size == SZ_16B  && f_sent > DW/8);
		cover(i_size == SZ_32B  && f_sent > DW/8);
		cover(i_size == SZ_BUS  && f_sent > DW/8);

		cover(i_size == SZ_BYTE && f_sent > 2*DW/8+1);
		cover(i_size == SZ_16B  && f_sent > 2*DW/8+1);
		cover(i_size == SZ_32B  && f_sent > 2*DW/8+1);
		cover(i_size == SZ_BUS  && f_sent > 2*DW/8+1);

		cover(i_size == SZ_BUS  && f_sent > 2*DW/8+2);
		cover(i_size == SZ_BUS  && f_sent > 2*DW/8+3);
		cover(i_size == SZ_BUS  && f_sent > 2*DW/8+4);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
`endif
// }}}
endmodule
