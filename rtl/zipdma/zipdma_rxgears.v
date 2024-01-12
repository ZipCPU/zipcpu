////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_rxgears.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- A gearbox to pack received data.  This is part of our
//		alignment process.  Data comes in, gets read, gets packed, goes
//	into the FIFO, gets unpacked, and eventually written back to the bus.
//	Here, we simply pack words prior to stuffing them into the FIFO.
//
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
module	zipdma_rxgears #(
		// {{{
		parameter	BUS_WIDTH = 64,
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
	localparam			WBLSB = $clog2(DW/8);
	reg	[2*DW-1:0]		sreg;
	reg	[WBLSB+1:0]		next_fill, fill;
	reg				m_valid, m_last, next_last,
					r_last, r_full;
	reg	[WBLSB:0]		m_bytes;
	reg	[WBLSB-1:0]		shift;

	reg	[DW-1:0]	s_data;
	integer			ik;

	// }}}

	// next_fill, next_last
	// {{{
	always @(*)
	begin
		next_fill = fill;
		if (M_VALID && M_READY)
		begin
			if (M_LAST)
				next_fill = 0;
			else
				next_fill[WBLSB+1:WBLSB]
						= next_fill[WBLSB+1:WBLSB] - 1;
		end

		if (S_VALID && S_READY)
			next_fill = next_fill + S_BYTES;

		next_last = 0;
		if (S_VALID && S_READY && S_LAST)
			next_last = (next_fill[WBLSB+1:WBLSB] == 2'b00)
					||((next_fill[WBLSB+1:WBLSB] == 2'b01)
						&&(next_fill[WBLSB-1:0] == 0));
					// Was next_fill <= DW/8);
	end
	// }}}

	// fill
	// {{{
	initial	fill = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		fill <= 0;
	else
		fill <= next_fill;
`ifdef	FORMAL
	always @(*)
		assert(fill < 2*DW/8);
`endif
	// }}}

	// r_full
	// {{{
/*
	// This isn't necessary, since r_full == fill[WBLSB];
	initial	r_full = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		r_full <= 0;
	else if (M_VALID && M_READY)
		r_full <= 1'b0;
	else if (S_VALID && S_READY)
		r_full <= (next_fill >= (DW/8));
*/
	always @(*)
		// Verilator lint_off WIDTH
		r_full = (fill >= (DW/8));
		// Verilator lint_on  WIDTH
	// }}}

	// m_valid
	// {{{
	initial	m_valid = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		m_valid <= 0;
	else if (!M_VALID || M_READY)
		m_valid <= r_last || (S_VALID && S_READY && S_LAST)
			|| (|next_fill[WBLSB+1:WBLSB]);
`ifdef	FORMAL
	always @(*)
	if (fill >= (DW/8) || r_last || m_last)
		assert(m_valid);

	always @(*)
	if (m_last)
		assert(m_bytes == fill);
`endif
	// }}}

	// m_bytes
	// {{{
	initial	m_bytes = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		m_bytes <= 0;
	else if (!M_VALID || M_READY)
		m_bytes <= (|next_fill[WBLSB+1:WBLSB])
				? { 1'b1, {(WBLSB){1'b0}} } // DW/8
				: { 1'b0, next_fill[WBLSB-1:0] };
		// m_bytes <= (next_fill > (DW/8)) ? DW/8 : next_fill;
	// }}}

	// r_last, m_last
	// {{{
	initial	{ r_last, m_last } = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		{ r_last, m_last } <= 0;
	else if (S_VALID && S_READY && S_LAST)
		{ r_last, m_last } <= { !next_last, next_last };
	else if (M_VALID && M_READY)
		{ r_last, m_last } <= { 1'b0, r_last };
	// }}}

	// sreg
	// {{{
	always @(*)
	begin
		s_data = 0;
		for(ik=0; ik<DW/8; ik=ik+1)
		if (ik < S_BYTES)
		begin
			if (OPT_LITTLE_ENDIAN)
				s_data[ik*8 +: 8] = S_DATA[ik*8 +: 8];
			else
				s_data[(DW/8-1-ik)*8 +: 8]
						= S_DATA[(DW/8-1-ik)*8 +: 8];
		end
	end

	always @(*)
	begin
		shift = fill[WBLSB-1:0];
		if (M_VALID && M_READY)
			// Verilator lint_off WIDTH
			shift = fill - DW/8;
			// Verilator lint_on  WIDTH
	end

	initial	sreg = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		sreg <= 0;
	else if (M_VALID && M_READY && M_LAST)
		sreg <= 0;
	else if (OPT_LITTLE_ENDIAN)
	begin
		// {{{
		if (M_VALID && M_READY)
		begin
			if (S_VALID && S_READY)
				// Verilator lint_off WIDTH
				sreg <= { {(DW){1'b0}}, sreg[2*DW-1:DW] }
					| ({{(DW){1'b0}}, s_data } << (shift*8));
				// Verilator lint_on  WIDTH
			else
				sreg <= { {(DW){1'b0}}, sreg[2*DW-1:DW] };
		end else if (S_VALID && S_READY)
			sreg <= sreg | ({ {(DW){1'b0}}, s_data } << shift*8);
		// }}}
	end else begin
		if (M_VALID && M_READY)
		begin
			if (S_VALID && S_READY)
				// Verilator lint_off WIDTH
				sreg <= { sreg[DW-1:0], {(DW){1'b0}} }
					| ({s_data, {(DW){1'b0}} } >>(shift*8));
				// Verilator lint_on  WIDTH
			else
				sreg <= { sreg[DW-1:0], {(DW){1'b0}} };
		end else if (S_VALID && S_READY)
			// Verilator lint_off WIDTH
			sreg <= sreg | ({ s_data, {(DW){1'b0}} } >> (shift*8));
			// Verilator lint_on  WIDTH
	end
	// Verilator lint_on  WIDTH
	// }}}

	assign	M_VALID = m_valid;
	assign	M_DATA  = (OPT_LITTLE_ENDIAN) ? sreg[DW-1:0] : sreg[2*DW-1:DW];
	assign	M_BYTES = m_bytes;
	assign	M_LAST  = m_last;

	assign	S_READY = (!M_LAST && !r_last)
				&& (!M_VALID || (M_READY || !r_full));
				//	|| (S_BYTES + fill < 2*DW/8))));

	// Keep Verilator happy
	// {{{
	// wire	unused;
	// assign	unused = &{ 1'b0, ... };
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
	localparam	F_LGCOUNT = 16;
	reg			f_past_valid;
	reg	[F_LGCOUNT-1:0]	f_rcvd, f_sent;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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

	always @(*)
	if (!i_reset && S_VALID)
	begin
		assume(S_BYTES <= (DW/8));
		assume(S_BYTES > 0);
	end

	initial	f_rcvd = 0;
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		f_rcvd <= 0;
	else if (S_VALID && S_READY)
	begin
		if (S_LAST)
			f_rcvd <= 0;
		else
			f_rcvd <= f_rcvd + S_BYTES;
	end

	always @(*)
	begin
		assume(!f_rcvd[F_LGCOUNT-1]);
		assume({ 1'b0, f_rcvd } + (S_VALID ? S_BYTES : 0)
						< (1<<(F_LGCOUNT-1)));
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
	if (!f_past_valid || $past(i_reset || i_soft_reset))
	begin
		assert(!M_VALID);
		assert(!r_last);
		assert(!M_LAST);
	end else if ($past(M_VALID && !M_READY))
	begin
		assert(M_VALID);
		assert($stable(M_DATA));
		assert($stable(M_BYTES));
		assert($stable(M_LAST));
	end

	always @(*)
	if (!i_reset && M_VALID)
	begin
		assert(M_BYTES <= (DW/8));
		assert(M_BYTES > 0);

		if (!M_LAST)
			assert(M_BYTES == (DW/8));
	end

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

	reg	[F_LGCOUNT-1:0]	f_buffered;

	always @(*)
	begin
		f_buffered = f_sent + fill;

		assert(!f_sent[F_LGCOUNT-1]);
		assert(!f_buffered[F_LGCOUNT-1]);

		assert(f_buffered >= f_sent);

		assert(f_sent[WBLSB-1:0] == 0);
	end

	always @(*)
	if (!i_reset)
	begin
		if (!m_last && !r_last)
		begin
			assert(f_sent + fill == f_rcvd);
			assert(f_sent <= f_rcvd);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!i_reset)
	begin
		assert(!r_last || !M_LAST);

		if (r_last)
			assert(M_VALID && fill > (DW/8));
	end

	always @(*)
	if (!i_reset)
	begin
		if (fill > (DW/8))
			assert(M_BYTES == (DW/8));
		else
			assert(M_BYTES == fill);
	end

	always @(*)
	if (!i_reset && (r_last || M_LAST))
		assert(f_rcvd == 0);
	else if (!i_reset)
		assert(fill[WBLSB-1:0] == f_rcvd[WBLSB-1:0]);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg			fc_check;
	(* anyconst *)	reg	[F_LGCOUNT-1:0]	fc_posn;
	(* anyconst *)	reg	[7:0]		fc_byte;

	wire			frx_check, ftx_check;
	reg	[WBLSB-1:0]	frx_shift;
	reg	[WBLSB+1:0]	ftx_shift;
	reg	[DW-1:0]	frx_shifted;
	reg	[2*DW-1:0]	ftx_shifted;

	always @(*)
		frx_shift = fc_posn [WBLSB-1:0]- f_rcvd[WBLSB-1:0];

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		frx_shifted = S_DATA >> (8*frx_shift);
	else
		frx_shifted = S_DATA << (8*frx_shift);

	assign	frx_check = fc_check && S_VALID && f_rcvd <= fc_posn
					&& (fc_posn < f_rcvd + S_BYTES);

	always @(*)
	if (!i_reset && frx_check)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			assume(frx_shifted[7:0] == fc_byte);
		end else begin
			assume(frx_shifted[DW-1:DW-8] == fc_byte);
		end
	end

	always @(*)
	begin
		ftx_shift = fc_posn[WBLSB:0]- f_sent[WBLSB:0];
		ftx_shift[WBLSB+1] = 0;
	end

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		ftx_shifted = sreg >> (8*ftx_shift);
	else
		ftx_shifted = sreg << (8*ftx_shift);

	assign	ftx_check = fc_check && f_sent <= fc_posn
					&& (fc_posn < f_sent + fill);

	always @(*)
	if (!i_reset && ftx_check)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			assert(ftx_shifted[7:0] == fc_byte);
		end else begin
			assert(ftx_shifted[2*DW-1:2*DW-8] == fc_byte);
		end
	end

	always @(*)
	if (!i_reset)
	begin
		for(ik=0; ik<2*DW/8; ik=ik+1)
		if (fill <= ik)
		begin
			if (OPT_LITTLE_ENDIAN)
				assert(sreg[8*ik +: 8] == 8'h00);
			else
				assert(sreg[2*DW-8-8*ik +: 8] == 8'h00);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
