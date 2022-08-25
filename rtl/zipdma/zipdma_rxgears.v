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
module	zipdma_rxgears #(
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
	// }}}

	// next_fill, next_last
	// {{{
	always @(*)
	begin
		next_fill = fill;
		if (S_VALID && S_READY)
			next_fill = next_fill + S_BYTES;
		if (M_VALID && M_READY)
		begin
			if (M_LAST)
				next_fill = 0;
			else
				next_fill[WBLSB+1:WBLSB]
						= next_fill[WBLSB+1:WBLSB] - 1;
		end

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
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		fill <= 0;
	else
		fill <= next_fill;
	// }}}

	// r_full
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		r_full <= 0;
	else if (M_VALID && M_READY)
		r_full <= 1'b0;
	else if (S_VALID)
		r_full <= (next_fill + S_BYTES >= (1<<(WBLSB+2)));
	// }}}

	// m_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		m_valid <= 0;
	else if (!M_VALID || M_READY)
		m_valid <= r_last || (|next_fill[WBLSB+1:WBLSB]);
				// was r_last || next_fill >= DW/8);
	// }}}

	// m_bytes
	// {{{
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
	always @(posedge i_clk)
	if (i_reset || i_soft_reset)
		sreg <= 0;
	else if (M_VALID && M_READY && M_LAST)
		sreg <= 0;
	else if (OPT_LITTLE_ENDIAN)
	begin
		if (M_VALID && M_READY)
		begin
			if (S_VALID && S_READY)
				// Verilator lint_off WIDTH
				sreg <= { {(DW){1'b0}}, sreg[2*DW-1:DW] }
					| ({{(DW){1'b0}}, S_DATA } << ((fill-DW/8)*8));
				// Verilator lint_on  WIDTH
			else
				sreg <= { {(DW){1'b0}}, sreg[2*DW-1:DW] };
		end else if (S_VALID && S_READY)
			sreg <= sreg | ({ {(DW){1'b0}}, S_DATA } << fill*8);
	end else begin
		if (M_VALID && M_READY)
		begin
			if (S_VALID && S_READY)
				// Verilator lint_off WIDTH
				sreg <= { sreg[DW-1:0], {(DW){1'b0}} }
					| (S_DATA >> ((fill-DW/8)*8));
				// Verilator lint_on  WIDTH
			else
				sreg <= { sreg[DW-1:0], {(DW){1'b0}} };
		end else if (S_VALID && S_READY)
			// Verilator lint_off WIDTH
			sreg <= sreg | ({ S_DATA, {(DW){1'b0}} } >> (fill*8));
			// Verilator lint_on  WIDTH
	end
	// Verilator lint_on  WIDTH
	// }}}

	assign	M_VALID = m_valid;
	assign	M_DATA  = (OPT_LITTLE_ENDIAN) ? sreg[DW-1:0] : sreg[2*DW-1:DW];
	assign	M_BYTES = m_bytes;
	assign	M_LAST  = m_last;

	// Verilator lint_off WIDTH
	assign	S_READY = (!M_VALID || (!M_LAST && (M_READY || !r_full)));
				//	|| (S_BYTES + fill < 2*DW/8))));
	// Verilator lint_on  WIDTH
endmodule
