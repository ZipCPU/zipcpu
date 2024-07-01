////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/axi_addr.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	The AXI (full) standard has some rather complicated addressing
//		modes, where the address can either be FIXED, INCRementing, or
//	even where it can WRAP around some boundary.  When in either INCR or
//	WRAP modes, the next address must always be aligned.  In WRAP mode,
//	the next address calculation needs to wrap around a given value, and
//	that value is dependent upon the burst size (i.e. bytes per beat) and
//	length (total numbers of beats).  Since this calculation can be
//	non-trivial, and since it needs to be done multiple times, the logic
//	below captures it for every time it might be needed.
//
// 20200918 - modified to accommodate (potential) AXI3 burst lengths
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
//
`default_nettype none
// }}}
module	axi_addr #(
		// {{{
		parameter	AW = 32,
				DW = 32,
		// parameter [0:0]	OPT_AXI3 = 1'b0,
		localparam	LENB = 8
		// }}}
	) (
		// {{{
		input	wire	[AW-1:0]	i_last_addr,
		input	wire	[2:0]		i_size, // 1b, 2b, 4b, 8b, etc
		input	wire	[1:0]		i_burst, // fixed, incr, wrap, reserved
		input	wire	[LENB-1:0]	i_len,
		output	reg	[AW-1:0]	o_next_addr
		// }}}
	);

	// Parameter/register declarations
	// {{{
	localparam		DSZ = $clog2(DW)-3;
	localparam [1:0]	FIXED     = 2'b00;
	// localparam [1:0]	INCREMENT = 2'b01;
	// localparam [1:0]	WRAP      = 2'b10;

	reg	[AW-1:0]	wrap_mask, increment;
	// }}}

	// Address increment
	// {{{
	always @(*)
	begin
		increment = 0;
		if (i_burst != 0)
		begin
			// Addresses increment from one beat to the next
			// {{{
			if (DSZ == 0)
				increment = 1;
			else if (DSZ == 1)
				increment = (i_size[0]) ? 2 : 1;
			else if (DSZ == 2)
				increment = (i_size[1]) ? 4 : ((i_size[0]) ? 2 : 1);
			else if (DSZ == 3)
				case(i_size[1:0])
				2'b00: increment = 1;
				2'b01: increment = 2;
				2'b10: increment = 4;
				2'b11: increment = 8;
				endcase
			else
				increment = (1<<i_size);
			// }}}
		end
	end
	// }}}

	// wrap_mask
	// {{{
	// The wrap_mask is used to determine which bits remain stable across
	// the burst, and which are allowed to change.  It is only used during
	// wrapped addressing.
	always @(*)
	begin
		// Start with the default, minimum mask
		wrap_mask = 1;

		/*
		// Here's the original code.  It works, but it's
		// not economical (uses too many LUTs)
		//
		if (i_len[3:0] == 1)
			wrap_mask = (1<<(i_size+1));
		else if (i_len[3:0] == 3)
			wrap_mask = (1<<(i_size+2));
		else if (i_len[3:0] == 7)
			wrap_mask = (1<<(i_size+3));
		else if (i_len[3:0] == 15)
			wrap_mask = (1<<(i_size+4));
		wrap_mask = wrap_mask - 1;
		*/

		// Here's what we *want*
		//
		// wrap_mask[i_size:0] = -1;
		//
		// On the other hand, since we're already guaranteed that our
		// addresses are aligned, do we really care about
		// wrap_mask[i_size-1:0] ?

		// What we want:
		//
		// wrap_mask[i_size+3:i_size] |= i_len[3:0]
		//
		// We could simplify this to
		//
		// wrap_mask = wrap_mask | (i_len[3:0] << (i_size));
		//
		// But verilator complains about the left-hand side of
		// the shift having only 3 bits.
		//
		if (DSZ < 2)
			wrap_mask = wrap_mask | ({{(AW-4){1'b0}},i_len[3:0]} << (i_size[0]));
		else if (DSZ < 4)
			wrap_mask = wrap_mask | ({{(AW-4){1'b0}},i_len[3:0]} << (i_size[1:0]));
		else
			wrap_mask = wrap_mask | ({{(AW-4){1'b0}},i_len[3:0]} << (i_size));

		if (AW > 12)
			wrap_mask[(AW-1):((AW>12)? 12:(AW-1))] = 0;
	end
	// }}}

	// o_next_addr
	// {{{
	always @(*)
	begin
		o_next_addr = i_last_addr + increment;
		if (i_burst != FIXED)
		begin
			// Align subsequent beats in any burst
			// {{{
			//
			// We use the bus size here to simplify the logic
			// required in case the bus is smaller than the
			// maximum.  This depends upon AxSIZE being less than
			// $clog2(DATA_WIDTH/8).
			if (DSZ < 2)
			begin
				// {{{
				// Align any subsequent address
				if (i_size[0])
					o_next_addr[0] = 0;
				// }}}
			end else if (DSZ < 4)
			begin
				// {{{
				// Align any subsequent address
				case(i_size[1:0])
				2'b00:  o_next_addr = o_next_addr;
				2'b01:  o_next_addr[  0] = 0;
				2'b10:  o_next_addr[(AW-1>1) ? 1 : (AW-1):0]= 0;
				2'b11:  o_next_addr[(AW-1>2) ? 2 : (AW-1):0]= 0;
				endcase
				// }}}
			end else begin
				// {{{
				// Align any subsequent address
				case(i_size)
				3'b001:  o_next_addr[  0] = 0;
				3'b010:  o_next_addr[(AW-1>1) ? 1 : (AW-1):0]=0;
				3'b011:  o_next_addr[(AW-1>2) ? 2 : (AW-1):0]=0;
				3'b100:  o_next_addr[(AW-1>3) ? 3 : (AW-1):0]=0;
				3'b101:  o_next_addr[(AW-1>4) ? 4 : (AW-1):0]=0;
				3'b110:  o_next_addr[(AW-1>5) ? 5 : (AW-1):0]=0;
				3'b111:  o_next_addr[(AW-1>6) ? 6 : (AW-1):0]=0;
				default: o_next_addr = o_next_addr;
				endcase
				// }}}
			end
			// }}}
		end

		// WRAP addressing
		// {{{
		if (i_burst[1])
		begin
			// WRAP!
			o_next_addr[AW-1:0] = (i_last_addr & ~wrap_mask)
					| (o_next_addr & wrap_mask);
		end
		// }}}

		// Guarantee only the bottom 12 bits change
		// {{{
		// This is really a logic simplification.  AXI bursts aren't
		// allowed to cross 4kB boundaries.  Given that's the case,
		// we don't have to suffer from the propagation across all
		// AW bits, and can limit any address propagation to just the
		// lower 12 bits
		if (AW > 12)
			o_next_addr[AW-1:((AW>12)? 12:(AW-1))]
				= i_last_addr[AW-1:((AW>12) ? 12:(AW-1))];
		// }}}
	end
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = (LENB <= 4) ? &{1'b0, i_len[0] }
				: &{ 1'b0, i_len[LENB-1:4], i_len[0] };
	// Verilator lint_on UNUSED
	// Verilator coverage_on
	// }}}
endmodule
