////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/rtl/iscachable.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A helper function to both dcache and its formal properties,
//		used to determine when a particular address is cachable.  This
//	module must be built of entirely combinatorial logic and nothing more.
//
//	This particular version is taylored to the test bench configuration
//	of the ZipCPU.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2025, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	iscachable #(
		// {{{
		parameter	ADDRESS_WIDTH=28,
		localparam	AW = ADDRESS_WIDTH, // Just for ease of notation below
		parameter [AW-1:0] 	MEM_ADDR  = {4'b0100, {(ADDRESS_WIDTH-4){1'b0}} },
		parameter [AW-1:0] 	MEM_MASK  = {4'b1111, {(ADDRESS_WIDTH-4){1'b0}} }
		// }}}
	) (
		// {{{
		input	wire	[AW-1:0]	i_addr,
		output	reg			o_cachable
		// }}}
	);


	always @(*)
	begin
		o_cachable = 1'b0;
		if ((MEM_ADDR !=0)&&((i_addr & MEM_MASK)== MEM_ADDR))
			o_cachable = 1'b1;
	end

endmodule
