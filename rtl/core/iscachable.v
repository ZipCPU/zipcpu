////////////////////////////////////////////////////////////////////////////////
//
// Filename:	iscachable.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A helper function to both dcache and its formal properties,
//		used to determine when a particular address is cachable.  This
//	module must be built of entirely combinatorial logic and nothing more.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2018-2024, Gisselquist Technology, LLC
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
		parameter	ADDRESS_WIDTH=32,
		localparam	AW = ADDRESS_WIDTH, // Just for ease of notation below
		parameter [AW-1:0] 	SDRAM_ADDR  = 0, SDRAM_MASK = 0,
		parameter [AW-1:0] 	BKRAM_ADDR = 32'h10000000,
					BKRAM_MASK = 32'h10000000,
		parameter [AW-1:0] 	FLASH_ADDR  = 0, FLASH_MASK  = 0
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
		if ((SDRAM_ADDR !=0)&&((i_addr & SDRAM_MASK)== SDRAM_ADDR))
			o_cachable = 1'b1;
		else if ((FLASH_ADDR !=0)&&((i_addr & FLASH_MASK)== FLASH_ADDR))
			o_cachable = 1'b1;
		else if ((BKRAM_ADDR !=0)&&((i_addr & BKRAM_MASK)== BKRAM_ADDR))
			o_cachable = 1'b1;
	end

endmodule
