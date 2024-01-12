////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fwb_counter.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2017-2024, Gisselquist Technology, LLC
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
module	fwb_counter(i_clk, i_reset,
		// The Wishbone bus
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_idata, i_wb_err,
		// Some convenience output parameters
		f_nreqs, f_nacks, f_outstanding);
	parameter		AW=32, DW=32;
	parameter		F_MAX_STALL = 0,
				F_MAX_ACK_DELAY = 0;
	parameter		F_LGDEPTH = 4;
	parameter [(F_LGDEPTH-1):0] F_MAX_REQUESTS = 0;
	//
	// If true, allow the bus to be kept open when there are no outstanding
	// requests.  This is useful for any master that might execute a
	// read modify write cycle, such as an atomic add.
	parameter [0:0]		F_OPT_RMW_BUS_OPTION = 1;
	//
	// 
	// If true, allow the bus to issue multiple discontinuous requests.
	// Unlike F_OPT_RMW_BUS_OPTION, these requests may be issued while other
	// requests are outstanding
	parameter	[0:0]	F_OPT_DISCONTINUOUS = 0;
	//
	//
	// If true, insist that there be a minimum of a single clock delay
	// between request and response.  This defaults to off since the
	// wishbone specification specifically doesn't require this.  However,
	// some interfaces do, so we allow it as an option here.
	parameter	[0:0]	F_OPT_MINCLOCK_DELAY = 0;
	//
	//
	localparam [(F_LGDEPTH-1):0] MAX_OUTSTANDING = {(F_LGDEPTH){1'b1}};
	localparam	MAX_DELAY = (F_MAX_STALL > F_MAX_ACK_DELAY)
				? F_MAX_STALL : F_MAX_ACK_DELAY;
	localparam	DLYBITS= (MAX_DELAY < 4) ? 2
				: ((MAX_DELAY <    16) ? 4
				: ((MAX_DELAY <    64) ? 6
				: ((MAX_DELAY <   256) ? 8
				: ((MAX_DELAY <  1024) ? 10
				: ((MAX_DELAY <  4096) ? 12
				: ((MAX_DELAY < 16384) ? 14
				: ((MAX_DELAY < 65536) ? 16
				: 32)))))));
	//
	input	wire			i_clk, i_reset;
	// Input/master bus
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[(AW-1):0]	i_wb_addr;
	input	wire	[(DW-1):0]	i_wb_data;
	input	wire	[(DW/8-1):0]	i_wb_sel;
	//
	input	wire			i_wb_ack;
	input	wire			i_wb_stall;
	input	wire	[(DW-1):0]	i_wb_idata;
	input	wire			i_wb_err;
	//
	output	reg	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks;
	output	wire	[(F_LGDEPTH-1):0]	f_outstanding;

	//
	// Let's just make sure our parameters are set up right
	//
	always @(*)
		assert(F_MAX_REQUESTS < {(F_LGDEPTH){1'b1}});

	//
	//
	// Bus requests
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Count outstanding requests vs acknowledgments
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Count the number of requests that have been received
	//
	initial	f_nreqs = 0;
	always @(posedge i_clk)
	if ((i_reset)||(!i_wb_cyc))
		f_nreqs <= 0;
	else if ((i_wb_stb)&&(!i_wb_stall))
		f_nreqs <= f_nreqs + 1'b1;


	//
	// Count the number of acknowledgements that have been returned
	//
	initial	f_nacks = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_nacks <= 0;
	else if (!i_wb_cyc)
		f_nacks <= 0;
	else if ((i_wb_ack)||(i_wb_err))
		f_nacks <= f_nacks + 1'b1;

	//
	// The number of outstanding requests is the difference between
	// the number of requests and the number of acknowledgements
	//
	assign	f_outstanding = (i_wb_cyc) ? (f_nreqs - f_nacks):0;
	// }}}
endmodule
