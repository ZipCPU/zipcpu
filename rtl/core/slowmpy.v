////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	slowmpy.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a signed (OPT_SIGNED=1) or unsigned (OPT_SIGNED=0)
// 		multiply designed for low logic and slow data signals.  It
// 	takes one clock per bit plus two more to complete the multiply.
//
//	The OPT_SIGNED version of this algorithm was found on Wikipedia at
//	https://en.wikipedia.org/wiki/Binary_multiplier.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018-2020, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
//
module	slowmpy(i_clk, i_reset, i_stb, i_a, i_b, i_aux, o_busy,
		o_done, o_p, o_aux);
	parameter			LGNA = 6;
	parameter	[LGNA:0]	NA = 33;
	parameter	[0:0]		OPT_SIGNED = 1'b1;
	localparam	NB = NA;	// Must be = NA for OPT_SIGNED to work
	//
	input	wire	i_clk, i_reset;
	//
	input	wire	i_stb;
	input	wire	signed	[(NA-1):0]	i_a;
	input	wire	signed	[(NB-1):0]	i_b;
	input	wire				i_aux;
	output	reg				o_busy, o_done;
	output	reg	signed	[(NA+NB-1):0]	o_p;
	output	reg				o_aux;

	reg	[LGNA-1:0]	count;
	reg	[NA-1:0]	p_a;
	reg	[NB-1:0]	p_b;
	reg	[NA+NB-1:0]	partial;
	reg			aux;

	reg	almost_done;

	wire	pre_done;
	assign	pre_done = (count == 0);
	initial	almost_done = 1'b0;
	always @(posedge i_clk)
		almost_done <= (!i_reset)&&(o_busy)&&(pre_done);

	initial	aux    = 0;
	initial	o_done = 0;
	initial	o_busy = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		aux    <= 0;
		o_done <= 0;
		o_busy <= 0;
	end else if ((!o_busy)&&(i_stb))
	begin
		o_done <= 0;
		o_busy <= 1;
		aux    <= i_aux;
	end else if ((o_busy)&&(almost_done))
	begin
		o_done <= 1;
		o_busy <= 0;
	end else
		o_done <= 0;

	wire	[NA-1:0]	pwire;
	assign	pwire = (p_b[0] ? p_a : 0);

	always @(posedge i_clk)
	if (!o_busy)
	begin
		count <= NA[LGNA-1:0]-1;
		partial <= 0;
		p_a <= i_a;
		p_b <= i_b;
	end else begin
		p_b <= (p_b >> 1);
		// partial[NA+NB-1:NB] <= partial[NA+NB
		partial[NB-2:0] <= partial[NB-1:1];
		if ((OPT_SIGNED)&&(pre_done))
			partial[NA+NB-1:NB-1] <= { 1'b0, partial[NA+NB-1:NB]} +
				{ 1'b0, pwire[NA-1], ~pwire[NA-2:0] };
		else if (OPT_SIGNED)
			partial[NA+NB-1:NB-1] <= {1'b0,partial[NA+NB-1:NB]} +
				{ 1'b0, !pwire[NA-1], pwire[NA-2:0] };
		else
			partial[NA+NB-1:NB-1] <= {1'b0, partial[NA+NB-1:NB]}
				+ ((p_b[0]) ? {1'b0,p_a} : 0);
		count <= count - 1;
	end

	always @(posedge i_clk)
	if (almost_done)
	begin
		if (OPT_SIGNED)
			o_p   <= partial[NA+NB-1:0]
				+ {1'b1,{(NA-2){1'b0}},1'b1, {(NB){1'b0}}};
		else
			o_p   <= partial[NA+NB-1:0];
		o_aux <= aux;
	end

`ifdef	FORMAL
`define	ASSERT	assert
`ifdef	SLOWMPY
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	initial	assume(i_reset);
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		`ASSERT(almost_done == 0);
		`ASSERT(o_done == 0);
		`ASSERT(o_busy == 0);
		`ASSERT(aux == 0);
	end

	// Assumptions about our inputs
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_stb))&&($past(o_busy)))
	begin
		`ASSUME(i_stb);
		`ASSUME($stable(i_a));
		`ASSUME($stable(i_b));
	end

	//
	// For now, just formally verify our internal signaling
	//

	always @(posedge i_clk)
		`ASSERT(almost_done == (o_busy&&(&count)));

	always @(*)
		if (!(&count[LGNA-1:1])||(count[0]))
			`ASSERT(!o_done);

	always @(posedge i_clk)
	if (o_done)
		`ASSERT(!o_busy);
	always @(posedge i_clk)
	if (!o_busy)
		`ASSERT(!almost_done);

	reg	[NA-1:0]	f_a, f_b;
	always @(posedge i_clk)
	if ((i_stb)&&(!o_busy))
	begin
		f_a <= i_a;
		f_b <= i_b;
	end

	always @(*)
	if (o_done)
	begin
		if ((f_a == 0)||(f_b == 0))
			`ASSERT(o_p == 0);
		else
			`ASSERT(o_p[NA+NB-1] == f_a[NA-1] ^ f_b[NA-1]);
	end

	always @(posedge i_clk)
		cover(o_done);

	reg	f_past_done;
	initial	f_past_done = 1'b0;
	always @(posedge i_clk)
	if (o_done)
		f_past_done = 1'b1;

	always @(posedge i_clk)
		cover((o_done)&&(f_past_done));
`endif
endmodule
