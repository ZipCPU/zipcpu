////////////////////////////////////////////////////////////////////////////////
//
// Filename:	busdelay.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Delay any access to the wishbone bus by a single clock.
//
//	When the first Zip System would not meet the timing requirements of
//	the board it was placed upon, this bus delay was added to help out.
//	It may no longer be necessary, having cleaned some other problems up
//	first, but it will remain here as a means of alleviating timing
//	problems.
//
//	The specific problem takes place on the stall line: a wishbone master
//	*must* know on the first clock whether or not the bus will stall.
//
//
//	After a period of time, I started a new design where the timing
//	associated with this original bus clock just wasn't ... fast enough.
//	I needed to delay the stall line as well.  A new busdelay was then
//	written and debugged whcih delays the stall line.  (I know, you aren't
//	supposed to delay the stall line--but what if you *have* to in order
//	to meet timing?)  This new logic has been merged in with the old,
//	and the DELAY_STALL line can be set to non-zero to use it instead
//	of the original logic.  Don't use it if you don't need it: it will
//	consume resources and slow your bus down more, but if you do need
//	it--don't be afraid to use it.  
//
//	Both versions of the bus delay will maintain a single access per
//	clock when pipelined, they only delay the time between the strobe
//	going high and the actual command being accomplished.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
module	busdelay #(
		// {{{
		parameter		AW=32, DW=32,
`ifdef	FORMAL
		localparam		F_LGDEPTH=4,
`endif
		parameter	 [0:0]	DELAY_STALL  = 1,
		parameter	 [0:0]	OPT_LOWPOWER = 0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Input/master bus
		// {{{
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(AW-1):0]	i_wb_addr,
		input	wire	[(DW-1):0]	i_wb_data,
		input	wire	[(DW/8-1):0]	i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[(DW-1):0]	o_wb_data,
		output	reg			o_wb_err,
		// }}}
		// Delayed bus
		// {{{
		output	reg			o_dly_cyc, o_dly_stb, o_dly_we,
		output	reg	[(AW-1):0]	o_dly_addr,
		output	reg	[(DW-1):0]	o_dly_data,
		output	reg	[(DW/8-1):0]	o_dly_sel,
		input	wire			i_dly_stall,
		input	wire			i_dly_ack,
		input	wire	[(DW-1):0]	i_dly_data,
		input	wire			i_dly_err
		// }}}
		// }}}
	);

`ifdef	FORMAL
	wire	[2+AW+DW+DW/8-1:0]	f_wpending;
`endif

	generate if (DELAY_STALL)
	begin : SKIDBUFFER
		// {{{
		reg			r_stb, r_we;
		reg	[(AW-1):0]	r_addr;
		reg	[(DW-1):0]	r_data;
		reg	[(DW/8-1):0]	r_sel;

		// o_dly_cyc
		// {{{
		initial	o_dly_cyc  = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc)
			o_dly_cyc <= 1'b0;
		else
			o_dly_cyc <= (!o_wb_err)&&((!i_dly_err)||(!o_dly_cyc));
		// }}}

		// o_dly_stb
		// {{{
		initial	o_dly_stb  = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc || o_wb_err || (o_dly_cyc && i_dly_err))
			o_dly_stb <= 1'b0;
		else if (!o_dly_stb || !i_dly_stall)
			o_dly_stb <= i_wb_stb || r_stb;
		// }}}

		// r_stb
		// {{{
		initial	r_stb      = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc || o_wb_err || i_dly_err
					|| !i_dly_stall || !o_dly_stb)
			r_stb <= 1'b0;
		else if (i_wb_stb && !o_wb_stall) // && (o_dly_stb&&i_dly_stall)
			r_stb <= 1'b1;
		// }}}

		// r_*
		// {{{
		initial { r_we, r_addr, r_data, r_sel } = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || !i_wb_cyc || i_dly_err
					|| !o_dly_stb || !i_dly_stall))
			{ r_we, r_addr, r_data, r_sel } <= 0;
		else if (i_wb_stb && !o_wb_stall) // && (o_dly_stb&&i_dly_stall)
			{ r_we, r_addr, r_data, r_sel }
				<= { i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };
		// }}}

		initial	o_dly_we   = 1'b0;
		initial	o_dly_addr = 0;
		initial	o_dly_data = 0;
		initial	o_dly_sel  = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || (!i_wb_cyc || o_wb_err || (o_dly_cyc && i_dly_err))))
			{ o_dly_we, o_dly_addr, o_dly_data, o_dly_sel } <= 0;
		else if (!o_dly_stb || !i_dly_stall)
		begin
			if (r_stb)
				{ o_dly_we, o_dly_addr, o_dly_data, o_dly_sel } <= { r_we, r_addr, r_data, r_sel };
			else if (!OPT_LOWPOWER || i_wb_stb)
				{ o_dly_we, o_dly_addr, o_dly_data, o_dly_sel } <= { i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };
			else
				{ o_dly_addr, o_dly_data, o_dly_sel } <= 0;

		end

		assign	o_wb_stall = r_stb;

		// o_wb_ack
		// {{{
		initial	o_wb_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc || o_wb_err || !o_dly_cyc)
			o_wb_ack <= 1'b0;
		else
			o_wb_ack  <= (i_dly_ack);
		// }}}

		// o_wb_data
		// {{{
		initial	o_wb_data = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || !i_wb_cyc || !o_dly_cyc
				|| o_wb_err || !i_dly_ack))
			o_wb_data <= 0;
		else
			o_wb_data <= i_dly_data;
		// }}}

		// o_wb_err
		// {{{
		initial	o_wb_err   = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wb_cyc || !o_dly_cyc)
			o_wb_err <= 1'b0;
		else
			o_wb_err  <= i_dly_err;
		// }}}


`ifdef	FORMAL
	// {{{
		assign	f_wpending = { r_stb, r_we, r_addr, r_data, r_sel };

		always @(*)
		if (OPT_LOWPOWER && !r_stb)
		begin
			assert(r_we   == 0);
			assert(r_addr == 0);
			assert(r_data == 0);
			assert(r_sel  == 0);
		end else if (r_stb)
			assert(r_we == o_dly_we);
		// }}}
`endif
		// }}}
	end else begin : NO_SKIDBUFFER
		// {{{
		initial	o_dly_cyc   = 1'b0;
		initial	o_dly_stb   = 1'b0;
		initial	o_dly_we    = 1'b0;
		initial	o_dly_addr  = 0;
		initial	o_dly_data  = 0;
		initial	o_dly_sel   = 0;

		always @(posedge i_clk)
		if (i_reset)
			o_dly_cyc <= 1'b0;
		else if ((i_dly_err)&&(o_dly_cyc))
			o_dly_cyc <= 1'b0;
		else if ((o_wb_err)&&(i_wb_cyc))
			o_dly_cyc <= 1'b0;
		else
			o_dly_cyc <= i_wb_cyc;

		// Add the i_wb_cyc criteria here, so we can simplify the
		// o_wb_stall criteria below, which would otherwise *and*
		// these two.
		always @(posedge i_clk)
		if (i_reset)
			o_dly_stb <= 1'b0;
		else if ((i_dly_err)&&(o_dly_cyc))
			o_dly_stb <= 1'b0;
		else if ((o_wb_err)&&(i_wb_cyc))
			o_dly_stb <= 1'b0;
		else if (!i_wb_cyc)
			o_dly_stb <= 1'b0;
		else if (!o_wb_stall)
			o_dly_stb <= (i_wb_stb);

		always @(posedge i_clk)
		if (!o_wb_stall)
			o_dly_we  <= i_wb_we;

		initial	o_dly_addr = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || !i_wb_cyc || o_wb_err
						|| (o_dly_cyc && i_dly_err)))
			{ o_dly_addr, o_dly_data, o_dly_sel } <= 0;
		else if (!o_dly_stb || !i_dly_stall)
		begin
			{ o_dly_addr, o_dly_data, o_dly_sel }	
				<= { i_wb_addr, i_wb_data, i_wb_sel };
			if (OPT_LOWPOWER && !i_wb_stb)
				{ o_dly_addr, o_dly_data, o_dly_sel } <= 0;
		end

		initial	o_wb_ack    = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_wb_ack <= 1'b0;
		else
			o_wb_ack  <= ((i_dly_ack)&&(!i_dly_err)
				&&(o_dly_cyc)&&(i_wb_cyc))
				&&(!o_wb_err);

		initial	o_wb_err    = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_wb_err <= 1'b0;
		else if (!o_dly_cyc)
			o_wb_err <= 1'b0;
		else
			o_wb_err  <= (o_wb_err)||(i_dly_err)&&(i_wb_cyc);

		initial	o_wb_data   = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (i_reset || !i_wb_cyc || !o_dly_cyc || o_wb_err || !i_dly_ack))
			o_wb_data <= 0;
		else
			o_wb_data <= i_dly_data;

		// Our only non-delayed line, yet still really delayed.  Perhaps
		// there's a way to register this?
		// o_wb_stall <= (i_wb_cyc)&&(i_wb_stb) ... or some such?
		// assign o_wb_stall=((i_wb_cyc)&&(i_dly_stall)&&(o_dly_stb));//&&o_cyc
		assign	o_wb_stall = (i_dly_stall)&&(o_dly_stb);

`ifdef	FORMAL
		// f_wpending isn't used if DELAY_STALL is zero, but we'll give
		// it a seemingly useful value anyway--if for no other reason
		// than to be sure we set it to the right number of bits
		assign	f_wpending = { i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };
`endif
		// }}}
	end endgenerate
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
	// Declarations
	// {{{
`ifdef	BUSDELAY
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	localparam	ACK_DELAY = 5,
			STALL_DELAY = 4;
	localparam	STB_BIT = 2+AW+DW+DW/8-1;

	wire	[(F_LGDEPTH-1):0]	f_wb_nreqs,f_wb_nacks, f_wb_outstanding,
				f_dly_nreqs, f_dly_nacks, f_dly_outstanding;

	wire				f_wb_busy, f_dly_busy, f_wb_req, f_dly_req;
	wire	[STB_BIT:0]		f_wb_request, f_dly_request;
	reg	[STB_BIT:0]		f_pending;
	reg	[(F_LGDEPTH-1):0]	f_pending_acks;
	reg	[(F_LGDEPTH-1):0]	f_pending_reqs;
	reg	[(F_LGDEPTH-1):0]	f_expected, f_exp_nreqs, f_exp_nacks;

	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;
	// }}}

	initial	`ASSUME(i_reset);
	always @(*)
		if (!f_past_valid)
			`ASSUME(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_slave #(.AW(AW), .DW(DW),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(STALL_DELAY+1),
			.F_MAX_ACK_DELAY(ACK_DELAY+1+2*STALL_DELAY),
			.F_MAX_REQUESTS((1<<F_LGDEPTH)-2),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbs(i_clk, i_reset,
			i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
				i_wb_sel,
			o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
			f_wb_nreqs, f_wb_nacks, f_wb_outstanding);

	fwb_master #(.AW(AW), .DW(DW),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_STALL(STALL_DELAY),
			.F_MAX_ACK_DELAY(ACK_DELAY),
			.F_MAX_REQUESTS(0),
			.F_OPT_RMW_BUS_OPTION(1),
			.F_OPT_DISCONTINUOUS(1))
		f_wbm(i_clk, i_reset,
			o_dly_cyc, o_dly_stb, o_dly_we, o_dly_addr, o_dly_data,
				o_dly_sel,
			i_dly_ack, i_dly_stall, i_dly_data, i_dly_err,
			f_dly_nreqs, f_dly_nacks, f_dly_outstanding);

	// }}}

	// WB and DLY request packets
	// {{{
	assign	f_wb_request = { i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };
	assign	f_dly_request={ o_dly_stb,o_dly_we,o_dly_addr,o_dly_data,o_dly_sel };
	// }}}

	// f_pending register
	// {{{
	initial	f_pending = 0;
	always @(posedge i_clk)
	if (!DELAY_STALL)
		f_pending = 0;
	else if ((i_reset)||(!i_wb_cyc)||(i_dly_err))
		f_pending[STB_BIT] <= 1'b0;
	else if ((i_wb_stb)&&(!o_wb_stall))
	begin
		f_pending <= f_wb_request;

		if ((!i_dly_stall)||(!o_dly_stb))
			f_pending[STB_BIT] <= 1'b0;

	end else if ((!i_dly_stall)&&(f_pending[STB_BIT]))
		f_pending[STB_BIT] <= 1'b0;
	// }}}

	assign	f_wb_busy  = (i_wb_stb )&&( o_wb_stall);
	assign	f_dly_busy = (o_dly_stb)&&( i_dly_stall);
	assign	f_wb_req   = (i_wb_stb )&&(!o_wb_stall);
	assign	f_dly_req  = (o_dly_stb)&&(!i_dly_stall);

	always @(posedge i_clk)
	if (!DELAY_STALL)
	begin
		if ((f_past_valid)&&($past(f_wb_req))&&(!$past(i_reset))
				&&(!$past(o_wb_err))&&(!o_wb_err))
			assert(($past(f_wb_request) == f_dly_request));
		if ((f_past_valid)&&($past(i_reset)))
			assert(!o_dly_stb);
		if ((f_past_valid)&&(!$past(i_wb_cyc)))
			assert(!o_dly_stb);
		if ((o_dly_stb)&&(i_dly_stall))
			assert(o_wb_stall);
	end else if ((DELAY_STALL)&&(f_past_valid))
	begin
		if ($past(i_reset))
			assert(!f_pending[STB_BIT]);
		if (!$past(f_dly_busy))
			assert(!f_pending[STB_BIT]);
		//
		if (($past(i_reset))||($past(i_dly_err)))
		begin
			assert(!f_pending[STB_BIT]);
		end else if ($past(f_wb_req))
		begin
			if ($past(f_dly_busy))
				assert($past(f_wb_request) == f_pending);
		end else if ((!$past(i_dly_stall))&&($past(f_pending[STB_BIT]))
				&&($past(i_wb_cyc)))
		begin
			assert(f_dly_request == $past(f_pending));
		end
	end

	// Constrain the induction solver: whatever's in our f_pending
	// hold register should be identical to whatever is in the f_wpending
	// wires above.
	always @(posedge i_clk)
	if ((DELAY_STALL)&&(f_past_valid)&&(!$past(i_reset) && i_wb_cyc && !o_wb_err))
	begin
		if (!$past(i_wb_cyc))
		begin
			assert((!f_pending[STB_BIT])
				&&(!f_wpending[STB_BIT]));
		end else if (($past(f_dly_busy))&&($past(f_wb_busy)))
		begin
			assert(f_pending == f_wpending);
		end else if(($past(f_dly_busy))&&($past(f_pending[STB_BIT])))
			assert(f_pending == f_wpending);
	end

	always @(posedge i_clk)
	if ((!DELAY_STALL)&&(f_past_valid)&&(!$past(i_reset))
			&&($past(i_wb_stb))&&(!$past(o_wb_stall))
			&&(!$past(o_wb_err))&&(!o_wb_err))
		assert(f_dly_request == $past(f_wb_request));

	always @(posedge i_clk)
	if ((DELAY_STALL)&&(!i_reset)&&(!o_wb_err))
		assert(f_pending[STB_BIT] == f_wpending[STB_BIT]);

	// Upon any request at the input, there should always be a request
	// on the output at the very next clock
	// {{{
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_wb_stb))&&(i_wb_cyc))
		assert((o_dly_stb)||(o_wb_err));
	// }}}

	// Following any dropping of CYC or raising of RESET, STB should
	// go down as well
	// {{{
	always @(posedge i_clk)
		if ((f_past_valid)&&(($past(!i_wb_cyc))||($past(i_reset))))
			assert(!o_dly_stb);

	always @(posedge i_clk)
	if ((DELAY_STALL)&&(f_past_valid)
			&&(!$past(i_reset))
			&&($past(i_wb_cyc))
			&&($past(f_pending[STB_BIT])))
	begin
		if ($past(i_dly_err))
		begin
			assert(!o_dly_stb);
		end else
			assert(o_dly_stb);
	end
	// }}}


	// Make sure we get no more than one ack per request
	// {{{
	always @(*)
	if (DELAY_STALL)
	begin
		f_pending_acks <= 0;
		if ((f_past_valid)
			&&((o_wb_err)||(o_wb_ack))
			&&(o_dly_cyc))
			f_pending_acks <= 1;
	end else
		f_pending_acks <= (((o_wb_ack)||(o_wb_err)) ? 1:0);

	always @(*)
	if (DELAY_STALL)
	begin
		f_pending_reqs <= ((o_dly_stb) ? 1:0)
			+ ((f_pending[STB_BIT]) ? 1:0);
	end else begin
		f_pending_reqs <= (!f_past_valid) ? 0 :
			((o_dly_stb) ? 1:0);
	end

	always @(*)
		f_expected <= f_dly_outstanding + f_pending_reqs+f_pending_acks;
	always @(*)
		f_exp_nreqs<= f_dly_nreqs + f_pending_reqs;
	always @(*)
		f_exp_nacks<= f_dly_nacks - f_pending_acks;
	always @(*)
	if (i_wb_cyc)
		assert(f_dly_outstanding <= f_wb_outstanding);

	always @(posedge i_clk)
		if ((!i_reset)&&(i_wb_cyc)&&(o_dly_cyc)&&(!i_dly_err))
			assert(f_expected == f_wb_outstanding);

	always @(posedge i_clk)
	if ((i_wb_cyc)&&(o_dly_cyc)&&(!i_reset)&&(!i_dly_err))
	begin
		assert(f_exp_nreqs == f_wb_nreqs);
		assert(f_exp_nacks == f_wb_nacks);
	end
	// }}}

	always @(posedge i_clk)
	if (i_wb_cyc && o_dly_stb || (f_wb_outstanding > 0 && f_dly_outstanding > 0))
		assert(i_wb_we == o_dly_we);

	////////////////////////////////////////////////////////////////////////
	//
	// The "never" property
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	BUSDELAY

	(* anyconst *)	reg	f_never;
	(* anyconst *)	reg	[STB_BIT:0]	f_nvr_request;

	always @(*)
	if (f_never && i_wb_stb)
		`ASSUME(f_wb_request != f_nvr_request);

	always @(*)
	if (f_never && f_pending[STB_BIT])
		assert(f_pending != f_nvr_request);

	always @(*)
	if (f_never && o_dly_stb)
		assert(f_dly_request != f_nvr_request);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Low power properties (if invoked)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_LOWPOWER)
	begin

		always @(*)
		if (!o_dly_stb)
		begin
			assert(o_dly_addr == 0);
			assert(o_dly_data == 0);
			assert(o_dly_sel  == 0);
		end

		always @(*)
		if (!o_wb_ack)
			assert(o_wb_data == 0);
	end endgenerate
	// }}}
`endif
// }}}
endmodule
