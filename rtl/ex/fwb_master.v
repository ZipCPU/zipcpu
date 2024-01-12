////////////////////////////////////////////////////////////////////////////////
//
// Filename:	fwb_master.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This file describes the rules of a wishbone interaction from the
//		perspective of a wishbone master.  These formal rules may be
//	used with SymbiYosys to *prove* that the master properly handles
//	outgoing transactions and incoming responses.
//
//	This module contains no functional logic.  It is intended for formal
//	verification only.  The outputs returned, the number of requests that
//	have been made, the number of acknowledgements received, and the number
//	of outstanding requests, are designed for further formal verification
//	purposes *only*.
//
//	This file is different from a companion formal_slave.v file in that the
//	assertions are made on the outputs of the wishbone master: o_wb_cyc,
//	o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, and o_wb_sel, while only
//	assumptions are made about the inputs: i_wb_stall, i_wb_ack, i_wb_data,
//	i_wb_err.  In the formal_slave.v, assumptions are made about the
//	slave inputs (the master outputs), and assertions are made about the
//	slave outputs (the master inputs).
//
//	In order to make it easier to compare the slave against the master,
//	assumptions with respect to the slave have been marked with the
//	`SLAVE_ASSUME macro.  Similarly, assertions the slave would make have
//	been marked with `SLAVE_ASSERT.  This allows the master to redefine
//	these two macros to be from his perspective, and therefore the
//	diffs between the two files actually show true differences, rather
//	than just these differences in perspective.
//
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
module	fwb_master #(
		// {{{
		parameter		AW=32, DW=32,
		parameter		F_MAX_STALL = 0,
					F_MAX_ACK_DELAY = 0,
		parameter		F_LGDEPTH = 4,
		parameter [(F_LGDEPTH-1):0] F_MAX_REQUESTS = 0,
		// OPT_BUS_ABORT: If true, the master can drop CYC at any time
		// and must drop CYC following any bus error
		parameter [0:0]		OPT_BUS_ABORT = 1'b1,
		//
		// If true, allow the bus to be kept open when there are no
		// outstanding requests.  This is useful for any master that
		// might execute a read modify write cycle, such as an atomic
		// add.
		parameter [0:0]		F_OPT_RMW_BUS_OPTION = 1,
		//
		//
		// If true, allow the bus to issue multiple discontinuous
		// requests.
		// Unlike F_OPT_RMW_BUS_OPTION, these requests may be issued
		// while other requests are outstanding
		parameter	[0:0]	F_OPT_DISCONTINUOUS = 1,
		//
		//
		// If true, insist that there be a minimum of a single clock
		// delay between request and response.  This defaults to off
		// since the wishbone specification specifically doesn't
		// require this.  However, some interfaces do, so we allow it
		// as an option here.
		parameter	[0:0]	F_OPT_MINCLOCK_DELAY = 0,
		//
		//
		//
		localparam [(F_LGDEPTH-1):0] MAX_OUTSTANDING
						= {(F_LGDEPTH){1'b1}},
		localparam	MAX_DELAY = (F_MAX_STALL > F_MAX_ACK_DELAY)
				? F_MAX_STALL : F_MAX_ACK_DELAY,
		localparam	DLYBITS= (MAX_DELAY < 4) ? 2
				: (MAX_DELAY >= 65536) ? 32
				: $clog2(MAX_DELAY+1),
		//
		parameter [0:0]		F_OPT_SHORT_CIRCUIT_PROOF = 0,
		//
		// If this is the source of a request, then we can assume STB and CYC
		// will initially start out high.  Master interfaces following the
		// source on the way to the slave may not have this property
		parameter [0:0]		F_OPT_SOURCE = 0
		//
		//
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// The Wishbone bus
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(AW-1):0]	i_wb_addr,
		input	wire	[(DW-1):0]	i_wb_data,
		input	wire	[(DW/8-1):0]	i_wb_sel,
		//
		input	wire			i_wb_ack,
		input	wire			i_wb_stall,
		input	wire	[(DW-1):0]	i_wb_idata,
		input	wire			i_wb_err,
		// Some convenience output parameters
		output	reg	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks,
		output	wire	[(F_LGDEPTH-1):0]	f_outstanding
		// }}}
	);

`define	SLAVE_ASSUME	assert
`define	SLAVE_ASSERT	assume
	//
	// Let's just make sure our parameters are set up right
	// {{{
	initial	assert(F_MAX_REQUESTS < {(F_LGDEPTH){1'b1}});
	// }}}

	// f_request
	// {{{
	// Wrap the request line in a bundle.  The top bit, named STB_BIT,
	// is the bit indicating whether the request described by this vector
	// is a valid request or not.
	//
	localparam	STB_BIT = 2+AW+DW+DW/8-1;
	wire	[STB_BIT:0]	f_request;
	assign	f_request = { i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };
	// }}}

	// f_past_valid and i_reset
	// {{{
	// A quick register to be used later to know if the $past() operator
	// will yield valid result
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		`SLAVE_ASSUME(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions regarding the initial (and reset) state
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Assume we start from a reset condition
	initial assert(i_reset);
	initial `SLAVE_ASSUME(!i_wb_cyc);
	initial `SLAVE_ASSUME(!i_wb_stb);
	//
	initial	`SLAVE_ASSERT(!i_wb_ack);
	initial	`SLAVE_ASSERT(!i_wb_err);

`ifdef	VERIFIC
	always @(*)
	if (!f_past_valid)
	begin
		`SLAVE_ASSUME(!i_wb_cyc);
		`SLAVE_ASSUME(!i_wb_stb);
		//
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
	end
`endif
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		`SLAVE_ASSUME(!i_wb_cyc);
		`SLAVE_ASSUME(!i_wb_stb);
		//
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
	end

	always @(*)
	if (!f_past_valid)
		`SLAVE_ASSUME(!i_wb_cyc);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus requests
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Following any bus error, the CYC line should be dropped to abort
	// the transaction
	always @(posedge i_clk)
	if (f_past_valid && OPT_BUS_ABORT && $past(i_wb_err)&& $past(i_wb_cyc))
		`SLAVE_ASSUME(!i_wb_cyc);

	always @(*)
	if (!OPT_BUS_ABORT && !i_reset && (f_nreqs != f_nacks))
		`SLAVE_ASSUME(i_wb_cyc);

	always @(posedge i_clk)
	if (f_past_valid && !OPT_BUS_ABORT
			&& $past(!i_reset && i_wb_stb && i_wb_stall))
		`SLAVE_ASSUME(i_wb_cyc);

	// STB can only be true if CYC is also true
	always @(*)
	if (i_wb_stb)
		`SLAVE_ASSUME(i_wb_cyc);

	// If a request was both outstanding and stalled on the last clock,
	// then nothing should change on this clock regarding it.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wb_stb))
			&&($past(i_wb_stall))&&(i_wb_cyc))
	begin
		`SLAVE_ASSUME(i_wb_stb);
		`SLAVE_ASSUME(i_wb_we   == $past(i_wb_we));
		`SLAVE_ASSUME(i_wb_addr == $past(i_wb_addr));
		`SLAVE_ASSUME(i_wb_sel  == $past(i_wb_sel));
		if (i_wb_we)
			`SLAVE_ASSUME(i_wb_data == $past(i_wb_data));
	end

	// Within any series of STB/requests, the direction of the request
	// may not change.
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_wb_stb))&&(i_wb_stb))
		`SLAVE_ASSUME(i_wb_we == $past(i_wb_we));


	// Within any given bus cycle, the direction may *only* change when
	// there are no further outstanding requests.
	always @(posedge i_clk)
	if ((f_past_valid)&&(f_outstanding > 0))
		`SLAVE_ASSUME(i_wb_we == $past(i_wb_we));

	// Write requests must also set one (or more) of i_wb_sel
	//
	// This test has been removed since down-sizers (taking bus from width
	// DW to width dw < DW) might actually create empty requests that this
	// would prevent.  Re-enabling it would also complicate AXI to WB
	// transfers, since AXI explicitly allows WSTRB == 0.  Finally, this
	// criteria isn't found in the WB spec--so while it might be a good
	// idea to check, in hind sight there are too many exceptions to be
	// dogmatic about it.
	//
	// always @(*)
	// if ((i_wb_stb)&&(i_wb_we))
	//	`SLAVE_ASSUME(|i_wb_sel);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus responses
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// If CYC was low on the last clock, then both ACK and ERR should be
	// low on this clock.
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_wb_cyc))&&(!i_wb_cyc))
	begin
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
		// Stall may still be true--such as when we are not
		// selected at some arbiter between us and the slave
	end

	//
	// Any time the CYC line drops, it is possible that there may be a
	// remaining (registered) ACK or ERR that hasn't yet been returned.
	// Restrict such out of band returns so that they are *only* returned
	// if there is an outstanding operation.
	//
	// Update: As per spec, WB-classic to WB-pipeline conversions require
	// that the ACK|ERR might come back on the same cycle that STB
	// is low, yet also be registered.  Hence, if STB & STALL are true on
	// one cycle, then CYC is dropped, ACK|ERR might still be true on the
	// cycle when CYC is dropped
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wb_cyc))&&(!i_wb_cyc))
	begin
		// Note that, unlike f_outstanding, f_nreqs and f_nacks are both
		// registered.  Hence, we can check here if a response is still
		// pending.  If not, no response should be returned.
		if (f_nreqs == f_nacks)
		begin
			`SLAVE_ASSERT(!i_wb_ack);
			`SLAVE_ASSERT(!i_wb_err);
		end
	end

	// ACK and ERR may never both be true at the same time
	always @(*)
		`SLAVE_ASSERT((!i_wb_ack)||(!i_wb_err));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stall checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (F_MAX_STALL > 0)
	begin : MXSTALL
		//
		// Assume the slave cannnot stall for more than F_MAX_STALL
		// counts.  We'll count this forward any time STB and STALL
		// are both true.
		//
		reg	[(DLYBITS-1):0]		f_stall_count;

		initial	f_stall_count = 0;
		always @(posedge i_clk)
		if ((!i_reset)&&(i_wb_stb)&&(i_wb_stall))
			f_stall_count <= f_stall_count + 1'b1;
		else
			f_stall_count <= 0;

		always @(*)
		if (i_wb_cyc)
			`SLAVE_ASSERT(f_stall_count < F_MAX_STALL);
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Maximum delay in any response
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (F_MAX_ACK_DELAY > 0)
	begin : MXWAIT
		//
		// Assume the slave will respond within F_MAX_ACK_DELAY cycles,
		// counted either from the end of the last request, or from the
		// last ACK received
		//
		reg	[(DLYBITS-1):0]		f_ackwait_count;

		initial	f_ackwait_count = 0;
		always @(posedge i_clk)
		if ((!i_reset)&&(i_wb_cyc)&&(!i_wb_stb)
				&&(!i_wb_ack)&&(!i_wb_err)
				&&(f_outstanding > 0))
			f_ackwait_count <= f_ackwait_count + 1'b1;
		else
			f_ackwait_count <= 0;

		always @(*)
		if ((!i_reset)&&(i_wb_cyc)&&(!i_wb_stb)
					&&(!i_wb_ack)&&(!i_wb_err)
					&&(f_outstanding > 0))
			`SLAVE_ASSERT(f_ackwait_count < F_MAX_ACK_DELAY);
	end endgenerate
	// }}}
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

	always @(*)
	if ((i_wb_cyc)&&(F_MAX_REQUESTS > 0))
	begin
		if (i_wb_stb)
		begin
			`SLAVE_ASSUME(f_nreqs < F_MAX_REQUESTS);
		end else
			`SLAVE_ASSUME(f_nreqs <= F_MAX_REQUESTS);
		`SLAVE_ASSERT(f_nacks <= f_nreqs);
		assert(f_outstanding < MAX_OUTSTANDING);
	end else
		assume(f_outstanding < MAX_OUTSTANDING);

	always @(*)
	if ((i_wb_cyc)&&(f_outstanding == 0))
	begin
		// If nothing is outstanding, then there should be
		// no acknowledgements ... however, an acknowledgement
		// *can* come back on the same clock as the stb is
		// going out.
		if (F_OPT_MINCLOCK_DELAY)
		begin
			`SLAVE_ASSERT(!i_wb_ack);
			`SLAVE_ASSERT(!i_wb_err);
		end else begin
			`SLAVE_ASSERT((!i_wb_ack)||((i_wb_stb)&&(!i_wb_stall)));
			// The same is true of errors.  They may not be
			// created before the request gets through
			`SLAVE_ASSERT((!i_wb_err)||((i_wb_stb)&&(!i_wb_stall)));
		end
	end else if (!i_wb_cyc && f_nacks == f_nreqs)
	begin
		`SLAVE_ASSERT(!i_wb_ack);
		`SLAVE_ASSERT(!i_wb_err);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus direction
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (!F_OPT_RMW_BUS_OPTION)
	begin
		// If we aren't waiting for anything, and we aren't issuing
		// any requests, then then our transaction is over and we
		// should be dropping the CYC line.
		always @(*)
		if (f_outstanding == 0)
			`SLAVE_ASSUME((i_wb_stb)||(!i_wb_cyc));
		// Not all masters will abide by this restriction.  Some
		// masters may wish to implement read-modify-write bus
		// interactions.  These masters need to keep CYC high between
		// transactions, even though nothing is outstanding.  For
		// these busses, turn F_OPT_RMW_BUS_OPTION on.
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Discontinuous request checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if ((!F_OPT_DISCONTINUOUS)&&(!F_OPT_RMW_BUS_OPTION))
	begin : INSIST_ON_NO_DISCONTINUOUS_STBS
		// Within my own code, once a request begins it goes to
		// completion and the CYC line is dropped.  The master
		// is not allowed to raise STB again after dropping it.
		// Doing so would be a *discontinuous* request.
		//
		// However, in any RMW scheme, discontinuous requests are
		// necessary, and the spec doesn't disallow them.  Hence we
		// make this check optional.
		always @(posedge i_clk)
		if ((f_past_valid)&&($past(i_wb_cyc))&&(!$past(i_wb_stb)))
			`SLAVE_ASSUME(!i_wb_stb);
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Master only checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (F_OPT_SHORT_CIRCUIT_PROOF)
	begin
		// In many ways, we don't care what happens on the bus return
		// lines if the cycle line is low, so restricting them to a
		// known value makes a lot of sense.
		//
		// On the other hand, if something above *does* depend upon
		// these values (when it shouldn't), then we might want to know
		// about it.
		//
		//
		always @(posedge i_clk)
		begin
			if (!i_wb_cyc)
			begin
				assume(!i_wb_stall);
				assume($stable(i_wb_idata));
			end else if ((!$past(i_wb_ack))&&(!i_wb_ack))
				assume($stable(i_wb_idata));
		end
	end endgenerate

	generate if (F_OPT_SOURCE)
	begin : SRC
		// Any opening bus request starts with both CYC and STB high
		// This is true for the master only, and more specifically
		// only for those masters that are the initial source of any
		// transaction.  By the time an interaction gets to the slave,
		// the CYC line may go high or low without actually affecting
		// the STB line of the slave.
		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_wb_cyc))&&(i_wb_cyc))
			`SLAVE_ASSUME(i_wb_stb);
	end endgenerate
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, f_request };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
`undef	SLAVE_ASSUME
`undef	SLAVE_ASSERT
