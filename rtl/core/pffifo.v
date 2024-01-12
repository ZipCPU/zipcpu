////////////////////////////////////////////////////////////////////////////////
//
// Filename:	pffifo.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a basic prefetch.  As with the other prefetches, its job
//		is to keep the CPU fed with instructions, (ideally) at one
//	instruction per clock cycle and with only a minimum number stalls.
//
//	This particular implementation is designed around a basic FIFO
//	implementation, like the dblfetch implementation, save that we allow a
//	FIFO that can hold more than two instructions at a time.  It will work
//	well for a CPU that doesn't do a lot of branching, but poorly under
//	a high branching load.
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
module	pffifo #(
		// {{{
		parameter	LGFIFO = 4,
		parameter	AW = 30,
		parameter	BUS_WIDTH = 128, // Num data bits on the bus
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter [0:0]	OPT_ASYNC_READ = (BUS_WIDTH != INSN_WIDTH),
		localparam	BUSW = BUS_WIDTH,
		parameter	INSN_WIDTH = 32,
		localparam	WBLSB = $clog2(BUS_WIDTH/8),
		localparam	ADDRESS_WIDTH=AW + WBLSB
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		// The interface with the rest of the CPU
		// {{{
		input	wire			i_new_pc,
		input	wire			i_clear_cache,
		input	wire			i_ready,
		input wire [ADDRESS_WIDTH-1:0]	i_pc,
		output	wire			o_valid,
		output	wire			o_illegal,
		output	wire [INSN_WIDTH-1:0]	o_insn,
		output reg [ADDRESS_WIDTH-1:0]	o_pc,
		// }}}
		// The wishbone bus interface
		// {{{
		output	reg			o_wb_cyc, o_wb_stb,
		// verilator coverage_off
		output	wire			o_wb_we,
		// verilator coverage_on
		output	reg	[AW-1:0]	o_wb_addr,
		// verilator coverage_off
		output	wire	[BUSW-1:0]	o_wb_data,
		output	wire	[BUSW/8-1:0]	o_wb_sel,
		// verilator coverage_on
		//
		input	wire			i_wb_stall, i_wb_ack, i_wb_err,
		input	wire	[BUSW-1:0]	i_wb_data
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam	INLSB = $clog2(INSN_WIDTH/8);

	reg			pending_err;
	reg	[LGFIFO:0]	wb_pending, pipe_fill;
	wire	[LGFIFO:0]	w_pipe_fill;
	wire			pipe_full, last_ack;

	wire			sfifo_reset, ign_sfifo_full, sfifo_empty,pf_err;
	wire	[LGFIFO:0]	sfifo_fill;	// Used to start operation
	wire	[BUS_WIDTH-1:0]	sfifo_word;
	wire			sfifo_read, pf_last;
`ifdef	FORMAL
	wire	[LGFIFO:0]	f_first_addr, f_second_addr,
				f_distance_to_first, f_distance_to_second;
	wire	[BUS_WIDTH:0]	f_first_data, f_second_data;
	wire			f_first_in_fifo, f_second_in_fifo;

	wire	[BUS_WIDTH-1:0]	f_wide_data;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Request instructions from the bus
	// {{{

	// o_wb_cyc, o_wb_stb, o_wb_addr, pending_err
	// {{{
	initial	pending_err = 1'b0;
	initial	{ o_wb_cyc, o_wb_stb } = 2'b00;
	always @(posedge i_clk)
	if (sfifo_reset)
	begin
		pending_err <= 1'b0;
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
		if (i_new_pc)
			o_wb_addr <= i_pc[ADDRESS_WIDTH-1:WBLSB];
		if (i_reset)
			o_wb_addr <= 0;
	end else if (o_wb_cyc && i_wb_err)
	begin
		pending_err <= 1'b1;
		o_wb_cyc <= 1'b0;
		o_wb_stb <= 1'b0;
		// Verilator lint_off WIDTH
		o_wb_addr <= o_wb_addr - wb_pending;
		// Verilator lint_on  WIDTH
	end else if (o_wb_cyc)
	begin
		pending_err <= 1'b0;
		if (o_wb_stb && !i_wb_stall)
			o_wb_addr <= o_wb_addr + 1;
		if (pipe_full && !i_wb_stall)
			o_wb_stb <= 1'b0;
		if ((!o_wb_stb || (pipe_full && !i_wb_stall)) && last_ack)
			o_wb_cyc <= 1'b0;
	end else if (sfifo_fill[LGFIFO:LGFIFO-1] == 2'b00 && !pending_err)
	begin
		o_wb_cyc <= 1'b1;
		o_wb_stb <= 1'b1;
		// o_wb_addr == same as before
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
		assert(o_wb_cyc == (o_wb_stb || wb_pending > 0));
`endif
	// }}}

	// o_wb_sel
	// {{{
	generate if (INSN_WIDTH == BUS_WIDTH)
	begin : GEN_ALWAYS_SEL
		assign	o_wb_sel = {(BUS_WIDTH/8){1'b1}};
	end else begin : GEN_WB_SEL
		reg	[BUS_WIDTH/8-1:0]	r_sel;
		wire	[WBLSB-INLSB-1:0]	new_shift;

		assign	new_shift = i_pc[WBLSB-1:INLSB];

		always @(posedge i_clk)
		if (i_new_pc)
		begin
			if (OPT_LITTLE_ENDIAN)
			begin
				r_sel <= {(BUS_WIDTH/8){1'b1}}
						<< ((INSN_WIDTH/8)*new_shift);
			end else begin
				r_sel <= {(BUS_WIDTH/8){1'b1}}
						>> ((INSN_WIDTH/8)*new_shift);
			end
		end else if (o_wb_stb && !i_wb_stall)
			r_sel <= {(BUS_WIDTH/8){1'b1}};

		assign	o_wb_sel = r_sel;
	end endgenerate
	// }}}

	// wb_pending: When do we shut off CYC?
	// {{{
	initial	wb_pending = 0;
	always @(posedge i_clk)
	if (sfifo_reset || i_wb_err)
		wb_pending <= 0;
	else case({ (o_wb_stb && !i_wb_stall), (o_wb_cyc && i_wb_ack) })
	2'b10: wb_pending <= wb_pending + 1;
	2'b01: wb_pending <= wb_pending - 1;
	default: begin end
	endcase
	// }}}

	// pipe_fill: When do we shut off STB?
	// {{{
	initial	pipe_fill = 0;
	always @(posedge i_clk)
	if (sfifo_reset || (o_wb_cyc && i_wb_err))
		pipe_fill <= 0;
	else if (!pending_err)
	case({ (o_wb_stb && !i_wb_stall), o_valid && i_ready && pf_last })
	2'b10: pipe_fill <= pipe_fill + 1;
	2'b01: pipe_fill <= pipe_fill - 1;
	default: begin end
	endcase
	// }}}

	assign	w_pipe_fill = pipe_fill + (o_wb_stb ? 1:0);
	assign	pipe_full = pending_err || w_pipe_fill[LGFIFO];

	assign	last_ack = (wb_pending + (o_wb_stb ? 1:0)) == (i_wb_ack ? 1:0);
	assign	o_wb_we = 1'b0;
	assign	o_wb_data = {(BUS_WIDTH){1'b0}};
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Placed returned instructions into a FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	sfifo_reset = i_reset || i_clear_cache || i_new_pc;

	sfifo #(
		.BW(BUS_WIDTH+1), .LGFLEN(LGFIFO),
		.OPT_ASYNC_READ(OPT_ASYNC_READ)
	) u_sfifo (
		.i_clk(i_clk), .i_reset(sfifo_reset),
		.i_wr(o_wb_cyc && (i_wb_ack || i_wb_err) && !pending_err),
			.i_data({ i_wb_err, i_wb_data }),
		.o_full(ign_sfifo_full), .o_fill(sfifo_fill),
		.i_rd(sfifo_read),
		.o_data({ pf_err, sfifo_word }),
		.o_empty(sfifo_empty)
`ifdef	FORMAL
		, .f_first_addr(f_first_addr),
		.f_second_addr(f_second_addr),
		.f_first_data(f_first_data),
		.f_second_data(f_second_data),
		.f_first_in_fifo(f_first_in_fifo),
		.f_second_in_fifo(f_second_in_fifo),
		.f_distance_to_first(f_distance_to_first),
		.f_distance_to_second(f_distance_to_second)
`endif
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Unpack wide responses into instructions for the CPU
	// {{{

	// o_pc
	// {{{
	always @(posedge i_clk)
	begin
		if (i_reset)
			o_pc <= 0;
		else if (i_new_pc)
			o_pc <= i_pc;
		else if (o_valid && i_ready)
			o_pc <= o_pc + INSN_WIDTH/8;

		o_pc[$clog2(INSN_WIDTH/8)-1:0] <= 0;
	end
	// }}}

	generate if (BUS_WIDTH == INSN_WIDTH)
	begin : NO_UNPACKING
		reg	r_illegal;

		assign	o_valid = !sfifo_empty;
		assign	sfifo_read = o_valid && i_ready;

		assign	o_insn = sfifo_word;

		// o_illegal
		// {{{
		initial	r_illegal = 1'b0;
		always @(posedge i_clk)
		if (sfifo_reset)
			r_illegal <= 1'b0;
		else if (o_valid && o_illegal)
			r_illegal <= 1'b1;

		assign	o_illegal = (pf_err && !sfifo_empty) || r_illegal;
		// }}}

		assign	pf_last = 1;
`ifdef	FORMAL
		assign	f_wide_data = sfifo_word;
`endif
	end else begin : UNPACK_BUS
		// {{{
		reg				r_valid, r_illegal;
		reg	[BUS_WIDTH-1:0]		r_data;
		reg	[WBLSB-INLSB-1:0]	first_shift;

		// o_valid
		// {{{
		initial	r_valid = 1'b0;
		always @(posedge i_clk)
		if (sfifo_reset)
			r_valid <= 1'b0;
		else if (!o_valid || i_ready)
			r_valid <= !sfifo_empty || (o_valid && !pf_last);

		assign	o_valid = r_valid;
		// }}}

		// first_shift
		// {{{
		always @(posedge i_clk)
		if (i_reset)
			first_shift <= 0;
		else if (i_new_pc)
			first_shift <= i_pc[WBLSB-1:INLSB];
		else if (sfifo_read && !sfifo_empty)
			first_shift <= 0;
`ifdef	FORMAL
		always @(*)
		if (i_reset)
		begin
		end else if (o_valid)
		begin
			assert(first_shift == 0);
		end else if (o_wb_cyc || pipe_fill > 0)
			assert(first_shift == o_pc[WBLSB-1:INLSB]);
`endif
		// }}}

		// o_insn
		// {{{
		initial	r_data = {(BUS_WIDTH){1'b0}};
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (sfifo_reset))
			r_data <= 0;
		else if (!o_valid || i_ready)
		begin
			if (o_valid && !pf_last)
			begin
				if (OPT_LITTLE_ENDIAN)
					r_data <= r_data >> INSN_WIDTH;
				else
					r_data <= r_data << INSN_WIDTH;
			end else if ((!OPT_LOWPOWER || !sfifo_empty)
				&& (pf_last || !o_valid))
			begin
				if (OPT_LITTLE_ENDIAN)
					r_data <= sfifo_word >> (INSN_WIDTH * first_shift);
				else
					r_data <= sfifo_word << (INSN_WIDTH * first_shift);
			end
		end

		if (OPT_LITTLE_ENDIAN)
		begin : ASSIGN_LOWBITS
			assign	o_insn = r_data[INSN_WIDTH-1:0];
		end else begin : ASSIGN_HIBITS
			assign	o_insn = r_data[BUS_WIDTH-INSN_WIDTH +: INSN_WIDTH];
		end
		// }}}

		assign	sfifo_read = (!o_valid || i_ready)
						&& (!o_valid || pf_last);

		assign	pf_last = (&o_pc[WBLSB-1:INLSB]);

		// o_illegal
		// {{{
		initial	r_illegal = 1'b0;
		always @(posedge i_clk)
		if (sfifo_reset)
			r_illegal <= 1'b0;
		else if (sfifo_read && !sfifo_empty)
			r_illegal <= r_illegal || pf_err;

		assign	o_illegal = r_illegal;
		// }}}
`ifdef	FORMAL
		assign	f_wide_data = r_data;
`endif
		// }}}
	end endgenerate


	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;

	assign	unused = &{ 1'b0, sfifo_fill[LGFIFO-2:0], ign_sfifo_full };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Declarations, reset, and f_past_valid
	// {{{
	localparam	F_LGDEPTH=LGFIFO+1;

	reg			f_past_valid;
	reg	[4:0]		f_cpu_delay;
	wire	[WBLSB+AW-1:0]	f_const_addr, f_address;
	wire			f_const_illegal;
	wire	[INSN_WIDTH-1:0]	f_const_insn;
	wire			f_fifo_extra;

	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;
	wire	[INSN_WIDTH-1:0]	f_insn;

	(* anyconst *)	reg	[BUS_WIDTH-1:0]		f_const_word;
	(* anyconst *)	reg	fnvr_err;

	reg			f_this_return, f_this_fifo;
	reg	[AW-1:0]	f_return_addr;



	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	//
	// Assume we start from a reset condition
	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	ffetch #(
		// {{{
		.ADDRESS_WIDTH(AW + WBLSB-INLSB), .OPT_CONTRACT(1'b1),
		.INSN_WIDTH(INSN_WIDTH)
		// }}}
	) fcpu(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.cpu_new_pc(i_new_pc),
		.cpu_clear_cache(i_clear_cache),
		.cpu_pc(i_pc), .cpu_ready(i_ready), .pf_valid(o_valid),
		.pf_insn(o_insn), .pf_pc(o_pc), .pf_illegal(o_illegal),
		.fc_pc(f_const_addr), .fc_illegal(f_const_illegal),
		.fc_insn(f_const_insn), .f_address(f_address)
		// }}}
	);

	always @(*)
	begin
		assume(f_address[INLSB-1:0] == 0);
	end

	always @(*)
	begin
		f_return_addr = o_wb_addr - wb_pending;
		f_this_return = (f_return_addr == f_const_addr[WBLSB +: AW]);
	end

	always @(*)
	if (f_this_return)
	begin
		if (f_const_illegal)
			assume(!i_wb_ack);
		else
			assume(!i_wb_err);

		if (i_wb_ack)
			assume(i_wb_data == f_const_word);
	end

	// f_const_word -- a wide bus word to check against
	// {{{
	generate if (INSN_WIDTH == BUS_WIDTH)
	begin : F_CONST_NOSHIFT
		always @(*)
			assume(f_const_word == f_const_insn);
	end else begin : F_CONST_SHIFT

		wire	[WBLSB-INLSB-1:0]	f_shift, f_shift_now;
		wire	[BUS_WIDTH-1:0]		f_shifted, f_now;
		wire	[INSN_WIDTH-1:0]	f_insn_check, f_insn_now;
		wire		f_now_check;

		assign	f_shift = f_const_addr[WBLSB-1:INLSB];
		assign	f_shift_now = f_const_addr[WBLSB-1:INLSB] - o_pc[WBLSB-1:INLSB];

		if (OPT_LITTLE_ENDIAN)
		begin
			assign	f_shifted = f_const_word >> (INSN_WIDTH * f_shift);
			assign	f_insn_check = f_shifted[INSN_WIDTH-1:0];


			assign	f_now = f_wide_data >> (INSN_WIDTH * f_shift_now);
			assign	f_insn_now = f_now[INSN_WIDTH-1:0];
		end else begin
			assign	f_shifted = f_const_word << (INSN_WIDTH * f_shift);
			assign	f_insn_check = f_shifted[BUS_WIDTH-1:BUS_WIDTH-INSN_WIDTH];

			assign	f_now = f_wide_data << (INSN_WIDTH * f_shift_now);
			assign	f_insn_now = f_now[BUS_WIDTH-1:BUS_WIDTH-INSN_WIDTH];
		end

		assign	f_now_check = o_valid && !o_illegal
				&& o_pc[WBLSB +: AW]==f_const_addr[WBLSB +: AW]
				&& f_const_addr[WBLSB-1:INLSB] >= o_pc[WBLSB-1:INLSB];

		always @(*)
			assume(f_insn_check == f_const_insn);
		
		always @(*)
		if (f_past_valid && f_now_check)
			assert(f_insn_now == f_const_insn);
		
	end endgenerate
	// }}}

`ifdef	SKIPME
	// {{{
	// Let's make some assumptions about how long it takes our
	// phantom bus and phantom CPU to respond.
	//
	// These delays need to be long enough to flush out any potential
	// errors, yet still short enough that the formal method doesn't
	// take forever to solve.
	//
	localparam	F_CPU_DELAY = 4;


	// Now, let's repeat this bit but now looking at the delay the CPU
	// takes to accept an instruction.
	always @(posedge i_clk)
	// If no instruction is ready, then keep our counter at zero
	if ((!o_valid)||(i_ready))
		f_cpu_delay <= 0;
	else
		// Otherwise, count the clocks the CPU takes to respond
		f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	PFCACHE
	always @(posedge i_clk)
		assume(f_cpu_delay < F_CPU_DELAY);
`endif
	// }}}
`else
	always @(*)
		f_cpu_delay = 0;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FIFO checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[AW-1:0]	fifo_addr, f_first_wbaddr, f_second_wbaddr;
	reg			f_first_is_last, f_second_is_last,
				f_known_return;

	assign	f_fifo_extra = o_valid && (INSN_WIDTH != BUS_WIDTH);

	// Relating o_pc to o_wb_addr
	always @(*)
	begin
		if (pending_err)
			fifo_addr = o_pc[WBLSB +: AW] + (f_fifo_extra ? 1:0);
		else begin
			fifo_addr = o_wb_addr - pipe_fill;
			if (f_fifo_extra)
				fifo_addr = fifo_addr + 1;
		end

		f_this_fifo = !sfifo_empty
				&& (fifo_addr == f_const_addr[WBLSB +: AW]);

		f_first_wbaddr  = o_pc[WBLSB +: AW] + f_distance_to_first;
		f_second_wbaddr = o_pc[WBLSB +: AW] + f_distance_to_second;

		if(f_fifo_extra)
		begin
			f_first_wbaddr  = f_first_wbaddr  + 1;
			f_second_wbaddr = f_second_wbaddr + 1;
		end

		f_first_is_last = (f_distance_to_first + 1 == sfifo_fill);
		f_second_is_last = (f_distance_to_second + 1 == sfifo_fill);

		f_known_return = (f_first_in_fifo && f_distance_to_first==0)
			|| (f_second_in_fifo && f_distance_to_second == 0);
	end

	always @(*)
	if (f_past_valid && (o_valid || o_wb_cyc || sfifo_fill > 0))
		assert(o_pc == f_address);

	always @(*)
	if (!sfifo_reset && !o_illegal && !pending_err)
		assert(o_pc[WBLSB +: AW] == fifo_addr - f_fifo_extra);

	always @(*)
	if (f_past_valid)
	begin
		if (f_first_in_fifo&& !o_illegal && f_first_wbaddr
						== f_const_addr[WBLSB +: AW])
		begin
			if (f_const_illegal)
				assert(f_first_data[BUS_WIDTH]);
			else
				assert(f_first_data== { 1'b0,f_const_word });
		end

		if (f_second_in_fifo&& !o_illegal && f_second_wbaddr
						== f_const_addr[WBLSB +: AW])
		begin
			if (f_const_illegal)
				assert(f_second_data[BUS_WIDTH]);
			else
				assert(f_second_data=={ 1'b0,f_const_word });
		end

		if (f_first_in_fifo && !f_first_is_last)
			assert(!f_first_data[BUS_WIDTH]);
		if (f_second_in_fifo && !f_second_is_last)
			assert(!f_second_data[BUS_WIDTH]);
		if (!f_known_return)
		begin
			if (sfifo_fill > 1)
				assume(!pf_err);
			if (!pending_err)
				assume(!pf_err);
			if (f_this_fifo)
			begin
				if (f_const_illegal)
					assume(pf_err);
				else
					assume(!pf_err && sfifo_word == f_const_word);
			end
		end

		if (!pending_err)
			assert(!o_illegal);
		if (o_valid && f_const_addr[WBLSB +: AW] == o_pc[WBLSB +: AW])
		begin
			if (f_const_illegal)
				assert(o_illegal);
		end

		if (pending_err)
		begin
			if (f_first_in_fifo && f_first_is_last)
			begin
				assert(f_first_data[BUS_WIDTH]);
			end else if (f_second_in_fifo && f_second_is_last)
			begin
				assert(f_second_data[BUS_WIDTH]);
			end else if (sfifo_fill == 1)
				assume(pf_err);
		end else begin
			if (f_first_in_fifo)
				assert(!f_first_data[BUS_WIDTH]);
			if (f_second_in_fifo)
				assert(!f_second_data[BUS_WIDTH]);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_master #(
		// {{{
		.AW(AW), .DW(BUSW), .F_LGDEPTH(F_LGDEPTH),
		.F_MAX_STALL(2), .F_MAX_ACK_DELAY(3),
		.F_MAX_REQUESTS(0), .F_OPT_SOURCE(1),
		.F_OPT_RMW_BUS_OPTION(0),
		.F_OPT_DISCONTINUOUS(0)
		// }}}
	) f_wbm(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(o_wb_cyc), .i_wb_stb(o_wb_stb),
		.i_wb_we(o_wb_we), .i_wb_addr(o_wb_addr),
			.i_wb_data(o_wb_data), .i_wb_sel(o_wb_sel),
		.i_wb_ack(i_wb_ack), .i_wb_stall(i_wb_stall),
			.i_wb_data(i_wb_data), .i_wb_err(i_wb_err),
		.f_nreqs(f_nreqs), .f_nacks(f_nacks),
			.f_outstanding(f_outstanding)
		// }}}
	);

	always @(*)
	if (fnvr_err)
		assume(!i_wb_err);

	always @(*)
	if (!i_reset && fnvr_err)
	begin
		assert(!pending_err);
		assert(!o_illegal);
	end

	// writes are also illegal for a prefetch.
	always @(posedge i_clk)
	if (o_wb_stb)
		assert(!o_wb_we);

	always @(posedge i_clk)
	begin
		assert(f_outstanding == wb_pending);
		assert(pipe_fill >= wb_pending);
		if (!pending_err)
		begin
			assert(pipe_fill >= sfifo_fill);
			assert(pipe_fill == sfifo_fill + wb_pending + f_fifo_extra);
		end
		assert(pipe_fill <= (1<<LGFIFO));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our return responses to the CPU
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!sfifo_reset)
		assert(o_illegal || o_pc == f_address);

	//
	// If an instruction is accepted, we should *always* move on to another
	// instruction.  The only exception is following an i_new_pc (or
	// other invalidator), at which point the next instruction should
	// be invalid.
	always @(posedge i_clk)
	if ((f_past_valid)&& $past(o_valid && i_ready && !o_illegal && !i_new_pc))
	begin
		// Should always advance the instruction pointer
		assert((!o_valid)||(o_pc != $past(o_pc)));
	end

	//
	// Once an instruction becomes valid, it should never become invalid
	// unless there's been a request for a new instruction.
	always @(posedge i_clk)
	if (!f_past_valid || $past(sfifo_reset))
	begin
		assert(!o_valid);
		assert(!o_illegal);
	end else if ($past(o_valid && !i_ready))
	begin
		if (!$past(o_illegal))
		begin
			assert(o_valid);
			assert(!o_illegal);
			assert($stable(o_insn));
		end else
			assert(o_illegal);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	f_valid_legal;
	always @(*)
		f_valid_legal = o_valid && (!o_illegal);
	always @(posedge i_clk)		// Trace 0
		cover((o_valid)&&( o_illegal));
	always @(posedge i_clk)		// Trace 1
		cover(f_valid_legal);
	always @(posedge i_clk)		// Trace 2
		cover((f_valid_legal)
			&&($past(!o_valid && !i_new_pc))
			&&($past(i_new_pc,4)));
	always @(posedge i_clk)
		cover((f_valid_legal)&&($past(f_valid_legal && i_ready)));
	always @(posedge i_clk)
		cover((f_valid_legal)
			&&($past(f_valid_legal && i_ready))
			&&($past(f_valid_legal && i_ready,2))
			&&($past(f_valid_legal && i_ready,3)));
	always @(posedge i_clk)
		cover((f_valid_legal)
			&&($past(f_valid_legal && i_ready))
			&&($past(f_valid_legal && i_ready,2))
			&&($past(!o_illegal && i_ready && i_new_pc,5))
			&&($past(f_valid_legal && i_ready,6)));
	// }}}
`endif	// FORMAL
// }}}
endmodule
