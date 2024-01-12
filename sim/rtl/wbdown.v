////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbdown.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Downconvert a Wishbone bus from a wider width to a smaller one.
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
module wbdown #(
		// {{{
		parameter	ADDRESS_WIDTH = 28, // Byte address width
		parameter	WIDE_DW = 64,
		parameter	SMALL_DW = 32,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter [0:0]	OPT_LOWLOGIC = 1'b0,
		localparam	WIDE_AW  = ADDRESS_WIDTH-$clog2(WIDE_DW/8),
		localparam	SMALL_AW = ADDRESS_WIDTH-$clog2(SMALL_DW/8)
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Incoming wide port
		// {{{
		input	wire			i_wcyc, i_wstb, i_wwe,
		input	wire	[WIDE_AW-1:0]	i_waddr,
		input	wire	[WIDE_DW-1:0]	i_wdata,
		input	wire	[WIDE_DW/8-1:0]	i_wsel,
		output	wire			o_wstall,
		output	wire			o_wack,
		output	wire	[WIDE_DW-1:0]	o_wdata,
		output	wire			o_werr,
		// }}}
		// Outgoing, small bus size, port
		// {{{
		output	wire			o_cyc, o_stb, o_we,
		output	wire	[SMALL_AW-1:0]	o_addr,
		output	wire	[SMALL_DW-1:0]	o_data,
		output	wire [SMALL_DW/8-1:0]	o_sel,
		input	wire			i_stall,
		input	wire			i_ack,
		input	wire	[SMALL_DW-1:0]	i_data,
		input	wire			i_err
		// }}}
		// }}}
	);

	// Verilator lint_off UNUSED
	localparam	WBLSB = $clog2(WIDE_DW/SMALL_DW);
	// Verilator lint_on  UNUSED
	generate if (WIDE_DW == SMALL_DW)
	begin : NO_ADJUSTMENT
		// {{{
		assign	o_cyc  = i_wcyc;
		assign	o_stb  = i_wstb;
		assign	o_we   = i_wwe;
		assign	o_addr = i_waddr;
		assign	o_data = i_wdata;
		assign	o_sel  = i_wsel;

		assign	o_wstall = i_stall;
		assign	o_wack   = i_ack;
		assign	o_wdata  = i_data;
		assign	o_werr   = i_err;

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_clk, i_reset };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
		// }}}
	end else if (OPT_LOWLOGIC)
	begin : CHEAP_DOWNSIZER
		// {{{
		// Local declarations
		// {{{
		localparam	LGFIFO = 5;
		reg			r_cyc, r_stb, r_we, r_ack, r_err;
		reg	[SMALL_AW-1:0]	r_addr;
		reg	[WIDE_DW-1:0]	s_data, r_data;
		reg	[WIDE_DW/8-1:0]	s_sel;
		reg	[WBLSB:0]	s_count;
		wire			fifo_full, ign_fifo_empty, fifo_ack;
		wire	[LGFIFO:0]	ign_fifo_fill;
`ifdef	FORMAL
		wire	[LGFIFO:0]	f_first_addr, f_second_addr;
		wire			f_first_data, f_second_data;
		wire			f_first_in_fifo, f_second_in_fifo;
		wire	[LGFIFO:0]	f_distance_to_first,
					f_distance_to_second;
`endif
		// }}}

		// r_cyc
		// {{{
		initial	r_cyc = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc ||(o_cyc && i_err) || o_werr)
			r_cyc <= 1'b0;
		else if (i_wcyc && i_wstb)
			r_cyc <= 1'b1;
		// }}}

		initial	r_stb   = 1'b0;
		initial	r_we    = 1'b0;
		initial	r_addr  = 0;
		initial	s_data  = 0;
		initial	s_sel   = 0;
		initial	s_count = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || o_werr || (o_cyc && i_err))
		begin
			// {{{
			r_stb   <= 1'b0;
			r_we    <= 1'b0;
			r_addr  <= 0;
			s_data  <= 0;
			s_sel   <= 0;
			s_count <= 0;
			// }}}
		end else if (i_wstb && !o_wstall) // New request
		begin
			// {{{
			r_stb  <= 1'b1;
			r_we   <= i_wwe;
			r_addr <= { i_waddr,
					{($clog2(WIDE_DW/SMALL_DW)){1'b0}} };
			s_data <= i_wdata;
			s_sel  <= i_wsel;
			// Verilator lint_off WIDTH
			s_count <= (WIDE_DW/SMALL_DW);
			// Verilator lint_on  WIDTH
			// }}}
		end else if (o_stb && !i_stall)
		begin
			// {{{
			s_count <=  s_count - 1;
			r_stb   <= (s_count > 1);
			r_addr[$clog2(WIDE_DW/SMALL_DW)-1:0]
				<= r_addr[$clog2(WIDE_DW/SMALL_DW)-1:0] + 1;
			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				s_data <= s_data >> SMALL_DW;
				s_sel  <= s_sel >> (SMALL_DW/8);
				// Verilator coverage_on
			end else begin
				s_data <= s_data << SMALL_DW;
				s_sel  <= s_sel << (SMALL_DW/8);
			end
			// }}}
		end

		assign	o_cyc = r_cyc;
		assign	o_stb = r_stb && !fifo_full;
		assign	o_we  = r_we;
		assign	o_addr= r_addr;

		if (OPT_LITTLE_ENDIAN)
		begin : OPT_LILEND_DATA
			// Verilator coverage_off
			assign	o_data = s_data[SMALL_DW-1:0];
			assign	o_sel  = s_sel[SMALL_DW/8-1:0];
			// Verilator coverage_on
		end else begin : OPT_BIGEND_DATA
			assign	o_data =s_data[WIDE_DW-1:WIDE_DW-SMALL_DW];
			assign	o_sel  =s_sel[WIDE_DW/8-1:(WIDE_DW-SMALL_DW)/8];
		end

		sfifo #(
			.BW(1), .LGFLEN(LGFIFO),
			.OPT_WRITE_ON_FULL(1'b1), .OPT_READ_ON_EMPTY(1'b1)
		) u_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || !i_wcyc),
			.i_wr(o_stb && !i_stall),
				.i_data({ (s_count == 1) ? 1'b1 : 1'b0 }),
				.o_full(fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(i_ack), .o_data(fifo_ack),
				.o_empty(ign_fifo_empty)
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
			// }}}
		);

		// r_data
		// {{{
		initial	r_data = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (!i_wcyc || !o_cyc || i_err))
			r_data <= 0;
		else if (i_ack)
		begin
			if (OPT_LITTLE_ENDIAN)
				// Verilator coverage_off
				r_data<= { i_data, r_data[WIDE_DW-1:SMALL_DW] };
				// Verilator coverage_on
			else
				r_data<={r_data[WIDE_DW-SMALL_DW-1:0], i_data };
		end
		// }}}

		// r_ack
		// {{{
		initial	r_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_cyc)
			r_ack <= 1'b0;
		else
			r_ack <= i_ack && fifo_ack;
		// }}}

		// r_err
		// {{{
		initial	r_err = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_cyc)
			r_err <= 1'b0;
		else
			r_err <= i_err;
		// }}}

		assign	o_wdata = r_data;
		assign	o_wack  = r_ack;
		assign	o_werr  = r_err;
		assign	o_wstall = (r_stb && (fifo_full || i_stall))
					|| (s_count > 1);

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_fifo_fill, ign_fifo_empty };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		parameter	F_LGDEPTH = LGFIFO+1;
		reg			f_past_valid;
		wire	[F_LGDEPTH-1:0]	fslv_nreqs, fslv_nacks,fslv_outstanding;
		wire	[F_LGDEPTH-1:0]	fmst_nreqs, fmst_nacks,fmst_outstanding;
		wire			f_first_ack, f_second_ack;
		reg	[LGFIFO:0]	f_acks_in_fifo;
		reg	[WBLSB-1:0]	f_first_subaddr, f_second_subaddr,
					f_this_subaddr;
		reg	[WIDE_DW/8-1:0]	f_mask;
		reg			f_subsequent;

		initial	f_past_valid = 0;
		always @(posedge i_clk)
			f_past_valid <= 1;

		always @(*)
		if (!f_past_valid)
			assume(i_reset);

		fwb_slave #(
			.AW(WIDE_AW), .DW(WIDE_DW),
		) fslv (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(i_wcyc), .i_wb_stb(i_wstb), .i_wb_we(i_wwe),
			.i_wb_addr(i_waddr), .i_wb_data(i_wdata),
				.i_wb_sel(i_wsel),
			.i_wb_stall(o_wstall), .i_wb_ack(o_wack),
				.i_wb_idata(o_wdata), .i_wb_err(o_werr),
			//
			.f_nreqs(fslv_nreqs), .f_nacks(fslv_nacks),
			.f_outstanding(fslv_outstanding)
			// }}}
		);

		fwb_master #(
			.AW(SMALL_AW), .DW(SMALL_DW),
		) fmst (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(o_cyc), .i_wb_stb(o_stb), .i_wb_we(o_we),
			.i_wb_addr(o_addr), .i_wb_data(o_data),
				.i_wb_sel(o_sel),
			.i_wb_stall(i_stall), .i_wb_ack(i_ack),
				.i_wb_idata(i_data), .i_wb_err(i_err),
			//
			.f_nreqs(fmst_nreqs), .f_nacks(fmst_nacks),
			.f_outstanding(fmst_outstanding)
			// }}}
		);

		always @(*)
		if (r_stb)
		begin
			assert(s_count > 0);
		end else begin
			assert(s_count == 0);
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc)
			assert(ign_fifo_fill == fmst_outstanding);

		always @(*)
		if (!i_reset && !o_cyc && i_wcyc && !o_werr)
			assert(ign_fifo_fill == 0);

		always @(*)
		if (!o_cyc)
			assert(!r_stb);

		always @(*)
		if ((r_stb || fslv_outstanding > 0) && i_wcyc && o_cyc)
			assert(o_we == i_wwe);

		always @(*)
		if (i_wcyc && fslv_outstanding > 0 && !o_werr)
			assert(o_cyc);

		initial	f_acks_in_fifo = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc)
			f_acks_in_fifo <= 0;
		else case({ o_stb && !i_stall && (s_count == 1),
				(i_ack && fifo_ack) })
		2'b01: f_acks_in_fifo <= f_acks_in_fifo - 1;
		2'b10: f_acks_in_fifo <= f_acks_in_fifo + 1;
		endcase

		always @(*)
		if (!i_reset && i_wcyc && o_cyc)
		begin
			assert(f_acks_in_fifo + (s_count > 0 ? 1:0)
				+ (o_wack ? 1:0) == fslv_outstanding);

			if (s_count == 0 && fslv_outstanding > (o_wack ? 1:0))
				assert(f_acks_in_fifo > 0);
		end

		assign	f_first_ack  = f_first_data;
		assign	f_second_ack = f_second_data;

		always @(*)
		begin
			// f_first_subaddr  = f_first_data[WBLSB-1:0];
			// f_second_subaddr = f_second_data[WBLSB-1:0];

			f_first_subaddr = (r_stb ? o_addr[WBLSB-1:0] : {(WBLSB){1'b0}})
					- ign_fifo_fill[WBLSB-1:0]
					+ f_distance_to_first[WBLSB-1:0];

			f_second_subaddr = (r_stb ? o_addr[WBLSB-1:0] : {(WBLSB){1'b0}})
					- ign_fifo_fill[WBLSB-1:0]
					+ f_distance_to_second[WBLSB-1:0];

			f_this_subaddr = (r_stb ? o_addr[WBLSB-1:0] : {(WBLSB){1'b0}})
					- ign_fifo_fill[WBLSB-1:0];
		end

		always @(*)
		begin
			if (!i_reset && o_cyc && i_wcyc && f_first_in_fifo)
			begin
				assert(f_first_ack == (&f_first_subaddr[WBLSB-1:0]));
			end
			if (!i_reset && o_cyc && i_wcyc && f_second_in_fifo)
			begin
				assert(f_second_ack == (&f_second_subaddr[WBLSB-1:0]));
			end
			assert(f_acks_in_fifo <= ign_fifo_fill);
			assert(!ign_fifo_empty || f_acks_in_fifo == 0);
			assert(f_acks_in_fifo >=
				((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0));
			assert(ign_fifo_fill - f_acks_in_fifo >=
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0));

			if (o_cyc && f_first_in_fifo && f_distance_to_first == ign_fifo_fill - 1)
				assert(f_first_ack || s_count > 0);
			if (o_cyc && f_second_in_fifo && f_distance_to_second == ign_fifo_fill - 1)
				assert(f_second_ack || s_count > 0);
			if (!i_reset && i_wcyc && o_cyc
					&& ign_fifo_fill > 0 && s_count == 0)
				assert(f_acks_in_fifo > 0);

			if (o_cyc&& i_wcyc  && f_first_in_fifo && s_count == 0 && !o_werr
				&& f_distance_to_first + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo > (f_first_ack ? 1:0));

			if (o_cyc && i_wcyc && f_second_in_fifo && s_count == 0 && !o_werr
					&& f_distance_to_second + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo >
					((f_first_in_fifo && f_first_ack) ? 1:0)
					+ (f_second_ack ? 1:0));
		end

		always @(*)
		begin
			if (f_second_in_fifo)
				f_subsequent = (f_distance_to_second + 1 < ign_fifo_fill);
			else if (f_first_in_fifo)
				f_subsequent = (f_distance_to_first + 1 < ign_fifo_fill);
			else
				f_subsequent = (f_acks_in_fifo > 0 && s_count == 0);
		end

		always @(*)
		if ((!f_first_in_fifo || f_distance_to_first > 0)
			&&(!f_second_in_fifo || f_distance_to_second > 0)
			&& !ign_fifo_empty)
		begin
			assume(!fifo_ack || (f_acks_in_fifo >
				((f_subsequent) ? 1:0)
				+ ((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0)));
			assume(fifo_ack || (ign_fifo_fill - f_acks_in_fifo >
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0)));
			if (f_acks_in_fifo == 1 && s_count == 0 && ign_fifo_fill > 1)
				assume(!fifo_ack);

			assume(fifo_ack == (&f_this_subaddr));
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc)
		begin
			if (f_first_in_fifo && f_second_in_fifo)
			begin
				assert(f_second_subaddr > f_first_subaddr
					|| f_first_ack);
			end else if (f_first_in_fifo && !f_first_ack)
			begin
				assert(s_count > 0
					&& o_addr[WBLSB-1:0] > f_first_subaddr);
			end
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc)
		begin
			assert(s_count <= (1<<WBLSB));
			if (r_stb)
				assert(s_count+o_addr[WBLSB-1:0] == (1<<WBLSB));
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc
			&& f_first_in_fifo && f_second_in_fifo)
		begin
			assert(f_second_subaddr > f_first_subaddr
				|| f_first_ack);
		end

		always @(*)
		if (OPT_LITTLE_ENDIAN)
			// Verilator coverage_off
			f_mask = {(WIDE_DW/8){1'b1}} >> (o_addr[WBLSB-1:0] * SMALL_DW/8);
			// Verilator coverage_on
		else
			f_mask = {(WIDE_DW/8){1'b1}} << (o_addr[WBLSB-1:0] * SMALL_DW/8);

		always @(*)
		if (s_count > 0)
		begin
			assert((s_sel & (~f_mask)) == 0);
		end
`endif
	// }}}
		// }}}
	end else begin : DOWNSIZE
		// {{{
		// Local declarations
		// {{{
		localparam	LGFIFO = 5;

		reg			r_cyc, r_stb, r_we, r_ack, r_err;
		reg	[SMALL_AW-1:0]	r_addr;
		reg			s_null;
		reg	[WIDE_DW-1:0]	s_data, r_data, nxt_mask, nxt_data;
		wire	[WIDE_DW/8-1:0]	i_nxtsel, s_nxtsel;
		reg	[WIDE_DW/8-1:0]	s_sel;
		reg	[WBLSB:0]	s_count;
		wire	[WBLSB-1:0]	fifo_addr, i_subaddr,s_subaddr;
		wire			fifo_full, fifo_empty, fifo_ack;
		wire	[LGFIFO:0]	ign_fifo_fill;
`ifdef	FORMAL
		wire	[LGFIFO:0]	f_first_addr, f_second_addr;
		wire	[WBLSB:0]	f_first_data, f_second_data;
		wire			f_first_in_fifo, f_second_in_fifo;
		wire	[LGFIFO:0]	f_distance_to_first,
					f_distance_to_second;
`endif
		// }}}

		// r_cyc
		// {{{
		initial	r_cyc = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc ||(o_cyc && i_err) || o_werr)
			r_cyc <= 1'b0;
		else if (i_wcyc && i_wstb)
			r_cyc <= 1'b1;
		// }}}

		// i_subaddr, s_subaddr, i_nxtsel, s_nxtsel
		// {{{
		assign	i_subaddr = subaddr_fn(i_wsel);

		if (OPT_LITTLE_ENDIAN)
		begin : OPT_LILEND_SHIFT
			assign	i_nxtsel = i_wsel >> (i_subaddr * SMALL_DW/8);
			assign	s_subaddr= 1 + subaddr_fn({ {(SMALL_DW/8){1'b0}}, s_sel[WIDE_DW/8-1:SMALL_DW/8] });
			assign	s_nxtsel = s_sel >> (s_subaddr * SMALL_DW/8);
		end else begin : OPT_BIGEND_SHIFT
			assign	i_nxtsel = i_wsel << (i_subaddr * SMALL_DW/8);
			assign	s_subaddr= 1 + subaddr_fn( { s_sel[WIDE_DW/8-SMALL_DW/8-1:0], {(SMALL_DW/8){1'b0}} } );
			assign	s_nxtsel = s_sel << (s_subaddr * SMALL_DW/8);
		end
		// }}}

		initial	r_stb   = 1'b0;
		initial	r_we    = 1'b0;
		initial	r_addr  = 0;
		initial	s_data  = 0;
		initial	s_sel   = 0;
		initial	s_count = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || o_werr || (o_cyc && i_err))
		begin
			// {{{
			r_stb   <= 1'b0;
			r_we    <= 1'b0;
			r_addr  <= 0;
			s_data  <= 0;
			s_sel   <= 0;
			s_count <= 0;
			s_null  <= 0;
			// }}}
		end else if (i_wstb && !o_wstall) // New request
		begin
			// {{{
			r_stb  <= (i_wsel != 0);
			r_we   <= i_wwe;
			r_addr <= { i_waddr, i_subaddr };

			s_null <= (i_wsel == 0);
			// Verilator lint_off WIDTH
			s_count <= (WIDE_DW/SMALL_DW) - i_subaddr;
			// Verilator lint_on  WIDTH

			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				s_data <= i_wdata >> (i_subaddr * SMALL_DW);
				s_sel  <= i_nxtsel;
				if (i_nxtsel[WIDE_DW/8-1:SMALL_DW/8] == 0)
					s_count <= 1;
				// Verilator coverage_on
			end else begin
				s_data <= i_wdata << (i_subaddr * SMALL_DW);
				s_sel  <= i_nxtsel;
				if (i_nxtsel[WIDE_DW/8-SMALL_DW/8-1:0] == 0)
					s_count <= 1;
			end

			if (i_wsel == 0)
				s_count <= 0;
			// }}}
		end else if (o_stb && !i_stall)
		begin
			// {{{
			s_count <=  s_count - s_subaddr;
			r_stb   <= (s_count > 1);
			r_addr[WBLSB-1:0] <= r_addr[WBLSB-1:0] + s_subaddr;
			if (OPT_LITTLE_ENDIAN)
			begin
				// Verilator coverage_off
				s_data <= s_data >> (s_subaddr *SMALL_DW);
				s_sel  <= s_nxtsel;
				if (s_count > 1 && s_nxtsel[WIDE_DW/8-1:SMALL_DW/8] == 0)
					s_count <= 1;
				// Verilator coverage_on
			end else begin
				s_data <= s_data << (s_subaddr *SMALL_DW);
				s_sel  <= s_nxtsel;
				if (s_count > 1 && s_nxtsel[WIDE_DW/8-SMALL_DW/8-1:0] == 0)
					s_count <= 1;
			end
			// }}}
		end else if (fifo_empty)
			s_null <= 0;

		assign	o_cyc = r_cyc;
		assign	o_stb = r_stb && !fifo_full;
		assign	o_we  = r_we;
		assign	o_addr= r_addr;

		if (OPT_LITTLE_ENDIAN)
		begin : OPT_LILODATA
			assign	o_data = s_data[SMALL_DW-1:0];
			assign	o_sel  = s_sel[SMALL_DW/8-1:0];
		end else begin : OPT_BIGODATA
			assign	o_data =s_data[WIDE_DW-1:WIDE_DW-SMALL_DW];
			assign	o_sel  =s_sel[WIDE_DW/8-1:(WIDE_DW-SMALL_DW)/8];
		end

		sfifo #(
			.BW(1+WBLSB), .LGFLEN(LGFIFO),
			.OPT_WRITE_ON_FULL(1'b1), .OPT_READ_ON_EMPTY(1'b1)
		) u_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || !i_wcyc),
			.i_wr(o_stb && !i_stall),
				.i_data({ {(s_count == 1) ? 1'b1 : 1'b0 },
					o_addr[WBLSB-1:0] }),
				.o_full(fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(i_ack),
				.o_data({ fifo_ack, fifo_addr }),
				.o_empty(fifo_empty)
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
			// }}}
		);

		// nxt_data, r_data
		// {{{
		always @(*)
		begin
			nxt_data = r_data;
			if (o_wack)
				nxt_data = 0;
			nxt_mask = {(WIDE_DW){1'b0}};
			if (i_ack)
			begin
				if (OPT_LITTLE_ENDIAN)
				begin
					// Verilator coverage_off
					nxt_mask = { {(WIDE_DW-SMALL_DW){1'b0}}, {(SMALL_DW){1'b1}} };
					nxt_mask = nxt_mask << (fifo_addr * SMALL_DW);
					nxt_mask = ~nxt_mask;
					nxt_data = (nxt_data & nxt_mask)
						| ({ {(WIDE_DW-SMALL_DW){1'b0}}, i_data } << (fifo_addr * SMALL_DW));
					// Verilator coverage_on
				end else begin
					nxt_mask = { {(SMALL_DW){1'b1}}, {(WIDE_DW-SMALL_DW){1'b0}} };
					nxt_mask = nxt_mask >> (fifo_addr * SMALL_DW);
					nxt_mask = ~nxt_mask;
					nxt_data = (nxt_data & nxt_mask)
						| ({ i_data, {(WIDE_DW-SMALL_DW){1'b0}} } >> (fifo_addr * SMALL_DW));
				end
			end
		end

		initial	r_data = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_cyc || i_err)
			r_data <= 0;
		else
			r_data <= nxt_data;
		// }}}

		// r_ack
		// {{{
		initial	r_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_cyc)
			r_ack <= 1'b0;
		else if (!fifo_empty)
			r_ack <= fifo_ack && i_ack;
		else
			r_ack <= s_null;
		// }}}

		// r_err
		// {{{
		initial	r_err = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc || !o_cyc)
			r_err <= 0;
		else
			r_err <= i_err;
		// }}}

		assign	o_wdata = r_data;
		assign	o_wack  = r_ack;
		assign	o_werr  = r_err;
		assign	o_wstall= (r_stb && (fifo_full || i_stall))
					|| (s_null && !fifo_empty)
					|| (s_count > 1);

		function [WBLSB-1:0]	subaddr_fn(input [WIDE_DW/8-1:0] sel);
			// {{{
			integer	fnk, fm;
		begin
			subaddr_fn = 0;
			for(fnk=0; fnk<WIDE_DW/SMALL_DW; fnk=fnk+1)
			begin
				fm = WIDE_DW/SMALL_DW-1-fnk;
				if (OPT_LITTLE_ENDIAN)
				begin
					// Verilator coverage_off
					if (sel[fm*SMALL_DW/8 +: SMALL_DW/8] != 0)
						subaddr_fn = fm[WBLSB-1:0];
					// Verilator coverage_on
				end else begin
					if (sel[fnk*SMALL_DW/8 +: SMALL_DW/8] != 0)
						subaddr_fn = fm[WBLSB-1:0];
				end
			end
		end endfunction
		// }}}

		// Keep Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_fifo_fill, fifo_empty };
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		parameter	F_LGDEPTH = LGFIFO+1;
		reg			f_past_valid;
		wire	[F_LGDEPTH-1:0]	fslv_nreqs, fslv_nacks,fslv_outstanding;
		wire	[F_LGDEPTH-1:0]	fmst_nreqs, fmst_nacks,fmst_outstanding;
		wire			f_first_ack, f_second_ack;
		reg	[LGFIFO:0]	f_acks_in_fifo;
		wire	[WBLSB-1:0]	f_first_subaddr, f_second_subaddr;
		reg	[WIDE_DW/8-1:0]	f_mask;
		reg			f_subsequent;


		initial	f_past_valid = 0;
		always @(posedge i_clk)
			f_past_valid <= 1;

		always @(*)
		if (!f_past_valid)
			assume(i_reset);

		fwb_slave #(
			.AW(WIDE_AW), .DW(WIDE_DW),
		) fslv (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(i_wcyc), .i_wb_stb(i_wstb), .i_wb_we(i_wwe),
			.i_wb_addr(i_waddr), .i_wb_data(i_wdata),
				.i_wb_sel(i_wsel),
			.i_wb_stall(o_wstall), .i_wb_ack(o_wack),
				.i_wb_idata(o_wdata), .i_wb_err(o_werr),
			//
			.f_nreqs(fslv_nreqs), .f_nacks(fslv_nacks),
			.f_outstanding(fslv_outstanding)
			// }}}
		);

		fwb_master #(
			.AW(SMALL_AW), .DW(SMALL_DW),
		) fmst (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(o_cyc), .i_wb_stb(o_stb), .i_wb_we(o_we),
			.i_wb_addr(o_addr), .i_wb_data(o_data),
				.i_wb_sel(o_sel),
			.i_wb_stall(i_stall), .i_wb_ack(i_ack),
				.i_wb_idata(i_data), .i_wb_err(i_err),
			//
			.f_nreqs(fmst_nreqs), .f_nacks(fmst_nacks),
			.f_outstanding(fmst_outstanding)
			// }}}
		);

		always @(*)
		if (r_stb)
		begin
			assert(s_count > 0);
			assert(o_sel  != 0);
		end else begin
			assert(s_sel   == 0);
			assert(s_count == 0);
		end

		always @(*)
			assert(!r_stb || !s_null);

		always @(*)
		if (r_stb)
		begin
			assert(o_sel != 0);

			if (OPT_LITTLE_ENDIAN)
			begin
				assert((s_count == 1) == (s_sel[WIDE_DW/8-1:SMALL_DW/8] == 0));
			end else begin
				assert((s_count == 1) == (s_sel[WIDE_DW/8-SMALL_DW/8-1:0] == 0));
			end
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc)
			assert(ign_fifo_fill == fmst_outstanding);

		always @(*)
		if (!i_reset && !o_cyc && i_wcyc && !o_werr)
			assert(ign_fifo_fill == 0);

		always @(*)
		if (!o_cyc)
			assert(!r_stb);

		always @(*)
		if ((r_stb || fslv_outstanding > 0) && i_wcyc && o_cyc)
			assert(o_we == i_wwe);

		always @(*)
		if (i_wcyc && fslv_outstanding > 0 && !o_werr)
			assert(o_cyc);

		always @(*)
		if (i_wcyc && !o_wack && fmst_outstanding == 0 && s_count == 0)
			assert(r_data == 0);

		initial	f_acks_in_fifo = 0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc)
			f_acks_in_fifo <= 0;
		else case({ o_stb && !i_stall && (s_count == 1),
				(i_ack && fifo_ack) })
		2'b01: f_acks_in_fifo <= f_acks_in_fifo - 1;
		2'b10: f_acks_in_fifo <= f_acks_in_fifo + 1;
		endcase

		always @(*)
		if (!i_reset && i_wcyc && o_cyc)
		begin
			assert(f_acks_in_fifo + (s_count > 0 ? 1:0)
				+ (s_null ? 1:0)
				+ (o_wack ? 1:0) == fslv_outstanding);

			if (s_count == 0 && fslv_outstanding > (s_null ? 1:0) + (o_wack ? 1:0))
				assert(f_acks_in_fifo > 0);
		end

		assign	f_first_ack  = f_first_data[WBLSB];
		assign	f_second_ack = f_second_data[WBLSB];

		assign	f_first_subaddr  = f_first_data[WBLSB-1:0];
		assign	f_second_subaddr = f_second_data[WBLSB-1:0];

		always @(*)
		begin
			assert(f_acks_in_fifo <= ign_fifo_fill);
			assert(!fifo_empty || f_acks_in_fifo == 0);
			assert(f_acks_in_fifo >=
				((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0));
			assert(ign_fifo_fill - f_acks_in_fifo >=
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0));

			if (o_cyc && f_first_in_fifo && f_distance_to_first == ign_fifo_fill - 1)
				assert(f_first_ack || s_count > 0);
			if (o_cyc && f_second_in_fifo && f_distance_to_second == ign_fifo_fill - 1)
				assert(f_second_ack || s_count > 0);
			if (!i_reset && i_wcyc && o_cyc
					&& ign_fifo_fill > 0 && s_count == 0)
				assert(f_acks_in_fifo > 0);

			if (o_cyc&& i_wcyc  && f_first_in_fifo && s_count == 0 && !o_werr
				&& f_distance_to_first + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo > (f_first_ack ? 1:0));

			if (o_cyc && i_wcyc && f_second_in_fifo && s_count == 0 && !o_werr
					&& f_distance_to_second + 1 < ign_fifo_fill)
				assert(f_acks_in_fifo >
					((f_first_in_fifo && f_first_ack) ? 1:0)
					+ (f_second_ack ? 1:0));
		end

		always @(*)
		begin
			if (f_second_in_fifo)
				f_subsequent = (f_distance_to_second + 1 < ign_fifo_fill);
			else if (f_first_in_fifo)
				f_subsequent = (f_distance_to_first + 1 < ign_fifo_fill);
			else
				f_subsequent = (f_acks_in_fifo > 0 && s_count == 0);
		end

		always @(*)
		if ((!f_first_in_fifo || f_distance_to_first > 0)
			&&(!f_second_in_fifo || f_distance_to_second > 0)
			&& !fifo_empty)
		begin
			assume(!fifo_ack || (f_acks_in_fifo >
				((f_subsequent) ? 1:0)
				+ ((f_first_in_fifo && f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && f_second_ack) ? 1:0)));
			assume(fifo_ack || (ign_fifo_fill - f_acks_in_fifo >
				((f_first_in_fifo && !f_first_ack) ? 1:0)
				+ ((f_second_in_fifo && !f_second_ack) ? 1:0)));
			if (f_acks_in_fifo == 1 && s_count == 0 && ign_fifo_fill > 1)
				assume(!fifo_ack);
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc)
		begin
			if (f_first_in_fifo && f_second_in_fifo)
			begin
				assert(f_second_subaddr > f_first_subaddr
					|| f_first_ack);
			end else if (f_first_in_fifo && !f_first_ack)
			begin
				assert(s_count > 0
					&& o_addr[WBLSB-1:0] > f_first_subaddr);
			end
		end

		always @(*)
		if (!i_reset && o_cyc && i_wcyc)
		begin
			assert(s_count <= (1<<WBLSB));
			assert(s_count + o_addr[WBLSB-1:0] <= (1<<WBLSB));
			if (s_count > 1)
				assert(s_count + o_addr[WBLSB-1:0]==(1<<WBLSB));
		end

		always @(*)
		if (f_first_in_fifo && f_second_in_fifo)
		begin
			assert(f_second_subaddr > f_first_subaddr
				|| f_first_ack);
		end

		always @(*)
		if (OPT_LITTLE_ENDIAN)
			f_mask = {(WIDE_DW/8){1'b1}} >> (o_addr[WBLSB-1:0] * SMALL_DW/8);
		else
			f_mask = {(WIDE_DW/8){1'b1}} << (o_addr[WBLSB-1:0] * SMALL_DW/8);

		always @(*)
		if (s_count > 0)
		begin
			assert((s_sel & (~f_mask)) == 0);
		end
`endif
	// }}}
		// }}}
	end endgenerate

endmodule
