////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_s2mm.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Writes data, having gone through the realignment
//		pipeline, back to the bus.  This data will be written either
//	1, 2, or 4 bytes at a time, or at the full width of the bus.
//
//	When writing 2 or 4 bytes at a time, the address must (currently) be
//	aligned.
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
module	zipdma_s2mm #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	BUS_WIDTH = 64,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter	LGPIPE = 10,
		// Abbreviations
		localparam	DW = BUS_WIDTH,
		localparam	AW = ADDRESS_WIDTH-$clog2(DW/8)
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Configuration
		// {{{
		input	wire			i_request,
		output	reg			o_busy, o_err,
		input	wire			i_inc,
		input	wire	[1:0]		i_size,
		// input wire	[LGLENGTH:0]	i_transferlen,
		input wire [ADDRESS_WIDTH-1:0]	i_addr,	// Byte address
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
		// Outgoing Wishbone interface
		// {{{
		output	reg			o_wr_cyc, o_wr_stb,
		output	wire			o_wr_we,
		output	reg	[AW-1:0]	o_wr_addr,
		output	reg	[DW-1:0]	o_wr_data,
		output	reg	[DW/8-1:0]	o_wr_sel,
		input	wire			i_wr_stall,
		input	wire			i_wr_ack,
		input	wire	[DW-1:0]	i_wr_data,	// UNUSED
		input	wire			i_wr_err
		// }}}
		// }}}
	);

	// Local decalarations
	// {{{
	localparam	[1:0]		SZ_BYTE = 2'b11,
					SZ_16B  = 2'b10,
					SZ_32B  = 2'b01,
					SZ_BUS  = 2'b00;
	localparam			WBLSB = $clog2(DW/8);
	integer				ik;
	//
	reg				r_inc;
	reg	[1:0]			r_size;
	//
	reg	[ADDRESS_WIDTH:0]	next_addr;
	reg	[WBLSB-1:0]		subaddr;
	reg	[2*DW-1:0]		next_data;
	reg	[DW-1:0]		r_data;
	reg	[2*DW/8-1:0]		next_sel, pre_sel;
	reg	[DW/8-1:0]		r_sel;
	reg				r_last;

	reg	[LGPIPE-1:0]		wb_outstanding;
	reg				wb_pipeline_full;
	reg				addr_overflow;
	// }}}

	assign	o_wr_we = 1'b1;

	// Copy config: r_inc, r_size(, r_addr)
	// {{{
	always @(posedge i_clk)
	if (i_request && !o_busy)
	begin
		r_inc  <= i_inc;
		r_size <= i_size;
		// r_addr <= i_addr;
	end
	// }}}

	// next_addr
	// {{{
	always @(*)
	begin
		next_addr = { 1'b0, o_wr_addr, subaddr };

		if (o_wr_stb && !i_wr_stall)
		case(r_size)
		SZ_BYTE: if (r_inc)
			next_addr = next_addr + 1;
		SZ_16B: begin	// 16-bit addressing
			if (r_inc)
				next_addr = next_addr + 2;
			else
				next_addr[  0] = 0;
			end
		SZ_32B: begin	// 32-bit addressing
			if (r_inc)
				next_addr = next_addr + 4;
			else
				next_addr[1:0] = 0;
			end
		SZ_BUS: begin	// Full word addressing
			if (r_inc)
				next_addr = next_addr + { {(AW-1){1'b0}}, 1'b1,
						{(WBLSB){1'b0}} };
			else
				next_addr[WBLSB-1:0] = 0;
			end
		endcase
	end

	always @(*)
		addr_overflow = next_addr[ADDRESS_WIDTH];
`ifdef	FORMAL
	always @(posedge i_clk)
	if (!i_reset && o_busy && !r_inc)
	case(r_size)
	SZ_BYTE: begin end
	SZ_16B: assert(next_addr[0] == 0);
	SZ_32B: assert(next_addr[1:0] == 0);
	SZ_BUS: assert(next_addr[WBLSB-1:0] == 0);
	endcase
`endif
	// }}}

	// next_data
	// {{{
	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		next_data = { {(DW){1'b0}}, r_data };

		// Zero out unused data
		for(ik=0; ik<DW/8; ik=ik+1)
		if (!r_sel[ik])
			next_data[ik * 8 +: 8] = 8'h0;

		if (S_VALID && !r_last)
			next_data = next_data | ({{(DW){1'b0}}, S_DATA }
					<< (next_addr[WBLSB-1:0]*8));
	end else begin
		next_data = { r_data, {(DW){1'b0}} };

		// Zero out unused data
		for(ik=0; ik<DW/8; ik=ik+1)
		if (!r_sel[ik])
			next_data[DW + ik * 8 +: 8] = 8'h0;

		if (S_VALID && !r_last)
			next_data = next_data | ({ S_DATA, {(DW){1'b0}} }
					>> (next_addr[WBLSB-1:0]*8));
	end
	// }}}

	// next_sel
	// {{{
	always @(*)
	begin
		pre_sel = 0;

		if (OPT_LITTLE_ENDIAN)
		begin
			for(ik=0; ik<DW/8; ik=ik+1)
			if (ik < S_BYTES)
				pre_sel[ik] = 1'b1;

			next_sel = { {(DW/8){1'b0}}, r_sel };
			if (S_VALID && !r_last)
				next_sel = next_sel | (pre_sel
						<< (next_addr[WBLSB-1:0]));
		end else begin
			for(ik=0; ik<DW/8; ik=ik+1)
			if (ik < S_BYTES)
				pre_sel[2*DW/8-1-ik] = 1'b1;

			next_sel = { r_sel, {(DW/8){1'b0}} };
			if (S_VALID && !r_last)
				next_sel = next_sel | (pre_sel
						>> (next_addr[WBLSB-1:0]));
		end
	end
	// }}}

	// wb_pipeline_full, wb_outstanding
	// {{{
	initial	wb_pipeline_full = 1'b0;
	initial	wb_outstanding   = 0;
	always @(posedge i_clk)
	if (i_reset || !o_wr_cyc || i_wr_err)
	begin
		wb_pipeline_full <= 1'b0;
		wb_outstanding   <= 0;
	end else case({ (o_wr_stb && !i_wr_stall), i_wr_ack })
	2'b10:	begin
		wb_pipeline_full <= (&wb_outstanding[LGPIPE-1:2])
						&& (|wb_outstanding[1:0]);
		wb_outstanding   <= wb_outstanding + 1;
		end
	2'b01: begin
		wb_pipeline_full <= (&wb_outstanding[LGPIPE-1:0]);
		wb_outstanding   <= wb_outstanding - 1;
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	if (!i_reset || !o_wr_cyc)
		assert(wb_pipeline_full == (&wb_outstanding[LGPIPE-1:1]));

	always @(*)
	if (!i_reset && o_wr_cyc && (&wb_outstanding))
		assert(!o_wr_stb);
`endif
	// }}}

	// crc, stb, o_wr_addr, o_wr_sel, o_busy, o_err, subaddr
	// {{{
	initial	o_wr_cyc = 1'b0;
	initial	o_wr_stb = 1'b0;
	initial	o_busy   = 1'b0;
	initial	o_err    = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_wr_cyc  <= 0;
		o_wr_stb  <= 0;
		o_wr_addr <= 0;

		o_busy <= 1'b0;
		o_err  <= 1'b0;
		{ o_wr_addr, subaddr } <= {(ADDRESS_WIDTH){1'b0}};
		r_last <= 1'b0;
		// }}}
	end else if (!o_busy || o_err || (o_wr_cyc && i_wr_err))
	begin
		// {{{
		o_wr_cyc  <= 0;
		o_wr_stb  <= 0;
		o_wr_addr <= 0;

		o_busy <= i_request && !o_busy;

		o_err <= o_wr_cyc && i_wr_err;
		if (o_wr_cyc && i_wr_err)
			o_busy <= 1'b0;

		o_wr_addr <= i_addr[ADDRESS_WIDTH-1:WBLSB];
		subaddr   <= i_addr[WBLSB-1:0];
		r_last <= 1'b0;
		// }}}
	end else if (!o_wr_stb || !i_wr_stall)
	begin
		// {{{
		o_wr_stb <= 1'b0;

		if (o_wr_stb)
			{ o_wr_addr, subaddr } <= next_addr[ADDRESS_WIDTH-1:0];

		if (addr_overflow)
			{ o_err, o_wr_cyc, o_wr_stb } <= 3'b100;
		else if (!wb_pipeline_full)
		begin
			if ((r_last && (|r_sel)) || (S_VALID && !r_last))
			begin
				// Need to flush our last result out
				{ o_wr_cyc, o_wr_stb } <= 2'b11;

			end else if (wb_outstanding + (o_wr_stb ? 1:0)
							== (i_wr_ack ? 1:0))
			begin
				// We are all done writing
				o_wr_cyc <= 1'b0;
				o_busy <= !r_last;
			end
		end

		if (S_VALID && !r_last)
			r_last <= S_LAST;
		// }}}
	end

`ifdef	FORMAL
	always @(posedge i_clk)
	if (i_reset || !o_busy || o_err || (o_wr_cyc && i_wr_err))
	begin
	end else if (!o_wr_stb || !i_wr_stall)
	begin
		// {{{
		if (addr_overflow)
		begin
		end else if (!wb_pipeline_full)
		begin
			if (r_last && (|r_sel))
			begin
				// Need to flush our last result out
				assert(!S_READY);
			end else if (S_VALID && !r_last)
			begin
				assert(S_VALID && S_READY);
			end else begin
				assert(!S_VALID || !S_READY);
			end
		end else begin
			assert(!S_READY);
		end
		// }}}
	end else begin
		assert(!S_READY);
	end

	always @(*)
	if (!i_reset && !o_busy)
		assert(!o_wr_cyc);
`endif
	// }}}

	// o_wr_data, o_wr_sel
	// {{{
	always @(posedge i_clk)
	if (!o_busy) // i_reset || !o_busy || o_err || (o_wr_cyc && i_wr_err))
	begin
		// {{{
		{ r_data, o_wr_data  } <= {(2*DW  ){1'b0}};
		{ r_sel,  o_wr_sel   } <= {(2*DW/8){1'b0}};
		// }}}
	end else if ((!o_wr_stb || !i_wr_stall) && !wb_pipeline_full
					&& (r_last || S_VALID))
	begin
		// {{{
		if (OPT_LITTLE_ENDIAN)
		begin
			{ r_data, o_wr_data } <= next_data;
			{ r_sel,  o_wr_sel  } <= next_sel;
		end else begin
			{ o_wr_data, r_data } <= next_data;
			{ o_wr_sel,  r_sel  } <= next_sel;
		end
		// }}}
	end
	// }}}

	assign	S_READY = !r_last && o_busy && (!o_wr_stb || !i_wr_stall)
				&& !wb_pipeline_full;

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wr_data };
	// Verilator lint_on  UNUSED
	// }}}
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
	localparam	F_LGDEPTH = LGPIPE+1;
			reg		f_past_valid;
	(* anyconst *)	reg	[ADDRESS_WIDTH-1:0]	f_cfg_addr;
	(* anyconst *)	reg	[1:0]	f_cfg_size;
	(* anyconst *)	reg		f_cfg_inc;
	wire	[F_LGDEPTH-1:0]		fwb_nreqs, fwb_nacks, fwb_outstanding;
	reg	[ADDRESS_WIDTH:0]	f_posn, fwb_addr, fwb_posn;
	reg	[WBLSB-1:0]	fr_sel_count, fr_sel_count_past;
	reg	[ADDRESS_WIDTH-1:0]	r_addr;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Control interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_request);
	else if ($past(i_request && o_busy))
	begin
		assume(i_request);
		assume($stable(i_inc));
		assume($stable(i_size));
		assume($stable(i_addr));
	end

	always @(posedge i_clk)
	if (i_request && !o_busy)
	begin
		// r_inc  <= i_inc;
		// r_size <= i_size;
		r_addr <= i_addr;
	end

	always @(*)
	if (!f_cfg_inc) case(f_cfg_size)
	SZ_BYTE: begin end
	SZ_16B:  assume(f_cfg_addr[0] == 1'b0);
	SZ_32B:  assume(f_cfg_addr[1:0] == 2'b0);
	SZ_BUS:  assume(f_cfg_addr[WBLSB-1:0] == 0);
	endcase

	always @(*)
	if (i_request && !o_busy)
	begin
		assume(i_inc  == f_cfg_inc);
		assume(i_size == f_cfg_size);
		assume(i_addr == f_cfg_addr);
	end

	always @(*)
	if (!i_reset && o_busy)
	begin
		assert(r_addr == f_cfg_addr);
		assert(r_size == f_cfg_size);
		assert(r_inc  == f_cfg_inc);

		if (!r_inc)
		case(r_size)
		SZ_BYTE: begin end
		SZ_16B: assert(r_addr[0] == 1'b0);
		SZ_32B: assert(r_addr[1:0] == 2'b0);
		SZ_BUS: assert(r_addr[WBLSB-1:0] == 0);
		endcase
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!S_VALID);
	end else if ($past(S_VALID && !S_READY))
	begin
		assume(S_VALID);
		assume($stable(S_DATA));
		assume($stable(S_BYTES));
		assume($stable(S_LAST));
	end

	always @(*)
	if (S_VALID)
	begin
		assume(S_BYTES <= DW/8);
		assume(S_BYTES > 0);

		if (!S_LAST)
		case(f_cfg_size)
		2'b11: assume(S_BYTES == 1);
		2'b10: assume(S_BYTES == 2);
		2'b01: assume(S_BYTES == 4);
		2'b00: assume(S_BYTES == (DW/8));
		endcase
		else case(f_cfg_size)
		2'b11: assume(S_BYTES == 1);
		2'b10: assume(S_BYTES <= 2);
		2'b01: assume(S_BYTES <= 4);
		2'b00: assume(S_BYTES <= (DW/8));
		endcase
	end

	always @(posedge i_clk)
	if (i_reset || !o_busy)
		f_posn <= 0;
	else if (S_VALID && S_READY)
		f_posn <= f_posn + S_BYTES;

	always @(*)
	if (o_busy)
		assume(!f_posn[ADDRESS_WIDTH] || (f_posn[ADDRESS_WIDTH-1:0]==0
			&& r_last));

	always @(*)
	if (!i_reset && o_busy)
	begin
		if (r_last)
		begin
		end else case(f_cfg_size)
		2'b11: begin end
		2'b10: assert(f_posn[0] == 1'b0);
		2'b01: assert(f_posn[1:0] == 2'b0);
		2'b00: assert(f_posn[WBLSB-1:0] == 0);
		endcase
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_master #(
		.AW(AW), .DW(DW), .F_LGDEPTH(F_LGDEPTH),
		.F_OPT_DISCONTINUOUS(1'b1),
		.F_MAX_STALL(2),
		.F_MAX_ACK_DELAY(2)
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc( o_wr_cyc),
		.i_wb_stb( o_wr_stb),
		.i_wb_we(  o_wr_we),
		.i_wb_addr(o_wr_addr),
		.i_wb_data(o_wr_data),
		.i_wb_sel( o_wr_sel),
		//
		.i_wb_stall(i_wr_stall),
		.i_wb_ack(  i_wr_ack),
		.i_wb_idata(i_wr_data),
		.i_wb_err(  i_wr_err),
		//
		.f_nreqs(fwb_nreqs),
		.f_nacks(fwb_nacks),
		.f_outstanding(fwb_outstanding)
		// }}}
	);

	always @(*)
	if (!i_reset && o_wr_stb)
		assert(|o_wr_sel);

	always @(*)
	if (o_wr_cyc)
		assert(fwb_outstanding == wb_outstanding);

	initial	fwb_posn = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		fwb_posn <= 0;
	else if (o_wr_stb && !i_wr_stall)
		fwb_posn <= fwb_posn + $countones(o_wr_sel);

	always @(*)
	if (!i_reset && o_busy && !o_err)
		assert(f_posn == fwb_posn + $countones(r_sel)
				+ (o_wr_stb ? $countones(o_wr_sel) : 0));

	always @(*)
	if (r_inc)
	begin
		fwb_addr = r_addr + fwb_posn;

		if (fwb_posn > 0)
		case(r_size)
		SZ_16B: fwb_addr[  0] = 0;
		SZ_32B: fwb_addr[1:0] = 0;
		SZ_BUS: fwb_addr[WBLSB-1:0] = 0;
		default: begin end
		endcase
	end else begin
		// fwb_addr = r_addr + fwb_posn;
		fwb_addr = r_addr;

		case(r_size)
		SZ_BYTE: begin end
		SZ_16B: fwb_addr[0] = 0;
		SZ_32B: fwb_addr[1:0] = 0;
		SZ_BUS: fwb_addr[WBLSB-1:0] = 0;
		endcase
	end

	always @(*)
	if (!i_reset && o_busy && !r_last && !o_err)
			// && (o_wr_stb || !fwb_addr[ADDRESS_WIDTH]) && !r_last)
	begin
		assert({ 1'b0, o_wr_addr } == fwb_addr[ADDRESS_WIDTH:WBLSB]);
		case(r_size)
		SZ_BUS: assert(subaddr == r_addr[WBLSB-1:0]);
		SZ_16B: assert(subaddr == { fwb_addr[WBLSB-1:1], r_addr[0] });
		SZ_32B: assert(subaddr == { fwb_addr[WBLSB-1:2], r_addr[1:0] });
		default:
			assert(subaddr == fwb_addr[WBLSB-1:0]);
		endcase
	end

	always @(*)
	if (o_busy && fwb_addr[ADDRESS_WIDTH] && !r_last)
	begin
		assert(o_err);
		// assert(fwb_addr[ADDRESS_WIDTH-1:0] <= DW/8);
	end

	always @(*)
	if (!o_busy || o_err)
		assert(!o_wr_cyc);

	always @(*)
	if (!i_reset && o_busy)
	begin
		if (!r_inc)
		case(r_size)
		SZ_BYTE: begin end
		SZ_16B: assert(subaddr[0] == 1'b0);
		SZ_32B: assert(subaddr[1:0] == 2'b00);
		SZ_BUS: assert(subaddr == 0);
		endcase else case(r_size)
		SZ_BYTE: begin end
		SZ_16B: assert(subaddr[0]   == r_addr[0]);
		SZ_32B: assert(subaddr[1:0] == r_addr[1:0]);
		SZ_BUS: assert(subaddr      == r_addr[WBLSB-1:0]);
		endcase
	end

	always @(*)
		fr_sel_count = $countones(r_sel);

	always @(posedge i_clk)
	if (!o_wr_sel || !i_wr_stall)
		fr_sel_count_past <= fr_sel_count;

	always @(posedge i_clk)
	if(!i_reset && o_busy && !o_err && !r_last && $past(S_VALID && S_READY))
	begin
		assert(o_wr_stb);
		assert($countones({ r_sel, o_wr_sel })
					== $past(S_BYTES + fr_sel_count));
	end

	always @(*)
	if (!i_reset && o_busy)
	begin
		if (o_err)
			assert(!o_wr_cyc);
		if (f_posn == 0)
		begin
			assert(r_sel == 0);
			assert(!o_wr_cyc);
			assert(wb_outstanding == 0);
		end else
		case(r_size)
		SZ_BYTE: assert(r_sel == 0);
		SZ_16B: begin
			if (OPT_LITTLE_ENDIAN)
			begin
				assert(r_sel[DW/8-1:1] == 0);
			end else begin
				assert(r_sel[DW/8-2:0] == 0);
			end

			if (!o_wr_stb) begin end
			else if (subaddr + 2 <= DW/8)
			begin
				assert(r_sel == 0);
			end else if (!r_last)
			begin
				assert(r_sel[(OPT_LITTLE_ENDIAN) ? 0 : (DW/8-1)] == (subaddr+2 > DW/8));
			end else begin
				assert(r_sel[(OPT_LITTLE_ENDIAN) ? 0 : (DW/8-1)] <= (subaddr+2 > DW/8));
			end end
		SZ_32B: begin
			if (OPT_LITTLE_ENDIAN)
			begin
				assert(r_sel[DW/8-1:3] == 0);
			end else begin
				assert(r_sel[DW/8-4:0] == 0);
			end

			if (!o_wr_stb) begin end
			else if (subaddr + 4 <= DW/8)
			begin
				assert(r_sel == 0);
			/*
			end else if (!r_last)
			begin
				assert($countones(r_sel) == subaddr+4-DW/8);
			end else begin
				assert($countones(r_sel) <= subaddr+4-DW/8);
			*/
			end end
		SZ_BUS: begin
			assert(!(&r_sel));
			if (subaddr == 0)
				assert(r_sel == 0);
			end
		default: begin end
		endcase

		if (OPT_LITTLE_ENDIAN)
		begin
			if (!o_wr_sel[DW/8-1])
				assert(!r_sel[0]);
		end else begin
			if (!o_wr_sel[0])
				assert(!r_sel[DW/8-1]);
		end

		for(ik=0; ik<DW/8; ik=ik+1)
		if (OPT_LITTLE_ENDIAN)
		begin
			case(r_size)
			SZ_32B: if (ik > 2)
				assert(!r_sel[ik]);
			SZ_BUS: if (ik >= r_addr[DW/8-1:0])
				assert(!r_sel[ik]);
			default: begin end
			endcase
		end else begin
			if (ik > 0 && !r_sel[DW/8-ik])
			begin
				assert(!r_sel[DW/8-1-ik]);
			end

			case(r_size)
			SZ_32B: begin
				/*if (ik >= 4 || subaddr + ik < DW/8
					|| subaddr + ik - DW/8 >= 4)
				// assert(!r_sel[subaddr+ik-DW/8]);
				assert(!r_sel[DW/5-1-ik-subaddr]);
				*/
				end
			SZ_BUS: begin
				/*
				if (ik > DW/8-1-i_addr[DW/8-1:0])
				assert(!r_sel[ik]);
				*/
				end
			default: begin end
			endcase
		end
	end

	always @(*)
	if (!i_reset && o_busy && !r_inc)
		assert(r_sel == 0);

	reg	[WBLSB-1:0]	f_sum;

	always @(*)
	if (r_inc)
		f_sum = fwb_posn[WBLSB-1:0] + r_addr[WBLSB-1:0];
	else
		f_sum = fwb_posn[WBLSB-1:0];

	always @(*)
	if (!i_reset && o_busy && fwb_posn > 0)
	begin
		if (!r_last) case(r_size)
		SZ_16B: assert(f_sum[  0] == 0);
		SZ_32B: assert(f_sum[1:0] == 0);
		SZ_BUS: assert(f_sum[WBLSB-1:0] == 0);
		default: begin end
		endcase
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg				fc_check;
	(* anyconst *)	reg	[ADDRESS_WIDTH:0]	fc_posn;
	(* anyconst *)	reg	[7:0]			fc_byte;

	reg	[ADDRESS_WIDTH:0]	f_shift, fwb_shift;
	reg	[DW-1:0]	fc_partial;
	reg	[2*DW-1:0]	fc_partial_wb;
	reg	[2*DW/8-1:0]	fc_partial_sel;
	wire	[DW-1:0]	fz_data;
	wire	[DW/8-1:0]	fz_sel;

	assign	fz_data = 0;
	assign	fz_sel  = 0;

	always @(*)
	begin
		f_shift = (fc_posn - f_posn);
		f_shift[ADDRESS_WIDTH:WBLSB] = 0;
	end

	always @(*)
	if (OPT_LITTLE_ENDIAN)
		fc_partial = S_DATA >> (8*f_shift);
	else
		fc_partial = S_DATA << (8*f_shift);

	wire fin_check, fwb_check;
	assign	fin_check = fc_check && S_VALID && (f_posn <= fc_posn)
				&& (fc_posn < f_posn + S_BYTES);
	assign	fwb_check = fc_check && o_busy && !o_err
		&& (fwb_posn <= fc_posn)
		&&((o_wr_stb && fc_posn < fwb_posn + $countones(o_wr_sel))
		||(!o_wr_stb && fc_posn < fwb_posn + $countones(r_sel)));

	always @(*)
	if (fin_check)
	begin
		if (OPT_LITTLE_ENDIAN)
			assume(fc_partial[7:0] == fc_byte);
		else
			assume(fc_partial[DW-1:DW-8] == fc_byte);
	end

	always @(*)
	begin
		fwb_shift = 0;
		if (r_inc)
		begin
			fwb_shift[WBLSB-1:0] = fc_posn[WBLSB-1:0]
				- fwb_posn[WBLSB-1:0];
			if (o_wr_stb)
				fwb_shift[WBLSB-1:0] = fwb_shift[WBLSB-1:0] + fwb_addr[WBLSB-1:0];
		end else
			fwb_shift[WBLSB-1:0] = fc_posn[WBLSB-1:0] - fwb_posn[WBLSB-1:0]
							+ r_addr[WBLSB-1:0];
	end

	always @(*)
	if (OPT_LITTLE_ENDIAN)
	begin
		if (o_wr_stb)
		begin
		fc_partial_wb ={ r_data, o_wr_data} >> (8*fwb_shift);
		fc_partial_sel={ r_sel,  o_wr_sel } >>    fwb_shift;
		end else begin
		fc_partial_wb ={ fz_data, r_data} >> (8*fwb_shift);
		fc_partial_sel={ fz_sel,  r_sel } >>    fwb_shift;
		end
	end else begin
		if (o_wr_stb)
		begin
			fc_partial_wb ={ o_wr_data, r_data }<< (8*fwb_shift);
			fc_partial_sel={ o_wr_sel,  r_sel } <<    fwb_shift;
		end else begin
			fc_partial_wb ={ r_data,fz_data } << (8*fwb_shift);
			fc_partial_sel={ r_sel, fz_sel  } <<    fwb_shift;
		end
	end

	always @(*)
	if (o_busy)
		assert(fwb_posn <= f_posn);

	always @(*)
	if (fwb_check)
	begin
		if (OPT_LITTLE_ENDIAN)
		begin
			assert(fc_partial_wb[7:0] == fc_byte);
			assert(fc_partial_sel[0]);
		end else begin
			assert(fc_partial_wb[2*DW-1:2*DW-8] == fc_byte);
			assert(fc_partial_sel[2*DW/8-1]);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset))
		cover(i_request);

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset))
		cover(o_busy);

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && $past(o_busy))
	begin
		cover(!o_busy);

		if (!o_busy)
		begin
			case({ r_inc, r_size })
			3'b000: cover(f_posn > DW/8);
			3'b001: cover(f_posn > DW/8);
			3'b010: cover(f_posn > DW/8);
			3'b011: cover(f_posn > DW/8);
			3'b100: cover(f_posn > DW/8);
			3'b101: cover(f_posn > DW/8);
			3'b110: cover(f_posn > DW/8);
			3'b111: cover(f_posn > DW/8);
			endcase
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	case(f_cfg_size)
	SZ_BYTE: begin end
	SZ_BUS: begin end
	SZ_16B: assume(f_cfg_addr[0] == 1'b0);
	SZ_32B: assume(f_cfg_addr[1:0] == 2'b0);
	endcase

	// }}}
`endif
// }}}
endmodule
