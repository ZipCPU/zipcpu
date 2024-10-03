////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zaxdma_mm2s.v
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Converts an AXI (full) memory port to an AXI-stream
//		interface.
//
//	While I am aware that other vendors sell similar components, if you
//	look under the hood you'll find no relation to anything but my own
//	work here.
//
// Registers:	(None--this IP is controlled from elsewhere)
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024-2024, Gisselquist Technology, LLC
// {{{
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	zaxdma_mm2s #(
		// {{{
		parameter	ADDRESS_WIDTH = 32,
		parameter	BUS_WIDTH = 32,
		parameter	AXI_IW = 1,
		//
		// AXI_ID is the ID we will use for all of our AXI transactions
		parameter [AXI_IW-1:0]	AXI_ID = 0,
		//
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		// LGMAXBURST is the log based 2 of the maximum number of
		// beats per burst.  The maximum ARLEN will then be
		// (1<<LGMAXBURST)-1.
		parameter	LGMAXBURST = 8,
		// The size of the FIFO.  Should nominally be big enough for
		// two bursts.
		parameter	LGFIFO = LGMAXBURST+1,
		//
		// The bottom AXILSB bits of any AXI address are subword bits
		localparam	AXILSB = $clog2(BUS_WIDTH/8),
		//
		// LGLENGTH: Log based 2 of the maximum number of bytes that
		// will ever be transferred in one request
		parameter	LGLENGTH = AXILSB + LGFIFO + 1
		// }}}
	) (
		// {{{
		input	wire			i_clk,
		input	wire			i_reset,
		input	wire			i_soft_reset,
		// Configuration
		// {{{
		input	wire			i_request,
		output	wire			o_busy, o_err,
		input	wire			i_inc,
		input	wire	[1:0]		i_size,
		input	wire	[LGLENGTH-1:0]	i_transferlen,
		input wire [ADDRESS_WIDTH-1:0]	i_addr, // Byte address
		// }}}
		// The AXI (full) read interface
		// {{{
		output	wire			M_AXI_ARVALID,
		input	wire			M_AXI_ARREADY,
		output	wire	[AXI_IW-1:0]	M_AXI_ARID,
		output	wire	[ADDRESS_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[7:0]		M_AXI_ARLEN,
		output	wire	[2:0]		M_AXI_ARSIZE,
		output	wire	[1:0]		M_AXI_ARBURST,
		output	wire			M_AXI_ARLOCK,
		output	wire	[3:0]		M_AXI_ARCACHE,
		output	wire	[2:0]		M_AXI_ARPROT,
		output	wire	[3:0]		M_AXI_ARQOS,
		//
		input	wire			M_AXI_RVALID,
		output	wire			M_AXI_RREADY,
		input	wire	[BUS_WIDTH-1:0]	M_AXI_RDATA,
		input	wire			M_AXI_RLAST,
		input	wire	[AXI_IW-1:0]	M_AXI_RID,
		input	wire	[1:0]		M_AXI_RRESP,
		// }}}
		// The stream interface
		// {{{
		output	wire			M_AXIS_VALID,
		input	wire			M_AXIS_READY,
		output	wire	[BUS_WIDTH-1:0]	M_AXIS_DATA,
		output	wire	[AXILSB:0]	M_AXIS_BYTES,
		output	wire			M_AXIS_LAST
		// }}}
		// }}}
	);

	// Key questions:
	//	OPT_CONTINUOUS: Do we allow a restart mid-op, or force the
	//		entire pipeline to flush between operations?
	//
	//	  The realignment FIFO, depending on axi_raddr, would struggle
	//		with such an option.
	//	  Soft resets would force discontinuities in things alread read
	//	  Bus errors might also struggle with such an option, if
	//		read returns were still in progress

	// Signal declarations
	// {{{
	// Local parameter declarations
	// {{{
	localparam [1:0]	SZ_BYTE = 2'b11,
				SZ_16B  = 2'b10,
				SZ_32B  = 2'b01,
				SZ_BUS  = 2'b00;
	localparam	LGMAXBURST_LIMIT =$clog2(4096*8/BUS_WIDTH);
	localparam	LCLMAXBURST = (LGMAXBURST > LGMAXBURST_LIMIT)
				? LGMAXBURST_LIMIT : LGMAXBURST;
	localparam	LGMAX_FIXED_BURST = (LGMAXBURST < 4) ? LGMAXBURST : 4,
			MAX_FIXED_BURST = (1<<LGMAX_FIXED_BURST);
	localparam	LCLMAXBURST_SUB = (LGMAXBURST > 8) ? 8 : LGMAXBURST;
	localparam	FIFO_WIDTH = 1+(AXILSB+1)+BUS_WIDTH;
	localparam	FIFO_BYTES = (BUS_WIDTH / 8) * (1<<LGFIFO);
	// localparam [AXILSB-1:0] LSBZEROS = 0;
	// }}}

	reg		r_busy, r_inc, r_err, cmd_abort;
	reg	[1:0]	r_size;
	reg	[2:0]	axi_size;
	reg	[7:0]	maxlen;

	reg	[LGLENGTH-1:0]	rawlen, rawbeats, rawbursts,
				rawfirstln, rawblkln;
	reg	[LGLENGTH-1:0]	ar_requests_remaining, ar_beats_remaining;
	reg			ar_none_remaining;
	reg			ar_none_outstanding;
	reg	[LGLENGTH-1:0]	ar_bursts_outstanding;
	// reg			rd_none_remaining;
	// reg	[LGLENGTH:0]	rd_reads_remaining;
	reg			w_complete;
	reg			start_burst, phantom_start;
	reg	[LGLENGTH-1:0]	ar_next_remaining;
	reg	[7:0]		axi_arlen;
	reg	[ADDRESS_WIDTH:0]	nxt_araddr, axi_araddr;
	reg				axi_arvalid;

	reg	[LGLENGTH-1:0]	returned_bytes, r_bytes_remaining;
	reg	[ADDRESS_WIDTH-1:0]	axi_raddr;
	reg				rx_valid, rx_last;
	wire				rx_ready;
	reg	[AXILSB:0]		rx_bytes;
	reg	[BUS_WIDTH-1:0]		rx_data;

	wire			gbox_valid, gbox_last;
	wire	[BUS_WIDTH-1:0]	gbox_data;
	wire	[AXILSB:0]	gbox_bytes;


	reg	[LGLENGTH:0]	nxt_commitment, rd_uncommitted;
	reg	[1:0]		rd_ubursts;
	wire			fifo_full, fifo_empty;
	wire	[LGFIFO:0]	ign_fifo_fill;

`ifdef	FORMAL
	wire	[LGLENGTH:0]	fgbox_rcvd, fgbox_sent;

	wire	[LGFIFO:0]	ffif_first_addr, ffif_second_addr;
	wire	[FIFO_WIDTH-1:0]	ffif_first_data, ffif_second_data;
	wire			ffif_first_in_fifo, ffif_second_in_fifo;
	wire	[LGFIFO:0]	ffif_distance_to_first, ffif_distance_to_second;

	wire			ffif_first_last, ffif_second_last;
	wire	[AXILSB:0]	ffif_first_bytes, ffif_second_bytes;
`endif

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Configuration logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_busy
	// {{{
	initial	r_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_busy <= 1'b0;
	else if (!o_busy && i_request && !i_soft_reset)
		r_busy <= 1'b1;
	else if (w_complete)
		r_busy <= 1'b0;
	assign	o_busy = r_busy;
	// }}}

	// r_inc, r_size, axi_size, maxlen
	// {{{
	always @(posedge i_clk)
	if (!o_busy && (!OPT_LOWPOWER || i_request))
	begin
		r_inc <= i_inc;
		r_size <= i_size;

		case(i_size)
		SZ_BYTE: axi_size <= 3'h0;
		SZ_16B:  axi_size <= 3'h1;
		SZ_32B:  axi_size <= 3'h2;
		SZ_BUS:  axi_size <= AXILSB[2:0];
		endcase

		if (i_inc)
		begin
			case(i_size)
			SZ_BYTE: maxlen <= (1<<LCLMAXBURST_SUB)-1;
			SZ_16B:  maxlen <= (1<<LCLMAXBURST_SUB)-1;
			SZ_32B:  maxlen <= (1<<LCLMAXBURST_SUB)-1;
			SZ_BUS:  maxlen <= (1<<LCLMAXBURST)-1;
			endcase
		end else
			maxlen <= MAX_FIXED_BURST-1;
	end
	// }}}

	// cmd_abort
	// {{{
	initial	cmd_abort = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cmd_abort <= 1'b0;
	else if (!o_busy || w_complete)
		cmd_abort <= 1'b0;
	else begin
		if (i_soft_reset)
			cmd_abort <= 1'b1;
		if (r_inc && nxt_araddr[ADDRESS_WIDTH] && !ar_none_remaining)
			cmd_abort <= 1'b1;
		if (M_AXI_RVALID && M_AXI_RREADY && M_AXI_RRESP[1])
			cmd_abort <= 1'b1;
		if (M_AXI_ARVALID && M_AXI_ARREADY && r_inc
				&& nxt_araddr[ADDRESS_WIDTH])
			cmd_abort <= 1'b1;
	end
	// }}}

	// o_err, r_err
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		r_err <= 1'b0;
	else if (!o_busy)
		r_err <= 1'b0;
	else if (M_AXI_RVALID && M_AXI_RREADY && M_AXI_RRESP[1])
		r_err <= 1'b1;
	assign	o_err = r_err;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The incoming AXI (full) protocol section
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	//

	// Some counters to keep track of our state
	// {{{

	/*
	always @(posedge i_clk)
	if (!r_busy)
		r_pre_start <= 1;
	else
		r_pre_start <= 0;
	*/

	always @(*)
	begin
		// Since we're doing beats of the given size, the
		// transfer length must be increased by whatever it
		// takes to align ourselves with a truncated word
		// (not burst) boundary.
		case(i_size)
		SZ_BYTE: rawlen = i_transferlen;
		// Verilator lint_off WIDTH
		SZ_16B:  begin
			rawlen = i_transferlen + i_addr[  0] + 1;
			rawlen[0] = 1'b0;
			end
		SZ_32B:  begin
			rawlen = i_transferlen + i_addr[1:0] + 3;
			rawlen[1:0] = 2'b00;
			end
		SZ_BUS:  begin
			rawlen = i_transferlen + i_addr[AXILSB-1:0]
				+ (1<<AXILSB)-1;
			rawlen[AXILSB-1:0] = 0;
			end
		// Verilator lint_on  WIDTH
		endcase

		case(i_size)
		SZ_BYTE: rawbeats = rawlen;
		// Verilator lint_off WIDTH
		SZ_16B:  rawbeats = rawlen >> 1;
		SZ_32B:  rawbeats = rawlen >> 2;
		SZ_BUS:  rawbeats = rawlen >> AXILSB;
		// Verilator lint_on  WIDTH
		endcase

		case(i_size)
		SZ_BYTE: begin
			// Verilator lint_off WIDTH
			rawblkln = i_transferlen + i_addr[LCLMAXBURST_SUB-1:0];
			rawblkln = rawblkln + (1<<LCLMAXBURST_SUB)-1;
			end
		SZ_16B:  begin
			rawblkln = i_transferlen + i_addr[LCLMAXBURST_SUB:0];
			rawblkln = rawblkln + (2<<LCLMAXBURST_SUB)-1;
			end
		SZ_32B:  begin
			rawblkln = i_transferlen + i_addr[LCLMAXBURST_SUB+1:0];
			rawblkln = rawblkln + (4<<LCLMAXBURST_SUB)-1;
			end
		SZ_BUS:  begin
			rawblkln= i_transferlen +i_addr[LCLMAXBURST+AXILSB-1:0];
			rawblkln = rawblkln + (1<<(AXILSB+LCLMAXBURST))-1;
			end
		// Verilator lint_on  WIDTH
		endcase

		if (i_inc)
		begin
			case(i_size)
			// Verilator lint_off WIDTH
			SZ_BYTE: rawbursts = rawblkln >> LCLMAXBURST_SUB;
			SZ_16B:  rawbursts = rawblkln >> (1+LCLMAXBURST_SUB);
			SZ_32B:  rawbursts = rawblkln >> (2+LCLMAXBURST_SUB);
			SZ_BUS:  rawbursts = rawblkln >> (AXILSB+LCLMAXBURST);
			endcase
		end else
			rawbursts = rawbeats[LGLENGTH-1:LGMAX_FIXED_BURST]
				+ ((|rawbeats[LGMAX_FIXED_BURST-1:0]) ? 1:0);
			// Verilator lint_on  WIDTH

		if (i_inc)
		begin
			case(i_size)
			// Verilator lint_off WIDTH
			SZ_BYTE:rawfirstln = (1<<LCLMAXBURST_SUB)
						- i_addr[0+:LCLMAXBURST_SUB]-1;
			SZ_16B: rawfirstln = (1<<LCLMAXBURST_SUB)
						- i_addr[1+:LCLMAXBURST_SUB]-1;
			SZ_32B: rawfirstln = (1<<LCLMAXBURST_SUB)
						- i_addr[2+:LCLMAXBURST_SUB]-1;
			SZ_BUS: rawfirstln = (1<<LCLMAXBURST)
					- i_addr[AXILSB +: LCLMAXBURST]-1;
			// Verilator lint_on  WIDTH
			endcase
		end else
			rawfirstln = MAX_FIXED_BURST-1;
		if (rawfirstln >= rawbeats)
			rawfirstln = rawbeats-1;
	end

	initial	ar_none_remaining = 1;
	initial	ar_requests_remaining = 0;
	initial	ar_beats_remaining = 0;
	always @(posedge i_clk)
	if (i_reset || cmd_abort)
	begin
		ar_requests_remaining <= 0;
		ar_beats_remaining <= 0;
		ar_none_remaining <= 1;
	end else if (!r_busy)
	begin
		if (!OPT_LOWPOWER || i_request)
		begin
			ar_requests_remaining <= rawbursts;
			ar_beats_remaining <= rawbeats;
			ar_none_remaining     <= (i_transferlen == 0);
		end
	end else if (phantom_start)
	begin
		// Verilator lint_off WIDTH
		ar_requests_remaining <= ar_requests_remaining - 1;
		ar_beats_remaining <= ar_beats_remaining - M_AXI_ARLEN - 1;
		ar_none_remaining <= (ar_requests_remaining <= 1);
		// Verilator lint_on  WIDTH
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset && r_busy)
		assert(ar_none_remaining == (ar_requests_remaining == 0));
	always @(*)
	if (!i_reset && phantom_start)
		assert(M_AXI_ARVALID);
`endif
	// }}}

	// Count the number of bursts outstanding--these are the number of
	// ARVALIDs that have been accepted, but for which the RVALID && RLAST
	// has not (yet) been returned.
	// {{{
	initial	ar_none_outstanding   = 1;
	initial	ar_bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ar_bursts_outstanding <= 0;
		ar_none_outstanding <= 1;
	end else case ({ phantom_start,
				M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST })
	2'b01:	begin
			ar_bursts_outstanding <=  ar_bursts_outstanding - 1;
			ar_none_outstanding   <= (ar_bursts_outstanding == 1);
		end
	2'b10:	begin
		ar_bursts_outstanding <= ar_bursts_outstanding + 1;
		ar_none_outstanding <= 0;
		end
	default: begin end
	endcase
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
		assert(ar_none_outstanding == (ar_bursts_outstanding == 0));
`endif
	// }}}

	// rd_reads_remaining, rd_none_remaining: Are we there yet?
	// {{{
	// initial	rd_reads_remaining = 0;
	// initial	rd_none_remaining = 1;
	// always @(posedge  i_clk)
	// if (!r_busy)
	// begin
		// rd_reads_remaining <= rawbeats;
		// rd_none_remaining  <= (i_transferlen == 0);
	// end else if (M_AXI_RVALID && M_AXI_RREADY)
	// begin
		// rd_reads_remaining <= rd_reads_remaining - 1;
		// rd_none_remaining  <= (rd_reads_remaining <= 1);
	// end

	always @(*)
	if (!r_busy || !ar_none_outstanding || M_AXI_ARVALID)
		w_complete = 0;
	else if (cmd_abort)
		w_complete = 1;
	else
		w_complete = //(rd_none_remaining && !M_AXIS_VALID)
			// && fifo_empty && !gbox_valid && !rx_valid;
			M_AXIS_VALID && M_AXIS_READY && M_AXIS_LAST;
	// }}}

	// start_burst, phantom_start
	// {{{
	always @(*)
	begin
		start_burst = !ar_none_remaining;
		if (r_inc && nxt_araddr[ADDRESS_WIDTH])
			start_burst = 1'b0;
		// Make sure there's room in the FIFO ... must we?  YES, WE MUST
		if (rd_ubursts == 0)
			start_burst = 0;
		if (phantom_start) // || r_pre_start)
			// Insist on a minimum of one clock between burst
			// starts, so we can get our lengths right
			start_burst = 0;
		if (M_AXI_ARVALID && !M_AXI_ARREADY)
			start_burst = 0;
		if (!r_busy || cmd_abort)
			start_burst  = 0;
	end

	initial	phantom_start = 0;
	always @(posedge i_clk)
	if (i_reset)
		phantom_start <= 0;
	else
		phantom_start <= start_burst;
	// }}}

	// Calculate ARLEN for the next ARVALID
	// {{{
	always @(*)
	begin
		ar_next_remaining = ar_beats_remaining;
		if (phantom_start)
			// Verilator lint_off WIDTH
			ar_next_remaining = ar_next_remaining - (M_AXI_ARLEN+1);
			// Verilator lint_on  WIDTH
	end

	always @(posedge i_clk)
	if (!r_busy)
		axi_arlen <= rawfirstln[7:0];
	else if (M_AXI_ARVALID && M_AXI_ARREADY)
	begin
		// Verilator lint_off WIDTH
		if (maxlen < ar_next_remaining)
			// Verilator lint_on  WIDTH
			axi_arlen <= maxlen;
		else
			axi_arlen <= ar_next_remaining[7:0]-1;
	end
	// }}}

	// Calculate ARADDR for the next ARVALID
	// {{{
	always @(*)
	begin
		nxt_araddr = 0;
		case(r_size)
		// Verilator lint_off WIDTH
		SZ_BYTE: nxt_araddr = axi_araddr + (M_AXI_ARLEN + 1);
		SZ_16B: nxt_araddr[ADDRESS_WIDTH:1]
			= axi_araddr[ADDRESS_WIDTH-1:1]
						+ (M_AXI_ARLEN + 1);
		SZ_32B: nxt_araddr[ADDRESS_WIDTH:2]
			= axi_araddr[ADDRESS_WIDTH-1:2]
						+ (M_AXI_ARLEN + 1);
		SZ_BUS: nxt_araddr[ADDRESS_WIDTH:AXILSB]
			= axi_araddr[ADDRESS_WIDTH-1:AXILSB]
						+ (M_AXI_ARLEN + 1);
		// Verilator lint_on  WIDTH
		endcase

		if (!r_busy || !r_inc || !M_AXI_ARVALID)
			nxt_araddr = axi_araddr;
	end

	initial	axi_araddr = 0;
	always @(posedge i_clk)
	begin
		if (M_AXI_ARVALID && M_AXI_ARREADY && r_inc)
			axi_araddr <= nxt_araddr;

		if (!r_busy)
		begin
			axi_araddr <= { 1'b0, i_addr };
			if (!i_inc)
			case(i_size)
			SZ_BYTE: begin end
			SZ_16B: axi_araddr[0] <= 0;
			SZ_32B: axi_araddr[1:0] <= 0;
			SZ_BUS: axi_araddr[AXILSB-1:0] <= 0;
			endcase

			if (OPT_LOWPOWER && !i_request)
				axi_araddr <= 0;
		end
	end
	// }}}

	// ARVALID
	// {{{
	initial	axi_arvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_arvalid <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		axi_arvalid <= start_burst;
	// }}}

	// Assignments to the actual M_AXI_* signals
	// {{{
	assign	M_AXI_ARVALID= axi_arvalid;
	assign	M_AXI_ARID   = AXI_ID;
	assign	M_AXI_ARADDR = axi_araddr[ADDRESS_WIDTH-1:0];
	assign	M_AXI_ARLEN  = axi_arlen;
	// Verilator lint_off WIDTH
	assign	M_AXI_ARSIZE = axi_size;
	// Verilator lint_on  WIDTH
	assign	M_AXI_ARBURST= { 1'b0, r_inc };
	assign	M_AXI_ARLOCK = 0;
	assign	M_AXI_ARCACHE= 4'b0011;
	assign	M_AXI_ARPROT = 0;
	assign	M_AXI_ARQOS  = 0;

	// We could try to be fancy here, but actually ... we're guaranteeing
	// via the gearbox and FIFO that we'll never request data we don't
	// have room for.  Hence, we can simplify our calculation and just
	// hold RREADY low.
	assign	M_AXI_RREADY = 1'b1;
	// assign	M_AXI_RREADY = (!rx_valid || ign_rx_ready);

	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// RX Gears
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// returned_bytes
	// {{{
	// Bytes returned this clock cycle -- if RVALID && RREADY true
	always @(*)
	case(r_size)
	SZ_BYTE: returned_bytes = 1;
		// Verilator lint_off WIDTH
	SZ_16B: if (r_bytes_remaining >= 2 - axi_raddr[0])
			returned_bytes = 2 - axi_raddr[0];
		else
			returned_bytes = r_bytes_remaining;
	SZ_32B: if (r_bytes_remaining >= 4 - axi_raddr[1:0])
			returned_bytes = 4 - axi_raddr[1:0];
		else
			returned_bytes = r_bytes_remaining;
	SZ_BUS: if (r_bytes_remaining >= (1<<AXILSB)
					- axi_raddr[AXILSB-1:0])
			returned_bytes = (1<<AXILSB)
					- axi_raddr[AXILSB-1:0];
		else
			returned_bytes = r_bytes_remaining;
		// Verilator lint_on  WIDTH
	endcase
	// }}}

	// r_bytes_remaining
	// {{{
	always @(posedge i_clk)
	if (!r_busy && (!OPT_LOWPOWER || i_request))
		r_bytes_remaining <= i_transferlen;
	else if (M_AXI_RVALID && M_AXI_RREADY)
		r_bytes_remaining <= r_bytes_remaining - returned_bytes;
	// }}}

	// axi_raddr
	// {{{
	initial	axi_raddr = 0;
	always @(posedge i_clk)
	begin
		if (M_AXI_RVALID && M_AXI_RREADY)
		begin
			if (r_inc)
			begin
				case(r_size)
				SZ_BYTE: axi_raddr <= axi_raddr + 1;
				SZ_16B:  begin
					axi_raddr <= axi_raddr + 2;
					axi_raddr[0] <= 1'b0;
					end
				SZ_32B:  begin
					axi_raddr <= axi_raddr + 4;
					axi_raddr[1:0] <= 2'b0;
					end
				SZ_BUS:  begin
					axi_raddr <= axi_raddr + (1<<AXILSB);
					axi_raddr[AXILSB-1:0] <= {(AXILSB){1'b0}};
					end
				endcase
			end else begin
				case(r_size)
				SZ_BYTE: begin end
				SZ_16B:  axi_raddr[0] <= 1'b0;
				SZ_32B:  axi_raddr[1:0] <= 2'b0;
				SZ_BUS:  axi_raddr[AXILSB-1:0] <= {(AXILSB){1'b0}};
				endcase
			end
		end

		if (!r_busy)
		begin
			axi_raddr <= i_addr;
			/*
			if (i_inc)
				axi_raddr <= i_addr;
			else case(i_size)
			SZ_BYTE: axi_raddr <= i_addr;
			SZ_16B: axi_raddr<= { i_addr[ADDRESS_WIDTH-1:1], 1'b0 };
			SZ_32B: axi_raddr<= { i_addr[ADDRESS_WIDTH-1:2], 2'b0 };
			SZ_BUS: axi_raddr<= { i_addr[ADDRESS_WIDTH-1:AXILSB],
							{(AXILSB){1'b0}} };
			endcase
			*/
		end
	end
	// }}}

	// rx_valid
	// {{{
	// Realign the data before releasing it (to the external FIFO)
	initial	rx_valid = 1'b0;
	always @(posedge i_clk)
	if(i_reset || cmd_abort || i_soft_reset)
		rx_valid <= 0;
	else if (M_AXI_RVALID && M_AXI_RREADY)
		rx_valid <= !M_AXI_RRESP[1];
	else if (rx_ready)
		rx_valid <= 0;
	// }}}

	// rx_data
	// {{{
	always @(posedge i_clk)
	if (M_AXI_RVALID && M_AXI_RREADY)
		rx_data <= M_AXI_RDATA >> (8*axi_raddr[AXILSB-1:0]);
	// }}}

	// rx_bytes
	// {{{
	always @(posedge i_clk)
	if (M_AXI_RVALID && M_AXI_RREADY)
	begin
		if (returned_bytes[AXILSB])
			rx_bytes <= (1<<AXILSB);
		else
			rx_bytes <= {1'b0,returned_bytes[AXILSB-1:0]};
	end
	// }}}

	// rx_last
	// {{{
	always @(posedge i_clk)
	if (M_AXI_RVALID && M_AXI_RREADY)
		rx_last <= (returned_bytes >= r_bytes_remaining);
	// }}}

	zipdma_rxgears #(
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_LITTLE_ENDIAN(1'b1)	// AXI is always little endian
`ifdef	FORMAL
		, .F_LGCOUNT(LGLENGTH+1)
`endif
	) u_rxgears (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_soft_reset(cmd_abort),
		//
		.S_VALID(rx_valid), .S_READY(rx_ready),
		.S_DATA(rx_data), .S_BYTES(rx_bytes), .S_LAST(rx_last),
		//
		.M_VALID(gbox_valid), .M_READY(1'b1 || !fifo_full),
		.M_DATA(gbox_data), .M_BYTES(gbox_bytes),
		.M_LAST(gbox_last)
`ifdef	FORMAL
		, .f_rcvd(fgbox_rcvd), .f_sent(fgbox_sent)
`endif
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Data FIFO / Outgoing stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// nxt_commitment
	// {{{
	always @(*)
	begin
		// Verilator lint_off WIDTH
		case(r_size)
		SZ_BYTE: nxt_commitment = M_AXI_ARLEN+1;
		SZ_16B:  nxt_commitment = ((M_AXI_ARLEN+1) << 1);
		SZ_32B:  nxt_commitment = ((M_AXI_ARLEN+1) << 2);
		SZ_BUS:  nxt_commitment = ((M_AXI_ARLEN+1) << AXILSB);
		endcase
		// Verilator lint_on  WIDTH
	end
	// }}}

	// rd_uncommitted (units: bytes)
	// {{{
	initial	rd_uncommitted = FIFO_BYTES;
	always @(posedge i_clk)
	if (i_reset || !r_busy || cmd_abort || i_soft_reset
			|| (M_AXIS_VALID && M_AXIS_READY && M_AXIS_LAST))
		rd_uncommitted <= FIFO_BYTES;
	else case({ phantom_start, M_AXIS_VALID && M_AXIS_READY })
	2'b00: begin end
	2'b01: rd_uncommitted <= rd_uncommitted + (BUS_WIDTH/8);
	2'b10: rd_uncommitted <= rd_uncommitted - nxt_commitment;
	2'b11: rd_uncommitted <= rd_uncommitted + (BUS_WIDTH/8)
						- nxt_commitment;
	endcase
	// }}}

	// rd_ubursts: Two bits, first bit indicates 2+ bursts can be made,
	// {{{
	// LSB indicates at least one burst can be made.
	initial	rd_ubursts = 2'b11;
	always @(posedge i_clk)
	if (i_reset || cmd_abort || i_soft_reset
			|| (M_AXIS_VALID && M_AXIS_READY && M_AXIS_LAST))
		rd_ubursts <= 2'b11;
	else begin
		if (r_inc)
		begin
			case(r_size)
			SZ_BYTE: rd_ubursts <= { (rd_uncommitted >= 512),
						(rd_uncommitted >= 256) };
			SZ_16B:  rd_ubursts <= { (rd_uncommitted >= 1024),
						(rd_uncommitted >= 512) };
			// Verilator lint_off WIDTH
			SZ_32B:  rd_ubursts <= { (rd_uncommitted >= 2048),
						(rd_uncommitted >= 1024) };
			SZ_BUS:  rd_ubursts <= {
					(rd_uncommitted >= 2 * BUS_WIDTH/8
							* (1<<LCLMAXBURST_SUB)),
					(rd_uncommitted >=     BUS_WIDTH/8
							* (1<<LCLMAXBURST_SUB))
				};
			// Verilator lint_on  WIDTH
			endcase
		end else begin
			case(r_size)
			SZ_BYTE: rd_ubursts <= { (rd_uncommitted >= 32),
						(rd_uncommitted >=  16) };
			SZ_16B: rd_ubursts <= { (rd_uncommitted >=  64),
						(rd_uncommitted >=  32) };
			SZ_32B: rd_ubursts <= { (rd_uncommitted >= 128),
						(rd_uncommitted >=  64) };
			SZ_BUS: rd_ubursts <= { (rd_uncommitted >= (BUS_WIDTH*4)),
						(rd_uncommitted >= (BUS_WIDTH*2)) };
			endcase
		end

		if (phantom_start)
			rd_ubursts[0] <= 1'b0;
	end
	// }}}

	sfifo #(
		// {{{
		.BW(FIFO_WIDTH), .LGFLEN(LGFIFO),
		.OPT_ASYNC_READ(1'b0),
		.OPT_WRITE_ON_FULL(1'b0),
		.OPT_READ_ON_EMPTY(1'b0)
		// }}}
	) u_fifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_abort),
		//
		.i_wr(gbox_valid),
			.i_data({ gbox_last, gbox_bytes, gbox_data }),
			.o_full(fifo_full), .o_fill(ign_fifo_fill),
		.i_rd(M_AXIS_READY),
			.o_data({ M_AXIS_LAST, M_AXIS_BYTES, M_AXIS_DATA }),
			.o_empty(fifo_empty)
`ifdef	FORMAL
		, .f_first_addr(ffif_first_addr),
		.f_second_addr(ffif_second_addr),
		.f_first_data(ffif_first_data),
		.f_second_data(ffif_second_data),
		.f_first_in_fifo(ffif_first_in_fifo),
		.f_second_in_fifo(ffif_second_in_fifo),
		.f_distance_to_first(ffif_distance_to_first),
		.f_distance_to_second(ffif_distance_to_second)
`endif
		// }}}
	);

	assign	M_AXIS_VALID = !fifo_empty;
`ifdef	FORMAL
	assign	ffif_first_last  = ffif_first_data[FIFO_WIDTH-1];
	assign	ffif_second_last = ffif_second_data[FIFO_WIDTH-1];
	assign	ffif_first_bytes  = ffif_first_data[BUS_WIDTH +: AXILSB+1];
	assign	ffif_second_bytes = ffif_second_data[BUS_WIDTH +: AXILSB+1];
`endif
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXI_RID, M_AXI_RRESP[0], ign_fifo_fill
			};
	// Verilator coverage_on
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
	reg	f_past_valid;
	reg	[LGLENGTH:0]	ftot_beats, frx_beats, ftot_bursts, frx_bursts,
				fbeat_count, fburst_count;
	reg	[ADDRESS_WIDTH:0]	frx_addr, flast_addr;

	reg	[ADDRESS_WIDTH:0]	far_pages, far_starting_page,
					far_ending_page;
	reg				f_bkfirst; // f_cklast;
	reg	[ADDRESS_WIDTH-1:0]	f_bkaddr, f_eob;
	reg				f_ckfirst, f_cklast;
	reg	[ADDRESS_WIDTH-1:0]	f_ckaddr, f_ckeob;

	(* anyconst *)	reg			fc_inc;
	(* anyconst *)	reg	[1:0]		fc_size;
	(* anyconst *)	reg	[LGLENGTH:0]	fc_transferlen;
	(* anyconst *)	reg [ADDRESS_WIDTH-1:0]	fc_addr;

	reg	[LGLENGTH:0]	f_committed, faxis_beats, ftot_count;
	reg			ffif_assume_result, fgbox_rcvd_valid;



	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Properties of the AXI-stream data interface
	// {{{
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// (These are captured by the FIFO within)

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		assume(fc_transferlen != 0);
		assume(fc_transferlen <= (1<<LGLENGTH));
	end

	always @(*)
	if (i_request && !o_busy)
	begin
		assume(i_inc == fc_inc);
		assume(i_size == fc_size);
		assume(i_transferlen == fc_transferlen);
		assume(i_addr == fc_addr);
	end else if (!i_reset && o_busy)
	begin
		assert(r_inc == fc_inc);
		assert(r_size == fc_size);
		if (r_inc)
			assert(cmd_abort || (ar_none_remaining && axi_araddr == 0) || axi_araddr >= fc_addr);
		else case(r_size)
		SZ_BYTE: assert(axi_araddr == fc_addr);
		SZ_16B: assert(axi_araddr == { fc_addr[ADDRESS_WIDTH-1:1], 1'b0 });
		SZ_32B: assert(axi_araddr == { fc_addr[ADDRESS_WIDTH-1:2], 2'b00 });
		SZ_BUS: assert(axi_araddr == { fc_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} });
		endcase

		case(r_size)
		SZ_BYTE: assert(M_AXI_ARSIZE == 3'h0);
		SZ_16B:  assert(M_AXI_ARSIZE == 3'h1);
		SZ_32B:  assert(M_AXI_ARSIZE == 3'h2);
		SZ_BUS:  assert(M_AXI_ARSIZE == AXILSB);
		endcase
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_request);
	else if ($past(i_request && o_busy))
	begin
		assume(i_request);
		assume($stable(i_inc));
		assume($stable(i_size));
		assume($stable(i_transferlen));
		assume($stable(i_addr));
	end

	always @(*)
	if (!i_reset && r_busy)
	begin
		if (fc_inc)
		begin
			case(fc_size)
			SZ_BYTE: assert(maxlen == (1<<LCLMAXBURST_SUB)-1);
			SZ_16B:  assert(maxlen == (1<<LCLMAXBURST_SUB)-1);
			SZ_32B:  assert(maxlen == (1<<LCLMAXBURST_SUB)-1);
			SZ_BUS:  assert(maxlen == (1<<LCLMAXBURST)-1);
			endcase
		end else
			assert(maxlen == MAX_FIXED_BURST-1);
	end

	always @(*)
	if (!i_reset && r_busy && (M_AXI_ARVALID || !ar_none_remaining))
		assert(M_AXI_ARLEN <= maxlen);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The AXI master memory interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	F_LGDEPTH = LGLENGTH+4;

	wire	[F_LGDEPTH-1:0]	faxi_awr_nbursts, faxi_rd_nbursts,
				faxi_rd_outstanding, faxi_wr_nburstss;
	wire	[9-1:0]		faxi_wr_pending;
	wire	[AXI_IW-1:0]	faxi_wr_checkid, faxi_rd_checkid;
	wire			faxi_wr_ckvalid, faxi_rd_ckvalid;
	wire	[ADDRESS_WIDTH-1:0]	faxi_wr_addr;
	wire	[7:0]		faxi_wr_incr;
	wire	[1:0]		faxi_wr_burst;
	wire	[2:0]		faxi_wr_size;
	wire	[7:0]		faxi_wr_len;
	wire			faxi_wr_lockd;

	wire	[9-1:0]		faxi_rd_cklen;
	wire	[ADDRESS_WIDTH-1:0]	faxi_rd_ckaddr;
	wire	[7:0]	faxi_rd_ckincr;
	wire	[1:0]	faxi_rd_ckburst;
	wire	[2:0]	faxi_rd_cksize;
	wire	[7:0]	faxi_rd_ckarlen;
	wire		faxi_rd_cklockd;

	wire	[F_LGDEPTH-1:0]	faxi_rdid_nbursts, faxi_rdid_outstanding,
			faxi_rdid_ckign_nbursts, faxi_rdid_ckign_outstanding;

	wire	[1:0]		faxi_ex_state;
	wire			faxi_ex_checklock;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_bursts_to_lock,
				faxi_wrid_bursts_to_exwrite;
		//
	wire	[ADDRESS_WIDTH-1:0]	faxi_exreq_addr;
	wire	[7:0]			faxi_exreq_len;
	wire	[1:0]			faxi_exreq_burst;
	wire	[2:0]			faxi_exreq_size;
	wire				faxi_exreq_return;

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(AXI_IW),
		.C_AXI_ADDR_WIDTH(ADDRESS_WIDTH),
		.C_AXI_DATA_WIDTH(BUS_WIDTH),
		//
		.OPT_EXCLUSIVE(1'b0),
		.OPT_NARROW_BURST(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxi(
		// {{{
		.i_clk(i_clk), .i_axi_reset_n(!i_reset),
		//
		.i_axi_awvalid(1'b0),
		.i_axi_awready(1'b0),
		.i_axi_awid(   AXI_ID),
		.i_axi_awaddr( 0),
		.i_axi_awlen(  0),
		.i_axi_awsize( 0),
		.i_axi_awburst(0),
		.i_axi_awlock( 0),
		.i_axi_awcache(0),
		.i_axi_awprot( 0),
		.i_axi_awqos(  0),
		//
		.i_axi_wvalid(0),
		.i_axi_wready(0),
		.i_axi_wdata( 0),
		.i_axi_wstrb( 0),
		.i_axi_wlast( 0),
		//
		.i_axi_bvalid(1'b0),
		.i_axi_bready(1'b0),
		.i_axi_bid(   AXI_ID),
		.i_axi_bresp( 2'b00),
		//
		.i_axi_arvalid(M_AXI_ARVALID),
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_arid(   M_AXI_ARID),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arlen(  M_AXI_ARLEN),
		.i_axi_arsize( M_AXI_ARSIZE),
		.i_axi_arburst(M_AXI_ARBURST),
		.i_axi_arlock( M_AXI_ARLOCK),
		.i_axi_arcache(M_AXI_ARCACHE),
		.i_axi_arprot( M_AXI_ARPROT),
		.i_axi_arqos(  M_AXI_ARQOS),
		//
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rlast( M_AXI_RLAST),
		.i_axi_rresp( M_AXI_RRESP),
		// Induction
		// {{{
		.f_axi_awr_nbursts(faxi_awr_nbursts),
		.f_axi_wr_pending(faxi_wr_pending),
		.f_axi_rd_nbursts(faxi_rd_nbursts),
		.f_axi_rd_outstanding(faxi_rd_outstanding),
		//
		.f_axi_wr_checkid(faxi_wr_checkid),
		.f_axi_wr_ckvalid(faxi_wr_ckvalid),
		.f_axi_wr_addr(faxi_wr_addr),
		.f_axi_wr_incr(faxi_wr_incr),
		.f_axi_wr_burst(faxi_wr_burst),
		.f_axi_wr_size(faxi_wr_size),
		.f_axi_wr_len(faxi_wr_len),
		.f_axi_wr_lockd(faxi_wr_lockd),
		//
		.f_axi_rd_checkid(faxi_rd_checkid),
		.f_axi_rd_ckvalid(faxi_rd_ckvalid),
		.f_axi_rd_cklen(faxi_rd_cklen),
		.f_axi_rd_ckaddr(faxi_rd_ckaddr),
		.f_axi_rd_ckincr(faxi_rd_ckincr),
		.f_axi_rd_ckburst(faxi_rd_ckburst),
		.f_axi_rd_cksize(faxi_rd_cksize),
		.f_axi_rd_ckarlen(faxi_rd_ckarlen),
		.f_axi_rd_cklockd(faxi_rd_cklockd),
		//
		.f_axi_rdid_nbursts(faxi_rdid_nbursts),
		.f_axi_rdid_outstanding(faxi_rdid_outstanding),
		.f_axi_rdid_ckign_nbursts(faxi_rdid_ckign_nbursts),
		.f_axi_rdid_ckign_outstanding(faxi_rdid_ckign_outstanding),
		//
		.f_axi_ex_state(faxi_ex_state),
		.f_axi_ex_checklock(faxi_ex_checklock),
		.f_axi_rdid_bursts_to_lock(faxi_rdid_bursts_to_lock),
		.f_axi_wrid_bursts_to_exwrite(faxi_wrid_bursts_to_exwrite),
		.i_active_lock(1'b0),
		.i_exlock_addr({(ADDRESS_WIDTH){1'b0}}),
		.i_exlock_len(8'h00),
		.i_exlock_burst(2'b0),
		.i_exlock_size(3'b0),
		//
		.f_axi_exreq_addr(faxi_exreq_addr),
		.f_axi_exreq_len(faxi_exreq_len),
		.f_axi_exreq_burst(faxi_exreq_burst),
		.f_axi_exreq_size(faxi_exreq_size),
		.f_axi_exreq_return(faxi_exreq_return)
		//
		// }}}
		// }}}
	);


	always @(*)
	begin
		assume(faxi_wr_checkid == AXI_ID);
		assume(faxi_rd_checkid == AXI_ID);

		if (f_past_valid)
		begin
			assert(faxi_awr_nbursts == 0);
			assert(faxi_wr_pending == 0);
			assert(faxi_rdid_nbursts == faxi_rd_nbursts);
			assert(faxi_rdid_outstanding == faxi_rd_outstanding);
			assert(faxi_rd_nbursts + ((M_AXI_ARVALID && !phantom_start) ? 1:0) == ar_bursts_outstanding);

			if (!o_busy)
			begin
				assert(!M_AXI_ARVALID);
				assert(faxi_rd_nbursts == 0);
				assert(faxi_rd_outstanding == 0);
				assert(!rx_valid);
				assert(!gbox_valid);
				assert(fifo_empty);
				assert(!M_AXIS_VALID);
				assert(!cmd_abort);
			end
		end
	end

	always @(posedge i_clk)
	if (f_past_valid && cmd_abort && $past(cmd_abort))
	begin
		assert(!$rose(M_AXI_ARVALID));
		assert(!rx_valid);
		assert(!gbox_valid);
		assert(fifo_empty);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// End-to-end byte counting
	// {{{

	// TRANSFERLEN == 
	//		r_bytes_remaining + (rx_valid ? rx_bytes : 0)
	//			+ (fgbox_rcvd-fgbox_sent)
	//			+ FIFO_FILL * (BUS_WIDTH/8) // If !LAST
	//

	// TRANSFERLEN == 
	//		(ar_requests_remaining + faxi_rd_outstanding) << burstsz
	//			+ (rx_valid ? rx_bytes : 0)
	//			+ (fgbox_rcvd-fgbox_sent)
	//			+ FIFO_FILL * (BUS_WIDTH/8) // If !LAST
	//

	always @(posedge i_clk)
	if (i_reset || cmd_abort || !r_busy)
		faxis_beats <= 0;
	else if (M_AXIS_VALID && M_AXIS_READY)
		faxis_beats <= faxis_beats + 1;

	always @(*)
	if (!i_reset && r_busy && r_bytes_remaining == 0 && !cmd_abort)
		assert(ar_none_outstanding && ar_none_remaining);

	always @(*)
	if (!i_reset && r_busy && !cmd_abort)
	begin
		case(fc_size)
		SZ_BYTE: begin
			assert(ar_beats_remaining + faxi_rd_outstanding
				+((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1) : 0)
					== r_bytes_remaining);
			end
		endcase
	end

	always @(*)
	if (!i_reset && r_busy && rx_valid)
	begin
		if (frx_beats == ftot_beats)
		begin
			// case(fc_size)
			// SZ_BYTE: begin end
			// SZ_16B: assert(rx_bytes == 2);
			// SZ_32B: assert(rx_bytes == 4);
			// SZ_BUS: assert(rx_bytes == (1<<AXILSB));
			// endcase
		end else if (frx_beats <= 1)
		begin
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: assert(rx_bytes == 2 - fc_addr[0]);
			SZ_32B: assert(rx_bytes == 4 - fc_addr[1:0]);
			SZ_BUS: assert(rx_bytes == (1<<AXILSB)
						- fc_addr[AXILSB-1:0]);
			endcase
		end else begin
			case(fc_size)
			SZ_BYTE: assert(rx_bytes == 1);
			SZ_16B:  assert(rx_bytes == 2);
			SZ_32B:  assert(rx_bytes == 4);
			SZ_BUS:  assert(rx_bytes == (1<<AXILSB));
			endcase
		end
	end

	always @(*)
	if (!i_reset && r_busy)
	begin
		assert(faxis_beats <= fc_transferlen[LGLENGTH:AXILSB]
					+ (|fc_transferlen[AXILSB-1:0]));
	end

	always @(*)
	begin
		fgbox_rcvd_valid = fgbox_rcvd > 0;
		if (r_bytes_remaining > 0)
			fgbox_rcvd_valid = 1;
	end

	always @(*)
	case(fc_size)
	SZ_BYTE: ftot_count = ar_beats_remaining
				+((M_AXI_ARVALID && !phantom_start)
							? (M_AXI_ARLEN+1):0)
				+ faxi_rd_outstanding
				+ (rx_valid ? rx_bytes : 0)
				+ ((fgbox_rcvd_valid)
					? (fgbox_rcvd - fgbox_sent)
					: (gbox_valid ? gbox_bytes : 0))
				+ (ign_fifo_fill << AXILSB)
				+ (faxis_beats << AXILSB);
	SZ_16B: begin
			ftot_count = ar_beats_remaining
				+((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0)
				+ faxi_rd_outstanding + (rx_valid ? 1 : 0)
				+ ((faxis_beats+ign_fifo_fill) << (AXILSB-1));

			
			if (fgbox_rcvd_valid)
			begin
				ftot_count = ftot_count
					+ ((fgbox_rcvd[0] != fgbox_sent[0])
							? 1:0)
					+ (fgbox_rcvd[LGLENGTH:1] - fgbox_sent[LGLENGTH:1]);
			end else if (gbox_valid)
				ftot_count = ftot_count + (gbox_bytes >> 1)
					+ (gbox_bytes[0]) + (!gbox_last);

			if (!fgbox_rcvd_valid && ftot_beats != fc_transferlen[LGLENGTH:1] + fc_transferlen[0])
				ftot_count = ftot_count + 1;
		end
	SZ_32B: begin
			ftot_count = ar_beats_remaining
				+((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0)
				+ faxi_rd_outstanding + (rx_valid ? 1 : 0)
				+ ((ign_fifo_fill + faxis_beats) << (AXILSB-2));

			if (fgbox_rcvd_valid)
			begin
				ftot_count = ftot_count
					+ ((fgbox_rcvd[1:0] != fgbox_sent[1:0]) ? 1:0)
					+ (fgbox_rcvd[LGLENGTH:2] - fgbox_sent[LGLENGTH:2]);
			end else if (gbox_valid)
			begin
				ftot_count = ftot_count + (gbox_bytes >> 2)
					+ (|gbox_bytes[1:0]) + (!gbox_last);
			end

			if (!fgbox_rcvd_valid && ftot_beats != fc_transferlen[LGLENGTH:2] + (|fc_transferlen[1:0]))
				ftot_count = ftot_count + 1;
		end
	SZ_BUS: begin
			ftot_count = ar_beats_remaining
				+((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0)
				+ faxi_rd_outstanding + (rx_valid ? 1 : 0)
				+ ign_fifo_fill + faxis_beats;

			if (fgbox_rcvd_valid)
			begin
				ftot_count = ftot_count
					+ ((fgbox_rcvd[AXILSB-1:0] != fgbox_sent[AXILSB-1:0]) ? 1:0)
					+ (gbox_valid ? 1:0);
			end else if (gbox_valid)
				ftot_count = ftot_count + 1 + (!gbox_last);
			if (!fgbox_rcvd_valid && ftot_beats != fc_transferlen[LGLENGTH:AXILSB] + (|fc_transferlen[AXILSB-1:0]))
				ftot_count = ftot_count + 1;
		end
	endcase

	always @(*)
	if (!i_reset && r_busy && !cmd_abort && (r_bytes_remaining > 0 || rx_valid || gbox_valid))
	begin
		case(fc_size)
		SZ_BYTE: begin
			assert(fc_transferlen == ftot_count);
			assert(ar_beats_remaining <= fc_transferlen);
			assert(faxi_rd_outstanding <= fc_transferlen);
			end
		SZ_16B: begin
			assert(ftot_beats == ftot_count);

			assert((r_bytes_remaining == 0)
				|| (fc_transferlen == r_bytes_remaining
				+ (frx_beats << 1)
				- ((r_bytes_remaining < fc_transferlen)
					? fc_addr[0] :0)));

			assert(ar_beats_remaining <= ftot_beats);
			assert(faxi_rd_outstanding <= ftot_beats);
			end
		SZ_32B: begin
			assert(ftot_beats == ftot_count);

			assert((r_bytes_remaining == 0)
				||(fc_transferlen == r_bytes_remaining
				+ (frx_beats << 2)
				- ((r_bytes_remaining < fc_transferlen)
					? fc_addr[1:0] :0)));

			assert(ar_beats_remaining <= ftot_beats);
			assert(faxi_rd_outstanding <= ftot_beats);
			end
		SZ_BUS: begin
			assert(ftot_beats == ftot_count);

			assert((r_bytes_remaining == 0)
				||(fc_transferlen == r_bytes_remaining
				+ (frx_beats << AXILSB)
				- ((r_bytes_remaining < fc_transferlen)
					? fc_addr[AXILSB-1:0] :0)));
			// assert(r_bytes_remaining == ftot_beats);
			assert(ar_beats_remaining <= ftot_beats);
			assert(faxi_rd_outstanding <= ftot_beats);
			end
		endcase
	end

	always @(*)
	if (r_busy)
	begin
		assert(cmd_abort || r_bytes_remaining <= fc_transferlen);
		assert(fgbox_rcvd < fc_transferlen);
		assert(fgbox_sent < fc_transferlen);
	end

	always @(*)
	if (r_busy && !cmd_abort && (r_bytes_remaining != 0 || rx_valid))
	begin
		assert((faxis_beats << AXILSB) < fc_transferlen);
		assert((ign_fifo_fill << AXILSB) < fc_transferlen);

		assert(fc_transferlen == r_bytes_remaining
			+ (rx_valid ? rx_bytes : 0)
			+ (fgbox_rcvd - fgbox_sent)
			+ (ign_fifo_fill << AXILSB)
			+ (faxis_beats << AXILSB));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Other formal properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// Beat count verification
	// {{{
	always @(*)
	case(fc_size)
	SZ_BYTE: ftot_beats = fc_transferlen;
	SZ_16B: begin
		ftot_beats = fc_transferlen + fc_addr[0] + 1;
		ftot_beats[0] = 1'b0;
		ftot_beats = ftot_beats >> 1;
		end
	SZ_32B: begin
		ftot_beats = fc_transferlen + fc_addr[1:0] + 3;
		ftot_beats[1:0] = 2'b0;
		ftot_beats = ftot_beats >> 2;
		end
	SZ_BUS: begin
		ftot_beats = fc_transferlen + fc_addr[AXILSB-1:0]
				+ (1<<AXILSB)-1;
		ftot_beats[AXILSB-1:0] = {(AXILSB){1'b0}};
		ftot_beats = ftot_beats >> AXILSB;
		end
	endcase

	always @(posedge i_clk)
	if (i_reset || !o_busy)
		frx_beats <= 0;
	else if (M_AXI_RVALID && M_AXI_RREADY)
		frx_beats <= frx_beats + 1;

	// Beats remaining = total_beats - beats received - beats_outstanding
	always @(*)
	begin
		fbeat_count = frx_beats + faxi_rd_outstanding
				+ ar_beats_remaining;
		if (M_AXI_ARVALID && !phantom_start)
			fbeat_count = fbeat_count + M_AXI_ARLEN + 1;
	end

	always @(*)
	if (!i_reset && o_busy)
	begin
		assert(frx_beats <= ftot_beats);
		assert(faxi_rd_outstanding <= ftot_beats);
		assert(ar_beats_remaining <= ftot_beats);
		assert(fbeat_count <= ftot_beats);

		if (cmd_abort)
		begin
			assert(fbeat_count <= ftot_beats);
		end else
			assert(fbeat_count == ftot_beats);
	end
	// }}}

	// Return (& request) Address verification
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_busy)
	begin
		frx_addr <= fc_addr;
	end else if (M_AXI_RVALID && M_AXI_RREADY)
	begin
		if (fc_inc)
		begin
			case(fc_size)
			SZ_BYTE: frx_addr <= frx_addr + 1;
			SZ_16B: begin
				frx_addr <= frx_addr + 2;
				frx_addr[0] <= 1'b0;
				end
			SZ_32B: begin
				frx_addr <= frx_addr + 4;
				frx_addr[1:0] <= 2'b0;
				end
			SZ_BUS: begin
				frx_addr <= frx_addr + (1<<AXILSB);
				frx_addr[AXILSB-1:0] <= {(AXILSB){1'b0}};
				end
			endcase
		end else begin
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: frx_addr[0] <= 1'b0;
			SZ_32B: frx_addr[1:0] <= 2'b0;
			SZ_BUS: frx_addr[AXILSB-1:0] <= {(AXILSB){1'b0}};
			endcase
		end
	end

	// Check the return address
	always @(*)
	if (!i_reset && o_busy && fc_inc)
	begin
		assert(frx_addr <= (1<<ADDRESS_WIDTH));
		assert(frx_addr >= fc_addr);
		if (frx_addr != fc_addr || rx_valid || fgbox_rcvd != 0)
		case(fc_size)
		SZ_BYTE: assert(frx_addr + faxi_rd_outstanding + (M_AXI_ARVALID ? (M_AXI_ARLEN+1):0) <= (1<<ADDRESS_WIDTH));
		SZ_16B:  assert(frx_addr + ((faxi_rd_outstanding + (M_AXI_ARVALID ? (M_AXI_ARLEN+1):0)) << 1) <= (1<<ADDRESS_WIDTH) + 1);
		SZ_32B:  assert(frx_addr + ((faxi_rd_outstanding + (M_AXI_ARVALID ? (M_AXI_ARLEN+1):0)) << 2) <= (1<<ADDRESS_WIDTH) + 3);
		SZ_BUS:  assert(frx_addr + ((faxi_rd_outstanding + (M_AXI_ARVALID ? (M_AXI_ARLEN+1):0)) << AXILSB) <= (1<<ADDRESS_WIDTH) + (1<<AXILSB)-1);
		endcase
	end

	always @(*)
	if (!i_reset && o_busy && (!cmd_abort || !frx_addr[ADDRESS_WIDTH]))
	begin
		assert(axi_raddr == frx_addr);
		if (fc_inc)
		begin
			assert(frx_addr >= fc_addr);
			case(fc_size)
			SZ_BYTE: assert(frx_addr <=  { 1'b0, fc_addr } + fc_transferlen);
			SZ_16B: assert(frx_addr <=  { 1'b0, fc_addr[ADDRESS_WIDTH-1:1], 1'b0 } + (ftot_beats << 1));
			SZ_32B: assert(frx_addr <=  { 1'b0, fc_addr[ADDRESS_WIDTH-1:2], 2'b00 } + (ftot_beats << 2));
			SZ_BUS: assert(frx_addr <=  { 1'b0, fc_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} } + (ftot_beats << AXILSB));
			endcase
		end
	end

	always @(*)
	if (!i_reset && r_busy && !cmd_abort && fc_inc)
	begin
		if (r_bytes_remaining > 0)
			assert(frx_addr + r_bytes_remaining == { 1'b0, fc_addr } + fc_transferlen);
	end

	always @(*)
	if (!i_reset && r_busy && !cmd_abort && !fc_inc)
	begin
		if (!ar_none_remaining)
		case(fc_size)
		SZ_BYTE: assert(ar_beats_remaining[LGMAX_FIXED_BURST-1:0] == fc_transferlen[LGMAX_FIXED_BURST-1:0]);
		SZ_16B:  assert(ar_beats_remaining[LGMAX_FIXED_BURST-1:0] == ftot_beats[LGMAX_FIXED_BURST-1:0]);
		SZ_32B:  assert(ar_beats_remaining[LGMAX_FIXED_BURST-1:0] == ftot_beats[LGMAX_FIXED_BURST-1:0]);
		SZ_BUS:  assert(ar_beats_remaining[LGMAX_FIXED_BURST-1:0] == ftot_beats[LGMAX_FIXED_BURST-1:0]);
		endcase

		if (r_bytes_remaining == fc_transferlen)
		begin
			assert(frx_addr == fc_addr);
		end else case(fc_size)
		SZ_BYTE: assert(frx_addr == fc_addr[ADDRESS_WIDTH-1:0]);
		SZ_16B:  assert(frx_addr == { fc_addr[ADDRESS_WIDTH-1:1], 1'b0 });
		SZ_32B:  assert(frx_addr == { fc_addr[ADDRESS_WIDTH-1:2], 2'b0 });
		SZ_BUS:  assert(frx_addr == { fc_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} });
		endcase
	end

	always @(*)
	if (!i_reset && r_busy && !cmd_abort && faxi_rd_ckvalid
					&& faxi_rdid_ckign_outstanding == 0)
	begin
		if (fc_inc || frx_addr != fc_addr)
			assert(frx_addr == faxi_rd_ckaddr);
	end

	always @(*)
	if (!i_reset && r_busy && fc_inc && !cmd_abort
		&& ftot_bursts != ar_requests_remaining + (M_AXI_ARVALID && !phantom_start))
	begin
		assert(ar_requests_remaining + (M_AXI_ARVALID && !phantom_start) <= ftot_bursts);
		if(ftot_bursts == ar_requests_remaining + (M_AXI_ARVALID && !phantom_start))
		begin
			assert(M_AXI_ARADDR == fc_addr);
		end else if (!ar_none_remaining || M_AXI_ARVALID)
		case(fc_size)
		SZ_BYTE: assert(M_AXI_ARADDR[LCLMAXBURST_SUB-1:0] == 0);
		SZ_16B:  assert(M_AXI_ARADDR[LCLMAXBURST_SUB  :0] == 0);
		SZ_32B:  assert(M_AXI_ARADDR[LCLMAXBURST_SUB+1:0] == 0);
		SZ_BUS:  assert(M_AXI_ARADDR[LCLMAXBURST+AXILSB-1:0] == 0);
		endcase
	end

	always @(*)
	if (!i_reset && r_busy && !cmd_abort && fc_inc)
	begin
		if (r_bytes_remaining > 0)
		assert(axi_raddr == fc_addr + (fc_transferlen - r_bytes_remaining));
	end

	always @(*)
	if (!i_reset && r_busy && !cmd_abort && fc_inc)
	begin
		if (phantom_start || !M_AXI_ARVALID)
		begin
			case(fc_size)
			SZ_BYTE: assert(M_AXI_ARADDR == fc_addr + (fc_transferlen - ar_beats_remaining));
			SZ_16B: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:1] == fc_addr[ADDRESS_WIDTH-1:1] + (ftot_beats - ar_beats_remaining));
			SZ_32B: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:2] == fc_addr[ADDRESS_WIDTH-1:2] + (ftot_beats - ar_beats_remaining));
			SZ_BUS: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:AXILSB] == fc_addr[ADDRESS_WIDTH-1:AXILSB] + (ftot_beats - ar_beats_remaining));
			endcase
		end else if (M_AXI_ARVALID && !phantom_start)
		begin
			case(fc_size)
			SZ_BYTE: assert(M_AXI_ARADDR == fc_addr + (fc_transferlen - ar_beats_remaining - (M_AXI_ARLEN+1)));
			SZ_16B: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:1] == fc_addr[ADDRESS_WIDTH-1:1] + (ftot_beats - ar_beats_remaining - (M_AXI_ARLEN+1)));
			SZ_32B: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:2] == fc_addr[ADDRESS_WIDTH-1:2] + (ftot_beats - ar_beats_remaining - (M_AXI_ARLEN+1)));
			SZ_BUS: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:AXILSB] == fc_addr[ADDRESS_WIDTH-1:AXILSB] + (ftot_beats - ar_beats_remaining - (M_AXI_ARLEN+1)));
			endcase
		end

		if (M_AXI_ARADDR != fc_addr)
		case(fc_size)
		SZ_BYTE: begin end
		SZ_16B: assert(M_AXI_ARADDR[0] == 1'b0);
		SZ_32B: assert(M_AXI_ARADDR[1:0] == 2'b00);
		SZ_BUS: assert(M_AXI_ARADDR[AXILSB-1:0] == 0);
		endcase
	end

	always @(*)
	if (!i_reset && r_busy)
	begin
		if (!fc_inc)
		begin
		end else if (!ar_none_remaining)
		begin
			case(fc_size)
			SZ_BYTE: begin
				assert(frx_addr + faxi_rd_outstanding == M_AXI_ARADDR);
				assert(M_AXI_ARADDR == fc_addr
					|| M_AXI_ARADDR[LCLMAXBURST_SUB-1:0] == 0);
				end
			SZ_16B:  begin
				assert(frx_addr[ADDRESS_WIDTH-1:1] + faxi_rd_outstanding == M_AXI_ARADDR[ADDRESS_WIDTH-1:1]);
				assert(M_AXI_ARADDR == fc_addr
					|| M_AXI_ARADDR[LCLMAXBURST_SUB:0] == 0);
				end
			SZ_32B:  begin
				assert(frx_addr[ADDRESS_WIDTH-1:2] + faxi_rd_outstanding == M_AXI_ARADDR[ADDRESS_WIDTH-1:2]);
				assert(M_AXI_ARADDR == fc_addr
					|| M_AXI_ARADDR[LCLMAXBURST_SUB+1:0] == 0);
				end
			SZ_BUS:  begin
				assert(frx_addr[ADDRESS_WIDTH-1:AXILSB] + faxi_rd_outstanding == M_AXI_ARADDR[ADDRESS_WIDTH-1:AXILSB]);
				assert(M_AXI_ARADDR == fc_addr
					|| M_AXI_ARADDR[AXILSB+LCLMAXBURST-1:0] == 0);
				end
			endcase
		end
	end

	// Address and ARLEN coupling
	always @(*)
	begin
		if (!fc_inc)
			f_eob = M_AXI_ARADDR;
		else case(fc_size)
		SZ_BYTE: f_eob = M_AXI_ARADDR + M_AXI_ARLEN + 1;
		SZ_16B: begin
			f_eob = M_AXI_ARADDR + ((M_AXI_ARLEN + 1)<<1);
			f_eob[0] = 1'b0;
			end
		SZ_32B: begin
			f_eob = M_AXI_ARADDR + ((M_AXI_ARLEN + 1)<<2);
			f_eob[1:0] = 2'b0;
			end
		SZ_BUS: begin
			f_eob = M_AXI_ARADDR + ((M_AXI_ARLEN + 1)<<AXILSB);
			f_eob[AXILSB-1:0] = 0;
			end
		endcase
	end

	always @(*)
	if (r_busy && fc_inc && !ar_none_remaining && !phantom_start
			&& ar_requests_remaining > 1)
	begin
		case(fc_size)
		SZ_BYTE: assert(f_eob[LCLMAXBURST_SUB-1:0] == 0);
		SZ_16B: assert(f_eob[LCLMAXBURST_SUB:0] == 0);
		SZ_32B: assert(f_eob[LCLMAXBURST_SUB+1:0] == 0);
		SZ_BUS: assert(f_eob[LCLMAXBURST+AXILSB-1:0] == 0);
		endcase
	end
	// }}}

	// Burst count verification
	// {{{
	always @(*)
	begin
		if (fc_inc)
			flast_addr = fc_addr + fc_transferlen - 1;
		else begin
			flast_addr = fc_addr;
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: flast_addr[0] = 1'b0;
			SZ_32B: flast_addr[1:0] = 1'b0;
			SZ_BUS: flast_addr[AXILSB-1:0] = {(AXILSB){1'b0}};
			endcase
		end

		if (!fc_inc)
		begin
			ftot_bursts = (ftot_beats + MAX_FIXED_BURST - 1)
						>> LGMAX_FIXED_BURST;
		end else case(fc_size)
		SZ_BYTE: begin
			ftot_bursts = flast_addr + (1<<(LCLMAXBURST_SUB))
				- { fc_addr[ADDRESS_WIDTH-1:LCLMAXBURST_SUB],
						{(LCLMAXBURST_SUB){1'b0}} };
			ftot_bursts = ftot_bursts >> (LCLMAXBURST_SUB);
			end
		SZ_16B: begin
			ftot_bursts = flast_addr + (1<<(LCLMAXBURST_SUB+1))
				- { fc_addr[ADDRESS_WIDTH-1:LCLMAXBURST_SUB+1],
						{(LCLMAXBURST_SUB+1){1'b0}} };
			ftot_bursts = ftot_bursts >> (LCLMAXBURST_SUB+1);
			end
		SZ_32B: begin
			ftot_bursts = flast_addr + (1<<(LCLMAXBURST_SUB+2))
				- { fc_addr[ADDRESS_WIDTH-1:LCLMAXBURST_SUB+2],
						{(LCLMAXBURST_SUB+2){1'b0}} };
			ftot_bursts = ftot_bursts >> (LCLMAXBURST_SUB+2);
			end
		SZ_BUS: begin
			ftot_bursts = flast_addr + (1<<(LCLMAXBURST+AXILSB))
				- { fc_addr[ADDRESS_WIDTH-1:LCLMAXBURST+AXILSB],
						{(LCLMAXBURST+AXILSB){1'b0}} };
			ftot_bursts = ftot_bursts >> (LCLMAXBURST+AXILSB);
			end
		endcase
	end

	always @(posedge i_clk)
	if (i_reset || !o_busy)
		frx_bursts <= 0;
	else if (M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST)
		frx_bursts <= frx_bursts + 1;

	// Bursts remaining = total_bursts - bursts received-bursts_outstanding
	always @(*)
	begin
		fburst_count = frx_bursts + faxi_rd_nbursts
				+ ar_requests_remaining;
		if (M_AXI_ARVALID && !phantom_start)
			fburst_count = fburst_count + 1;
	end

	always @(*)
	if (!i_reset && o_busy && !cmd_abort)
		assert(fburst_count == ftot_bursts);

	always @(*)
	if (!i_reset && o_busy && !cmd_abort && fc_inc)
	begin
		case(fc_size)
		SZ_BYTE: assert({ 1'b0, M_AXI_ARADDR } + ar_beats_remaining + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0) == { 1'b0, flast_addr } + 1);
		SZ_16B: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:1] + ar_beats_remaining + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0) == flast_addr[ADDRESS_WIDTH-1:1] + 1);
		SZ_32B: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:2] + ar_beats_remaining + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0) == flast_addr[ADDRESS_WIDTH-1:2] + 1);
		SZ_BUS: assert(M_AXI_ARADDR[ADDRESS_WIDTH-1:AXILSB] + ar_beats_remaining + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0) == flast_addr[ADDRESS_WIDTH-1:AXILSB] + 1);
		endcase
	end

	always @(*)
	begin
		// f_bkfirst: Is this the first beat of the transaction?
		f_bkfirst = r_busy && M_AXI_ARVALID
			&& faxi_rdid_outstanding == 0
			&& r_bytes_remaining == fc_transferlen;


		// f_bkaddr: The check address
		// {{{
		f_bkaddr = fc_addr;
		if (!fc_inc)
		begin
			// Fixed addressing
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: f_bkaddr[ 0] = 1'b0;
			SZ_32B: f_bkaddr[1:0] = 2'b0;
			SZ_BUS: f_bkaddr[AXILSB-1:0] = 0;
			endcase
		end else if (!f_bkfirst)
		begin
			case(fc_size)
			SZ_BYTE: f_bkaddr <= frx_addr
					+ faxi_rdid_outstanding;
			SZ_16B: begin
				f_bkaddr<= { frx_addr[ADDRESS_WIDTH-1:1], 1'b0 }
					+ { faxi_rdid_outstanding, 1'b0 };
				end
			SZ_32B: begin
				f_bkaddr<= { frx_addr[ADDRESS_WIDTH-1:2], 2'b0 }
					+ { faxi_rdid_outstanding, 2'b0 };
				end
			SZ_BUS: begin
				f_bkaddr <= { frx_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} }
					+ { faxi_rdid_outstanding, {(AXILSB){1'b0}} };
				end
			endcase
		end
		// }}}
	end

	always @(*)
	if (!i_reset && r_busy && (M_AXI_ARVALID || !ar_none_remaining))
	begin
		if (ar_requests_remaining == ftot_bursts)
		begin
			if (!fc_inc)
			begin
				case(fc_size)
				SZ_BYTE: assert(M_AXI_ARADDR == fc_addr);
				SZ_16B: assert(M_AXI_ARADDR == { fc_addr[ADDRESS_WIDTH-1:1], 1'b0 });
				SZ_32B: assert(M_AXI_ARADDR == { fc_addr[ADDRESS_WIDTH-1:2], 2'b00 });
				SZ_BUS: assert(M_AXI_ARADDR == { fc_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} });
				endcase
			end else
				assert(M_AXI_ARADDR == fc_addr);
		end else
			assert(M_AXI_ARADDR == f_bkaddr);
	end
	// }}}

	// AR request burst count to beat count verification
	// {{{
	always @(*)
	begin
		far_starting_page = (phantom_start) ? M_AXI_ARADDR : nxt_araddr;
		if (!fc_inc)
		begin
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: far_starting_page[0] = 0;
			SZ_32B: far_starting_page[1:0] = 0;
			SZ_BUS: far_starting_page[AXILSB-1:0] = 0;
			endcase
		end else begin
			/*
			case(fc_size)
			SZ_BYTE: far_starting_page = far_starting_page + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0);
			SZ_16B: far_starting_page[ADDRESS_WIDTH:1] = far_starting_page[ADDRESS_WIDTH:1] + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0);
			SZ_32B: far_starting_page[ADDRESS_WIDTH:2] = far_starting_page[ADDRESS_WIDTH:2] + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0);
			SZ_BUS: far_starting_page[ADDRESS_WIDTH:AXILSB] = far_starting_page[ADDRESS_WIDTH:AXILSB] + ((M_AXI_ARVALID && !phantom_start) ? (M_AXI_ARLEN+1):0);
			endcase
			*/

			case(fc_size)
			SZ_BYTE: far_starting_page[LCLMAXBURST_SUB-1:0] = 0;
			SZ_16B: far_starting_page[LCLMAXBURST_SUB:0] = 0;
			SZ_32B: far_starting_page[LCLMAXBURST_SUB+1:0] = 0;
			SZ_BUS: far_starting_page[AXILSB+LCLMAXBURST-1:0] = 0;
			endcase
		end

		far_ending_page = (phantom_start) ? M_AXI_ARADDR : nxt_araddr;
		if (fc_inc)
		begin
			case(fc_size)
			SZ_BYTE: begin
				far_ending_page = far_ending_page + ar_beats_remaining;
				far_ending_page = far_ending_page + (1<<LCLMAXBURST_SUB)-1;
				end
			SZ_16B: begin
				far_ending_page = (far_ending_page[ADDRESS_WIDTH-1:1] + ar_beats_remaining)<<1;
				far_ending_page = far_ending_page + (2<<LCLMAXBURST_SUB)-1;
				end
			SZ_32B: begin
				far_ending_page = (far_ending_page[ADDRESS_WIDTH-1:2] + ar_beats_remaining)<<2;
				far_ending_page = far_ending_page + (4<<LCLMAXBURST_SUB)-1;
				end
			SZ_BUS: begin
				far_ending_page = (far_ending_page[ADDRESS_WIDTH-1:AXILSB] + ar_beats_remaining)<<AXILSB;
				far_ending_page = far_ending_page + (1<<AXILSB+LCLMAXBURST)-1;
				end
			endcase
		end

		far_pages = far_ending_page - far_starting_page;
		case(fc_size)
		SZ_BYTE: far_pages = far_pages >>  LCLMAXBURST_SUB;
		SZ_16B:  far_pages = far_pages >> (LCLMAXBURST_SUB+1);
		SZ_32B:  far_pages = far_pages >> (LCLMAXBURST_SUB+2);
		SZ_BUS:  far_pages = far_pages >> (LCLMAXBURST + AXILSB);
		endcase

		if (!fc_inc)
			far_pages = (ar_beats_remaining + MAX_FIXED_BURST-1) >> LGMAX_FIXED_BURST;
	end

	always @(*)
	if (r_busy && !cmd_abort)
	begin
		if (ar_none_remaining)
		begin
			assert(ar_beats_remaining == 0);
			assert(ar_requests_remaining == 0);
		end else
			assert(far_pages == ar_requests_remaining); // + ((M_AXI_ARVALID && !phantom_start) ? 1:0));
	end
	// }}}

	// Mid-run transfer length checking

	// Mid-read burst attribute verification
	// {{{
	always @(*)
	begin
		// f_ckfirst: Is this the first beat of the transaction?
		f_ckfirst = r_busy && faxi_rd_ckvalid
			&&((faxi_rd_cklen + frx_beats) == (faxi_rd_ckarlen+1))
			&& faxi_rdid_ckign_outstanding == 0;

		// f_ckaddr: The check address
		// {{{
		f_ckaddr = fc_addr;
		if (!fc_inc)
		begin
			// Fixed addressing
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: f_ckaddr[ 0] = 1'b0;
			SZ_32B: f_ckaddr[1:0] = 2'b0;
			SZ_BUS: f_ckaddr[AXILSB-1:0] = 0;
			endcase
		end else if (!f_ckfirst || faxi_rd_cklen != faxi_rd_ckarlen+1)
		begin
			case(fc_size)
			SZ_BYTE: begin
				f_ckaddr <= frx_addr
					+ faxi_rdid_ckign_outstanding;
					// + faxi_rd_ckarlen + 1 - faxi_rd_cklen;
				end
			SZ_16B: begin
				f_ckaddr<= { frx_addr[ADDRESS_WIDTH-1:1], 1'b0 }
					+ { faxi_rdid_ckign_outstanding, 1'b0 };
				end
			SZ_32B: begin
				f_ckaddr<= { frx_addr[ADDRESS_WIDTH-1:2], 2'b0 }
					+ { faxi_rdid_ckign_outstanding, 2'b0 };
				end
			SZ_BUS: begin
				f_ckaddr[AXILSB-1:0] = {(AXILSB){1'b0}};
				f_ckaddr <= { frx_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} }
					+ { faxi_rdid_ckign_outstanding, {(AXILSB){1'b0}} };
				end
			endcase
		end
		// }}}
	end

	always @(*)
	begin
		// f_cklast = check burst is the last one
		f_cklast = ar_none_remaining && faxi_rd_ckvalid && r_busy
			&& faxi_rdid_nbursts == faxi_rdid_ckign_nbursts + 1
			&& !M_AXI_ARVALID;

		// f_ckeob = last address of the burst inclusive
		// {{{
		f_ckeob = faxi_rd_ckaddr;
		if (fc_inc)
		begin
			case(fc_size)
			SZ_BYTE: f_ckeob = faxi_rd_ckaddr + faxi_rd_cklen-1;
			SZ_16B: f_ckeob = ((faxi_rd_ckaddr[ADDRESS_WIDTH-1:1] + faxi_rd_cklen)<<1) - 1;
			SZ_32B: f_ckeob = ((faxi_rd_ckaddr[ADDRESS_WIDTH-1:2] + faxi_rd_cklen) << 2) - 1;
			SZ_BUS: f_ckeob = ((faxi_rd_ckaddr[ADDRESS_WIDTH-1:AXILSB] + faxi_rd_cklen) << AXILSB) - 1;
			endcase
		end else if (!f_ckfirst && faxi_rd_cklen > 1)
		begin
			case(fc_size)
			SZ_BYTE: begin end
			SZ_16B: f_ckeob[0] = 1'b0;
			SZ_32B: f_ckeob[1:0] = 2'b00;
			SZ_BUS: f_ckeob[AXILSB-1:0] = {(AXILSB){1'b0}};
			endcase
		end
		// }}}
	end

	always @(*)
	if (!i_reset && r_busy && fc_addr == M_AXI_ARADDR && fc_inc
			&& !cmd_abort)
	begin
		assert(ar_requests_remaining
			+ ((M_AXI_ARVALID && !phantom_start) ? 1:0)
				== ftot_bursts);
	end

	always @(*)
	if (!i_reset && r_busy && !fc_inc && !ar_none_remaining)
	begin
		if ((ar_requests_remaining > 1) || (M_AXI_ARVALID && !phantom_start))
		begin
			assert(M_AXI_ARLEN == maxlen);
			assert(M_AXI_ARLEN + 1 == { 1'b0, MAX_FIXED_BURST });
		end else begin
			assert(M_AXI_ARLEN + 1 == ar_beats_remaining);
		end
	end

	always @(*)
	if (!i_reset && r_busy && fc_addr != M_AXI_ARADDR && fc_inc
				&& (!ar_none_remaining || M_AXI_ARVALID))
	begin
		if (ar_requests_remaining > 1 || (!ar_none_remaining && M_AXI_ARVALID && !phantom_start))
		begin
			case(fc_size)
			SZ_BYTE: assert(M_AXI_ARLEN == (1<<LCLMAXBURST_SUB)-1);
			SZ_16B:  assert(M_AXI_ARLEN == (1<<LCLMAXBURST_SUB)-1);
			SZ_32B:  assert(M_AXI_ARLEN == (1<<LCLMAXBURST_SUB)-1);
			SZ_BUS:  assert(M_AXI_ARLEN == (1<<LCLMAXBURST)-1);
			endcase
		end else if (!ar_none_remaining)
		begin
			assert(M_AXI_ARLEN + 1 == ar_beats_remaining);
		end

		case(fc_size)
		SZ_BYTE: assert(M_AXI_ARADDR[LCLMAXBURST_SUB-1:0] == 0);
		SZ_16B:  assert(M_AXI_ARADDR[LCLMAXBURST_SUB  :0] == 0);
		SZ_32B:  assert(M_AXI_ARADDR[LCLMAXBURST_SUB+1:0] == 0);
		SZ_BUS:  assert(M_AXI_ARADDR[LCLMAXBURST+AXILSB-1:0] == 0);
		endcase
	end

	always @(*)
	if (!i_reset && faxi_rd_ckvalid)
	begin
		assert(faxi_rd_checkid == AXI_ID);
		// .f_axi_rd_cklen(faxi_rd_cklen),
		// .f_axi_rd_ckaddr(faxi_rd_ckaddr),
		if (!f_ckfirst)
		begin
			if (fc_inc)
			begin
				if (faxi_rd_cklen == faxi_rd_ckarlen+1)
				begin
				case(fc_size)
				SZ_BYTE: assert(faxi_rd_ckaddr[LCLMAXBURST_SUB-1:0]==0);
				SZ_16B: assert(faxi_rd_ckaddr[LCLMAXBURST_SUB:0]==0);
				SZ_32B: assert(faxi_rd_ckaddr[LCLMAXBURST_SUB+1:0]==0);
				SZ_BUS: assert(faxi_rd_ckaddr[LCLMAXBURST+AXILSB-1:0]==0);
				endcase
				end
			end else begin
				// Fixed address
				case(fc_size)
				SZ_BYTE: assert(faxi_rd_ckaddr == fc_addr);
				SZ_16B: assert(faxi_rd_ckaddr == { fc_addr[ADDRESS_WIDTH-1:1], 1'b0 });
				SZ_32B: assert(faxi_rd_ckaddr == { fc_addr[ADDRESS_WIDTH-1:2], 2'b0 });
				SZ_BUS: assert(faxi_rd_ckaddr == { fc_addr[ADDRESS_WIDTH-1:AXILSB], {(AXILSB){1'b0}} });
				endcase
			end
		end else begin
			// assert(frx_beats == 0);
			assert(faxi_rdid_ckign_outstanding == 0);
		end

		if (!f_cklast && fc_inc)
		begin
			case(fc_size)
			SZ_BYTE: assert(&f_ckeob[LCLMAXBURST_SUB-1:0]);
			SZ_16B:  assert(&f_ckeob[LCLMAXBURST_SUB  :1]);
			SZ_32B:  assert(&f_ckeob[LCLMAXBURST_SUB+1:2]);
			SZ_BUS:  assert(&f_ckeob[LCLMAXBURST+AXILSB-1:AXILSB]);
			endcase
		end

		if (!f_cklast && (!fc_inc || !f_ckfirst))
		begin
			if (!fc_inc)
			begin
				assert(faxi_rd_ckarlen == MAX_FIXED_BURST-1);
			end else if (fc_size == SZ_BUS)
			begin
				assert(faxi_rd_ckarlen == (1<<LCLMAXBURST)-1);
			end else begin
				assert(faxi_rd_ckarlen == (1<<LCLMAXBURST_SUB)-1);
			end
		end

		assert(faxi_rd_ckaddr == f_ckaddr);
		// if (first_burst && first_beat)
		//	assert(faxi_rd_ckaddr == 
		// .f_axi_rd_ckincr(faxi_rd_ckincr),

		// Increment v fixed
		assert(faxi_rd_ckburst == { 1'b0, fc_inc });

		// Size
		assert(faxi_rd_cksize == axi_size);
		case(fc_size)
		SZ_BYTE: assert(axi_size == 3'h0);
		SZ_16B:  assert(axi_size == 3'h1);
		SZ_32B:  assert(axi_size == 3'h2);
		SZ_BUS:  assert(axi_size == AXILSB);
		endcase

		// .f_axi_rd_ckarlen(faxi_rd_ckarlen),

		assert(!faxi_rd_cklockd);
	end

	always @(*)
	if (!i_reset && (!faxi_rd_ckvalid || faxi_rdid_ckign_outstanding > 0)
		&& M_AXI_RVALID)
	begin
		if (fc_inc) case(fc_size)
		SZ_BYTE: assume(M_AXI_RLAST == (&axi_raddr[LCLMAXBURST_SUB-1:0]));
		SZ_16B: assume(M_AXI_RLAST == (&axi_raddr[LCLMAXBURST_SUB:1]));
		SZ_32B: assume(M_AXI_RLAST == (&axi_raddr[LCLMAXBURST_SUB+1:2]));
		SZ_BUS: assume(M_AXI_RLAST == (&axi_raddr[LCLMAXBURST+AXILSB-1:0]));
		endcase
	end
	// }}}
		//

	// Gearbox checks
	// {{{
	always @(*)
	if (!i_reset && !r_busy)
	begin
		assert(fgbox_rcvd == 0);
		assert(fgbox_sent == 0);
	end

	always @(*)
	if (r_busy && !cmd_abort && (!ar_none_remaining || !ar_none_outstanding || rx_valid))
	begin
		if (frx_beats == 0)
		begin
			assert(!rx_valid);
			assert(fgbox_rcvd == 0);
		end else if (r_bytes_remaining == 0)
		begin
			assert(frx_beats == ftot_beats);
			assert(fgbox_rcvd + (rx_valid ? rx_bytes : 0)
					== fc_transferlen);
		end else case(fc_size)
		SZ_BYTE: assert(fgbox_rcvd + (rx_valid ? 1:0) == frx_beats);
		SZ_16B: assert(fgbox_rcvd + (rx_valid ? rx_bytes : 0)
			== { frx_beats, 1'b0 } - fc_addr[0]);
		SZ_32B: assert(fgbox_rcvd + (rx_valid ? rx_bytes : 0)
			== { frx_beats, 2'b0 } - fc_addr[1:0]);
		SZ_BUS: assert(fgbox_rcvd + (rx_valid ? rx_bytes : 0)
				== { frx_beats, {(AXILSB){1'b0}} }
					- fc_addr[AXILSB-1:0]);
		endcase
	end

	// While flushing the system ...
	always @(*)
	if (r_busy && ar_none_remaining && ar_none_outstanding && !rx_valid && !cmd_abort)
		assert(fgbox_rcvd == 0);
	// }}}

	// Check the rd_uncommitted (units: bytes) counter
	// {{{
	always @(*)
	begin
		f_committed = faxi_rd_outstanding + frx_beats;
		if (M_AXI_ARVALID && !phantom_start)
			f_committed = f_committed + M_AXI_ARLEN + 1;

		case(fc_size)
		SZ_BYTE: begin end
		SZ_16B: f_committed = f_committed << 1;
		SZ_32B: f_committed = f_committed << 2;
		SZ_BUS: f_committed = f_committed << AXILSB;
		endcase

		f_committed = f_committed - (faxis_beats << AXILSB);

		if (cmd_abort)
			f_committed = 0;
	end

	always @(*)
	if (!i_reset && r_busy)
	begin
		assert(f_committed <= FIFO_BYTES);
		assert(rd_uncommitted <= FIFO_BYTES);

		assert(ign_fifo_fill <= f_committed[LGLENGTH:AXILSB]
				+ (|f_committed[AXILSB-1:0]));
		if (!cmd_abort)
		begin
			assert(f_committed + rd_uncommitted == FIFO_BYTES);
			if (frx_beats == ftot_beats && !rx_valid && !gbox_valid)
			begin
				assert(f_committed[LGLENGTH:AXILSB]
					+(|f_committed[AXILSB-1:0])
							>= ign_fifo_fill);
				// assert(ign_fifo_fill
				//	== f_committed[LGLENGTH:AXILSB]
				//		+ (|f_committed[AXILSB-1:0]));
			end
		end
	end

	always @(*)
	if (!i_reset && !r_busy)
		assert(fifo_empty);

	always @(*)
	if (!i_reset && r_busy && fifo_full)
	begin
		assert(!M_AXI_ARVALID);
		assert(faxi_rd_outstanding == 0);
		assert(!rx_valid);
		assert(!gbox_valid);
	end
	// }}}


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FIFO checking
	// {{{

	always @(*)
	begin
		ffif_assume_result = 1;
		if (ffif_first_in_fifo && ffif_distance_to_first == 0)
			ffif_assume_result = 0;
		if (ffif_second_in_fifo && ffif_distance_to_second == 0)
			ffif_assume_result = 0;
		if (fifo_empty)
			ffif_assume_result = 0;
	end

	always @(*)
	if(!ar_none_outstanding || !ar_none_remaining || rx_valid || gbox_valid)
	begin
		if (ffif_first_in_fifo)
		begin
			assert(!ffif_first_last);
			assert(ffif_first_bytes == (1<<AXILSB));
		end

		if (ffif_second_in_fifo)
		begin
			assert(!ffif_second_last);
			assert(ffif_second_bytes == (1<<AXILSB));
		end

		if (ffif_assume_result)
		begin
			assume(!M_AXIS_LAST);
			assume(M_AXIS_BYTES == (1<<AXILSB));
		end
	end else if (!cmd_abort)
	begin
		assert(fgbox_rcvd == 0);
		assert(fgbox_sent == 0);
		// Last should be in the FIFO
		if (ffif_first_in_fifo)
			assume(ffif_first_last == (ffif_distance_to_first + 1 == ign_fifo_fill));
		if (ffif_second_in_fifo)
			assume(ffif_second_last == (ffif_distance_to_second + 1 == ign_fifo_fill));
		if (ffif_assume_result)
			assume(M_AXIS_LAST == (ign_fifo_fill == 1));
	end

	always @(*)
	begin
		if (ffif_first_in_fifo)
		begin
			assert(ffif_first_bytes > 0);
			assert(ffif_first_bytes <= (1<<AXILSB));
			if(!ffif_first_last)
				assert(ffif_first_bytes == (1<<AXILSB));
		end

		if (ffif_second_in_fifo)
		begin
			assert(ffif_second_bytes > 0);
			assert(ffif_second_bytes <= (1<<AXILSB));
			if(!ffif_second_last)
				assert(ffif_second_bytes == (1<<AXILSB));
		end

		if (ffif_assume_result)
		begin
			assume(M_AXIS_BYTES > 0);
			assume(M_AXIS_BYTES <= (1<<AXILSB));
			if (!M_AXIS_LAST)
				assume(M_AXIS_BYTES == (1<<AXILSB));
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) && !$past(i_soft_reset)
				&& !$past(cmd_abort))
	begin
		cover(o_busy);
		cover(M_AXI_ARVALID);		// !!!
		cover(M_AXI_RVALID);		// !!!
		cover($fell(o_busy));		// !!!
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// always @(*) assume(fc_size == 2'b00);
	always @(*)
		assume({ 1'b0, fc_addr } + { 1'b0, fc_transferlen } < (1<<ADDRESS_WIDTH));

	// always @(*) assume(!fifo_full);
	always @(*)
		assume(!cmd_abort);
	// always @(*) assume(M_AXI_ARREADY);
	// always @(*) assume(fc_inc);
	// always @(*) if (!fc_inc) assume(!fifo_full);
	// }}}
`endif
// }}}
endmodule
