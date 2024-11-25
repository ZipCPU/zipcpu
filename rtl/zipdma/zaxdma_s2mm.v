////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zaxdma_s2mm.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Writes data from a stream to the bus, in this case to
//		an AXI bus.  Data arrives packed, goes through a gearbox and
//	gets unpacked to either 1, 2, 4, or (bus width) bytes at a time.  Data
//	is also then realigned to handle writing to unaligned addresses.  The
//	result is then written to the bus.
//
//	This particular S2MM component is designed for external RTL, not CPU
//	configuration.  This should allow it to be used as a component of
//	this (and other) designs.  If you would rather a CPU configured S2MM
//	module, see the module in wb2axip/rtl/axis2mm.v.
//
//	Key configuration inputs:
//	i_clk, i_reset	-- Self explanatory.  The reset is active HIGH.
//	i_request	-- True on any transactionm request.
//	i_soft_reset	-- True on any abort request.  A soft reset will
//			cause the IP (if active) to 1) immediately cease
//			producing M_AWVALID signals (once M_AWREADY), 2) to
//			clear M_WSTRB (once !M_VALID || M_READY) and then to
//			wait for all data to be received before ceasing to be
//			"busy".
//	o_busy		-- True if the IP is in operation
//	o_err		-- True for one cycle following any error.
//	i_inc		-- True if the request is for one where the destination
//			address increments from one beat to the next.
//	i_size		-- One of SZ_BYTE (2'b11) for transferring one byte at
//			a time, SZ_16B (2'b10) for transmitting two bytes at a
//			time, SZ_32B (2'b01) for transmitting four bytes at a
//			time, or SZ_BUS (2'b00) for transfers up the the full
//			width of the bus.
//	i_addr		-- Specifies the first address of the transaction.  If
//			using a fixed address (i_inc=0), then this address will
//			be automatically aligned to the first 16b, 32b, or bus
//			word for the first write.
//	S_* -- AXI stream data input.  If LAST is not set, then all words are
//		full, containing DW/8 bytes, and BYTES will be set to DW/8.
//		If S_LAST is set, S_BYTES will contain the number of valid
//		bytes.  All words are packed to the LSB, so S_DATA[7:0] is
//		always the "first" byte in any stream.
//	M_* -- AXI (full) memory mapped master bus control signals
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
module	zaxdma_s2mm #(
		// {{{
		parameter		ADDRESS_WIDTH=30, // Byte addresses
		parameter		BUS_WIDTH = 64,
		// AXI is always little endian
		// parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b1,
		parameter [0:0]		OPT_LOWPOWER = 1'b1,
		// LGMAXBURST is the log_2() of the maximum number of beats in
		// a burst.  Ideally, this value should be 8 to specify a use
		// of 256 beats per burst.  Smaller values may use fewer
		// resources, and may also hog the bus less.
		parameter		LGMAXBURST = 8,
		// The FIFO should ideally be at least twice the size of the
		// maximum burst for best (i.e. ping-pong) performance.  Smaller
		// sizes may force the stream to stall.  Larger sizes may not
		// be required.
		parameter		LGFIFO = LGMAXBURST+1,
		// IW is the AXI ID width.
		parameter		IW = 2,
		// We only ever use a single ID here.  That ID can be specified
		// here as AXI_ID.  AWID will be set to this value, but in all
		// other cases it will be totally ignored.
		parameter [IW-1:0]	AXI_ID=0,
		// DEF_AWCACHE controls AWCACHE.  This is a constant value.
		parameter [3:0]		DEF_AWCACHE = 4'b0011,
		// DEF_AWPROT controls AWPROT.  This is a constant value.
		parameter [2:0]		DEF_AWPROT = 3'h0,
		// DEF_AWQOS controls AWQOS.  This is a constant value.  Setting
		// this to zero sets it to both the lowest Quality-of-Service
		// value, as well as the value appropriate for a design not
		// participating in QOS arbitration.
		parameter [3:0]		DEF_AWQOS = 4'h0,
		// Abbreviations
		localparam	DW = BUS_WIDTH,
		localparam	AW = ADDRESS_WIDTH
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Configuration
		// {{{
		input	wire			i_request,
		input	wire			i_soft_reset,
		output	wire			o_busy, o_err,
		input	wire			i_inc,
		input	wire	[1:0]		i_size,
		// input wire	[LGLENGTH:0]	i_transferlen,
		input wire [AW-1:0]	i_addr,	// Byte address
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
		// AXI Write interface
		// {{{
		output	wire			M_AWVALID,
		input	wire			M_AWREADY,
		output	wire	[IW-1:0]	M_AWID,
		output wire [AW-1:0]	M_AWADDR,
		output	wire	[7:0]		M_AWLEN,
		output	wire	[2:0]		M_AWSIZE,
		output	wire	[1:0]		M_AWBURST,
		// We'll never lock the bus, so AWLOCK=0
		output	wire			M_AWLOCK,
		output	wire	[3:0]		M_AWCACHE,
		output	wire	[2:0]		M_AWPROT,
		output	wire	[3:0]		M_AWQOS,
		//
		output	wire			M_WVALID,
		input	wire			M_WREADY,
		output	wire	[DW-1:0]	M_WDATA,
		output	wire	[DW/8-1:0]	M_WSTRB,
		output	wire			M_WLAST,
		//
		input	wire			M_BVALID,
		output	wire			M_BREADY,
		// BID will always equal AXI_ID, so ... it can (and will) be
		// ignored internally.
		input	wire	[IW-1:0]	M_BID,
		// BRESP[1] is only relevant for exclusive access transactions,
		// and this DMA has no reason to use them.
		input	wire	[1:0]		M_BRESP
		// }}}
		// }}}
	);

	// Local decalarations
	// {{{
	localparam	[1:0]		SZ_BYTE = 2'b11,
					SZ_16B  = 2'b10,
					SZ_32B  = 2'b01,
					SZ_BUS  = 2'b00;
	localparam			AXILSB = $clog2(BUS_WIDTH/8);
	// Burst sizes
	//
	// The largest possible burst is 4096kB
	//	We convert that to beats by (* 8b/byte) / BUS_WIDTH (bits/beat)
	//	No burst can have more than this many beats.  $clog2() provides
	//	the log_2 of this number
	localparam	LGMAXBURST_LIMIT = $clog2(4096*8/BUS_WIDTH),
			LCLMAXBURST=(LGMAXBURST > LGMAXBURST_LIMIT)
				? LGMAXBURST_LIMIT : LGMAXBURST;
	//
	// A fixed burst can only ever be 16 beats in length, never more.
	// A 16beat burst will never break a 4kB limit.  Therefore, we only
	// need to limit this by the LGMAXBURST user requirement.
	localparam	LGMAX_FIXED_BURST= (LGMAXBURST < 4) ? LGMAXBURST : 4,
			MAX_FIXED_BURST = (1<<LGMAX_FIXED_BURST);
	//
	// For sizes smaller than SZ_BUS, the maximum burst size has nothing
	// to do with the 4kB limit.  Hence, we can use the full user requested
	// burst size if necessary.
	localparam	LCLMAXBURST_SUB = (LGMAXBURST > 8) ? 8: LGMAXBURST;

	localparam	FULL_BEAT_BYTES = (BUS_WIDTH/8),
			FULL_FIFO_BYTES = (1<<LGFIFO) * FULL_BEAT_BYTES,
			LGMAX_FIFO_BYTES= $clog2(FULL_FIFO_BYTES+1);

	//
	// Configuration
	reg				r_inc;
	reg	[1:0]			r_size;
	reg	[2:0]			axi_size;
	reg				cmd_abort, r_busy, r_err,
					r_overflow;
	wire				w_complete, w_overflow;
	//
	// FIFO stage
	reg				last_rcvd;
	reg	[AXILSB:0]		beat_bytes;
	reg	[LGMAX_FIFO_BYTES-1:0]	bytes_not_written;

	wire				fif_full, fif_read, fif_last,
					fif_empty;
	wire	[LGFIFO:0]		ign_fif_fill;
	wire	[$clog2(BUS_WIDTH/8):0]	fif_bytes;
	wire	[BUS_WIDTH-1:0]		fif_data;

	// Gearbox stage
	wire				gears_valid, gears_ready, gears_last;
	wire	[$clog2(BUS_WIDTH/8):0]	gears_bytes;
	wire	[BUS_WIDTH-1:0]		gears_data;

	// Realignment stage
	reg			sr_valid;
	wire			sr_ready;
	reg	[AXILSB-1:0]	sr_offset;
	reg	[2*DW-9:0]	pre_shift, sr_data;
	// reg	[AXILSB:0]	sr_step; // sr_bytes;
	reg	[1:0]		sr_last;

	reg	[AXILSB+8:0]		burst_bytes;
	reg	[LGMAX_FIFO_BYTES:0]	awbytes_uncommitted;
	reg	[1:0]			aw_bursts_available;
	reg	[LGMAX_FIFO_BYTES:0]	beats_committed;

	// AW*
	reg				w_start_aw, phantom_aw, axi_awvalid;
	// Verilator lint_off UNUSED
	reg	[AW:0]			nxt_awaddr;
	// Verilator lint_on  UNUSED
	reg	[AW-1:0]		axi_awaddr;
	reg	[AW-1:0]		bursts_outstanding;

	// W*
	reg	w_start_w, phantom_w, axi_wvalid, axi_wlast;
	reg	[AW:0]	nxt_waddr;
	reg	[AW-1:0]	axi_waddr;
	reg	[BUS_WIDTH-1:0]		axi_wdata, nxt_wdata;
	reg	[BUS_WIDTH/8-1:0]	axi_wstrb, base_wstrb, nxt_wstrb;
	reg	[AXILSB-1:0]		last_count;
	reg	[1:0]			wpipe;
	reg	[BUS_WIDTH/8-1:0]	w_last_mask, last_mask;
	reg				data_sent;

	reg	[7:0]	r_max_burst;
	reg	[7:0]	axi_awlen;
	reg	[LGMAX_FIXED_BURST-1:0]	wfix_burst_count;

	reg		r_initial_burst;
	reg	[7:0]	r_max_initial;
	wire	[7:0]	w_max_burst;


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Configuration
	// {{{

	// Copy config: r_inc, r_size, axi_size
	// {{{
	initial	r_inc  = 1'b0;
	initial	r_size = 2'b00;
	initial	axi_size = 3'h0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
	begin
		r_inc  <= 1'b0;
		r_size <= 2'b00;
		axi_size <= 3'h0;
	end else if (!o_busy && (!OPT_LOWPOWER || i_request))
	begin
		r_inc  <= i_inc;
		r_size <= i_size;

		case(i_size)
		SZ_BYTE: axi_size <= 3'h0;
		SZ_16B:  axi_size <= 3'h1;
		SZ_32B:  axi_size <= 3'h2;
		SZ_BUS:  axi_size <= AXILSB[2:0];
		endcase
	end
	// }}}

	assign	w_overflow = r_overflow && aw_bursts_available[0]
				&& bursts_outstanding == 0 && !phantom_aw;

	// cmd_abort
	// {{{
	initial	cmd_abort = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		cmd_abort <= 1'b0;
	else begin
		if (i_soft_reset)
			cmd_abort <= 1'b1;
		if (M_BVALID && M_BREADY && M_BRESP[1])
			cmd_abort <= 1'b1;
		if (w_overflow)
			cmd_abort <= 1'b1;
	end
	// }}}

	// r_err
	// {{{
	initial	r_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		r_err <= 1'b0;
	else begin
		if (M_BVALID && M_BREADY && M_BRESP[1])
			r_err <= 1'b1;
		if (w_overflow)
			r_err <= 1'b1;
	end

	assign	o_err = r_err;
`ifdef	FORMAL
	always @(*)
	if (o_err)
		assert(cmd_abort);
`endif
	// }}}

	// r_busy
	// {{{
	initial	r_busy = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_busy <= 1'b0;
	else if (r_busy && w_complete)
		r_busy <= 1'b0;
	else if (!r_busy && i_request)
		r_busy <= 1'b1;

	assign	o_busy = r_busy;

	assign	w_complete = data_sent && !M_AWVALID && !M_WVALID
		&& (bursts_outstanding <= ((M_BVALID && M_BREADY) ? 1:0));
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming FIFO
	// {{{

	// last_rcvd
	// {{{
	// Set to true once we've received the *LAST* value in the stream, and
	// held so until we are no longer busy.  While true, no further items
	// will be allowed into the stream.
	initial	last_rcvd = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		last_rcvd <= 1'b0;
	else if (S_VALID && S_READY && S_LAST)
		last_rcvd <= 1'b1;
	// }}}

	// beat_bytes, bytes_not_written
	// {{{
	always @(*)
		beat_bytes = $countones(M_WSTRB);

	always @(posedge i_clk)
	if (i_reset || i_soft_reset || !r_busy)
		bytes_not_written <= 0; // FULL_FIFO_BYTES;
	else case({ S_VALID && S_READY, M_WVALID && M_WREADY })
	2'b00: begin end
	// Verilator lint_off WIDTH
	2'b10: bytes_not_written <= bytes_not_written + S_BYTES;
	2'b01: bytes_not_written <= bytes_not_written - beat_bytes;
	2'b11: bytes_not_written <= bytes_not_written + S_BYTES - beat_bytes;
	// Verilator lint_on  WIDTH
	endcase
	// }}}

	localparam	FIFO_WIDTH = 2 + $clog2(BUS_WIDTH/8) + BUS_WIDTH;
`ifdef	FORMAL
	wire	[LGFIFO:0]	ffif_first_addr, ffif_second_addr;
	wire [FIFO_WIDTH-1:0]	ffif_first_data, ffif_second_data;
	wire			ffif_first_in_fifo, ffif_second_in_fifo;
	wire	[LGFIFO:0]	ffif_distance_to_first, ffif_distance_to_second;
`endif

	sfifo #(
		// {{{
		.BW(FIFO_WIDTH),
		.LGFLEN(LGFIFO),
		.OPT_ASYNC_READ(1'b0),
		.OPT_WRITE_ON_FULL(1'b0), .OPT_READ_ON_EMPTY(1'b0)
		// }}}
	) u_fifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_abort || !o_busy),
		.i_wr(S_VALID && S_READY),
		.i_data({ S_LAST, S_BYTES, S_DATA }),
		.o_full(fif_full), .o_fill(ign_fif_fill),
		.i_rd(fif_read),
		.o_data({ fif_last, fif_bytes, fif_data }),
		.o_empty(fif_empty)
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

	assign	S_READY = !fif_full && r_busy && !last_rcvd;

	// Need to assume S_BYTES == (DW/8) unless S_LAST

	// Need to wait on issuing AWVALID until there's enough data available
	// to finish the burst

	// Incoming data:
	//	S_VALID, S_READY, S_DATA, S_BYTES=0, S_LAST

	// Transformed data:
	//	fif_valid, fif_ready, fif_data, fif_last
	//	case(r_size)
	//	SZ_BYTE: fif_bytes = 1
	//	SZ_16B:  fif_bytes = 2
	//	SZ_32B:  fif_bytes = 4
	//	SZ_BUS:  fif_bytes = 0
	//	endcase // unless fif_last

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Resizing gearbox (txgears)
	// {{{
`ifdef	FORMAL
	localparam	F_LGCOUNT = 16;

	wire	[F_LGCOUNT-1:0]	f_gears_rcvd, f_gears_sent;
`endif

	zipdma_txgears #(
`ifdef	FORMAL
		.F_LGCOUNT(F_LGCOUNT),
`endif
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_LITTLE_ENDIAN(1'b1)	// AXI is always little endian
	) u_txgears (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_soft_reset(i_soft_reset || cmd_abort || !r_busy),
		.i_size(r_size),
		.S_VALID(!fif_empty && !cmd_abort), .S_READY( fif_read),
			.S_DATA( fif_data), .S_BYTES( fif_bytes),
			.S_LAST( fif_last),
		.M_VALID(gears_valid), .M_READY(gears_ready),
			.M_DATA( gears_data), .M_BYTES(gears_bytes),
			.M_LAST( gears_last)
`ifdef	FORMAL
		, .f_rcvd(f_gears_rcvd), .f_sent(f_gears_sent)
`endif
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Realignment stage
	// {{{

	// sr_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		sr_valid <= 0;
	else if (!sr_valid || sr_ready)
		sr_valid <= gears_valid || sr_last[1];
	// }}}

	initial	sr_offset = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || (!o_busy && !i_request)))
		sr_offset <= 0;
	else if (!o_busy)
	begin
		sr_offset <= 0;
		case(i_size)
		SZ_BYTE: sr_offset <= 0;
		SZ_16B:  sr_offset[0] <= i_addr[0];
		SZ_32B:  sr_offset[1:0] <= i_addr[1:0];
		SZ_BUS:  sr_offset <= i_addr[AXILSB-1:0];
		endcase
	end

	always @(*)
	case(r_size)
	SZ_BYTE: pre_shift = { {(2*DW-16){1'b0}}, gears_data[7:0] };
	SZ_16B:  begin
		// Verilator lint_off WIDTH
		if (sr_offset[0])
			pre_shift = { {(2*DW-4*8){1'b0}},
				gears_data[15:0], sr_data[23:16] };
		else
			pre_shift = { {(2*DW-3*8){1'b0}}, gears_data[15:0] };
		end
	SZ_32B:  begin
		pre_shift = { {(2*DW-4*8){1'b0}}, sr_data[55:32] };
		pre_shift = pre_shift | (gears_data[31:0] << (sr_offset*8));
		end
	SZ_BUS:  begin
		pre_shift = { {(DW){1'b0}}, sr_data[2*DW-9:DW] };
		pre_shift = pre_shift | (gears_data[DW-1:0] << (sr_offset*8));
		end
		// Verilator lint_on  WIDTH
	endcase

	initial	sr_data = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		sr_data <= 0;
	else if (!o_busy)
		sr_data <= 0;
	else if ((gears_valid && gears_ready)
			|| (sr_valid && sr_ready && |sr_last))
		sr_data <= pre_shift;

	initial	sr_last = 0;
	always @(posedge i_clk)
	if (!o_busy)
		sr_last <= 0;
	else if (gears_valid && gears_ready)
	begin
		sr_last <= 2'b00;
		if (gears_last)
		begin
			// sr_last[1] equals
			//	1. We've seen gears_last, *AND*
			//	2. Some data is going to spill into the next
			//		clock cycle
			// sr_last[0] is always set on the last sr_valid
			//	It should not be set earlier, as it will be used
			//	to directly set WLAST on the last beat of the
			//	entire transfer.
			sr_last <= 2'b01;
			case(r_size)
			// Verilator lint_off WIDTH
			SZ_BYTE: begin end // sr_last[0] <= 1'b1;
			SZ_16B:  if (gears_bytes + sr_offset[0] > 2)
					sr_last <= 2'b10;
			SZ_32B:  if (gears_bytes+sr_offset[1:0] > 4)
					sr_last <= 2'b10;
			SZ_BUS:  if (gears_bytes + sr_offset[AXILSB-1:0] > DW/8)
					sr_last <= 2'b10;
			// Verilator lint_on  WIDTH
			endcase
		end
	end else if (sr_ready && |sr_last)
		sr_last <= 2'b01;

	// Output
	//	sr_valid, sr_ready, sr_data, sr_last
	//
	//	case(r_size)
	//	SZ_BYTE:
	//		first sr_bytes = 1;
	//		subsequent sr_bytes = 1;
	//	SZ_16B:
	//		first sr_bytes = 2 - r_inc && i_addr[0];
	//		subsequent sr_bytes = 2;
	//	SZ_32B:
	//		first sr_bytes = 4 - (r_inc ? i_addr[1:0] : 2'b00);
	//		subsequent sr_bytes = 4;
	//	SZ_BUS:
	//		first sr_bytes = (DW/8) - (1<<waddr[AXILSB-1:0]);
	//		subsequent sr_bytes = DW/8;
	//	endcase
	//

	assign	gears_ready = !sr_valid || sr_ready;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus driving stage
	// {{{

	// burst_bytes
	// {{{
	always @(*)
	begin
		// Verilator lint_off WIDTH
		case(r_size)
		SZ_BYTE: burst_bytes =  M_AWLEN + 1;
		SZ_16B:  burst_bytes = ((M_AWLEN + 1)<<1);// - M_AWADDR[  0];
		SZ_32B:  burst_bytes = ((M_AWLEN + 1)<<2);// - M_AWADDR[1:0];
		SZ_BUS:  burst_bytes = ((M_AWLEN + 1) << AXILSB);
						// - M_AWADDR[AXILSB-1:0];
		endcase

		if (burst_bytes > awbytes_uncommitted)
			burst_bytes = awbytes_uncommitted;
		// Verilator lint_on  WIDTH

		if (!M_AWVALID)
			burst_bytes = 0;
	end
	// }}}

	// awbytes_uncommitted
	// {{{
	// This is the number of bytes received, for which no AW* transaction
	// has committed them to the bus.  It is decremented on the cycle where
	// phantom_aw is high, and so may seem a cycle late.
	initial	awbytes_uncommitted = 0;
	always @(posedge i_clk)
	if (i_reset && OPT_LOWPOWER)
		awbytes_uncommitted <= 0;
	else if (!r_busy)
	begin
		awbytes_uncommitted <= 0;
		if (!OPT_LOWPOWER || i_request)
		begin
			case(i_size)
			SZ_BYTE: begin end // awbytes_uncommitted <= 0;
			SZ_16B:  awbytes_uncommitted[0] <= i_addr[0];
			SZ_32B:  awbytes_uncommitted[1:0] <= i_addr[1:0];
			SZ_BUS:  awbytes_uncommitted[AXILSB-1:0] <= i_addr[AXILSB-1:0];
			endcase
		end
	end else case({ S_VALID && S_READY, phantom_aw })
	2'b00: begin end
	// Verilator lint_off WIDTH
	2'b01: awbytes_uncommitted<=awbytes_uncommitted - burst_bytes;
	2'b10: awbytes_uncommitted<=awbytes_uncommitted + S_BYTES;
	2'b11: awbytes_uncommitted<=awbytes_uncommitted + S_BYTES - burst_bytes;
	// Verilator lint_on  WIDTH
	endcase
	// }}}

	// aw_bursts_available
	// {{{
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		aw_bursts_available <= 2'b00;
	else begin
		case(r_size)
		SZ_BYTE: aw_bursts_available <= {
			awbytes_uncommitted >= (2<<LCLMAXBURST_SUB),
			(last_rcvd && awbytes_uncommitted > 0)
			 	||(awbytes_uncommitted>= (1<<LCLMAXBURST_SUB))};
		SZ_16B: aw_bursts_available <= {
			awbytes_uncommitted >= (4<<LCLMAXBURST_SUB),
			(last_rcvd && awbytes_uncommitted > 0)
				||(awbytes_uncommitted>= (2<<LCLMAXBURST_SUB))};
		SZ_32B: aw_bursts_available <= {
			awbytes_uncommitted >= (8<<LCLMAXBURST_SUB),
			(last_rcvd && awbytes_uncommitted > 0)
				||(awbytes_uncommitted>= (4<<LCLMAXBURST_SUB))};
		SZ_BUS: aw_bursts_available <= {
			awbytes_uncommitted >= (2<<(AXILSB+LCLMAXBURST)),
			(last_rcvd && awbytes_uncommitted > 0)
				||(awbytes_uncommitted
						>= (1<<(AXILSB+LCLMAXBURST)))};
		endcase

		if (phantom_aw)
			aw_bursts_available[0] <= 1'b0;
	end
	// }}}

	// w_start_aw
	// {{{
	always @(*)
	begin
		w_start_aw = |aw_bursts_available;
		if (phantom_aw && !aw_bursts_available[1])
			w_start_aw = 1'b0;
		if (!r_busy || !sr_valid || cmd_abort || i_soft_reset)
			w_start_aw = 0;
		if (r_overflow || (nxt_awaddr[AW] && r_inc))
			w_start_aw = 0;
`ifdef	FORMAL
		if (M_WVALID && (!M_WREADY || !M_WLAST))
			w_start_aw = 0;
`endif
	end
	// }}}

	// phantom_aw
	// {{{
	initial	phantom_aw = 0;
	always @(posedge i_clk)
	if (i_reset)
		phantom_aw <= 0;
	else
		phantom_aw <= w_start_aw && (!M_AWVALID || M_AWREADY);
	// }}}

	// r_overflow
	// {{{
	initial	r_overflow = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		r_overflow <= 1'b0;
	else if (phantom_aw && nxt_awaddr[AW] && r_inc)
		// This is really a *would* overflow signal.  We haven't
		// overflowed yet, but we will if we start any more bursts.
		r_overflow <= 1'b1;
	// }}}

	// axi_awvalid
	// {{{
	initial	axi_awvalid = 0;
	always @(posedge i_clk)
	if (i_reset)
		axi_awvalid <= 0;
	else if (!M_AWVALID || M_AWREADY)
		axi_awvalid <= w_start_aw;
	// }}}

	// axi_awaddr
	// {{{
	always @(*)
	case(r_size)
	// Verilator lint_off WIDTH
	SZ_BYTE: begin
		nxt_awaddr = axi_awaddr +  (1<<LCLMAXBURST_SUB);
		nxt_awaddr[LCLMAXBURST_SUB-1:0] = 0;
		end
	SZ_16B:  begin
		nxt_awaddr = axi_awaddr + (2<<LCLMAXBURST_SUB);
		nxt_awaddr[LCLMAXBURST_SUB:0] = 0;
		end
	SZ_32B:  begin
		nxt_awaddr = axi_awaddr + (4<<LCLMAXBURST_SUB);
		nxt_awaddr[LCLMAXBURST_SUB+1:0] = 0;
		end
	SZ_BUS:  begin
		nxt_awaddr = axi_awaddr + (1<<(LCLMAXBURST+AXILSB));
		nxt_awaddr[LCLMAXBURST+AXILSB-1:0] = 0;
		end
	// Verilator lint_on  WIDTH
	endcase

	initial	axi_awaddr = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || (!o_busy && !i_request)))
		axi_awaddr <= 0;
	else if (!o_busy)
	begin
		axi_awaddr <= i_addr;

		if (!i_inc)
		begin
			// In the case of fixed addresses, we insist on
			// all transactions being aligned with the fixed
			// address.  If the initial i_addr isn't so aligned,
			// we'll catch that with the shift register, and just
			// fill the remainder with stuff (i.e. 0) bits.
			case(i_size)
			SZ_BYTE: begin end
			SZ_16B: axi_awaddr[0] <= 1'b0;
			SZ_32B: axi_awaddr[1:0] <= 2'b0;
			SZ_BUS: axi_awaddr[AXILSB-1:0] <= 0;
			endcase
		end
	end else if (M_AWVALID && M_AWREADY && r_inc)
		// We only need to worry about incrementing/adjusting the
		// address if r_inc is set.  Otherwise, the address remains
		// fixed.
		axi_awaddr <= nxt_awaddr[AW-1:0];
	// }}}

	// r_max_burst
	// {{{
	always @(posedge i_clk)
	if (!r_busy)
	begin
		if (!i_inc)
			r_max_burst <= MAX_FIXED_BURST-1;
		else if (i_size == SZ_BUS)
			r_max_burst <= (1<<LCLMAXBURST)-1;
		else
			r_max_burst <= (1<<LCLMAXBURST_SUB)-1;
	end

	initial	r_initial_burst = 1'b1;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		r_initial_burst <= (!i_request || i_inc);
	else if (w_start_aw)
		r_initial_burst <= 1'b0;

	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || (!o_busy && !i_request)))
		r_max_initial <= 0;
	else if (!o_busy && i_inc)
	begin
		// Verilator lint_off WIDTH
		case(i_size)
		SZ_BYTE: if (i_addr[0 +: LCLMAXBURST_SUB] != 0)
			begin
				r_max_initial <= -i_addr[0+: LCLMAXBURST_SUB]-1;
			end else
				r_max_initial <= (9'h1 << LCLMAXBURST_SUB)-1;
		SZ_16B: if (i_addr[1 +: LCLMAXBURST_SUB] != 0)
			begin
				r_max_initial <= -i_addr[1+: LCLMAXBURST_SUB]-1;
			end else
				r_max_initial <= (9'h1 << LCLMAXBURST_SUB)-1;
		SZ_32B: if (i_addr[2 +: LCLMAXBURST_SUB] != 0)
			begin
				r_max_initial <= -i_addr[2+: LCLMAXBURST_SUB]-1;
			end else
				r_max_initial <= (9'h1 << LCLMAXBURST_SUB)-1;
		SZ_BUS: if (i_addr[AXILSB +: LCLMAXBURST] != 0)
			begin
				r_max_initial <= (1<<LCLMAXBURST)-1
						- i_addr[AXILSB +: LCLMAXBURST];
			end else
				r_max_initial <= (9'h1 << LCLMAXBURST)-1;
		endcase
		// Verilator lint_on  WIDTH
	end

	assign	w_max_burst = (r_initial_burst) ? r_max_initial : r_max_burst;
	// }}}

	// axi_awlen
	// {{{
	initial	axi_awlen = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || !r_busy))
		axi_awlen <= 0;
	else if (!M_AWVALID || M_AWREADY)
	begin
		axi_awlen <= w_max_burst;
		if (last_rcvd) case(r_size)
		// Verilator lint_off WIDTH
		SZ_BYTE: if ((w_max_burst + 1) > awbytes_uncommitted)
			axi_awlen <= awbytes_uncommitted-1;
		SZ_16B: if ((w_max_burst + 1) > awbytes_uncommitted[LGMAX_FIFO_BYTES:1]
				+ awbytes_uncommitted[0])
			axi_awlen <= awbytes_uncommitted[LGMAX_FIFO_BYTES:1]
					+ awbytes_uncommitted[0] - 1;
		SZ_32B: if ((w_max_burst + 1) > awbytes_uncommitted[LGMAX_FIFO_BYTES:2]
				+ (|awbytes_uncommitted[1:0]))
			axi_awlen <= awbytes_uncommitted[LGMAX_FIFO_BYTES:2]
					+ (|awbytes_uncommitted[1:0]) - 1;
		SZ_BUS: if ((w_max_burst + 1) > awbytes_uncommitted[LGMAX_FIFO_BYTES:AXILSB]
				+ (|awbytes_uncommitted[AXILSB-1:0]))
			axi_awlen <= awbytes_uncommitted[LGMAX_FIFO_BYTES:AXILSB]
					+ (|awbytes_uncommitted[AXILSB-1:0])-1;
		// Verilator lint_on  WIDTH
		endcase
	end
	// }}}

	// beats_committed: AWVALIDs vs WVALIDs
	// {{{
	initial	beats_committed = 0;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		beats_committed <= 0;
	else case({ phantom_aw, phantom_w })
	2'b00: begin end
	2'b01: beats_committed <= beats_committed - 1;
	// Verilator lint_off WIDTH
	2'b10: beats_committed <= beats_committed + axi_awlen + 1;
	2'b11: beats_committed <= beats_committed + axi_awlen; // + 1 - 1
	// Verilator lint_on  WIDTH
	endcase
	// }}}

	// w_start_w
	// {{{
	always @(*)
	begin
		w_start_w = w_start_aw;
		if (M_WVALID && !M_WLAST)
			w_start_w = 1;
		// if (w_start_aw && (!M_AWVALID || M_AWREADY))
		//	Not necessary ... the default already captures this
		//	w_start_w = 1;
		if (beats_committed > 1)
			w_start_w = 1;
		if (!M_WVALID && beats_committed > 0)
			w_start_w = 1;
		if (M_WVALID && !M_WREADY)
			w_start_w = 0;
		if (!r_busy || (!sr_valid && !cmd_abort))
			w_start_w = 0;
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset && w_start_w)
		assert(sr_valid || cmd_abort);
`endif
	// }}}

	// phantom_w
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		phantom_w <= 0;
	else // if (!M_WVALID || M_WREADY)
		phantom_w <= w_start_w;
	// }}}

	// axi_wvalid
	// {{{
	initial	axi_wvalid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		axi_wvalid <= 0;
	else if (!M_WVALID || M_WREADY)
		axi_wvalid <= w_start_w;
	// }}}

	// axi_waddr
	// {{{
	always @(*)
	begin
		nxt_waddr = 0;
		case(r_size)
		SZ_BYTE: nxt_waddr = axi_waddr + 1;
		SZ_16B:  nxt_waddr[AW:1] = axi_waddr[AW-1:1] + 1;
		SZ_32B:  nxt_waddr[AW:2] = axi_waddr[AW-1:2] + 1;
		SZ_BUS:  nxt_waddr[AW:AXILSB] = axi_waddr[AW-1:AXILSB] + 1;
		endcase

		if (!M_WVALID || !M_WREADY)
			nxt_waddr = { 1'b0, axi_waddr };
	end

	initial	axi_waddr = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || (!o_busy && !i_request)))
		axi_waddr <= 0;
	else if (!o_busy)
	begin
		axi_waddr <= i_addr;

		// Zero out the LSBs, since the gearbox will be handling the
		// first initial shift in all cases.
		// NOTE: The gearboxes will be shifting things, yes, but we're
		// also using this waddr to shift the data.  Hence, we don't
		// want to shift data a second time (here and in the gearbox),
		// thus we *always* align this address.
		// if (!i_inc)
		case(i_size)
		SZ_BYTE: begin end
		SZ_16B: axi_waddr[0] <= 1'b0;
		SZ_32B: axi_waddr[1:0] <= 2'b0;
		SZ_BUS: axi_waddr[AXILSB-1:0] <= 0;
		endcase
	end else if (M_WVALID && M_WREADY && r_inc)
		axi_waddr <= nxt_waddr[AW-1:0];
	// }}}

	// axi_wdata
	// {{{
	always @(*)
	begin
		case(r_size)
		SZ_BYTE: nxt_wdata = { {(DW- 8){1'b0}}, sr_data[ 7:0] };
		SZ_16B:  nxt_wdata = { {(DW-16){1'b0}}, sr_data[15:0] };
		SZ_32B:  nxt_wdata = { {(DW-32){1'b0}}, sr_data[31:0] };
		SZ_BUS:  nxt_wdata = sr_data[DW-1:0];
		endcase

		nxt_wdata = nxt_wdata << (8*nxt_waddr[AXILSB-1:0]);
	end

	always @(posedge i_clk)
	if (i_reset && OPT_LOWPOWER)
		axi_wdata <= 0;
	else if (!M_WVALID || M_WREADY)
	begin
		axi_wdata <= nxt_wdata;
		if(OPT_LOWPOWER && (!r_busy || cmd_abort
				|| !sr_valid || (r_inc && nxt_waddr[AW])))
			axi_wdata <= 0;
	end
	// }}}

	// axi_wstrb
	// {{{
	always @(posedge i_clk)
	if (!o_busy)
	begin
		if (i_request)
		case(i_size)
		SZ_BYTE: base_wstrb <= 1;
		SZ_16B : begin
			base_wstrb <= { {(DW/8-2){1'b0}}, 2'h3 } << i_addr[0];
			base_wstrb[DW/8-1:2] <= 0;
			end
		SZ_32B : begin
			base_wstrb <= { {(DW/8-4){1'b0}}, 4'hf }<< i_addr[1:0];
			if (DW > 32)
				base_wstrb[DW/8-1:(DW > 32 ? 4:0)] <= 0;
			end
		SZ_BUS: base_wstrb <= {(DW/8){1'b1}} << i_addr[AXILSB-1:0];
		endcase
	end else if (sr_valid && sr_ready)
	case(r_size)
	SZ_BYTE: base_wstrb <= 1;
	SZ_16B : base_wstrb <= { {(DW/8-2){1'b0}}, 2'h3 };
	SZ_32B : base_wstrb <= { {(DW/8-4){1'b0}}, 4'hf };
	SZ_BUS:  base_wstrb <= {(DW/8){1'b1}};
	endcase

	always @(posedge i_clk)
	if (!o_busy)
	begin
		last_count <= 0;
		if (i_request)
		case(i_size)
		SZ_BYTE: last_count <= 0;
		SZ_16B:  last_count[  0] <= i_addr[  0];
		SZ_32B:  last_count[1:0] <= i_addr[1:0];
		SZ_BUS:  last_count      <= i_addr[AXILSB-1:0];
		endcase
	end else if (S_VALID && S_READY)
	begin
		// Verilator lint_off WIDTH
		last_count <= last_count + S_BYTES;
		// Verilator lint_on  WIDTH
		case(r_size)
		SZ_BYTE: last_count <= 1;
		SZ_16B:  last_count[AXILSB-1:1] <= 0;
		SZ_32B:  if (AXILSB > 2)
			last_count[AXILSB-1:(AXILSB > 2 ? 2 : 0)] <= 0;
		SZ_BUS:  begin end
		endcase
		// else the count = count + the full bus width, which
		//	 would overflow and leave us with no change.
	end

	always @(posedge i_clk)
	if (!r_busy || (S_VALID && !S_LAST))
		wpipe <= 2'b00;
	else if (S_VALID && S_READY && S_LAST)
		wpipe <= 2'b10;
	else
		wpipe <= wpipe >> 1;

	always @(*)
	begin
		w_last_mask = -1;
		if (last_count != 0)
		begin
		w_last_mask = w_last_mask << last_count;
		w_last_mask = ~w_last_mask;
		case(r_size)
		SZ_BYTE: w_last_mask = -1;
		SZ_16B:  w_last_mask = {(DW/8/2){w_last_mask[1:0]}};
		SZ_32B:  w_last_mask = {(DW/8/4){w_last_mask[3:0]}};
		SZ_BUS:  begin end // w_last_mask= {(1){w_last_mask[DW/8-1:0]}};
		endcase
		end
	end
	
	always @(posedge i_clk)
	if (wpipe == 2'b10)
		last_mask <= w_last_mask;

	always @(*)
	begin
		nxt_wstrb = base_wstrb << nxt_waddr[AXILSB-1:0];
		if (sr_last[0])
			nxt_wstrb = nxt_wstrb & last_mask;
	end

	always @(posedge i_clk)
	if (i_reset && OPT_LOWPOWER)
		axi_wstrb <= 0;
	else if (!M_WVALID || M_WREADY)
	begin
		axi_wstrb <= nxt_wstrb;
		if (cmd_abort || (r_inc && nxt_waddr[AW]))
			axi_wstrb <= 0;
	end
	// }}}

	// wfix_burst_count
	// {{{
	// Since we can't use the address register, we need a special register
	// to keep track of where we are within a burst during fixed addressing.
	// We need this to set WLAST--but only during fixed addressing.
	always @(posedge i_clk)
	if (i_reset || !o_busy || r_inc || M_WLAST)
		wfix_burst_count <= 1;
	else if (M_WVALID && M_WREADY)
		wfix_burst_count <= wfix_burst_count + 1;
	// }}}

	// axi_wlast
	// {{{
	always @(posedge i_clk)
	if ((i_reset && OPT_LOWPOWER) || !o_busy)
		axi_wlast <= 1'b0;
	else if (!M_WVALID || M_WREADY)
	begin
		if (r_inc)
		begin
			case(r_size)
			SZ_BYTE: axi_wlast <= (&nxt_waddr[0 +: LCLMAXBURST_SUB]);
			SZ_16B:  axi_wlast <= (&nxt_waddr[1 +: LCLMAXBURST_SUB]);
			SZ_32B:  axi_wlast <= (&nxt_waddr[2 +: LCLMAXBURST_SUB]);
			SZ_BUS:  axi_wlast <= (&nxt_waddr[AXILSB +: LCLMAXBURST]);
			endcase
		end else
			axi_wlast <= &wfix_burst_count;

		if ((sr_valid || !OPT_LOWPOWER) && sr_last[0])
			axi_wlast <= 1'b1;
		// Verilator lint_off WIDTH
		if (cmd_abort && beats_committed == 1 + phantom_w)
			// Verilator lint_on  WIDTH
			axi_wlast <= 1'b1;
	end
`ifdef	FORMAL
	always @(*)
	if (M_WVALID && beats_committed == (phantom_aw ? 1:0))
		assert(axi_wlast);
`endif
	// }}}

	// data_sent
	// {{{
	// We use this to determine w_complete, to then lower r_busy
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		data_sent <= 1'b0;
	else if (sr_valid && sr_ready && sr_last[0])
	begin
		// data_sent[0] = M_VALID is for the last beat of transfer
		// data_sent[1] = All beats complete.  Sticky bit.
		data_sent <= 1'b1;
	end else if (cmd_abort && (!M_AWVALID || M_AWREADY)
			&&(!M_WVALID || (M_WREADY && M_WLAST)))
		data_sent <= 1'b1;
	// }}}

	// bursts_outstanding -- how many BVALIDs left to expect
	// {{{
	initial	bursts_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
		bursts_outstanding <= 0;
	else case({ phantom_aw, M_BVALID && M_BREADY })
	2'b10: bursts_outstanding <= bursts_outstanding + 1;
	2'b01: bursts_outstanding <= bursts_outstanding - 1;
	default: begin end
	endcase
	// }}}

	assign	sr_ready = w_start_w && (!M_WVALID || M_WREADY);

	assign	M_AWVALID = axi_awvalid;
	assign	M_AWID    = AXI_ID;
	assign	M_AWADDR  = axi_awaddr;
	assign	M_AWLEN   = axi_awlen;
	assign	M_AWBURST = { 1'b0, r_inc };
	assign	M_AWSIZE  = axi_size;
	assign	M_AWLOCK  = 1'b0;
	assign	M_AWCACHE = DEF_AWCACHE;
	assign	M_AWPROT  = DEF_AWPROT;
	assign	M_AWQOS   = DEF_AWQOS;

	assign	M_WVALID = axi_wvalid;
	assign	M_WDATA  = axi_wdata;
	assign	M_WSTRB  = axi_wstrb;
	assign	M_WLAST  = axi_wlast;
	//
	assign	M_BREADY = 1'b1;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_BID, M_BRESP[0], ign_fif_fill };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
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
	localparam	F_LGDEPTH = LCLMAXBURST+1;
			reg		f_past_valid;
	(* anyconst *)	reg	[AW-1:0]	f_cfg_addr;
	(* anyconst *)	reg	[1:0]	f_cfg_size;
	(* anyconst *)	reg		f_cfg_inc;
	// wire	[F_LGDEPTH-1:0]		fwb_nreqs, fwb_nacks, fwb_outstanding;
	reg	[ADDRESS_WIDTH:0]	f_posn, f_waddr, faxi_wposn,
					f_fifo_bytes, faxi_awposn;
	reg	[AXILSB-1:0]	fr_sel_count, fr_sel_count_past;
	reg	[AXILSB:0]	ffif_last_bytes, f_sr_bytes;
	wire	[AXILSB:0]	f_gears_bytes;
	reg	[AXILSB-1:0]	f_last_count;

	wire			faxi_ckvalid, faxi_arckvalid, faxi_lockd;
	wire	[F_LGDEPTH-1:0]	faxi_nbursts, faxi_wrid_nbursts,
				faxi_rd_nbursts, faxi_rd_outstanding;
	wire	[9-1:0]		faxi_pending;
	wire	[IW-1:0]	faxi_checkid;
	wire	[AW-1:0]	faxi_waddr;
	wire	[7:0]		faxi_incr;
	wire	[1:0]		faxi_burst;
	wire	[2:0]		faxi_size;
	wire	[7:0]		faxi_len;

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

	always @(*)
	if (!f_cfg_inc) case(f_cfg_size)
	SZ_BYTE: begin end
	SZ_16B:  assume(f_cfg_addr[0] == 1'b0);
	SZ_32B:  assume(f_cfg_addr[1:0] == 2'b0);
	SZ_BUS:  assume(f_cfg_addr[AXILSB-1:0] == 0);
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
		assert(r_size == f_cfg_size);
		assert(r_inc  == f_cfg_inc);

		if (!r_inc)
		case(r_size)
		SZ_BYTE: begin end
		SZ_16B: assert(f_cfg_addr[0] == 1'b0);
		SZ_32B: assert(f_cfg_addr[1:0] == 2'b0);
		SZ_BUS: assert(f_cfg_addr[AXILSB-1:0] == 0);
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
		begin
			assume(S_BYTES == (DW/8));
		end else case(f_cfg_size)
		2'b11: assume(S_BYTES == 1);
		2'b10: assume(S_BYTES <= 2);
		2'b01: assume(S_BYTES <= 4);
		2'b00: assume(S_BYTES <= (DW/8));
		endcase
	end

	always @(*)
	if (fif_empty)
		f_fifo_bytes = 0;
	else if (!last_rcvd)
		f_fifo_bytes = ign_fif_fill << AXILSB;
	else
		f_fifo_bytes = ((ign_fif_fill-1) << AXILSB) + ffif_last_bytes;

	always @(*)
	if (!last_rcvd)
		assert(f_fifo_bytes == (ign_fif_fill << AXILSB));

	always @(*)
	if (!fif_empty)
	begin
		if (!last_rcvd || ign_fif_fill > 1)
		begin
			assert(!fif_last);
			assert(fif_bytes == (DW/8));
		end else begin
			assert(fif_last);
			assert(fif_bytes > 0);
			assert(fif_bytes == ffif_last_bytes);
		end
	end

	// ffif_last_bytes: How many bytes should the last beat in the FIFO
	// have?
	initial	ffif_last_bytes = DW/8;
	always @(posedge i_clk)
	if (i_reset || !r_busy)
		ffif_last_bytes <= DW/8;
	else if (S_VALID && S_READY && S_LAST)
		ffif_last_bytes <= S_BYTES;

	always @(*)
	begin
		assert(ffif_last_bytes > 0);
		assert(ffif_last_bytes <= DW/8);
		if (!last_rcvd)
			assert(ffif_last_bytes == DW/8);

		case(f_cfg_size)
		SZ_BYTE: f_last_count = 1;
		SZ_16B:  begin
			f_last_count = f_cfg_addr[0] + ffif_last_bytes[0];
			f_last_count[AXILSB-1:1] = 0;
			end
		SZ_32B:  begin
			f_last_count = f_cfg_addr[1:0] + ffif_last_bytes[1:0];
			f_last_count[AXILSB-1:2] = 0;
			end
		SZ_BUS:  begin
			f_last_count = f_cfg_addr[AXILSB-1:0]
						+ ffif_last_bytes[AXILSB-1:0];
			end
		endcase

		if (r_busy && (last_rcvd || f_cfg_size != SZ_BYTE))
			assert(f_last_count == last_count);
	end

	always @(posedge i_clk)
	if (i_reset || !o_busy)
		f_posn <= 0;
	else if (S_VALID && S_READY)
		f_posn <= f_posn + S_BYTES;

	always @(*)
	if (o_busy)
		assume(!f_posn[ADDRESS_WIDTH] || f_posn[ADDRESS_WIDTH-1:0]==0);

	/*
	always @(*)
	if (!i_reset && o_busy)
	begin
		if (r_last)
		begin
		end else case(f_cfg_size)
		2'b11: begin end
		2'b10: assert(f_posn[0] == 1'b0);
		2'b01: assert(f_posn[1:0] == 2'b0);
		2'b00: assert(f_posn[AXILSB-1:0] == 0);
		endcase
	end
	*/

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(IW),
		.C_AXI_ADDR_WIDTH(AW),
		.C_AXI_DATA_WIDTH(DW),
		.OPT_MAXBURST((9'h01<<LCLMAXBURST)-1),
		.OPT_EXCLUSIVE(1'b0),
		.OPT_NARROW_BURST(1'b1),
		// .F_OPT_NO_RESET(1'b0),
		.F_LGDEPTH(F_LGDEPTH),
		.F_OPT_READCHECK(1'b0)
		// }}}
	) faxi (
		// {{{
		.i_clk(i_clk),
		.i_axi_reset_n(!i_reset),
		// AW
		// {{{
		.i_axi_awvalid(	M_AWVALID),
		.i_axi_awready(	M_AWREADY),
		.i_axi_awid(	M_AWID),
		.i_axi_awaddr(	M_AWADDR),
		.i_axi_awlen(	M_AWLEN),
		.i_axi_awsize(	M_AWSIZE),
		.i_axi_awburst(	M_AWBURST),
		.i_axi_awlock(	M_AWLOCK),
		.i_axi_awcache(	M_AWCACHE),
		.i_axi_awprot(	M_AWPROT),
		.i_axi_awqos(	M_AWQOS),
		// }}}
		// W*
		// {{{
		.i_axi_wvalid(M_WVALID),
		.i_axi_wready(M_WREADY),
		.i_axi_wdata(M_WDATA),
		.i_axi_wstrb(M_WSTRB),
		.i_axi_wlast(M_WLAST),
		// }}}
		// B*
		// {{{
		.i_axi_bvalid(M_BVALID),
		.i_axi_bready(M_BREADY),
		.i_axi_bid(M_BID),
		.i_axi_bresp(M_BRESP),
		// }}}
		// AR*
		// {{{
		.i_axi_arvalid(	1'b0),
		.i_axi_arready(	1'b0),
		.i_axi_arid(	AXI_ID),
		.i_axi_araddr(	{(AW){1'b0}}),
		.i_axi_arlen(	8'h00),
		.i_axi_arsize(	3'h00),
		.i_axi_arburst(	2'b00),
		.i_axi_arlock(	1'b0),
		.i_axi_arcache(	4'h0),
		.i_axi_arprot(	3'h0),
		.i_axi_arqos(	4'h0),
		// }}}
		// R*
		// {{{
		.i_axi_rvalid(	1'b0),
		.i_axi_rready(	1'b0),
		.i_axi_rid(	AXI_ID),
		.i_axi_rdata(	{(DW){1'b0}}),
		.i_axi_rlast(	1'b0),
		.i_axi_rresp(	2'b00),
		// }}}
		// Induction
		// {{{
		.f_axi_awr_nbursts(faxi_nbursts),
		.f_axi_wr_pending(faxi_pending),
		.f_axi_rd_nbursts(faxi_rd_nbursts),
		.f_axi_rd_outstanding(faxi_rd_outstanding),
		// WR counting
		// {{{
		.f_axi_wr_checkid(	faxi_checkid),
		.f_axi_wr_ckvalid(	faxi_ckvalid),
		.f_axi_wrid_nbursts(	faxi_wrid_nbursts),
		.f_axi_wr_addr(		faxi_waddr),
		.f_axi_wr_incr(		faxi_incr),
		.f_axi_wr_burst(	faxi_burst),
		.f_axi_wr_size(		faxi_size),
		.f_axi_wr_len(		faxi_len),
		.f_axi_wr_lockd(	faxi_lockd),
		// }}}
		// RD Counting
		// {{{
		.f_axi_rd_checkid(),
		.f_axi_rd_ckvalid(faxi_arckvalid),
		.f_axi_rd_cklen(),
		.f_axi_rd_ckaddr(),
		.f_axi_rd_ckincr(),
		.f_axi_rd_ckburst(),
		.f_axi_rd_cksize(),
		.f_axi_rd_ckarlen(),
		.f_axi_rd_cklockd(),
		//
		.f_axi_rdid_nbursts(),
		.f_axi_rdid_outstanding(),
		.f_axi_rdid_ckign_nbursts(),
		.f_axi_rdid_ckign_outstanding(),
		// }}}
		// Exclusive access handling
		// {{{
		.f_axi_ex_state(),
		.f_axi_ex_checklock(),
		.f_axi_rdid_bursts_to_lock(),
		.f_axi_wrid_bursts_to_exwrite(),
		.i_active_lock(1'b0),
		.i_exlock_addr({(AW){1'b0}}),
		.i_exlock_len(8'h00),
		.i_exlock_burst(2'b00),
		.i_exlock_size(3'h0),
		.f_axi_exreq_addr(),
		.f_axi_exreq_len(),
		.f_axi_exreq_burst(),
		.f_axi_exreq_size(),
		.f_axi_exreq_return()
		// }}}
		// }}}
		// }}}
	);

	always @(*)
	begin
		assert(faxi_arckvalid == 1'b0);
		assert(faxi_rd_nbursts == 0);
		assert(faxi_rd_outstanding == 0);

		assume(faxi_checkid == AXI_ID);
		assert(faxi_wrid_nbursts == faxi_nbursts);
		assert(bursts_outstanding == faxi_nbursts
				+ ((M_AWVALID && !phantom_aw) ? 1:0));
		if (faxi_ckvalid)
		begin
			assert(r_busy);
			assert(cmd_abort || faxi_waddr == f_waddr);
			// assert(faxi_incr  == f_waddr);
			assert(faxi_burst  == { 1'b0, r_inc });
			assert(faxi_size   == axi_size);
			// assert(faxi_wlen   == ?);
			assert(faxi_lockd  == 1'b0);

			if (phantom_aw || !M_AWVALID)
			begin
				assert(beats_committed == faxi_pending
					- ((M_WVALID && !phantom_w) ? 1:0));
			end else begin
				assert(beats_committed == faxi_pending
					+ (M_AWLEN+1)
					- ((M_WVALID && !phantom_w) ? 1:0));
			end
		end
	end

	always @(*)
	if (!i_reset && M_WVALID)
		assert(cmd_abort || (|M_WSTRB));

	always @(*)
	if (!i_reset && r_busy)
	begin
		if (r_initial_burst)
		begin
			assert(faxi_wposn == 0);
		end

		if (r_inc)
		begin
			if (r_initial_burst)
			begin
				assert(M_AWADDR == f_cfg_addr);
			end else if (M_AWADDR != f_cfg_addr || !M_AWVALID)
			case(r_size)
			SZ_BYTE: assert(M_AWADDR[0 +: LCLMAXBURST_SUB] == 0);
			SZ_16B:  assert(M_AWADDR[0 +: (1+LCLMAXBURST_SUB)]== 0);
			SZ_32B:  assert(M_AWADDR[0 +: (2+LCLMAXBURST_SUB)]== 0);
			SZ_BUS:  assert(M_AWADDR[0 +: (AXILSB+LCLMAXBURST)]==0);
			endcase
		end else case(r_size)
		SZ_BYTE: assert(M_AWADDR == f_cfg_addr);
		SZ_16B:  assert(M_AWADDR == { f_cfg_addr[AW-1:1], 1'b0 });
		SZ_32B:  assert(M_AWADDR == { f_cfg_addr[AW-1:2], 2'b00 });
		SZ_BUS:  assert(M_AWADDR == { f_cfg_addr[AW-1:AXILSB], {(AXILSB){1'b0}} });
		endcase
	end

	initial	faxi_wposn = 0;
	always @(posedge i_clk)
	if (i_reset || !o_busy)
		faxi_wposn <= 0;
	else if (M_WVALID && M_WREADY)
		faxi_wposn <= faxi_wposn + $countones(M_WSTRB);

	always @(*)
	if (!f_past_valid || !r_busy || r_initial_burst)
		faxi_awposn = 0;
	else begin
		case(r_size)
		SZ_BYTE: faxi_awposn = faxi_wposn -  beats_committed
			+ ((M_AWVALID && !phantom_aw) ? (M_AWLEN+1) : 0);
		SZ_16B:  faxi_awposn = faxi_wposn - (beats_committed<<1) - f_cfg_addr[0]
			+ ((M_AWVALID && !phantom_aw) ? ((M_AWLEN+1)<<1) : 0);
		SZ_32B:  faxi_awposn = faxi_wposn - (beats_committed<<2) - f_cfg_addr[1:0]
			+ ((M_AWVALID && !phantom_aw) ? ((M_AWLEN+1)<<2) : 0);
		SZ_BUS:  faxi_awposn = faxi_wposn - (beats_committed<<AXILSB)
				- f_cfg_addr[AXILSB-1:0]
			+ ((M_AWVALID && !phantom_aw) ? ((M_AWLEN+1)<<AXILSB) : 0);
		endcase
	end

	always @(*)
	if (!i_reset && r_busy)
	begin
		if (r_inc && !last_rcvd)
			assert(M_AWADDR == f_cfg_addr + faxi_awposn);
		// The following *should* be true, but needs to be modified
		// to fit the last number of bytes in the last beat
		// assert(f_awposn <= f_posn);
	end

	// How many valid bytes are in the shift register?
	// Can we use ffif_last_bytes here to calculate this?
	//	f_gears_last = (ffif_last_bytes % WIDTH)?
	// if (sr_last[0])
	always @(*)
	if (!sr_valid && (|sr_last || r_initial_burst))
		f_sr_bytes = 0;
	else if (sr_valid)
	begin
		case(f_cfg_size)
		SZ_BYTE: f_sr_bytes = 1;
		SZ_16B: f_sr_bytes = 2 + (r_initial_burst ? 0 : f_cfg_addr[0]);
		SZ_32B: f_sr_bytes = 4 + (r_initial_burst ? 0 : f_cfg_addr[1:0]);
		SZ_BUS:  f_sr_bytes = (DW/8) + (r_initial_burst ? 0 : f_cfg_addr[AXILSB-1:0]);
		endcase
	end else if (!sr_valid)
	begin
		case(f_cfg_size)
		SZ_BYTE: f_sr_bytes = 0;
		SZ_16B:  f_sr_bytes = f_cfg_addr[0];
		SZ_32B:  f_sr_bytes = f_cfg_addr[1:0];
		SZ_BUS:  f_sr_bytes = f_cfg_addr[AXILSB-1:0];
		endcase
	end

	assign	f_gears_bytes = (gears_valid && gears_last) ? gears_bytes
			: (f_gears_rcvd - f_gears_sent);

	always @(*)
	if (!i_reset)
	begin
		assert(f_gears_rcvd <= f_posn);
		if (!gears_valid || !gears_last)
			assert(f_gears_rcvd >= f_gears_sent);
		if (gears_valid && gears_last)
			assert(last_rcvd && fif_empty);
	end

	always @(*)
	if (!i_reset && !cmd_abort)
	begin
		if (sr_last == 0 && (!gears_valid || !gears_last))
		begin
			assert(f_posn == f_gears_rcvd + f_fifo_bytes);
		end else
			assert(f_gears_rcvd == 0);
	end

	always @(*)
	if (!i_reset && o_busy && !o_err && !cmd_abort
					&& (sr_last == 0 || !sr_valid))
		assert(f_posn == faxi_wposn + f_fifo_bytes
			+ f_gears_bytes + f_sr_bytes
			+ (M_WVALID ? $countones(M_WSTRB) : 0));

	always @(*)
	if (r_inc)
	begin
		f_waddr = f_cfg_addr + faxi_wposn;

		if (faxi_wposn > 0)
		case(r_size)
		SZ_16B: f_waddr[  0] = 0;
		SZ_32B: f_waddr[1:0] = 0;
		SZ_BUS: f_waddr[AXILSB-1:0] = 0;
		default: begin end
		endcase
	end else begin
		// faxi_waddr = f_cfg_addr + fwb_posn;
		f_waddr = f_cfg_addr;

		case(r_size)
		SZ_BYTE: begin end
		SZ_16B: f_waddr[0] = 0;
		SZ_32B: f_waddr[1:0] = 0;
		SZ_BUS: f_waddr[AXILSB-1:0] = 0;
		endcase
	end

	/*
	always @(*)
	if (!i_reset && o_busy && !r_last && !o_err)
	begin
		assert({ 1'b0, axi_waddr } == f_waddr[ADDRESS_WIDTH:AXILSB]);
		case(r_size)
		SZ_BUS: assert(subaddr == f_cfg_addr[AXILSB-1:0]);
		SZ_16B: assert(subaddr == { f_waddr[AXILSB-1:1], f_cfg_addr[0] });
		SZ_32B: assert(subaddr == { f_waddr[AXILSB-1:2], f_cfg_addr[1:0] });
		default:
			assert(subaddr == f_waddr[AXILSB-1:0]);
		endcase
	end

	always @(*)
	if (o_busy && faxi_waddr[ADDRESS_WIDTH] && !r_last)
	begin
		assert(o_err);
		// assert(faxi_waddr[ADDRESS_WIDTH-1:0] <= DW/8);
	end

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
		SZ_16B: assert(subaddr[0]   == f_cfg_addr[0]);
		SZ_32B: assert(subaddr[1:0] == f_cfg_addr[1:0]);
		SZ_BUS: assert(subaddr      == f_cfg_addr[AXILSB-1:0]);
		endcase
	end

	always @(*)
		fr_sel_count = $countones(r_sel);

	// always @(posedge i_clk)
	// if (!o_wr_sel || !i_wr_stall)
	//	fr_sel_count_past <= fr_sel_count;

	always @(posedge i_clk)
	if(!i_reset && o_busy && !o_err && !r_last && $past(S_VALID && S_READY))
	begin
		assert(M_WVALID);
		assert($countones({ r_sel, M_WSTRB })
					== $past(S_BYTES + fr_sel_count));
	end
	*/

	/*
	always @(*)
	if (!i_reset && o_busy)
	begin
		if (f_posn == 0)
		begin
			assert(r_sel == 0);
		end else
		case(r_size)
		SZ_BYTE: assert(r_sel == 0);
		SZ_16B: begin
			assert(r_sel[DW/8-1:1] == 0);

			if (!M_WVALID) begin end
			else if (subaddr + 2 <= DW/8)
			begin
				assert(r_sel == 0);
			end else if (!r_last)
			begin
				assert(r_sel[0] == (subaddr+2 > DW/8));
			end else begin
				assert(r_sel[0] <= (subaddr+2 > DW/8));
			end end
		SZ_32B: begin
			assert(r_sel[DW/8-1:3] == 0);

			if (!M_WVALID) begin end
			else if (subaddr + 4 <= DW/8)
			begin
				assert(r_sel == 0);
			end end
		SZ_BUS: begin
			assert(!(&r_sel));
			if (subaddr == 0)
				assert(r_sel == 0);
			end
		default: begin end
		endcase

		if (!M_WSTRB[DW/8-1])
			assert(!r_sel[0]);

		for(ik=0; ik<DW/8; ik=ik+1)
		begin
			case(r_size)
			SZ_32B: if (ik > 2)
				assert(!r_sel[ik]);
			SZ_BUS: if (ik >= f_cfg_addr[DW/8-1:0])
				assert(!r_sel[ik]);
			default: begin end
			endcase
		end
	end
	*/

	reg	[AXILSB-1:0]	f_sum;

	always @(*)
	if (r_inc)
		f_sum = faxi_wposn[AXILSB-1:0] + f_cfg_addr[AXILSB-1:0];
	else
		f_sum = faxi_wposn[AXILSB-1:0];

	/*
	always @(*)
	if (!i_reset && o_busy && faxi_wposn > 0)
	begin
		if (!r_last) case(r_size)
		SZ_16B: assert(f_sum[  0] == 0);
		SZ_32B: assert(f_sum[1:0] == 0);
		SZ_BUS: assert(f_sum[AXILSB-1:0] == 0);
		default: begin end
		endcase
	end
	*/

	always @(*)
		f_tmp_last = f_posn + f_cfg_addr;

	always @(*)
	if (r_busy)
	begin
		if (!last_rcvd)
		begin
			case(r_size)
			SZ_BYTE: assert(0 == last_count);
			SZ_16B:  assert(last_count == { {(AW-1){1'b0}}, f_cfg_addr[  0] });
			SZ_32B:  assert(last_count == { {(AW-2){1'b0}}, f_cfg_addr[1:0] });
			SZ_BUS:  assert(last_count == { {(AW-AXILSB){1'b0}}, f_cfg_addr[AXILSB-1:0] });
		end else begin
			case(r_size)
			SZ_BYTE: assert(last_count == 1);
			SZ_16B:  assert(last_count == { f_tmp_last[AXILSB-1:1], 1'b0 });
			SZ_32B:  assert(last_count == { f_tmp_last[AXILSB-1:2], 2'b0 });
			endcase
		end
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

	reg	[ADDRESS_WIDTH:0]	f_shift, faxi_shift;
	reg	[DW-1:0]	fc_partial;
	reg	[2*DW-1:0]	fc_partial_axi;
	reg	[2*DW/8-1:0]	fc_partial_sel;
	wire	[DW-1:0]	fz_data;
	wire	[DW/8-1:0]	fz_sel;
	wire			fin_check, fax_check;

	assign	fz_data = 0;
	assign	fz_sel  = 0;

	always @(*)
	begin
		f_shift = (fc_posn - f_posn);
		f_shift[ADDRESS_WIDTH:AXILSB] = 0;
	end

	always @(*)
		fc_partial = S_DATA >> (8*f_shift);

	assign	fin_check = fc_check && S_VALID && (f_posn <= fc_posn)
				&& (fc_posn < f_posn + S_BYTES);
	assign	fax_check = fc_check && o_busy && !o_err
		&& (faxi_wposn <= fc_posn)
		&& (M_WVALID && fc_posn < faxi_wposn + $countones(M_WSTRB));

	always @(*)
	if (fin_check)
		assume(fc_partial[7:0] == fc_byte);

	always @(*)
	begin
		faxi_shift = 0;
		if (r_inc)
		begin
			faxi_shift[AXILSB-1:0] = fc_posn[AXILSB-1:0]
				- faxi_wposn[AXILSB-1:0];
			if (M_WVALID)
				faxi_shift[AXILSB-1:0] = faxi_shift[AXILSB-1:0] + faxi_waddr[AXILSB-1:0];
		end else
			faxi_shift[AXILSB-1:0] = fc_posn[AXILSB-1:0] - faxi_wposn[AXILSB-1:0]
							+ f_cfg_addr[AXILSB-1:0];
	end

	always @(*)
	begin
		fc_partial_axi = { {(DW  ){1'b0}}, M_WDATA } >> (8*faxi_shift);
		fc_partial_sel = { {(DW/8){1'b0}}, M_WSTRB } >>    faxi_shift;
	end

	always @(*)
	if (o_busy)
		assert(faxi_wposn <= f_posn);

	always @(*)
	if (fax_check)
	begin
		assert(fc_partial_axi[7:0] == fc_byte);
		assert(fc_partial_sel[0]);
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

	// }}}
`endif
// }}}
endmodule
