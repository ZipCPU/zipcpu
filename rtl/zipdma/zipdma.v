////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zipdma.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	(Upgraded) Wishbone DMA controller for the ZipCPU
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
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module zipdma #(
		// {{{
		parameter	ADDRESS_WIDTH=30, LGMEMLEN = 10,
		parameter	LGDMALENGTH=ADDRESS_WIDTH,
		parameter	SLV_WIDTH=32,
		parameter	BUS_WIDTH=512,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter [0:0]	OPT_REGISTER_RAM = 1'b0,
		localparam	AW=ADDRESS_WIDTH-$clog2(BUS_WIDTH/8)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Slave port
		// {{{
		// Slave/control wishbone inputs
		input	wire			i_swb_cyc, i_swb_stb, i_swb_we,
		input	wire	[1:0]		i_swb_addr,
		input	wire	[SLV_WIDTH-1:0]	i_swb_data,
		input	wire [SLV_WIDTH/8-1:0]	i_swb_sel,
		// Slave/control wishbone outputs
		output	wire			o_swb_stall,
		output	wire			o_swb_ack,
		output	wire	[SLV_WIDTH-1:0]	o_swb_data,
		// }}}
		// Master/DMA port
		// {{{
		output	wire			o_mwb_cyc, o_mwb_stb, o_mwb_we,
		output	wire	[AW-1:0]	o_mwb_addr,
		output	wire	[BUS_WIDTH-1:0]	o_mwb_data,
		output	wire [BUS_WIDTH/8-1:0]	o_mwb_sel,
		// Master/DMA wishbone responses from the bus
		input	wire			i_mwb_stall, i_mwb_ack,
		input	wire	[BUS_WIDTH-1:0]	i_mwb_data,
		input	wire			i_mwb_err,
		// }}}
		// The interrupt device interrupt lines
		input	wire [31:0]		i_dev_ints,
		// An interrupt to be set upon completion
		output	wire			o_interrupt
		// }}}
	);

	// Local declarations
	// {{{
	localparam	FIFO_WIDTH = BUS_WIDTH+$clog2(BUS_WIDTH/8)+2;
	localparam	LGFIFO = LGMEMLEN-$clog2(BUS_WIDTH/8);

	wire				dma_request, dma_abort,
					dma_busy, dma_err;
	wire	[ADDRESS_WIDTH-1:0]	dma_src, dma_dst,
					read_addr, write_addr;
	wire	[LGDMALENGTH-1:0]	dma_length, remaining_len;
	wire	[LGMEMLEN:0]		dma_transferlen;
	wire				dma_trigger;

	wire				mm2s_request, s2mm_request;
	wire				mm2s_busy, s2mm_busy;
	wire				mm2s_err, s2mm_err;
	wire				mm2s_inc, s2mm_inc;
	wire	[1:0]			mm2s_size, s2mm_size;
	wire	[ADDRESS_WIDTH-1:0]	mm2s_addr, s2mm_addr;
	wire	[LGMEMLEN:0]		mm2s_transferlen, s2mm_transferlen;

	wire				mm2s_rd_cyc, mm2s_rd_stb, mm2s_rd_we,
					mm2s_rd_stall, mm2s_rd_ack, mm2s_rd_err;
	wire	[AW-1:0]		mm2s_rd_addr;
	wire	[BUS_WIDTH-1:0]		mm2s_rd_data;
	wire	[BUS_WIDTH/8-1:0]	mm2s_rd_sel;

	wire				mm2s_valid, mm2s_ready, mm2s_last;
	wire	[BUS_WIDTH-1:0]		mm2s_data;
	wire	[$clog2(BUS_WIDTH/8):0]	mm2s_bytes;

	wire				rx_valid, rx_ready, rx_last;
	wire	[BUS_WIDTH-1:0]		rx_data;
	wire	[$clog2(BUS_WIDTH/8):0]	rx_bytes;

	wire				tx_valid, tx_ready, tx_last;
	wire	[BUS_WIDTH-1:0]		tx_data;
	wire	[$clog2(BUS_WIDTH/8):0]	tx_bytes;

	wire			sfifo_full, sfifo_empty;
	wire	[LGFIFO:0]	ign_sfifo_fill;

	wire			s2mm_valid, s2mm_ready, s2mm_last;
	wire	[BUS_WIDTH-1:0]	s2mm_data;
	wire	[$clog2(BUS_WIDTH/8):0]	s2mm_bytes;

	wire				s2mm_wr_cyc, s2mm_wr_stb, s2mm_wr_we,
					s2mm_wr_stall, s2mm_wr_ack, s2mm_wr_err;
	wire	[AW-1:0]		s2mm_wr_addr;
	wire	[BUS_WIDTH-1:0]		s2mm_wr_data;
	wire	[BUS_WIDTH/8-1:0]	s2mm_wr_sel;

	wire				wb_cyc, wb_stb, wb_we,
					wb_stall, wb_ack, wb_err;
	wire	[AW-1:0]		wb_addr;
	wire	[BUS_WIDTH-1:0]		wb_data, wb_idata;
	wire	[BUS_WIDTH/8-1:0]	wb_sel;
	// }}}


	zipdma_ctrl #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.LGMEMLEN(LGMEMLEN),
		.LGDMALENGTH(ADDRESS_WIDTH),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) u_controller (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// Slave WB control port
		// {{{
		// Slave/control wishbone inputs
		.i_cyc(i_swb_cyc), .i_stb(i_swb_stb), .i_we(i_swb_we),
		.i_addr(i_swb_addr),
		.i_data(i_swb_data), .i_sel(i_swb_sel),
		// Slave/control wishbone outputs
		.o_stall(o_swb_stall),
		.o_ack(o_swb_ack), .o_data(o_swb_data),
		// }}}
		// Internal DMA controls
		// {{{
		.o_dma_request(dma_request), .o_dma_abort(dma_abort),
		.i_dma_busy(dma_busy),	.i_dma_err(dma_err),
		.o_src_addr(dma_src),	.o_dst_addr(dma_dst),
		.o_length(dma_length),	.o_transferlen(dma_transferlen),
		.o_mm2s_inc(mm2s_inc),	.o_mm2s_size(mm2s_size),
		.o_s2mm_inc(s2mm_inc),	.o_s2mm_size(s2mm_size),
		//
		.o_trigger(dma_trigger),
		//
		.i_current_src(read_addr),
		.i_current_dst(write_addr),
		.i_remaining_len(remaining_len),
		// }}}
		.i_dma_int(i_dev_ints), .o_interrupt(o_interrupt)
		// }}}
	);

	zipdma_fsm #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.LGDMALENGTH(ADDRESS_WIDTH),
		.LGSUBLENGTH(LGMEMLEN)
		// }}}
	) u_dma_fsm (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_soft_reset(dma_abort),
		// DMA control
		// {{{
		.i_dma_request(dma_request),
		.o_dma_busy(dma_busy),	.o_dma_err(dma_err),
		.i_src_addr(dma_src),	.i_dst_addr(dma_dst),
		.i_length(dma_length),	.i_transferlen(dma_transferlen),
		.i_trigger(dma_trigger),
		.o_remaining_len(remaining_len),
		// }}}
		// Downstream MM2S configuration
		// {{{
		.o_mm2s_request(mm2s_request),
		.i_mm2s_busy(mm2s_busy),
		.i_mm2s_err(mm2s_err),
		.i_mm2s_inc(mm2s_inc),
		.o_mm2s_addr(mm2s_addr),
		.o_mm2s_transferlen(mm2s_transferlen),
		// }}}
		// Downstream S2MM configuration
		// {{{
		.o_s2mm_request(s2mm_request),
		.i_s2mm_busy(s2mm_busy),
		.i_s2mm_err(s2mm_err),
		.i_s2mm_inc(s2mm_inc),
		.o_s2mm_addr(s2mm_addr),
		.o_s2mm_transferlen(s2mm_transferlen)
		// }}}
		// }}}
	);

	zipdma_mm2s #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.BUS_WIDTH(BUS_WIDTH),
		.LGLENGTH(LGMEMLEN),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) u_mm2s (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || dma_abort),
		// DMA control
		// {{{
		.i_request(mm2s_request),
		.o_busy(mm2s_busy),	.o_err(mm2s_err),
		.i_inc(mm2s_inc),	.i_size(mm2s_size),
		.i_transferlen(mm2s_transferlen),
		.i_addr(mm2s_addr),
		// }}}
		// Wishbone master interface
		// {{{
		.o_rd_cyc(mm2s_rd_cyc),
		.o_rd_stb(mm2s_rd_stb),
		.o_rd_we(mm2s_rd_we),
		.o_rd_addr(mm2s_rd_addr),
		.o_rd_data(mm2s_rd_data),
		.o_rd_sel(mm2s_rd_sel),
		//
		.i_rd_stall(mm2s_rd_stall),
		.i_rd_ack(mm2s_rd_ack),
		.i_rd_data(wb_idata),
		.i_rd_err(mm2s_rd_err),
		// }}}
		// MM2S Stream interface
		// {{{
		.M_VALID(mm2s_valid),
		.M_READY(mm2s_ready),
		.M_DATA(mm2s_data),
		.M_BYTES(mm2s_bytes),
		.M_LAST(mm2s_last)
		// }}}
		// }}}
	);

	zipdma_rxgears #(
		// {{{
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN)
		// }}}
	) u_rxgears (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_soft_reset(dma_abort),
		//
		.S_VALID(mm2s_valid), .S_READY(mm2s_ready),
		.S_DATA(mm2s_data), .S_BYTES(mm2s_bytes),
		.S_LAST(mm2s_last),
		//
		.M_VALID(rx_valid), .M_READY(rx_ready),
		.M_DATA(rx_data), .M_BYTES(rx_bytes),
		.M_LAST(rx_last)
		// }}}
	);

	sfifo #(
		// {{{
		.BW(FIFO_WIDTH),
		.LGFLEN(LGFIFO),
		.OPT_ASYNC_READ(!OPT_REGISTER_RAM),
		.OPT_WRITE_ON_FULL(1'b0),
		.OPT_READ_ON_EMPTY(1'b0)
		// }}}
	) u_sfifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || dma_abort),
		//
		.i_wr(rx_valid), .i_data({ rx_last, rx_bytes, rx_data }),
		.o_full(sfifo_full), .o_fill(ign_sfifo_fill),
		//
		.i_rd(tx_ready), .o_data({ tx_last, tx_bytes, tx_data }),
		.o_empty(sfifo_empty)
		// }}}
	);

	assign	rx_ready = !sfifo_full;
	assign	tx_valid = !sfifo_empty;

	zipdma_txgears #(
		// {{{
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN)
		// }}}
	) u_txgears (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_soft_reset(dma_abort), .i_size(s2mm_size),
		// Incoming stream
		// {{{
		.S_VALID(tx_valid),	.S_READY(tx_ready),
		.S_DATA(tx_data),	.S_BYTES(tx_bytes),
		.S_LAST(tx_last),
		// }}}
		// Outgoing stream to S2MM
		// {{{
		.M_VALID(s2mm_valid),	.M_READY(s2mm_ready),
		.M_DATA(s2mm_data),	.M_BYTES(s2mm_bytes),
		.M_LAST(s2mm_last)
		// }}}
		// }}}
	);

	zipdma_s2mm #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.LGPIPE(LGMEMLEN)
		// }}}
	) u_s2mm (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || dma_abort),
		// S2MM configuration
		// {{{
		.i_request(s2mm_request),
		.o_busy(s2mm_busy),	.o_err(s2mm_err),
		.i_inc(s2mm_inc),	.i_size(s2mm_size),
		.i_addr(s2mm_addr),
		// }}}
		// Stream data source
		// {{{
		.S_VALID(s2mm_valid),	.S_READY(s2mm_ready),
		.S_DATA(s2mm_data),	.S_BYTES(s2mm_bytes),
		.S_LAST(s2mm_last),
		// }}}
		// Outgoing Wishbone interface
		// {{{
		.o_wr_cyc(s2mm_wr_cyc),
		.o_wr_stb(s2mm_wr_stb),
		.o_wr_we(s2mm_wr_we),
		.o_wr_addr(s2mm_wr_addr),
		.o_wr_data(s2mm_wr_data),
		.o_wr_sel(s2mm_wr_sel),
		//
		.i_wr_stall(s2mm_wr_stall),
		.i_wr_ack(s2mm_wr_ack),
		.i_wr_data({(BUS_WIDTH){1'b0}}),
		.i_wr_err(s2mm_wr_err)
		// }}}
		// }}}
	);

	wbarbiter #(
		// {{{
		.DW(BUS_WIDTH), .AW(AW), .OPT_ZERO_ON_IDLE(OPT_LOWPOWER)
		// }}}
	) u_arbiter (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_a_cyc(mm2s_rd_cyc),		.i_a_stb(mm2s_rd_stb),
		.i_a_we(mm2s_rd_we),		.i_a_adr(mm2s_rd_addr),
		.i_a_dat((OPT_LOWPOWER) ? mm2s_rd_data : s2mm_wr_data),
						.i_a_sel(mm2s_rd_sel),
		.o_a_stall(mm2s_rd_stall),	.o_a_ack(mm2s_rd_ack),
		.o_a_err(mm2s_rd_err),
		//
		.i_b_cyc(s2mm_wr_cyc),		.i_b_stb(s2mm_wr_stb),
		.i_b_we(s2mm_wr_we),		.i_b_adr(s2mm_wr_addr),
		.i_b_dat(s2mm_wr_data),		.i_b_sel(s2mm_wr_sel),
		.o_b_stall(s2mm_wr_stall),	.o_b_ack(s2mm_wr_ack),
		.o_b_err(s2mm_wr_err),
		//
		.o_cyc(wb_cyc),			.o_stb(wb_stb),
		.o_we(wb_we),			.o_adr(wb_addr),
		.o_dat(wb_data),		.o_sel(wb_sel),
		.i_stall(wb_stall),		.i_ack(wb_ack),
		.i_err(wb_err)
		// }}}
	);

	assign	o_mwb_cyc  = wb_cyc;
	assign	o_mwb_stb  = wb_stb;
	assign	o_mwb_we   = wb_we;
	assign	o_mwb_addr = wb_addr;
	assign	o_mwb_data = wb_data;
	assign	o_mwb_sel  = wb_sel;
	assign	wb_stall   = i_mwb_stall;
	assign	wb_ack     = i_mwb_ack;
	assign	wb_idata   = i_mwb_data;
	assign	wb_err     = i_mwb_err;

	assign	read_addr  = { mm2s_rd_addr, {($clog2(BUS_WIDTH/8)){1'b0}} };
	assign	write_addr = { s2mm_wr_addr, {($clog2(BUS_WIDTH/8)){1'b0}} };

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_sfifo_fill, mm2s_rd_data, rx_ready,
				s2mm_transferlen };
	// verilator lint_on  UNUSED
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

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
`endif
// }}}
endmodule
