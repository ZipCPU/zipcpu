////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zaxdma.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	AXI DMA controller for the ZipCPU
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024-2024, Gisselquist Technology, LLC
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
module zaxdma #(
		// {{{
		parameter	ADDRESS_WIDTH=30, LGMEMLEN = 10,
		parameter	LGDMALENGTH=ADDRESS_WIDTH,
		parameter	BUS_WIDTH=512,
		parameter	IW=2,
		parameter	LGMAXBURST=LGMEMLEN-$clog2(BUS_WIDTH/8)-1,
		parameter [IW-1:0]	AXI_ID = 0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		localparam	AW=ADDRESS_WIDTH,
		localparam	DW=BUS_WIDTH
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Slave port
		// {{{
		input	wire		S_AXIL_AWVALID,
		output	wire		S_AXIL_AWREADY,
		input	wire	[3:0]	S_AXIL_AWADDR,
		input	wire	[2:0]	S_AXIL_AWPROT,
		//
		input	wire		S_AXIL_WVALID,
		output	wire		S_AXIL_WREADY,
		input	wire	[31:0]	S_AXIL_WDATA,
		input	wire	[3:0]	S_AXIL_WSTRB,
		//
		output	wire		S_AXIL_BVALID,
		input	wire		S_AXIL_BREADY,
		output	wire	[1:0]	S_AXIL_BRESP,
		//
		input	wire		S_AXIL_ARVALID,
		output	wire		S_AXIL_ARREADY,
		input	wire	[3:0]	S_AXIL_ARADDR,
		input	wire	[2:0]	S_AXIL_ARPROT,
		//
		output	wire		S_AXIL_RVALID,
		input	wire		S_AXIL_RREADY,
		output	wire	[31:0]	S_AXIL_RDATA,
		output	wire	[1:0]	S_AXIL_RRESP,
		// }}}
		// }}}
		// Master/DMA port
		// {{{
		output	wire			M_AXI_AWVALID,
		input	wire			M_AXI_AWREADY,
		output	wire	[IW-1:0]	M_AXI_AWID,
		output	wire	[AW-1:0]	M_AXI_AWADDR,
		output	wire	[7:0]		M_AXI_AWLEN,
		output	wire	[2:0]		M_AXI_AWSIZE,
		output	wire	[1:0]		M_AXI_AWBURST,
		output	wire			M_AXI_AWLOCK,
		output	wire	[3:0]		M_AXI_AWCACHE,
		output	wire	[2:0]		M_AXI_AWPROT,
		output	wire	[3:0]		M_AXI_AWQOS,
		//
		output	wire			M_AXI_WVALID,
		input	wire			M_AXI_WREADY,
		output	wire	[DW-1:0]	M_AXI_WDATA,
		output	wire	[DW/8-1:0]	M_AXI_WSTRB,
		output	wire	M_AXI_WLAST,
		//
		input	wire			M_AXI_BVALID,
		output	wire			M_AXI_BREADY,
		input	wire	[IW-1:0]	M_AXI_BID,
		input	wire	[1:0]		M_AXI_BRESP,
		//
		output	wire			M_AXI_ARVALID,
		input	wire			M_AXI_ARREADY,
		output	wire	[IW-1:0]	M_AXI_ARID,
		output	wire	[AW-1:0]	M_AXI_ARADDR,
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
		input	wire	[IW-1:0]	M_AXI_RID,
		input	wire	[DW-1:0]	M_AXI_RDATA,
		input	wire	[1:0]		M_AXI_RRESP,
		input	wire			M_AXI_RLAST,
		// }}}
		// The interrupt device interrupt lines
		input	wire [31:0]		i_dev_ints,
		// An interrupt to be set upon completion
		output	wire			o_interrupt
		// }}}
	);

	// Local declarations
	// {{{
	localparam	LGFIFO = LGMAXBURST+1;

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
	wire	[LGDMALENGTH-1:0]	mm2s_transferlen; // s2mm_transferlen;

	wire				mm2s_valid, mm2s_ready, mm2s_last;
	wire	[BUS_WIDTH-1:0]		mm2s_data;
	wire	[$clog2(BUS_WIDTH/8):0]	mm2s_bytes;

	wire			s2mm_valid, s2mm_ready, s2mm_last;
	wire	[BUS_WIDTH-1:0]	s2mm_data;
	wire	[$clog2(BUS_WIDTH/8):0]	s2mm_bytes;
	// }}}

	zaxdma_ctrl #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.LGMEMLEN(LGMEMLEN),
		.LGDMALENGTH(ADDRESS_WIDTH),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) u_controller (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// AXI-Lite control port
		// {{{
		.S_AXIL_AWVALID(S_AXIL_AWVALID),
		.S_AXIL_AWREADY(S_AXIL_AWREADY),
		.S_AXIL_AWADDR(S_AXIL_AWADDR),
		.S_AXIL_AWPROT(S_AXIL_AWPROT),
		//
		.S_AXIL_WVALID(S_AXIL_WVALID),
		.S_AXIL_WREADY(S_AXIL_WREADY),
		.S_AXIL_WDATA(S_AXIL_WDATA),
		.S_AXIL_WSTRB(S_AXIL_WSTRB),
		//
		.S_AXIL_BVALID(S_AXIL_BVALID),
		.S_AXIL_BREADY(S_AXIL_BREADY),
		.S_AXIL_BRESP(S_AXIL_BRESP),
		//
		.S_AXIL_ARVALID(S_AXIL_ARVALID),
		.S_AXIL_ARREADY(S_AXIL_ARREADY),
		.S_AXIL_ARADDR(S_AXIL_ARADDR),
		.S_AXIL_ARPROT(S_AXIL_ARPROT),
		//
		.S_AXIL_RVALID(S_AXIL_RVALID),
		.S_AXIL_RREADY(S_AXIL_RREADY),
		.S_AXIL_RDATA(S_AXIL_RDATA),
		.S_AXIL_RRESP(S_AXIL_RRESP),
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

	zaxdma_fsm #(
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
		.o_s2mm_addr(s2mm_addr)
		// .o_s2mm_transferlen(s2mm_transferlen)
		// }}}
		// }}}
	);

	zaxdma_mm2s #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.AXI_IW(IW),
		.AXI_ID(AXI_ID),
		.LGMAXBURST(LGMAXBURST),	// = 8
		.LGFIFO(LGFIFO),		// = 9
		.BUS_WIDTH(BUS_WIDTH),
		.LGLENGTH(LGDMALENGTH),
		// .OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.OPT_LOWPOWER(OPT_LOWPOWER)
		// }}}
	) u_mm2s (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_soft_reset(dma_abort),
		// DMA control
		// {{{
		.i_request(mm2s_request),
		.o_busy(mm2s_busy),	.o_err(mm2s_err),
		.i_inc(mm2s_inc),	.i_size(mm2s_size),
		.i_transferlen(mm2s_transferlen),
		.i_addr(mm2s_addr),
		// }}}
		// AXI master interface
		// {{{
		.M_AXI_ARVALID(M_AXI_ARVALID),
		.M_AXI_ARREADY(M_AXI_ARREADY),
		.M_AXI_ARID(M_AXI_ARID),
		.M_AXI_ARADDR(M_AXI_ARADDR),
		.M_AXI_ARLEN(M_AXI_ARLEN),
		.M_AXI_ARSIZE(M_AXI_ARSIZE),
		.M_AXI_ARBURST(M_AXI_ARBURST),
		.M_AXI_ARLOCK(M_AXI_ARLOCK),
		.M_AXI_ARCACHE(M_AXI_ARCACHE),
		.M_AXI_ARPROT(M_AXI_ARPROT),
		.M_AXI_ARQOS(M_AXI_ARQOS),
		//
		.M_AXI_RVALID(M_AXI_RVALID),
		.M_AXI_RREADY(M_AXI_RREADY),
		.M_AXI_RID(M_AXI_RID),
		.M_AXI_RDATA(M_AXI_RDATA),
		.M_AXI_RLAST(M_AXI_RLAST),
		.M_AXI_RRESP(M_AXI_RRESP),
		// }}}
		// MM2S Stream interface
		// {{{
		.M_AXIS_VALID(mm2s_valid),
		.M_AXIS_READY(mm2s_ready),
		.M_AXIS_DATA(mm2s_data),
		.M_AXIS_BYTES(mm2s_bytes),
		.M_AXIS_LAST(mm2s_last)
		// }}}
		// }}}
	);

	assign	s2mm_valid = mm2s_valid;
	assign	mm2s_ready = s2mm_ready;
	assign	s2mm_data  = mm2s_data;
	assign	s2mm_bytes = mm2s_bytes;
	assign	s2mm_last  = mm2s_last;

	zaxdma_s2mm #(
		// {{{
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.BUS_WIDTH(BUS_WIDTH),
		// .OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.LGFIFO(LGMEMLEN)
		// }}}
	) u_s2mm (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_soft_reset(dma_abort),
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
		.M_AWVALID(M_AXI_AWVALID),
		.M_AWREADY(M_AXI_AWREADY),
		.M_AWID(   M_AXI_AWID),
		.M_AWADDR( M_AXI_AWADDR),
		.M_AWLEN(  M_AXI_AWLEN),
		.M_AWSIZE( M_AXI_AWSIZE),
		.M_AWBURST(M_AXI_AWBURST),
		.M_AWLOCK( M_AXI_AWLOCK),
		.M_AWCACHE(M_AXI_AWCACHE),
		.M_AWPROT( M_AXI_AWPROT),
		.M_AWQOS(  M_AXI_AWQOS),
		//
		.M_WVALID(M_AXI_WVALID),
		.M_WREADY(M_AXI_WREADY),
		.M_WDATA(M_AXI_WDATA),
		.M_WSTRB(M_AXI_WSTRB),
		.M_WLAST(M_AXI_WLAST),
		//
		.M_BVALID(M_AXI_BVALID),
		.M_BREADY(M_AXI_BREADY),
		.M_BID(M_AXI_BID),
		.M_BRESP(M_AXI_BRESP)
		// }}}
		// }}}
	);

	assign	read_addr  = M_AXI_ARADDR;
	assign	write_addr = M_AXI_AWADDR;

	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// verilator lint_on  UNUSED
	// verilator coverage_on
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
