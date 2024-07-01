////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/rtl/axiempty.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A basic AXI core to provide a response to an AXI master when
//		no other slaves are connected to the bus.  All results are
//	bus errors.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
module axiempty #(
		// {{{
		parameter integer C_AXI_ID_WIDTH	= 2,
		parameter integer C_AXI_DATA_WIDTH	= 32,
		// Verilator lint_off UNUSED
		parameter integer C_AXI_ADDR_WIDTH	= 6
		// Verilator lint_on  UNUSED
		// Some useful short-hand definitions
		// localparam	AW = C_AXI_ADDR_WIDTH,
		// localparam	DW = C_AXI_DATA_WIDTH
		// }}}
	) (
		// {{{
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		//
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire [C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		//
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire				S_AXI_WLAST,
		//
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	wire [C_AXI_ID_WIDTH-1:0]	S_AXI_BID,
		output	wire	[1:0]			S_AXI_BRESP,
		//
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire [C_AXI_ID_WIDTH-1:0]	S_AXI_ARID,
		input	wire	[7:0]			S_AXI_ARLEN,
		//
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	wire [C_AXI_ID_WIDTH-1:0]	S_AXI_RID,
		output	wire [C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire				S_AXI_RLAST,
		output	wire	[1:0]			S_AXI_RRESP
		// }}}
	);

	localparam	IW = C_AXI_ID_WIDTH;
	// Double buffer the write response channel only
	reg	[IW-1 : 0]	axi_bid;
	reg			axi_bvalid;

	////////////////////////////////////////////////////////////////////////
	//
	// Write logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Start with the two skid buffers
	// {{{
	wire			m_awvalid, m_wvalid;
	wire			m_awready, m_wready, m_wlast;
	wire	[IW-1:0]	m_awid;
	//
	skidbuffer #(.DW(IW), .OPT_OUTREG(1'b0))
	awskd(S_AXI_ACLK, !S_AXI_ARESETN,
		S_AXI_AWVALID, S_AXI_AWREADY, S_AXI_AWID,
		m_awvalid, m_awready, m_awid );

	skidbuffer #(.DW(1), .OPT_OUTREG(1'b0))
	wskd(S_AXI_ACLK, !S_AXI_ARESETN,
		S_AXI_WVALID, S_AXI_WREADY, S_AXI_WLAST,
		m_wvalid, m_wready, m_wlast );
	// }}}

	// m_awready, m_wready
	// {{{
	// The logic here is pretty simple--accept a write address burst
	// into the skid buffer, then leave it there while the write data comes
	// on.  Once we get to the last write data element, accept both it and
	// the address.  This spares us the trouble of counting out the elements
	// in the write burst.
	//
	assign	m_awready= (m_awvalid && m_wvalid && m_wlast)
			&& (!S_AXI_BVALID || S_AXI_BREADY);
	assign	m_wready = !m_wlast || m_awready;
	// }}}

	// bvalid
	// {{{
	// As soon as m_awready above, a packet has come through successfully.
	// Acknowledge it with a bus error.
	//
	initial	axi_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_bvalid <= 1'b0;
	else if (m_awready)
		axi_bvalid <= 1'b1;
	else if (S_AXI_BREADY)
		axi_bvalid <= 1'b0;
	// }}}

	// bid
	// {{{
	always @(posedge S_AXI_ACLK)
	if (m_awready)
		axi_bid <= m_awid;
	// }}}

	assign	S_AXI_BVALID = axi_bvalid;
	assign	S_AXI_BID    = axi_bid;
	assign	S_AXI_BRESP  = 2'b11;	// An interconnect bus error
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read half
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[IW-1:0]	rid, axi_rid;
	reg			axi_arready, axi_rlast, axi_rvalid;
	reg	[8:0]		axi_rlen;

	// axi_arready
	// {{{
	initial axi_arready = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_arready <= 1;
	else if (S_AXI_ARVALID && S_AXI_ARREADY)
		axi_arready <= (S_AXI_ARLEN==0)&&(!S_AXI_RVALID|| S_AXI_RREADY);
	else if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		if ((!axi_arready)&&(S_AXI_RVALID))
			axi_arready <= (axi_rlen <= 2);
	end
	// }}}

	// axi_rlen
	// {{{
	initial	axi_rlen = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_rlen <= 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY)
		axi_rlen <= (S_AXI_ARLEN+1)
				+ ((S_AXI_RVALID && !S_AXI_RREADY) ? 1:0);
	else if (S_AXI_RREADY && S_AXI_RVALID)
		axi_rlen <= axi_rlen - 1;
	// }}}

	// rid
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARREADY)
		rid      <= S_AXI_ARID;
	// }}}

	// axi_rvalid
	// {{{
	initial	axi_rvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_rvalid <= 0;
	else if (S_AXI_ARVALID || (axi_rlen > 1))
		axi_rvalid <= 1;
	else if (S_AXI_RREADY)
		axi_rvalid <= 0;
	// }}}

	// axi_rid
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		if (S_AXI_ARVALID && S_AXI_ARREADY)
			axi_rid <= S_AXI_ARID;
		else
			axi_rid <= rid;
	end
	// }}}

	// axi_rlast
	// {{{
	initial axi_rlast   = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		if (S_AXI_ARVALID && S_AXI_ARREADY)
			axi_rlast <= (S_AXI_ARLEN == 0);
		else if (S_AXI_RVALID)
			axi_rlast <= (axi_rlen == 2);
		else
			axi_rlast <= (axi_rlen == 1);
	end
	// }}}

	//
	assign	S_AXI_ARREADY = axi_arready;
	assign	S_AXI_RVALID  = axi_rvalid;
	assign	S_AXI_RID     = axi_rid;
	assign	S_AXI_RDATA   = 0;
	assign	S_AXI_RRESP   = 2'b11;
	assign	S_AXI_RLAST   = axi_rlast;
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
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
	//
	// The following properties are only some of the properties used
	// to verify this core
	//
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	faxi_slave	#(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH)
		// }}}
	f_slave(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		// Address write channel
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awid(   S_AXI_AWID),
		.i_axi_awaddr( {(C_AXI_ADDR_WIDTH){1'b0}}),
		.i_axi_awlen(  S_AXI_AWLEN),
		.i_axi_awsize( LSB[2:0]),
		.i_axi_awburst(2'b0),
		.i_axi_awlock( 1'b0),
		.i_axi_awcache(4'h0),
		.i_axi_awprot( 3'h0),
		.i_axi_awqos(  4'h0),
	//
	//
		//
		// Write Data Channel
		//
		// Write Data
		.i_axi_wdata({(C_AXI_DATA_WIDTH){1'b0}}),
		.i_axi_wstrb({(C_AXI_DATA_WIDTH/8){1'b0}}),
		.i_axi_wlast(S_AXI_WLAST),
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
	//
	//
		// Response ID tag. This signal is the ID tag of the
		// write response.
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bid(   S_AXI_BID),
		.i_axi_bresp( S_AXI_BRESP),
	//
	//
		//
		// Read address channel
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_arid(   S_AXI_ARID),
		.i_axi_araddr( {(C_AXI_ADDR_WIDTH){1'b0}}),
		.i_axi_arlen(  S_AXI_ARLEN),
		.i_axi_arsize( LSB[2:0]),
		.i_axi_arburst(2'b00),
		.i_axi_arlock( 1'b0),
		.i_axi_arcache(4'h0),
		.i_axi_arprot( 3'h0),
		.i_axi_arqos(  4'h0),
	//
	//
		//
		// Read data return channel
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rid(S_AXI_RID),
		.i_axi_rdata(S_AXI_RDATA),
		.i_axi_rresp(S_AXI_RRESP),
		.i_axi_rlast(S_AXI_RLAST),
		//
		// ...
		// }}}
	);

	//

	////////////////////////////////////////////////////////////////////////
	//
	// Write induction properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{


	//
	// ...
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read induction properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	// ...
	//

	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $rose(S_AXI_RLAST))
		assert(S_AXI_ARREADY);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	//
	// ...
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg	f_wr_cvr_valid, f_rd_cvr_valid;

	initial	f_wr_cvr_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_wr_cvr_valid <= 0;
	else if (S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_AWLEN > 4)
		f_wr_cvr_valid <= 1;

	always @(*)
		cover(!S_AXI_BVALID && axi_awready && !m_awvalid
			&& f_wr_cvr_valid /* && ... */));

	initial	f_rd_cvr_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_rd_cvr_valid <= 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLEN > 4)
		f_rd_cvr_valid <= 1;

	always @(*)
		cover(S_AXI_ARREADY && f_rd_cvr_valid /* && ... */);

	//
	// Generate cover statements associated with multiple successive bursts
	//
	// These will be useful for demonstrating the throughput of the core.
	//
	reg	[4:0]	f_dbl_rd_count, f_dbl_wr_count;

	initial	f_dbl_wr_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_dbl_wr_count = 0;
	else if (S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_AWLEN == 3)
	begin
		if (!(&f_dbl_wr_count))
			f_dbl_wr_count <= f_dbl_wr_count + 1;
	end

	always @(*)
		cover(S_AXI_ARESETN && (f_dbl_wr_count > 1));	//!

	always @(*)
		cover(S_AXI_ARESETN && (f_dbl_wr_count > 3));	//!

	always @(*)
		cover(S_AXI_ARESETN && (f_dbl_wr_count > 3) && !m_awvalid
			&&(!S_AXI_AWVALID && !S_AXI_WVALID && !S_AXI_BVALID)
			&& (f_axi_awr_nbursts == 0)
			&& (f_axi_wr_pending == 0));	//!!

	initial	f_dbl_rd_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_dbl_rd_count = 0;
	else if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLEN == 3)
	begin
		if (!(&f_dbl_rd_count))
			f_dbl_rd_count <= f_dbl_rd_count + 1;
	end

	always @(*)
		cover(!S_AXI_ARESETN && (f_dbl_rd_count > 3)
			/* && ... */
			&& !S_AXI_ARVALID && !S_AXI_RVALID);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions necessary to pass a formal check
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// No limiting assumptions at present, check is currently full and
	// complete
	//
`endif
// }}}
endmodule
