////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/axi2axilite.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Convert from AXI to AXI-lite with no performance loss.
//
// Performance:	The goal of this converter is to convert from AXI to AXI-lite
//		while still maintaining the one-clock per transaction speed
//	of AXI.  It currently achieves this goal.  The design needs very little
//	configuration to be useful, but you might wish to resize the FIFOs
//	within depending upon the length of your slave's data path.  The current
//	FIFO length, LGFIFO=4, is sufficient to maintain full speed.  If the
//	slave, however, can maintain full speed but requires a longer
//	processing cycle, then you may need longer FIFOs.
//
//	The AXI specification does require an additional 2 clocks per
//	transaction when using this core, so your latency will go up.
//
// Related:	There's a related axidouble.v core in the same repository as
//		well.  That can be used to convert the AXI protocol to something
//	simpler (even simpler than AXI-lite), but it can also do so for multiple
//	downstream slaves at the same time.
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
//
`default_nettype	none
// }}}
module axi2axilite #(
		// {{{
		parameter integer C_AXI_ID_WIDTH	= 2,
		parameter integer C_AXI_DATA_WIDTH	= 32,
		parameter integer C_AXI_ADDR_WIDTH	= 6,
		parameter	 [0:0]	OPT_WRITES	= 1,
		parameter	 [0:0]	OPT_READS	= 1,
		parameter	 [0:0]	OPT_LOWPOWER    = 0,
		// Log (based two) of the maximum number of outstanding AXI
		// (not AXI-lite) transactions.  If you multiply 2^LGFIFO * 256,
		// you'll get the maximum number of outstanding AXI-lite
		// transactions
		parameter	LGFIFO			= 4
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK,
		input	wire	S_AXI_ARESETN,
		// AXI4 slave interface
		// {{{
		// Write address channel
		// {{{
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_AWID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		input	wire	[7:0]			S_AXI_AWLEN,
		input	wire	[2:0]			S_AXI_AWSIZE,
		input	wire	[1:0]			S_AXI_AWBURST,
		input	wire				S_AXI_AWLOCK,
		input	wire	[3:0]			S_AXI_AWCACHE,
		input	wire	[2:0]			S_AXI_AWPROT,
		input	wire	[3:0]			S_AXI_AWQOS,
		// }}}
		// Write data channel
		// {{{
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire	[(C_AXI_DATA_WIDTH/8)-1:0] S_AXI_WSTRB,
		input	wire				S_AXI_WLAST,
		// }}}
		// Write return channel
		// {{{
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_BID,
		output	wire	[1:0]			S_AXI_BRESP,
		// }}}
		// Read address channel
		// {{{
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	S_AXI_ARID,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[7:0]			S_AXI_ARLEN,
		input	wire	[2:0]			S_AXI_ARSIZE,
		input	wire	[1:0]			S_AXI_ARBURST,
		input	wire				S_AXI_ARLOCK,
		input	wire	[3:0]			S_AXI_ARCACHE,
		input	wire	[2:0]			S_AXI_ARPROT,
		input	wire	[3:0]			S_AXI_ARQOS,
		// }}}
		// Read data channel
		// {{{
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0] S_AXI_RID,
		output	wire	[C_AXI_DATA_WIDTH-1:0] S_AXI_RDATA,
		output	wire	[1:0]			S_AXI_RRESP,
		output	wire				S_AXI_RLAST,
		// }}}
		// }}}
		// AXI-lite master interface
		// {{{
		// AXI-lite Write interface
		// {{{
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	wire	[2 : 0]			M_AXI_AWPROT,
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire	[(C_AXI_DATA_WIDTH/8)-1:0] M_AXI_WSTRB,
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		input	wire	[1 : 0]			M_AXI_BRESP,
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		// }}}
		// AXI-lite read interface
		// {{{
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire	[C_AXI_DATA_WIDTH-1 : 0] M_AXI_RDATA,
		input	wire	[1 : 0]			M_AXI_RRESP
		// }}}
		// }}}
		// }}}
	);

	// Local parameters, register, and net declarations
	// {{{
	localparam [1:0]	SLVERR = 2'b10;
	// localparam [1:0]	OKAY   = 2'b00,
	//			EXOKAY = 2'b01,
	//			DECERR = 2'b10;
	localparam	AW = C_AXI_ADDR_WIDTH;
	localparam	DW = C_AXI_DATA_WIDTH;
	localparam	IW = C_AXI_ID_WIDTH;
	// }}}
	// Register declarations
	// {{{
	//
	// Write registers
	wire				s_axi_wready;
	reg	[C_AXI_ADDR_WIDTH-1:0]	axi_awaddr;
	wire	[7:0]			axi_awlen;
	reg	[1:0]			axi_awburst;
	reg	[2:0]			axi_awsize;
	wire	[4:0]			wfifo_count;
	wire				wfifo_full;
	wire				wfifo_empty;
	wire	[7:0]			wfifo_bcount;
	wire	[IW-1:0]		wfifo_bid;
	wire	[8:0]			bcounts;
	wire				read_from_wrfifo;
	//
	// Read register
	wire	[4:0]			rfifo_count;
	wire				rfifo_full;
	wire				rfifo_empty;
	wire	[7:0]			axi_arlen;
	wire	[IW-1:0]		rid;

	//
	// S_AXI_AW* skid buffer
	wire			skids_awvalid, skids_awready;
	wire	[IW-1:0]	skids_awid;
	wire	[AW-1:0]	skids_awaddr;
	wire	[7:0]		skids_awlen;
	wire	[2:0]		skids_awsize;
	wire	[1:0]		skids_awburst;
	//
	// S_AXI_W* skid buffer
	wire			skids_wvalid, skids_wready, skids_wlast;
	wire	[DW-1:0]	skids_wdata;
	wire	[DW/8-1:0]	skids_wstrb;
	//
	// S_AXI_B* skid buffer isn't needed
	//
	// M_AXI_AW* skid buffer isn't needed
	//
	// M_AXI_W* skid buffer
	wire			skidm_wvalid, skidm_wready;
	wire	[DW-1:0]	skidm_wdata;
	wire	[DW/8-1:0]	skidm_wstrb;
	//
	// M_AXI_B* skid buffer
	wire			skidm_bvalid, skidm_bready;
	wire	[1:0]		skidm_bresp;
	//
	//
	//
	// S_AXI_AR* skid buffer
	wire			skids_arvalid, skids_arready;
	wire	[IW-1:0]	skids_arid;
	wire	[AW-1:0]	skids_araddr;
	wire	[7:0]		skids_arlen;
	wire	[2:0]		skids_arsize;
	wire	[1:0]		skids_arburst;
	//
	// S_AXI_R* skid buffer isn't needed
	//
	// M_AXI_AR* skid buffer isn't needed
	// M_AXI_R* skid buffer
	wire			skidm_rvalid, skidm_rready;
	wire	[DW-1:0]	skidm_rdata;
	wire	[1:0]		skidm_rresp;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_WRITES)
	begin : IMPLEMENT_WRITES
		// {{{
		reg				s_axi_bvalid;
		reg	[1:0]			r_axi_bresp;
		wire	[1:0]			axi_bresp;
		reg	[C_AXI_ID_WIDTH-1:0]	r_axi_bid, r_bid;
		wire	[C_AXI_ID_WIDTH-1:0]	axi_bid, bid;
		reg	[8:0]			r_bcounts;
		wire	[C_AXI_ADDR_WIDTH-1:0]	next_write_addr;
		reg	[7:0]			r_axi_awlen, axi_blen;
		reg				r_axi_wready;
		reg				m_axi_awvalid;

		// The write address channel's skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(IW+AW+8+3+2), .OPT_LOWPOWER(0), .OPT_OUTREG(0)
			// }}}
		) awskid(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			S_AXI_AWVALID, S_AXI_AWREADY,
			{ S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN, S_AXI_AWSIZE,
				S_AXI_AWBURST },
			skids_awvalid, skids_awready,
			{ skids_awid, skids_awaddr, skids_awlen, skids_awsize,
				skids_awburst }
			// }}}
		);
		// }}}
		//
		// The write data channel's skid buffer (S_AXI_W*)
		// {{{
		skidbuffer #(
			// {{{
			.DW(DW+DW/8+1), .OPT_LOWPOWER(0), .OPT_OUTREG(0)
			// }}}
		) wskid(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			S_AXI_WVALID, S_AXI_WREADY,
			{ S_AXI_WDATA, S_AXI_WSTRB, S_AXI_WLAST },
			skids_wvalid, skids_wready,
			{ skids_wdata, skids_wstrb, skids_wlast }
			// }}}
		);
		// }}}
		//
		// The downstream AXI-lite write data (M_AXI_W*) skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(DW+DW/8), .OPT_LOWPOWER(0), .OPT_OUTREG(1)
			// }}}
		) mwskid(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			skidm_wvalid, skidm_wready, { skidm_wdata, skidm_wstrb },
			M_AXI_WVALID,M_AXI_WREADY,{ M_AXI_WDATA, M_AXI_WSTRB }
			// }}}
		);
		// }}}
		//
		// The downstream AXI-lite response (M_AXI_B*) skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(2), .OPT_LOWPOWER(0), .OPT_OUTREG(0)
			// }}}
		) bskid(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			M_AXI_BVALID, M_AXI_BREADY, { M_AXI_BRESP },
			skidm_bvalid, skidm_bready, { skidm_bresp }
			// }}}
		);
		// }}}

		// m_axi_awvalid
		// {{{
		initial	m_axi_awvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_awvalid <= 0;
		else if (skids_awvalid & skids_awready)
			m_axi_awvalid <= 1;
		else if (M_AXI_AWREADY && axi_awlen == 0)
			m_axi_awvalid <= 0;

		assign	M_AXI_AWVALID = m_axi_awvalid;
		// }}}

		// skids_awready
		// {{{
		assign	skids_awready = (!M_AXI_AWVALID
				|| ((axi_awlen == 0)&&M_AXI_AWREADY))
				&& !wfifo_full
				&&(!s_axi_wready || (skids_wvalid && skids_wlast && skids_wready));
		// }}}

		// Address processing
		// {{{
		always @(posedge S_AXI_ACLK)
		if (skids_awvalid && skids_awready)
		begin
			axi_awaddr <= skids_awaddr;
			axi_blen   <= skids_awlen;
			axi_awburst<= skids_awburst;
			axi_awsize <= skids_awsize;
		end else if (M_AXI_AWVALID && M_AXI_AWREADY)
			axi_awaddr <= next_write_addr;
		// }}}

		// axi_awlen
		// {{{
		initial	r_axi_awlen = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_axi_awlen <= 0;
		else if (skids_awvalid && skids_awready)
			r_axi_awlen <= skids_awlen;
		else if (M_AXI_AWVALID && M_AXI_AWREADY && axi_awlen > 0)
			r_axi_awlen <= r_axi_awlen - 1;

		assign	axi_awlen = r_axi_awlen;
		// }}}

		// axi_addr
		// {{{
		axi_addr #(
			// {{{
			.AW(C_AXI_ADDR_WIDTH), .DW(C_AXI_DATA_WIDTH)
			// }}}
		) calcwraddr(
			// {{{
			axi_awaddr, axi_awsize, axi_awburst,
			axi_blen, next_write_addr
			// }}}
		);
		// }}}

		// s_axi_wready
		// {{{
		// We really don't need to do anything special to the write
		// channel.
		initial	r_axi_wready = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_axi_wready <= 0;
		else if (skids_awvalid && skids_awready)
			r_axi_wready <= 1;
		else if (skids_wvalid && skids_wready && skids_wlast)
			r_axi_wready <= 0;
		assign	s_axi_wready = r_axi_wready;
		// }}}

		// skidm*, and read_from_wrfifo
		// {{{
		assign	skidm_wdata  = skids_wdata;
		assign	skidm_wstrb  = skids_wstrb;
		assign	skidm_wvalid = skids_wvalid && s_axi_wready;
		assign	skids_wready = s_axi_wready && skidm_wready;

		assign	read_from_wrfifo = (bcounts <= 1)&&(!wfifo_empty)
			    &&(skidm_bvalid && skidm_bready);
		// }}}

		// BFIFO
		// {{{
		sfifo	#(
			.BW(C_AXI_ID_WIDTH+8), .LGFLEN(LGFIFO)
		) bidlnfifo(
			S_AXI_ACLK, !S_AXI_ARESETN,
			skids_awvalid && skids_awready,
			{ skids_awid, skids_awlen },
			wfifo_full, wfifo_count,
			read_from_wrfifo,
			{ wfifo_bid, wfifo_bcount }, wfifo_empty);
		// }}}

		// bcounts
		// {{{
		// Return counts
		initial	r_bcounts = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_bcounts <= 0;
		else if (read_from_wrfifo)
		begin
			r_bcounts <= wfifo_bcount + bcounts;
		end else if (skidm_bvalid && skidm_bready)
			r_bcounts <= bcounts - 1;
		assign	bcounts = r_bcounts;
		// }}}

		// bid
		// {{{
		always @(posedge S_AXI_ACLK)
		if (read_from_wrfifo)
			r_bid <= wfifo_bid;
		assign	bid = r_bid;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_BVALID || S_AXI_BREADY)
			r_axi_bid <= (read_from_wrfifo && bcounts==0) ? wfifo_bid : bid;
		assign	axi_bid = r_axi_bid;
		// }}}

		// s_axi_bvalid
		// {{{
		initial	s_axi_bvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_bvalid <= 0;
		else if (skidm_bvalid && skidm_bready)
			s_axi_bvalid <= (bcounts == 1)
				||((bcounts == 0) && (!wfifo_empty) && (wfifo_bcount == 0));
		else if (S_AXI_BREADY)
			s_axi_bvalid <= 0;
		// }}}

		// axi_bresp
		// {{{
		initial	r_axi_bresp = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_axi_bresp <= 0;
		else if (S_AXI_BVALID && S_AXI_BREADY)
		begin
			if (skidm_bvalid && skidm_bready)
				r_axi_bresp <= skidm_bresp;
			else
				r_axi_bresp <= 0;
		end else if (skidm_bvalid && skidm_bready)
		begin
			// Let SLVERR take priority over DECERR
			casez({ S_AXI_BRESP, skidm_bresp })
			4'b??0?: r_axi_bresp <= S_AXI_BRESP;
			4'b0?1?: r_axi_bresp <= skidm_bresp;
			4'b1?10: r_axi_bresp <= SLVERR;
			4'b1011: r_axi_bresp <= SLVERR;
			4'b1111: r_axi_bresp <= skidm_bresp;
			endcase
		end

		assign	axi_bresp = r_axi_bresp;
		// /}}}

		// M_AXI_AW*
		// {{{
		assign	M_AXI_AWVALID= m_axi_awvalid;
		assign	M_AXI_AWADDR = axi_awaddr;
		assign	M_AXI_AWPROT = 0;
		// }}}

		// skidm_bready, S_AXI_B*
		// {{{
		assign	skidm_bready = ((bcounts > 0)||(!wfifo_empty))&&(!S_AXI_BVALID | S_AXI_BREADY);
		assign	S_AXI_BID    = axi_bid;
		assign	S_AXI_BRESP  = axi_bresp;
		assign	S_AXI_BVALID = s_axi_bvalid;
		// }}}
		// }}}
	end else begin : NO_WRITE_SUPPORT
		// {{{
		assign	S_AXI_AWREADY = 0;
		assign	S_AXI_WREADY  = 0;
		assign	S_AXI_BID     = 0;
		assign	S_AXI_BRESP   = 2'b11;
		assign	S_AXI_BVALID  = 0;
		assign	S_AXI_BID     = 0;

		//
		assign	M_AXI_AWVALID = 0;
		assign	M_AXI_AWADDR  = 0;
		assign	M_AXI_AWPROT  = 0;
		//
		assign	M_AXI_WVALID  = 0;
		assign	M_AXI_WDATA   = 0;
		assign	M_AXI_WSTRB   = 0;
		//
		assign	M_AXI_BREADY  = 0;

		assign	axi_awaddr = 0;
		assign	axi_awlen  = 0;
		// Verilator lint_off WIDTH
		assign	axi_awsize = $clog2(C_AXI_DATA_WIDTH/8);
		// Verilator lint_on  WIDTH
		assign	axi_awburst= 2'b01;
		//
		// S_AXI_AW* skid buffer
		assign	skids_awvalid = 0;
		assign	skids_awready = 0;
		assign	skids_awid    = 0;
		assign	skids_awaddr  = 0;
		assign	skids_awlen   = 0;
		assign	skids_awsize  = 0;
		assign	skids_awburst = 0;
		//
		// S_AXI_W* skid buffer
		assign	skids_wvalid = S_AXI_WVALID;
		assign	skids_wready = S_AXI_WREADY;
		assign	skids_wdata  = S_AXI_WDATA;
		assign	skids_wstrb  = S_AXI_WSTRB;
		assign	skids_wlast  = S_AXI_WLAST;
		//
		// S_AXI_B* skid buffer isn't needed
		//
		// M_AXI_AW* skid buffer isn't needed
		//
		// M_AXI_W* skid buffer
		assign	skidm_wvalid = M_AXI_WVALID;
		assign	skidm_wready = M_AXI_WREADY;
		assign	skidm_wdata  = M_AXI_WDATA;
		assign	skidm_wstrb  = M_AXI_WSTRB;
		//
		// M_AXI_B* skid buffer
		assign	skidm_bvalid = M_AXI_BVALID;
		assign	skidm_bready = M_AXI_BREADY;
		assign	skidm_bresp  = M_AXI_BRESP;
		//
		//
		assign	s_axi_wready = 0;
		assign	axi_awlen    = 0;
		assign	bcounts = 0;

		assign	wfifo_full  = 0;
		assign	wfifo_empty = 1;
		assign	wfifo_bid   = 0;
		assign	wfifo_count = 0;
		assign	wfifo_bcount= 0;
		assign	read_from_wrfifo = 0;

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_write_signals;
		assign	unused_write_signals = &{ 1'b0,
				S_AXI_AWVALID, S_AXI_AWID, S_AXI_AWADDR,
					S_AXI_AWLEN,
					S_AXI_AWSIZE, S_AXI_AWBURST,
				M_AXI_AWREADY,
				M_AXI_WREADY, S_AXI_BREADY,
				M_AXI_BVALID, M_AXI_BREADY,
				read_from_wrfifo, wfifo_full,
				bcounts,
				wfifo_bcount, wfifo_bid, wfifo_empty,
				skidm_wvalid, skidm_wready, skidm_wdata,
					skidm_wstrb,
				s_axi_wready,
				axi_awaddr, axi_awlen, axi_awsize, axi_awburst,
				skids_awvalid, skids_awready, skids_awid,
					skids_awaddr, skids_awlen,
					skids_awburst, skids_awsize,
				skids_wvalid, skids_wready, skids_wdata,
					skids_wstrb,
				skidm_bvalid, skidm_bready, skidm_bresp
				};
		// Verilator lint_on  UNUSED
		// }}}

		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_READS)
	begin : IMPLEMENT_READS
		// {{{
		reg				m_axi_arvalid;
		reg	[C_AXI_ID_WIDTH-1:0]	s_axi_rid;
		wire	[C_AXI_ID_WIDTH-1:0]	rfifo_rid;
		reg	[IW-1:0]		r_rid;
		wire				read_from_rdfifo;
		reg	[C_AXI_DATA_WIDTH-1:0]	s_axi_rdata;
		reg				s_axi_rlast;
		reg	[C_AXI_ADDR_WIDTH-1:0]	axi_araddr;
		reg	[7:0]			r_axi_arlen, axi_rlen;
		reg	[1:0]			axi_arburst;
		reg	[2:0]			axi_arsize;
		wire	[C_AXI_ADDR_WIDTH-1:0]	next_read_addr;
		reg				s_axi_rvalid;
		reg	[1:0]			s_axi_rresp;
		reg	[8:0]			r_rcounts;
		wire	[8:0]			rcounts;
		wire	[7:0]			rfifo_rcount;

		// S_AXI_AR* skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(IW+AW+8+3+2), .OPT_LOWPOWER(0), .OPT_OUTREG(0)
			// }}}
		) arskid(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			S_AXI_ARVALID, S_AXI_ARREADY,
			{ S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN, S_AXI_ARSIZE,
				S_AXI_ARBURST },
			skids_arvalid, skids_arready,
			{ skids_arid, skids_araddr, skids_arlen, skids_arsize,
				skids_arburst }
			// }}}
		);
		// }}}
		// M_AXI_R* skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(DW+2), .OPT_LOWPOWER(0), .OPT_OUTREG(0)
			// }}}
		) rskid(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			M_AXI_RVALID, M_AXI_RREADY,{ M_AXI_RDATA, M_AXI_RRESP },
			skidm_rvalid,skidm_rready,{ skidm_rdata, skidm_rresp }
			// }}}
		);
		// }}}
		// m_axi_arvalid
		// {{{
		initial	m_axi_arvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_arvalid <= 0;
		else if (skids_arvalid && skids_arready)
			m_axi_arvalid <= 1;
		else if (M_AXI_ARREADY && axi_arlen == 0)
			m_axi_arvalid <= 0;
		// }}}

		// Read address processing
		// {{{
		always @(posedge S_AXI_ACLK)
		if (skids_arvalid && skids_arready)
		begin
			axi_araddr  <= skids_araddr;
			axi_arburst <= skids_arburst;
			axi_arsize  <= skids_arsize;
			axi_rlen    <= skids_arlen;
		end else if (M_AXI_ARREADY)
		begin
			axi_araddr <= next_read_addr;
			if (OPT_LOWPOWER && axi_arlen == 0)
				axi_araddr <= 0;
		end

		axi_addr #(
			// {{{
			.AW(C_AXI_ADDR_WIDTH), .DW(C_AXI_DATA_WIDTH)
			// }}}
		) calcrdaddr(
			// {{{
			axi_araddr, axi_arsize, axi_arburst,
			axi_rlen, next_read_addr
			// }}}
		);
		// }}}

		// axi_arlen, Read length processing
		// {{{
		initial	r_axi_arlen = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_axi_arlen <= 0;
		else if (skids_arvalid && skids_arready)
			r_axi_arlen <= skids_arlen;
		else if (M_AXI_ARVALID && M_AXI_ARREADY && axi_arlen > 0)
			r_axi_arlen <= axi_arlen - 1;

		assign	axi_arlen = r_axi_arlen;
		// }}}

		assign	skids_arready = (!M_AXI_ARVALID ||
				((axi_arlen == 0) && M_AXI_ARREADY))
				&& !rfifo_full;

		assign	read_from_rdfifo = skidm_rvalid && skidm_rready
					&& (rcounts <= 1) && !rfifo_empty;

		// Read ID FIFO
		// {{{
		sfifo	#(
			// {{{
			.BW(C_AXI_ID_WIDTH+8), .LGFLEN(LGFIFO)
			// }}}
		) ridlnfifo(
			// {{{
			S_AXI_ACLK, !S_AXI_ARESETN,
			skids_arvalid && skids_arready,
			{ skids_arid, skids_arlen },
			rfifo_full, rfifo_count,
			read_from_rdfifo,
			{ rfifo_rid, rfifo_rcount }, rfifo_empty
			// }}}
		);
		// }}}

		assign	skidm_rready = (!S_AXI_RVALID || S_AXI_RREADY);

		// s_axi_rvalid
		// {{{
		initial	s_axi_rvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_rvalid <= 0;
		else if (skidm_rvalid && skidm_rready)
			s_axi_rvalid <= 1;
		else if (S_AXI_RREADY)
			s_axi_rvalid <= 0;
		// }}}

		// s_axi_rresp, s_axi_rdata
		// {{{
		always @(posedge S_AXI_ACLK)
		if (skidm_rvalid && skidm_rready)
		begin
			s_axi_rresp <= skidm_rresp;
			s_axi_rdata <= skidm_rdata;
		end else if (S_AXI_RREADY)
		begin
			s_axi_rresp <= 0;
			s_axi_rdata <= 0;
		end
		// }}}

		// rcounts, Return counts
		// {{{
		initial	r_rcounts = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_rcounts <= 0;
		else if (read_from_rdfifo)
			r_rcounts <= rfifo_rcount + rcounts;
		else if (skidm_rvalid && skidm_rready)
			r_rcounts <= rcounts - 1;

		assign	rcounts = r_rcounts;
		// }}}

		// rid
		// {{{
		initial	r_rid = 0;
		always @(posedge S_AXI_ACLK)
		if (read_from_rdfifo)
			r_rid <= rfifo_rid;
		assign	rid = r_rid;
		// }}}

		// s_axi_rlast
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_RVALID || S_AXI_RREADY)
		begin
			// if (rcounts == 1) s_axi_rlast <= 1; else
			if (read_from_rdfifo)
				s_axi_rlast <= (rfifo_rcount == 0);
			else
				s_axi_rlast <= 0;

			if (rcounts == 1)
				s_axi_rlast <= 1;
		end
		// }}}

		// s_axi_rid
		// {{{
		initial	s_axi_rid = 0;
		always @(posedge S_AXI_ACLK)
		if ((S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST)
				||(!S_AXI_RVALID && rcounts == 0))
			s_axi_rid <= (read_from_rdfifo)&&(rcounts == 0)?rfifo_rid : rid;
		// }}}

		// M_AXI_AR*
		// {{{
		assign	M_AXI_ARVALID= m_axi_arvalid;
		assign	M_AXI_ARADDR = axi_araddr;
		assign	M_AXI_ARPROT = 0;
		// }}}
		// S_AXI_R*
		// {{{
		assign	S_AXI_RVALID = s_axi_rvalid;
		assign	S_AXI_RDATA  = s_axi_rdata;
		assign	S_AXI_RRESP  = s_axi_rresp;
		assign	S_AXI_RLAST  = s_axi_rlast;
		assign	S_AXI_RID    = s_axi_rid;
		// }}}
		// }}}
	end else begin : NO_READ_SUPPORT // if (!OPT_READS)
		// {{{
		assign	M_AXI_ARVALID= 0;
		assign	M_AXI_ARADDR = 0;
		assign	M_AXI_ARPROT = 0;
		assign	M_AXI_RREADY = 0;
		//
		assign	S_AXI_ARREADY= 0;
		assign	S_AXI_RVALID = 0;
		assign	S_AXI_RDATA  = 0;
		assign	S_AXI_RRESP  = 0;
		assign	S_AXI_RLAST  = 0;
		assign	S_AXI_RID    = 0;

		//
		assign	skids_arvalid = S_AXI_ARVALID;
		assign	skids_arready = S_AXI_ARREADY;
		assign	skids_arid    = S_AXI_ARID;
		assign	skids_araddr  = S_AXI_ARADDR;
		assign	skids_arlen   = S_AXI_ARLEN;
		assign	skids_arsize  = S_AXI_ARSIZE;
		assign	skids_arburst = S_AXI_ARBURST;
		//
		assign	skidm_rvalid  = M_AXI_RVALID;
		assign	skidm_rready  = M_AXI_RREADY;
		assign	skidm_rdata   = M_AXI_RDATA;
		assign	skidm_rresp   = M_AXI_RRESP;
		//
		//
		assign	axi_arlen = 0;
		// assign	rcounts   = 0;
		assign	rid       = 0;
		assign	rfifo_empty = 1;
		assign	rfifo_full  = 0;
		assign	rfifo_count = 0;

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_read_signals;
		assign	unused_read_signals = &{ 1'b0,
				rid, rfifo_empty, rfifo_count, rfifo_full,
				axi_arlen,
				skids_arvalid, skids_arready, skids_arid, skids_araddr, skids_arlen, skids_arsize, skids_arburst,
				skidm_rvalid, skidm_rready,
					skidm_rdata, skidm_rresp,
				M_AXI_ARREADY, S_AXI_RREADY };
		// Verilator lint_on  UNUSED
		// }}}

		// }}}
	end endgenerate
	// }}}
	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	[35-1:0]	unused;
	assign	unused = {
		S_AXI_AWLOCK, S_AXI_AWCACHE, S_AXI_AWPROT, S_AXI_AWQOS,
		skids_wlast, wfifo_count,
		S_AXI_ARLOCK, S_AXI_ARCACHE, S_AXI_ARPROT, S_AXI_ARQOS,
		rfifo_count };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
// The following are a subset of the formal properties used to verify this core
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = LGFIFO+1+8;

	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// AXI channel properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxi_slave #(.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(DW),
			.C_AXI_ADDR_WIDTH(AW),
			//
			)
		faxi(.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address
			.i_axi_awready(skids_awready),
			.i_axi_awid(   skids_awid),
			.i_axi_awaddr( skids_awaddr),
			.i_axi_awlen(  skids_awlen),
			.i_axi_awsize( skids_awsize),
			.i_axi_awburst(skids_awburst),
			.i_axi_awlock( 0),
			.i_axi_awcache(0),
			.i_axi_awprot( 0),
			.i_axi_awqos(  0),
			.i_axi_awvalid(skids_awvalid),
			// Write data
			.i_axi_wready( skids_wready),
			.i_axi_wdata(  skids_wdata),
			.i_axi_wstrb(  skids_wstrb),
			.i_axi_wlast(  skids_wlast),
			.i_axi_wvalid( skids_wvalid),
			// Write return response
			.i_axi_bid(    S_AXI_BID),
			.i_axi_bresp(  S_AXI_BRESP),
			.i_axi_bvalid( S_AXI_BVALID),
			.i_axi_bready( S_AXI_BREADY),
			// Read address
			.i_axi_arready(skids_arready),
			.i_axi_arid(   skids_arid),
			.i_axi_araddr( skids_araddr),
			.i_axi_arlen(  skids_arlen),
			.i_axi_arsize( skids_arsize),
			.i_axi_arburst(skids_arburst),
			.i_axi_arlock( 0),
			.i_axi_arcache(0),
			.i_axi_arprot( 0),
			.i_axi_arqos(  0),
			.i_axi_arvalid(skids_arvalid),
			// Read response
			.i_axi_rid(    S_AXI_RID),
			.i_axi_rresp(  S_AXI_RRESP),
			.i_axi_rvalid( S_AXI_RVALID),
			.i_axi_rdata(  S_AXI_RDATA),
			.i_axi_rlast(  S_AXI_RLAST),
			.i_axi_rready( S_AXI_RREADY),
			//
			// Formal property data
			.f_axi_awr_nbursts(   faxi_awr_nbursts),
			.f_axi_wr_pending(    faxi_wr_pending),
			.f_axi_rd_nbursts(    faxi_rd_nbursts),
			.f_axi_rd_outstanding(faxi_rd_outstanding),
			//
			// ...
			);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxil_master #(.C_AXI_DATA_WIDTH(DW), .C_AXI_ADDR_WIDTH(AW),
			.F_OPT_NO_RESET(1),
			.F_AXI_MAXWAIT(5),
			.F_AXI_MAXDELAY(4),
			.F_AXI_MAXRSTALL(0),
			.F_OPT_WRITE_ONLY(OPT_WRITES && !OPT_READS),
			.F_OPT_READ_ONLY(!OPT_WRITES &&  OPT_READS),
			.F_LGDEPTH(F_AXIL_LGDEPTH))
		faxil(.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address channel
			.i_axi_awvalid(M_AXI_AWVALID),
			.i_axi_awready(M_AXI_AWREADY),
			.i_axi_awaddr( M_AXI_AWADDR),
			.i_axi_awprot( M_AXI_AWPROT),
			// Write data
			.i_axi_wready( skidm_wready),
			.i_axi_wdata(  skidm_wdata),
			.i_axi_wstrb(  skidm_wstrb),
			.i_axi_wvalid( skidm_wvalid),
			// Write response
			.i_axi_bresp(  skidm_bresp),
			.i_axi_bvalid( skidm_bvalid),
			.i_axi_bready( skidm_bready),
			// Read address
			.i_axi_arvalid(M_AXI_ARVALID),
			.i_axi_arready(M_AXI_ARREADY),
			.i_axi_araddr( M_AXI_ARADDR),
			.i_axi_arprot( M_AXI_ARPROT),
			// Read data return
			.i_axi_rvalid( skidm_rvalid),
			.i_axi_rready( skidm_rready),
			.i_axi_rdata(  skidm_rdata),
			.i_axi_rresp(  skidm_rresp),
			//
			// Formal check variables
			.f_axi_rd_outstanding(faxil_rd_outstanding),
			.f_axi_wr_outstanding(faxil_wr_outstanding),
			.f_axi_awr_outstanding(faxil_awr_outstanding));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assume that the two write channels stay within an appropriate
	// distance of each other.  This is to make certain that the property
	// file features are not violated, although not necessary true for
	// actual operation
	//
	always @(*)
		assert(s_axi_wready == (OPT_WRITES && faxi_wr_pending > 0));

	////////////////////////////////////////////////////////////////////////
	//
	// Write induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// These are extra properties necessary to pass write induction
	//

	always @(*)
	if ((bcounts == 0)&&(!read_from_wrfifo))
		assert(!skidm_bvalid || !skidm_bready);

	always @(*)
	if (axi_awlen > 0)
	begin
		assert(m_axi_awvalid);
		if (axi_awlen > 1)
		begin
			assert(!skids_awready);
		end else if (wfifo_full)
		begin
			assert(!skids_awready);
		end else if (M_AXI_AWVALID && !M_AXI_AWREADY)
			assert(!skids_awready);
	end


	always @(*)
		assert(axi_bresp != EXOKAY);

	reg	[F_LGDEPTH-1:0]	f_wfifo_bursts, f_wfifo_bursts_minus_one,
				f_wfifo_within,
				f_wfiid_bursts, f_wfiid_bursts_minus_one;
	reg	[IW-1:0]	f_awid;
	always @(posedge S_AXI_ACLK)
	if (skids_awvalid && skids_awready)
		f_awid = skids_awid;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!S_AXI_RVALID && rcounts > 0)
		assert(rid == S_AXI_RID);

	always @(*)
	if (S_AXI_RVALID && !S_AXI_RLAST)
		assert(rid == S_AXI_RID);

	always @(*)
	if ((rcounts == 0)&&(!read_from_rdfifo))
		assert(!skidm_rvalid || !skidm_rready);

	always @(*)
	if (axi_arlen > 0)
	begin
		assert(m_axi_arvalid);
		assert(!skids_arready);
	end

	//
	// ...
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Select only write or only read operation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (!OPT_WRITES)
	begin
		always @(*)
		begin
			assume(!skids_awvalid);
			assume(!skids_wvalid);
			assert(M_AXI_AWVALID == 0);
			assert(faxil_awr_outstanding == 0);
			assert(faxil_wr_outstanding == 0);
			assert(!skidm_bvalid);
			assert(!S_AXI_BVALID);
		end
	end endgenerate

	generate if (!OPT_READS)
	begin

		always @(*)
		begin
			assume(!S_AXI_ARVALID);
			assert(M_AXI_ARVALID == 0);
			assert(faxil_rd_outstanding == 0);
		end

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover statements, to show performance
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_WRITES)
	begin
		// {{{
		reg	[3:0]	cvr_write_count, cvr_write_count_simple;

		initial	cvr_write_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_write_count_simple <= 0;
		else if (S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_AWLEN == 0)
			cvr_write_count_simple <= cvr_write_count_simple + 1;

		initial	cvr_write_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_write_count <= 0;
		else if (S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_AWLEN > 2)
			cvr_write_count <= cvr_write_count + 1;

		always @(*)
			cover(cvr_write_count_simple > 6 && /* ... */ !S_AXI_BVALID);
		always @(*)
			cover(cvr_write_count > 2 && /* ... */ !S_AXI_BVALID);
		// }}}
	end endgenerate

	generate if (OPT_READS)
	begin
		// {{{
		reg	[3:0]	cvr_read_count, cvr_read_count_simple;

		initial	cvr_read_count_simple = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_read_count_simple <= 0;
		else if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLEN == 0)
			cvr_read_count_simple <= cvr_read_count_simple + 1;

		initial	cvr_read_count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			cvr_read_count <= 0;
		else if (S_AXI_ARVALID && S_AXI_ARREADY && S_AXI_ARLEN > 2)
			cvr_read_count <= cvr_read_count + 1;

		always @(*)
			cover(cvr_read_count_simple > 6 && /* ... */ !S_AXI_RVALID);
		always @(*)
			cover(cvr_read_count > 2 && /* ... */ !S_AXI_RVALID);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// ...
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// }}}
`undef	BMC_ASSERT
`endif
// }}}
endmodule
