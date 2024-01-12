///////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/axi2axilsub.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Convert from AXI to AXI-lite with no performance loss, and to
//		a potentially smaller bus width.
//
// Performance:	The goal of this converter is to convert from AXI to an AXI-lite
//		bus of a smaller width, while still maintaining the one-clock
//	per transaction speed of AXI.  It currently achieves this goal.  The
//	design needs very little configuration to be useful, but you might
//	wish to resize the FIFOs within depending upon the length of your
//	slave's data path.  The current FIFO length, LGFIFO=4, is sufficient to
//	maintain full speed.  If the slave, however, can maintain full speed but
//	requires a longer processing cycle, then you may need longer FIFOs.
//
//	The AXI specification does require an additional 2 clocks per
//	transaction when using this core, so your latency will go up.
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
//
`ifdef	FORMAL
`ifdef	BMC
`define	BMC_ASSERT	assert
`else
`define	BMC_ASSERT	assume
`endif
`endif
//
// }}}
module axi2axilsub #(
		// {{{
		parameter integer C_AXI_ID_WIDTH	= 2,
		parameter integer C_S_AXI_DATA_WIDTH	= 64,
		parameter integer C_M_AXI_DATA_WIDTH	= 32,
		parameter integer C_AXI_ADDR_WIDTH	= 6,
		parameter	 [0:0]	OPT_LOWPOWER	= 1,
		parameter	 [0:0]	OPT_WRITES	= 1,
		parameter	 [0:0]	OPT_READS	= 1,
		parameter		SLVSZ = $clog2(C_S_AXI_DATA_WIDTH/8),
		parameter		MSTSZ = $clog2(C_M_AXI_DATA_WIDTH/8),
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
		input	wire [C_S_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire [(C_S_AXI_DATA_WIDTH/8)-1:0] S_AXI_WSTRB,
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
		output	wire [C_AXI_ID_WIDTH-1:0]	S_AXI_RID,
		output	wire [C_S_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
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
		output	wire [C_M_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire [(C_M_AXI_DATA_WIDTH/8)-1:0] M_AXI_WSTRB,
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
		input	wire	[C_M_AXI_DATA_WIDTH-1 : 0] M_AXI_RDATA,
		input	wire	[1 : 0]			M_AXI_RRESP
		// }}}
		// }}}
		// }}}
	);

	// Local parameters, register, and net declarations
	// {{{
	// Verilator lint_off UNUSED
	localparam [1:0]	OKAY   = 2'b00,
				EXOKAY = 2'b01,
				SLVERR = 2'b10;
	// localparam [1:0]	DECERR = 2'b10;

	// Verilator lint_on UNUSED
	localparam	AW = C_AXI_ADDR_WIDTH;
	localparam	SLVDW = C_S_AXI_DATA_WIDTH;
	localparam	MSTDW = C_M_AXI_DATA_WIDTH;
	localparam	IW = C_AXI_ID_WIDTH;
	// localparam	LSB = $clog2(C_AXI_DATA_WIDTH)-3;
	// }}}
	// Register declarations
	// {{{
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_WRITES && SLVDW == MSTDW)
	begin : IMPLEMENT_AXI2AXILITE_WRITES
		// {{{

		// (Unused) signal declarations
		// {{{
		// Verilator lint_off UNUSED
		wire				ign_arready, ign_rvalid,
						ign_rlast,
						ign_arvalid, ign_rready;
		wire	[IW-1:0]		ign_rid;
		wire [SLVDW-1:0]	ign_rdata;
		wire	[1:0]			ign_rresp;
		wire	[AW-1:0]	ign_araddr;
		wire	[2:0]			ign_arprot;
		// Verilator lint_on  UNUSED
		// }}}

		axi2axilite #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.OPT_WRITES(1),
			.OPT_READS(0),
			.LGFIFO(LGFIFO)
			// }}}
		) axilwrite (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			// AXI4 slave interface
			// {{{
			// Write address channel
			// {{{
			.S_AXI_AWVALID(S_AXI_AWVALID),
			.S_AXI_AWREADY(S_AXI_AWREADY),
			.S_AXI_AWID(   S_AXI_AWID),
			.S_AXI_AWADDR( S_AXI_AWADDR),
			.S_AXI_AWLEN(  S_AXI_AWLEN),
			.S_AXI_AWSIZE( S_AXI_AWSIZE),
			.S_AXI_AWBURST(S_AXI_AWBURST),
			.S_AXI_AWLOCK( S_AXI_AWLOCK),
			.S_AXI_AWCACHE(S_AXI_AWCACHE),
			.S_AXI_AWPROT( S_AXI_AWPROT),
			.S_AXI_AWQOS(  S_AXI_AWQOS),
			// }}}
			// Write data channel
			// {{{
			.S_AXI_WVALID(S_AXI_WVALID),
			.S_AXI_WREADY(S_AXI_WREADY),
			.S_AXI_WDATA( S_AXI_WDATA),
			.S_AXI_WSTRB( S_AXI_WSTRB),
			.S_AXI_WLAST( S_AXI_WLAST),
			// }}}
			// Write return channel
			// {{{
			.S_AXI_BVALID(S_AXI_BVALID),
			.S_AXI_BREADY(S_AXI_BREADY),
			.S_AXI_BID(   S_AXI_BID),
			.S_AXI_BRESP( S_AXI_BRESP),
			// }}}
			// Read address channel
			// {{{
			.S_AXI_ARVALID(1'b0),
			.S_AXI_ARREADY(ign_arready),
			.S_AXI_ARID(   {(IW){1'b0}}),
			.S_AXI_ARADDR( {(AW){1'b0}}),
			.S_AXI_ARLEN(  8'h0),
			.S_AXI_ARSIZE( 3'h0),
			.S_AXI_ARBURST(2'h0),
			.S_AXI_ARLOCK( 1'b0),
			.S_AXI_ARCACHE(4'h0),
			.S_AXI_ARPROT( 3'h0),
			.S_AXI_ARQOS(  4'h0),
			// }}}
			// Read data channel
			// {{{
			.S_AXI_RVALID(ign_rvalid),
			.S_AXI_RREADY(1'b1),
			.S_AXI_RID(   ign_rid),
			.S_AXI_RDATA( ign_rdata),
			.S_AXI_RRESP( ign_rresp),
			.S_AXI_RLAST( ign_rlast),
			// }}}
			// }}}
			// AXI-lite master interface
			// {{{
			// AXI-lite Write interface
			// {{{
			.M_AXI_AWVALID(M_AXI_AWVALID),
			.M_AXI_AWREADY(M_AXI_AWREADY),
			.M_AXI_AWADDR(M_AXI_AWADDR),
			.M_AXI_AWPROT(M_AXI_AWPROT),
			//
			.M_AXI_WVALID(M_AXI_WVALID),
			.M_AXI_WREADY(M_AXI_WREADY),
			.M_AXI_WDATA(M_AXI_WDATA),
			.M_AXI_WSTRB(M_AXI_WSTRB),
			//
			.M_AXI_BVALID(M_AXI_BVALID),
			.M_AXI_BREADY(M_AXI_BREADY),
			.M_AXI_BRESP(M_AXI_BRESP),
			// }}}
			// AXI-lite read interface
			// {{{
			.M_AXI_ARVALID(ign_arvalid),
			.M_AXI_ARREADY(1'b1),
			.M_AXI_ARADDR(ign_araddr),
			.M_AXI_ARPROT(ign_arprot),
			//
			.M_AXI_RVALID(1'b0),
			.M_AXI_RREADY(ign_rready),
			.M_AXI_RDATA({(MSTDW){1'b0}}),
			.M_AXI_RRESP(2'b00)
			// }}}
			// }}}
			// }}}
		);

		// }}}
	end else begin : WDN
	if (OPT_WRITES)
	begin : IMPLEMENT_WRITES
		// {{{

		// Register declarations
		// {{{
		localparam	BIDFIFOBW = IW+1+(SLVSZ-MSTSZ+1);

		//
		// S_AXI_AW* skid buffer
		wire			skids_awvalid;
		wire			skids_awready;
		wire	[IW-1:0]	skids_awid;
		wire	[AW-1:0]	skids_awaddr;
		wire	[7:0]		skids_awlen;
		wire	[2:0]		skids_awsize;
		wire	[1:0]		skids_awburst;
		wire	[2:0]		skids_awprot;
		//
		// S_AXI_W* skid buffer
		wire			skids_wvalid, skids_wready;
		wire	[SLVDW-1:0]	skids_wdata;
		wire	[SLVDW/8-1:0]	skids_wstrb;

		wire			slv_awready, slv_wready;
		reg	[SLVDW-1:0]	slv_wdata;
		reg	[SLVDW/8-1:0]	slv_wstrb;

		reg	[IW-1:0]			slv_awid;
		reg	[AW-1:0]			slv_awaddr,
							slv_next_awaddr;
		reg	[2:0]				slv_awsize;
		reg	[1:0]				slv_awburst;
		reg	[7:0]				slv_awlen;
		reg	[8:0]				slv_wlen;
		reg					slv_awlast;

		// Write registers
		reg				m_axi_awvalid;
		reg				bfifo_write, wfifo_wlast;
		reg	[IW+1+SLVSZ-MSTSZ:0]	bfifo_wdata;
		wire	[LGFIFO:0]		wfifo_count;
		wire				wfifo_full;
		wire				wfifo_empty;
		wire	[SLVSZ-MSTSZ:0]		wfifo_subcount;
		wire	[IW-1:0]		wfifo_bid;
		reg	[SLVSZ-MSTSZ:0]		bcounts;
		reg	[IW-1:0]	s_axi_bid, bid;
		reg				blast;
		reg	[1:0]			s_axi_bresp, bresp;
		reg				s_axi_bvalid;
		reg				b_return_stall;
		wire				read_from_wrfifo;
		//
		// S_AXI_B* skid buffer isn't needed
		//
		// M_AXI_AW* skid buffer isn't needed
		//
		// M_AXI_W* skid buffer isn't needed
		//
		// M_AXI_B* skid buffer
		wire			skidm_bvalid, skidm_bready;
		wire	[1:0]		skidm_bresp;

		reg				m_axi_wvalid;
		reg	[AW-1:0]		mst_awaddr;
		reg	[2:0]			mst_awprot;
		reg	[SLVSZ-MSTSZ:0]		mst_awbeats,
						mst_wbeats, next_slv_beats;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Incoming write address / data handling
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		////////////////////////////////////////
		//
		// Clock #1: The skid buffer
		// {{{

		// The write address channel's skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(IW+AW+8+3+2+3),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) awskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWID, S_AXI_AWADDR, S_AXI_AWLEN,
				S_AXI_AWSIZE, S_AXI_AWBURST, S_AXI_AWPROT }),
			.o_valid(skids_awvalid), .i_ready(skids_awready),
			.o_data({ skids_awid, skids_awaddr, skids_awlen,
				skids_awsize, skids_awburst, skids_awprot })
			// }}}
		);
		// }}}
		//
		// The write data channel's skid buffer (S_AXI_W*)
		// {{{
		skidbuffer #(
			// {{{
			.DW(SLVDW+SLVDW/8),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) wskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
			.o_valid(skids_wvalid), .i_ready(skids_wready),
			.o_data({ skids_wdata, skids_wstrb })
			// }}}
		);
		// }}}

		assign	skids_awready = skids_wvalid && skids_wready
					&& slv_awlast;

		assign	skids_wready = slv_wready;
		// }}}
		////////////////////////////////////////
		//
		// Clock 2: slv_* clock
		// {{{

		// When are we ready for a next SLAVE beat?
		assign	slv_awready = (skids_wvalid && skids_wready);

		// slv_aw*
		// {{{
		// slv_awaddr is the address of the value *CURRENTLY* in the
		// buffer, *NOT* the next address.
		initial	slv_awlast = 1;
		always @(posedge S_AXI_ACLK)
		if (skids_awvalid && skids_awready)
		begin
			slv_awid    <= skids_awid;
			slv_awaddr  <= skids_awaddr;
			slv_awlen   <= skids_awlen;
			slv_awsize  <= skids_awsize;
			slv_awburst <= skids_awburst;
		end else if (slv_awready && slv_wlen > 0)
		begin
			// Step forward a full beat -- but only when we have
			// the data to do so
			slv_awaddr <= slv_next_awaddr;
		end
		// }}}

		// slv_awlast
		// {{{
		initial	slv_awlast = 1;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			slv_awlast <= 1;
		else if (skids_awvalid && skids_awready)
			slv_awlast  <= (skids_awlen == 0);
		else if (skids_wvalid && skids_wready)
			slv_awlast <= (slv_wlen <= 2);

`ifdef	FORMAL
		always @(*)
			assert(slv_awlast == (slv_wlen <= 1));
`endif
		// }}}

		// slv_wlen = Number of beats remaining
		// {{{
		// ... in the slave's data space, to include the one we've
		// just ingested.  Therefore, this is a 1-up counter.  If
		// slv_wlen == 0, then we are idle.
		initial	slv_wlen = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			slv_wlen <= 0;
		else if (skids_awvalid && skids_awready)
		begin
			slv_wlen <= skids_awlen + 1;
		end else if (skids_wvalid && skids_wready) // (slv_awready && slv_wlen > 0)
		begin
			slv_wlen <= slv_wlen - 1;
`ifdef	FORMAL
			assert(slv_wlen > 0);
`endif
		end else if (slv_wlen == 1 && slv_wready)
			slv_wlen <= 0;
		// }}}

		// next_slv_beats
		// {{{
		always @(*)
		begin
			// Verilator lint_off WIDTH
			next_slv_beats = (1<<(skids_awsize-MSTSZ[2:0]))
				  - (skids_awaddr[SLVSZ-1:0] >> skids_awsize);
			if (skids_awsize <= MSTSZ[2:0])
				next_slv_beats = 1;
			// Verilator lint_on  WIDTH
		end
		// }}}


		// slv_next_awaddr
		// {{{
		axi_addr #(
			// {{{
			.AW(AW),
			.DW(SLVDW)
			// }}}
		) get_next_slave_addr (
			// {{{
			.i_last_addr(slv_awaddr),
			.i_size(slv_awsize),
			.i_burst(slv_awburst),
			.i_len(slv_awlen),
			.o_next_addr(slv_next_awaddr)
			// }}}
		);
		// }}}

		assign	slv_wready = (mst_awbeats <= (M_AXI_AWREADY ? 1:0))
					&& (mst_wbeats <= (M_AXI_WREADY ? 1:0))
					&& (!bfifo_write || !wfifo_full);

		// slv_wstrb, slv_wdata
		// {{{
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			{ slv_wstrb, slv_wdata } <= 0;
		else if (skids_awready)
		begin
			slv_wstrb <= skids_wstrb >> (skids_awaddr[SLVSZ-1:MSTSZ]*MSTDW/8);
			slv_wdata <= skids_wdata >> (skids_awaddr[SLVSZ-1:MSTSZ]*MSTDW);
			if (OPT_LOWPOWER && !skids_awvalid)
			begin
				slv_wstrb <= 0;
				slv_wdata <= 0;
			end
		end else if (skids_wready)
		begin
			slv_wstrb <= skids_wstrb >> (slv_next_awaddr[SLVSZ-1:MSTSZ]*MSTDW/8);
			slv_wdata <= skids_wdata >> (slv_next_awaddr[SLVSZ-1:MSTSZ]*MSTDW);
			if (OPT_LOWPOWER && !skids_wvalid)
			begin
				slv_wstrb <= 0;
				slv_wdata <= 0;
			end
		end else if (M_AXI_WVALID && M_AXI_WREADY)
		begin
			slv_wstrb <= slv_wstrb >> (MSTDW/8);
			slv_wdata <= slv_wdata >> (MSTDW);
		end
		// }}}

		// }}}
		////////////////////////////////////////
		//
		// Clock 2 (continued): mst_* = M_AXI_*
		// {{{

		// mst_awaddr, mst_awprot, mst_awbeats
		// {{{
		initial	mst_awaddr = 0;
		initial	mst_awprot = 0;
		always @(posedge S_AXI_ACLK)
		begin
			if (!M_AXI_AWVALID || M_AXI_AWREADY)
			begin
				if (skids_awvalid && skids_awready)
				begin
					mst_awaddr <= skids_awaddr;
					mst_awprot <= skids_awprot;
					mst_awbeats<= next_slv_beats;
				end else if (skids_wvalid && skids_wready)
				begin
					mst_awaddr <= slv_next_awaddr;
					mst_awbeats<= 1;
					if (slv_awsize >= MSTSZ[2:0])
						mst_awbeats <= (1<<(slv_awsize - MSTSZ[2:0]));
				end else begin
					if (mst_awbeats > 1)
					begin
						mst_awaddr <= mst_awaddr + (1<<MSTSZ);
						mst_awaddr[MSTSZ-1:0] <= 0;
					end else if (OPT_LOWPOWER)
					begin
						mst_awaddr <= 0;
					end

					if (mst_awbeats > 0)
						mst_awbeats <= mst_awbeats - 1;
				end
			end

			if (!S_AXI_ARESETN)
			begin
				// {{{
				mst_awbeats <= 0;
				if (OPT_LOWPOWER)
				begin
					mst_awaddr  <= 0;
					mst_awprot  <= 0;
				end
				// }}}
			end
		end
`ifdef	FORMAL
		always @(*)
		if(S_AXI_ARESETN && OPT_LOWPOWER && mst_awbeats == 0)
		begin
			assert(mst_awaddr == 0);
		end

		always @(*)
		if (S_AXI_ARESETN)
			assert(m_axi_awvalid == (mst_awbeats > 0));
`endif
		// }}}

		// m_axi_awvalid
		// {{{
		initial	m_axi_awvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_awvalid <= 0;
		else if (!M_AXI_AWVALID || M_AXI_AWREADY)
		begin
			if (skids_wvalid && skids_wready)
				m_axi_awvalid <= 1'b1;
			else if (mst_awbeats == 1)
				m_axi_awvalid <= 1'b0;
		end
		// }}}

		assign	M_AXI_AWVALID = m_axi_awvalid;
		assign	M_AXI_AWVALID = m_axi_awvalid;
		assign	M_AXI_AWADDR  = mst_awaddr;
		assign	M_AXI_AWPROT  = mst_awprot;

		// M_AXI_WVALID, mst_wbeats
		// {{{
		initial	m_axi_wvalid = 0;
		initial	mst_wbeats   = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			m_axi_wvalid <= 0;
			mst_wbeats   <= 0;
		end else if (!M_AXI_WVALID || M_AXI_WREADY)
		begin
			if (skids_wvalid && skids_wready)
			begin
				m_axi_wvalid <= 1'b1;
				if (skids_awvalid && skids_awready)
					mst_wbeats   <= next_slv_beats;
				else if (slv_awsize <= MSTSZ[2:0])
					mst_wbeats <= 1;
				else
					mst_wbeats <= (1<<(slv_awsize - MSTSZ[2:0]));
			end else begin
				if (mst_wbeats <= 1)
					m_axi_wvalid <= 1'b0;
				if (mst_wbeats > 0)
					mst_wbeats   <= mst_wbeats - 1;
			end
		end
`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN)
			assert(M_AXI_WVALID == (mst_wbeats > 0));
`endif
		// }}}

		// M_AXI_WDATA, M_AXI_WSTRB
		// {{{
		assign	M_AXI_WDATA = slv_wdata[MSTDW-1:0];
		assign	M_AXI_WSTRB = slv_wstrb[MSTDW/8-1:0];
		// }}}

		assign	M_AXI_WVALID = m_axi_wvalid;
		assign	M_AXI_WDATA  = slv_wdata[MSTDW-1:0];
		assign	M_AXI_WSTRB  = slv_wstrb[MSTDW/8-1:0];
		// }}}
		////////////////////////////////////////
		//
		// Clock 3: The B FIFO
		// {{{

		// bfifo_write
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bfifo_write <= 0;
		else if (!bfifo_write || !wfifo_full)
			bfifo_write <= skids_wvalid && skids_wready;
		// }}}

		// bfifo_wdata
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bfifo_wdata <= 0;
		else if (skids_awvalid && skids_awready)
		begin
			bfifo_wdata[SLVSZ-MSTSZ:0] <= next_slv_beats;
			bfifo_wdata[SLVSZ-MSTSZ+1] <= (skids_awlen == 0);
			bfifo_wdata[SLVSZ-MSTSZ+2 +: IW] <= skids_awid;
`ifdef	FORMAL
			assert(skids_wvalid && skids_wready);
`endif
		end else if (skids_wvalid && skids_wready)
		begin
			bfifo_wdata[SLVSZ-MSTSZ+2 +: IW] <= slv_awid;
			bfifo_wdata[SLVSZ-MSTSZ+1] <= (slv_wlen <= 2)
						? 1'b1 : 1'b0;

			if (slv_awsize <= MSTSZ[2:0])
				bfifo_wdata[SLVSZ-MSTSZ:0] <= 1;
			else
				bfifo_wdata[SLVSZ-MSTSZ:0]
					<= (1<<(slv_awsize - MSTSZ[2:0]));
		end
		// }}}

		// BFIFO
		// {{{
		sfifo	#(
			// {{{
			.BW(BIDFIFOBW), .LGFLEN(LGFIFO)
			// }}}
		) bidlnfifo(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_wr(bfifo_write), .i_data(bfifo_wdata),
				.o_full(wfifo_full), .o_fill(wfifo_count),
			.i_rd(read_from_wrfifo),
			.o_data({ wfifo_bid, wfifo_wlast,wfifo_subcount }),
			.o_empty(wfifo_empty)
			// }}}
		);
		// }}}

		// read_from_wrfifo
		// {{{
		assign	read_from_wrfifo = (bcounts <= 1)&&(!wfifo_empty)
			    &&(skidm_bvalid && skidm_bready);
		// }}}
		// }}}
		////////////////////////////////////////
		//
		// Return clock 1: the skid buffer
		// {{{

		//
		// The downstream AXI-lite response (M_AXI_B*) skid buffer
		skidbuffer #(
			// {{{
			.DW(2),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) bskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(M_AXI_BVALID), .o_ready(M_AXI_BREADY),
				.i_data({ M_AXI_BRESP }),
			.o_valid(skidm_bvalid), .i_ready(skidm_bready),
				.o_data({ skidm_bresp })
			// }}}
		);

		assign	skidm_bready = ((bcounts > 0)||(!wfifo_empty))
				&& !b_return_stall;
		// }}}
		////////////////////////////////////////
		//
		// Return staging: Counting returns
		// {{{

		// bcounts
		// {{{
		// Return counts
		initial	bcounts = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bcounts <= 0;
		else if (skidm_bvalid && skidm_bready)
		begin
			if (read_from_wrfifo)
			begin
				/*
				if (bcounts == 0 && wfifo_subcount <= 1
						&& wfifo_wlast)
					// Go straight to S_AXI_BVALID, no
					// more bursts to count here
					bcounts <= 0;
				else
				*/
					bcounts <= wfifo_subcount + bcounts - 1;
			end else
				bcounts <= bcounts - 1;
		end
		// }}}

		// blast
		// {{{
		always @(posedge S_AXI_ACLK)
		if (read_from_wrfifo)
			blast <= wfifo_wlast;
		// }}}

		// bid
		// {{{
		always @(posedge S_AXI_ACLK)
		if (read_from_wrfifo)
			bid <= wfifo_bid;
		// }}}

		// bresp
		// {{{
		initial	bresp = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			bresp <= OKAY;
		else if (!S_AXI_BVALID || S_AXI_BREADY)
			bresp <= OKAY;
		else if (skidm_bvalid && skidm_bready)
		begin
			// Let SLVERR take priority over DECERR
			casez({ bresp, skidm_bresp })
			4'b??0?: bresp <= bresp;
			4'b0?1?: bresp <= skidm_bresp;
			4'b1?10: bresp <= SLVERR;
			4'b1011: bresp <= SLVERR;
			4'b1111: bresp <= skidm_bresp;
			endcase

			if (blast)
				bresp <= OKAY;
		end
		// }}}
		// }}}
		////////////////////////////////////////
		//
		// Return clock 2: S_AXI_* returns
		// {{{

		// s_axi_bid
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_BVALID || S_AXI_BREADY)
		begin
			if (bcounts > 0 && blast)
				s_axi_bid <= bid;
			else if (read_from_wrfifo)
				s_axi_bid <= wfifo_bid;
			else
				s_axi_bid <= bid;
		end
		// }}}

		// s_axi_bvalid, b_return_stall
		// {{{
		always @(*)
		begin
			// Force simulation evaluation on reset
			if (!S_AXI_ARESETN)
				b_return_stall = 0;

			// Default: stalled if the output is stalled
			b_return_stall = S_AXI_BVALID && !S_AXI_BREADY;

			if (bcounts > 1)
				b_return_stall = 0;
			else if (bcounts == 1 && !blast)
				b_return_stall = 0;
			else if (bcounts == 0
				&& (wfifo_subcount > 1 || !wfifo_wlast))
				b_return_stall = 0;
		end

		initial	s_axi_bvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_bvalid <= 0;
		else if (!S_AXI_BVALID || S_AXI_BREADY)
		begin
			s_axi_bvalid <= 0;
			if (skidm_bvalid && skidm_bready)
				s_axi_bvalid <= ((bcounts == 1)&& blast)
					||((bcounts == 0) && (!wfifo_empty)
						&& (wfifo_subcount <= 1)&& wfifo_wlast);
		end
		// }}}

		// s_axi_bresp
		// {{{
		initial	s_axi_bresp = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_bresp <= OKAY;
		else if (!S_AXI_BVALID || S_AXI_BREADY)
		begin
			if (skidm_bvalid && skidm_bready)
			begin
				// Let SLVERR take priority over DECERR
				casez({ bresp, skidm_bresp[1] })
				3'b??0: s_axi_bresp <= s_axi_bresp;
				3'b0?1: s_axi_bresp <= skidm_bresp;
				3'b101: s_axi_bresp <= SLVERR;
				3'b111: s_axi_bresp <= skidm_bresp;
				endcase
			end else
				s_axi_bresp <= bresp;
		end
		// }}}

		// S_AXI_B* assignments
		// {{{
		assign	S_AXI_BID    = s_axi_bid;
		assign	S_AXI_BRESP  = s_axi_bresp;
		assign	S_AXI_BVALID = s_axi_bvalid;
		// }}}
		// }}}
		// }}}
		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_write;
		assign	unused_write = &{ 1'b0, wfifo_count, S_AXI_WLAST };
		// Verilator lint_on  UNUSED
		// }}}
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		//
		// Formal properties, write half
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		// These are only a subset of the formal properties used to
		// verify this design.  While I will warrant that the full
		// property set will work, I don't really expect the below
		// properties to be sufficient or for that matter even
		// syntactically correct.
		//
		// Register declarations
		// {{{
		localparam	F_LGDEPTH = LGFIFO+1+8;

		wire	[F_LGDEPTH-1:0]		faxi_awr_nbursts;
		wire	[9-1:0]			faxi_wr_pending;
		wire	[F_LGDEPTH-1:0]		faxi_rd_nbursts;
		wire	[F_LGDEPTH-1:0]		faxi_rd_outstanding;

		//
		// ...
		//

		localparam	F_AXIL_LGDEPTH = F_LGDEPTH;
		wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
						faxil_wr_outstanding,
						faxil_awr_outstanding;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI channel properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxi_slave #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_LGDEPTH(F_AXIL_LGDEPTH),
			.OPT_EXCLUSIVE(0)
			// ...
			// }}}
		) faxi(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address
			// {{{
			.i_axi_awvalid(skids_awvalid),
			.i_axi_awready(skids_awready),
			.i_axi_awid(   skids_awid),
			.i_axi_awaddr( skids_awaddr),
			.i_axi_awlen(  skids_awlen),
			.i_axi_awsize( skids_awsize),
			.i_axi_awburst(skids_awburst),
			.i_axi_awlock( 0),
			.i_axi_awcache(0),
			.i_axi_awprot( skids_awprot),
			.i_axi_awqos(  0),
			// }}}
			// Write data
			// {{{
			.i_axi_wvalid( skids_wvalid),
			.i_axi_wready( skids_wready),
			.i_axi_wdata(  skids_wdata),
			.i_axi_wstrb(  skids_wstrb),
			.i_axi_wlast(  S_AXI_WLAST),
			// }}}
			// Write return response
			// {{{
			.i_axi_bvalid( S_AXI_BVALID),
			.i_axi_bready( S_AXI_BREADY),
			.i_axi_bid(    S_AXI_BID),
			.i_axi_bresp(  S_AXI_BRESP),
			// }}}
			// Read address
			// {{{
			.i_axi_arvalid(1'b0),
			.i_axi_arready(1'b0),
			.i_axi_arid(   skids_awid),
			.i_axi_araddr( skids_awaddr),
			.i_axi_arlen(  skids_awlen),
			.i_axi_arsize( skids_awsize),
			.i_axi_arburst(skids_awburst),
			.i_axi_arlock( 0),
			.i_axi_arcache(0),
			.i_axi_arprot( 0),
			.i_axi_arqos(  0),
			// }}}
			// Read response
			// {{{
			.i_axi_rvalid( 1'b0),
			.i_axi_rready( 1'b0),
			.i_axi_rid(    S_AXI_RID),
			.i_axi_rdata(  S_AXI_RDATA),
			.i_axi_rlast(  S_AXI_RLAST),
			.i_axi_rresp(  S_AXI_RRESP),
			// }}}
			// Formal property data
			// {{{
			.f_axi_awr_nbursts(   faxi_awr_nbursts),
			.f_axi_wr_pending(    faxi_wr_pending),
			.f_axi_rd_nbursts(    faxi_rd_nbursts),
			.f_axi_rd_outstanding(faxi_rd_outstanding)
			//
			// ...
			//
			// }}}
			// }}}
		);

		always @(*)
		begin
			// ...
			assert(faxi_rd_nbursts == 0);
		end

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI-lite properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		faxil_master #(
			// {{{
			.C_AXI_DATA_WIDTH(MSTDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_NO_RESET(1),
			.F_AXI_MAXWAIT(5),
			.F_AXI_MAXDELAY(4),
			.F_AXI_MAXRSTALL(0),
			.F_OPT_WRITE_ONLY(1),
			.F_OPT_READ_ONLY(1'b0),
			.F_LGDEPTH(F_AXIL_LGDEPTH)
			// }}}
		) faxil(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address channel
			// {{{
			.i_axi_awvalid(M_AXI_AWVALID),
			.i_axi_awready(M_AXI_AWREADY),
			.i_axi_awaddr( M_AXI_AWADDR),
			.i_axi_awprot( M_AXI_AWPROT),
			// }}}
			// Write data
			// {{{
			.i_axi_wvalid( M_AXI_WVALID),
			.i_axi_wready( M_AXI_WREADY),
			.i_axi_wdata(  M_AXI_WDATA),
			.i_axi_wstrb(  M_AXI_WSTRB),
			// }}}
			// Write response
			// {{{
			.i_axi_bvalid( skidm_bvalid),
			.i_axi_bready( skidm_bready),
			.i_axi_bresp(  skidm_bresp),
			// }}}
			// Read address
			// {{{
			.i_axi_arvalid(M_AXI_ARVALID),
			.i_axi_arready(M_AXI_ARREADY),
			.i_axi_araddr( M_AXI_ARADDR),
			.i_axi_arprot( M_AXI_ARPROT),
			// }}}
			// Read data return
			// {{{
			.i_axi_rvalid( 1'b0),
			.i_axi_rready( 1'b1),
			.i_axi_rdata(  {(C_M_AXI_DATA_WIDTH){1'b0}}),
			.i_axi_rresp(  2'b00),
			// }}}
			// Formal check variables
			// {{{
			.f_axi_rd_outstanding(faxil_rd_outstanding),
			.f_axi_wr_outstanding(faxil_wr_outstanding),
			.f_axi_awr_outstanding(faxil_awr_outstanding)
			// }}}
			// }}}
		);

		always @(*)
		if (S_AXI_ARESETN)
		begin
			assert(faxil_rd_outstanding == 0);

			assert(faxil_awr_outstanding
				+ ((mst_awbeats > 0) ? mst_awbeats : 0)
				== f_wfifo_beats
				+ (bfifo_write ? bfifo_wdata[SLVSZ-MSTSZ:0] : 0)
				+ bcounts);

			assert(faxil_wr_outstanding
				+ ((mst_wbeats > 0) ? mst_wbeats : 0)
				== f_wfifo_beats
				+ (bfifo_write ? bfifo_wdata[SLVSZ-MSTSZ:0] : 0)
				+ bcounts);
		end


		always @(*)
			assert(faxil_awr_outstanding <= { 1'b1, {(LGFIFO+8){1'b0}} } + bcounts);
		always @(*)
			assert(faxil_wr_outstanding  <= { 1'b1, {(LGFIFO+8){1'b0}} } + bcounts);

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// BFIFO property checking
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		//
		// ...
		//

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN)
		begin
			assert(faxi_awr_nbursts == f_bfifo_packets
				+ (slv_awvalid ? 1:0));
			assert(f_bfifo_packets <= wfifo_count);

			// ...
		end

		//
		// ...
		//

		// }}}
`endif
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
		// }}}
	end end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_READS && SLVDW == MSTDW)
	begin : IMPLEMENT_AXI2AXILITE_READS
		// {{{

		// (Unused) signal declarations
		// {{{
		// Verilator lint_off UNUSED
		wire				ign_awready, ign_wready,
						ign_bvalid;
		wire	[IW-1:0]	ign_bid;
		wire	[1:0]			ign_bresp;

		wire				ign_awvalid, ign_wvalid,
						ign_bready;
		wire	[AW-1:0]	ign_awaddr;
		wire	[2:0]			ign_awprot;
		wire	[MSTDW-1:0]	ign_wdata;
		wire	[MSTDW/8-1:0]	ign_wstrb;
		// Verilator lint_on  UNUSED
		// }}}

		axi2axilite #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.OPT_WRITES(0),
			.OPT_READS(1),
			.LGFIFO(LGFIFO)
			// }}}
		) axilread (
		// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),
			// AXI4 slave interface
			// {{{
			// Write address channel
			// {{{
			.S_AXI_AWVALID(1'b0),
			.S_AXI_AWREADY(ign_awready),
			.S_AXI_AWID(   {(IW){1'b0}} ),
			.S_AXI_AWADDR( {(AW){1'b0}} ),
			.S_AXI_AWLEN(  8'h0),
			.S_AXI_AWSIZE( 3'h0),
			.S_AXI_AWBURST(2'h0),
			.S_AXI_AWLOCK( 1'b0),
			.S_AXI_AWCACHE(4'h0),
			.S_AXI_AWPROT( 3'h0),
			.S_AXI_AWQOS(  4'h0),
			// }}}
			// Write data channel
			// {{{
			.S_AXI_WVALID(1'b0),
			.S_AXI_WREADY(ign_wready),
			.S_AXI_WDATA( {(SLVDW){1'b0}}),
			.S_AXI_WSTRB( {(SLVDW/8){1'b0}}),
			.S_AXI_WLAST( 1'b0),
			// }}}
			// Write return channel
			// {{{
			.S_AXI_BVALID(ign_bvalid),
			.S_AXI_BREADY(1'b1),
			.S_AXI_BID(   ign_bid),
			.S_AXI_BRESP( ign_bresp),
			// }}}
			// Read address channel
			// {{{
			.S_AXI_ARVALID(S_AXI_ARVALID),
			.S_AXI_ARREADY(S_AXI_ARREADY),
			.S_AXI_ARID(   S_AXI_ARID),
			.S_AXI_ARADDR( S_AXI_ARADDR),
			.S_AXI_ARLEN(  S_AXI_ARLEN),
			.S_AXI_ARSIZE( S_AXI_ARSIZE),
			.S_AXI_ARBURST(S_AXI_ARBURST),
			.S_AXI_ARLOCK( S_AXI_ARLOCK),
			.S_AXI_ARCACHE(S_AXI_ARCACHE),
			.S_AXI_ARPROT( S_AXI_ARPROT),
			.S_AXI_ARQOS(  S_AXI_ARQOS),
			// }}}
			// Read data channel
			// {{{
			.S_AXI_RVALID(S_AXI_RVALID),
			.S_AXI_RREADY(S_AXI_RREADY),
			.S_AXI_RID(   S_AXI_RID),
			.S_AXI_RDATA( S_AXI_RDATA),
			.S_AXI_RRESP( S_AXI_RRESP),
			.S_AXI_RLAST( S_AXI_RLAST),
			// }}}
			// }}}
			// AXI-lite master interface
			// {{{
			// AXI-lite Write interface
			// {{{
			.M_AXI_AWVALID(ign_awvalid),
			.M_AXI_AWREADY(1'b1),
			.M_AXI_AWADDR(ign_awaddr),
			.M_AXI_AWPROT(ign_awprot),
			//
			.M_AXI_WVALID(ign_wvalid),
			.M_AXI_WREADY(1'b1),
			.M_AXI_WDATA(ign_wdata),
			.M_AXI_WSTRB(ign_wstrb),
			//
			.M_AXI_BVALID(1'b0),
			.M_AXI_BREADY(ign_bready),
			.M_AXI_BRESP(2'b00),
			// }}}
			// AXI-lite read interface
			// {{{
			.M_AXI_ARVALID(M_AXI_ARVALID),
			.M_AXI_ARREADY(M_AXI_ARREADY),
			.M_AXI_ARADDR(M_AXI_ARADDR),
			.M_AXI_ARPROT(M_AXI_ARPROT),
			//
			.M_AXI_RVALID(M_AXI_RVALID),
			.M_AXI_RREADY(M_AXI_RREADY),
			.M_AXI_RDATA(M_AXI_RDATA),
			.M_AXI_RRESP(M_AXI_RRESP)
			// }}}
			// }}}
			// }}}
		);

		// }}}
	end else begin : RDN
	if (OPT_READS)
	begin : IMPLEMENT_READS
		// {{{

		// Declarations
		// {{{
		wire				slv_arvalid, slv_arready;
		reg	[IW-1:0]		slv_arid, mst_arid;
		reg	[AW-1:0]		slv_araddr, mst_araddr;
		wire	[AW-1:0]		slv_next_araddr;
		reg	[7:0]			slv_arlen;
		reg				slv_arlast, mst_arlast,
						mst_arsublast;
		reg	[2:0]			slv_arprot, mst_arprot;
		reg	[2:0]			slv_arsize;
		reg	[1:0]			slv_arburst;
		reg	[SLVSZ-MSTSZ:0]		slv_arbeats, mst_arbeats;
		reg	[8:0]			slv_rlen;

		wire	[SLVSZ-MSTSZ-1:0]	rfifo_addr;
		wire				rfifo_end_of_beat,
						rfifo_rlast;
		wire	[4:0]			rfifo_count;
		//
		reg				m_axi_arvalid;
		wire				rfifo_full;
		wire				rfifo_empty;
		reg				s_axi_rvalid;
		reg	[1:0]			s_axi_rresp;
		reg	[IW-1:0]		s_axi_rid;
		wire	[IW-1:0]		rfifo_rid;
		reg	[SLVDW-1:0]		s_axi_rdata, next_rdata;
		reg				s_axi_rlast;
		reg	[IW-1:0]		rid;
		wire				read_from_rdfifo;

		//
		//
		// S_AXI_AR* skid buffer
		wire			skids_arvalid, skids_arready;
		wire	[IW-1:0]	skids_arid;
		wire	[AW-1:0]	skids_araddr;
		wire	[7:0]		skids_arlen;
		wire	[2:0]		skids_arsize, skids_arprot;
		wire	[1:0]		skids_arburst;
		//
		// S_AXI_R* skid buffer isn't needed
		//
		// M_AXI_AR* skid buffer isn't needed
		// M_AXI_R* skid buffer
		wire			skidm_rvalid, skidm_rready;
		wire	[MSTDW-1:0]	skidm_rdata;
		wire	[1:0]		skidm_rresp;
		// }}}

		// S_AXI_AR* skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(IW+AW+8+3+2+3),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) arskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data({ S_AXI_ARID, S_AXI_ARADDR, S_AXI_ARLEN,
				S_AXI_ARSIZE, S_AXI_ARBURST, S_AXI_ARPROT }),
			.o_valid(skids_arvalid), .i_ready(skids_arready),
			.o_data({ skids_arid, skids_araddr, skids_arlen,
				skids_arsize, skids_arburst, skids_arprot })
			// }}}
		);
		// }}}
		// M_AXI_R* skid buffer
		// {{{
		skidbuffer #(
			// {{{
			.DW(MSTDW+2),
			.OPT_LOWPOWER(OPT_LOWPOWER),
			.OPT_OUTREG(0)
			// }}}
		) rskid(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(M_AXI_RVALID), .o_ready(M_AXI_RREADY),
				.i_data({ M_AXI_RDATA, M_AXI_RRESP }),
			.o_valid(skidm_rvalid), .i_ready(skidm_rready),
				.o_data({ skidm_rdata, skidm_rresp })
			// }}}
		);
		// }}}

		assign	skids_arready = (slv_rlen <= (slv_arready ? 1:0))
					&&(mst_arbeats <=(M_AXI_ARREADY ? 1:0));

		// slv_*
		// {{{
		always @(posedge S_AXI_ACLK)
		begin
			if (OPT_LOWPOWER && (slv_rlen <= (slv_arready ? 1:0)))
			begin
				// {{{
				slv_arid    <= 0;
				slv_araddr  <= 0;
				slv_arlen   <= 0;
				slv_arsize  <= 0;
				slv_arburst <= 0;
				slv_arprot  <= 0;

				slv_rlen    <= 0;
				// }}}
			end

			if (skids_arvalid && skids_arready)
			begin
				// {{{
				slv_arid    <= skids_arid;
				slv_araddr  <= skids_araddr;
				slv_arlen   <= skids_arlen;
				slv_arsize  <= skids_arsize;
				slv_arburst <= skids_arburst;
				slv_arlast  <= (skids_arlen == 0);
				slv_arprot  <= skids_arprot;

				slv_rlen    <= skids_arlen+1;
				// }}}
			end else if (slv_arready && slv_rlen > 0)
			begin
				// {{{
				slv_araddr  <= (!OPT_LOWPOWER || slv_rlen > 1)
							? slv_next_araddr : 0;
				slv_rlen    <= slv_rlen - 1;
				slv_arlast  <= (slv_rlen <= 2);
				// }}}
			end

			if (OPT_LOWPOWER && !S_AXI_ARESETN)
			begin
				// {{{
				slv_arid    <= 0;
				slv_araddr  <= 0;
				slv_arlen   <= 0;
				slv_arsize  <= 0;
				slv_arburst <= 0;
				slv_arprot  <= 0;

				slv_arlast  <= 1;
				// }}}
			end

			if (!S_AXI_ARESETN)
				slv_rlen <= 0;
		end

		assign	slv_arvalid = (slv_rlen > 0);
`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN)
		begin
			assert(slv_arlast == (slv_rlen <= 1));
			assert(slv_rlen <= (slv_arlen + 1));
		end
`endif
		// }}}

		// slv_next_araddr
		// {{{
		axi_addr #(
			// {{{
			.AW(AW),
			.DW(SLVDW)
			// }}}
		) get_next_slave_addr (
			// {{{
			.i_last_addr(slv_araddr),
			.i_size(slv_arsize),
			.i_burst(slv_arburst),
			.i_len(slv_arlen),
			.o_next_addr(slv_next_araddr)
			// }}}
		);
		// }}}

		// slv_arbeats
		// {{{
		always @(*)
		if (slv_rlen > 0)
		begin
			// Master beats to turn this slave beat into
			if (slv_arsize >= MSTSZ[2:0])
				slv_arbeats = (1<<(slv_arsize-MSTSZ[2:0]))
					- (slv_araddr[MSTSZ-1:0] >> slv_arsize);
			else
				slv_arbeats = 1;
		end else
			slv_arbeats = 0;
		// }}}

		// mst_araddr, mst_arprot, mst_arbeats
		// {{{
		always @(posedge S_AXI_ACLK)
		begin
			if (slv_arready)
			begin
				// {{{
				mst_arid    <= slv_arid;
				mst_araddr  <= slv_araddr;
				mst_arprot  <= slv_arprot;

				// Beats to turn this beat into
				mst_arbeats <= slv_arbeats;
				mst_arlast  <= slv_arlast;
				mst_arsublast <= (slv_arbeats <= 1);

				if (OPT_LOWPOWER && slv_rlen == 0)
				begin
					mst_arid   <= 0;
					mst_araddr <= 0;
					mst_arprot <= 0;
				end
				// }}}
			end else if ((mst_arbeats > 0)
					&&(M_AXI_ARVALID && M_AXI_ARREADY))
			begin
				// {{{
				mst_araddr <= mst_araddr + (1<<MSTSZ);
				mst_araddr[MSTSZ-1:0] <= 0;
				mst_arbeats <= mst_arbeats - 1;

				mst_arsublast <= (mst_arbeats <= 2);
				// }}}
			end

			if (!S_AXI_ARESETN)
			begin
				// {{{
				mst_arbeats <= 0;
				if (OPT_LOWPOWER)
				begin
					mst_arid    <= 0;
					mst_araddr  <= 0;
					mst_arprot  <= 0;
				end
				// }}}
			end
		end
`ifdef	FORMAL
		always @(*)
		if(OPT_LOWPOWER && S_AXI_ARESETN && mst_arbeats == 0)
		begin
			assert(mst_arid   == 0);
			assert(mst_araddr == 0);
			assert(mst_arprot == 0);
		end
`endif
		// }}}

		// m_axi_arvalid
		// {{{
		initial	m_axi_arvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_axi_arvalid <= 0;
		else if (slv_arvalid && slv_arready)
			m_axi_arvalid <= 1;
		else if (M_AXI_ARVALID && M_AXI_ARREADY)
			m_axi_arvalid <= (mst_arbeats > 1);

		assign	M_AXI_ARVALID = m_axi_arvalid;
`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN)
			assert(M_AXI_ARVALID == (mst_arbeats > 0));
`endif
		// }}}

		assign	slv_arready = (mst_arbeats <= (M_AXI_ARREADY ? 1:0));
		assign	read_from_rdfifo = skidm_rvalid && skidm_rready
					&&(!S_AXI_RVALID || S_AXI_RREADY);

		// Read ID FIFO
		// {{{
		sfifo	#(
			// {{{
			.BW(IW+2+SLVSZ-MSTSZ),
			.LGFLEN(LGFIFO)
			// }}}
		) ridlnfifo(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			//
			.i_wr(M_AXI_ARVALID && M_AXI_ARREADY),
			.i_data({ mst_arid, mst_arlast, mst_arsublast,
				M_AXI_ARADDR[SLVSZ-1:MSTSZ] }),
			.o_full(rfifo_full), .o_fill(rfifo_count),
			//
			.i_rd(read_from_rdfifo),
			.o_data({ rfifo_rid, rfifo_rlast, rfifo_end_of_beat,
				rfifo_addr }),
			.o_empty(rfifo_empty)
			// }}}
		);
		// }}}

		assign	skidm_rready = (!S_AXI_RVALID || S_AXI_RREADY)
				&& !rfifo_empty;

		// s_axi_rvalid
		// {{{
		initial	s_axi_rvalid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_rvalid <= 0;
		else if (skidm_rvalid && skidm_rready && rfifo_end_of_beat)
			s_axi_rvalid <= 1'b1;
		else if (S_AXI_RREADY)
			s_axi_rvalid <= 0;
		// }}}

		// s_axi_rdata
		// {{{
		always @(*)
		begin
			next_rdata = s_axi_rdata;
			if (S_AXI_RVALID)
				next_rdata = 0;
			if (skidm_rvalid)
				next_rdata = next_rdata | ({ {(SLVDW-MSTDW){1'b0}}, skidm_rdata } << (rfifo_addr * MSTDW));
		end

		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
			s_axi_rdata <= 0;
		else if (!S_AXI_RVALID || S_AXI_RREADY)
			s_axi_rdata <= next_rdata;
		// }}}

		// s_axi_rresp
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_axi_rresp <= OKAY;
		else if (!S_AXI_RVALID || S_AXI_RREADY)
		begin
			if (S_AXI_RVALID)
				s_axi_rresp <= (skidm_rvalid) ? skidm_rresp : OKAY;
			else if (skidm_rvalid)
			casez({ s_axi_rresp, skidm_rresp[1] })
			// Let SLVERR take priority over DECERR
			3'b??0: s_axi_rresp <= s_axi_rresp;
			3'b0?1: s_axi_rresp <= skidm_rresp;
			3'b101: s_axi_rresp <= SLVERR;
			3'b111: s_axi_rresp <= skidm_rresp;
			endcase
		end
		// }}}

		// rid
		// {{{
		initial	rid = 0;
		always @(posedge S_AXI_ACLK)
		if (read_from_rdfifo)
			rid <= rfifo_rid;
		// }}}

		// s_axi_rlast
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_RVALID || S_AXI_RREADY)
		begin
			if (read_from_rdfifo)
				s_axi_rlast <= rfifo_rlast;
			else
				s_axi_rlast <= 0;
		end
		// }}}

		// s_axi_rid
		// {{{
		initial	s_axi_rid = 0;
		always @(posedge S_AXI_ACLK)
		if ((S_AXI_RVALID && S_AXI_RREADY && S_AXI_RLAST)
				||(!S_AXI_RVALID && rfifo_end_of_beat))
			s_axi_rid <= (read_from_rdfifo && rfifo_end_of_beat)?rfifo_rid : rid;
		// }}}

		// M_AXI_AR*
		// {{{
		assign	M_AXI_ARVALID= m_axi_arvalid;
		assign	M_AXI_ARADDR = mst_araddr;
		assign	M_AXI_ARPROT = mst_arprot;
		// }}}
		// S_AXI_R*
		// {{{
		assign	S_AXI_RVALID = s_axi_rvalid;
		assign	S_AXI_RDATA  = s_axi_rdata;
		assign	S_AXI_RRESP  = s_axi_rresp;
		assign	S_AXI_RLAST  = s_axi_rlast;
		assign	S_AXI_RID    = s_axi_rid;
		// }}}
		// Make Verilator happy
		// {{{
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_read;
		assign	unused_read = &{ 1'b0,
				/*
				S_AXI_AWID, S_AXI_AWVALID,
				S_AXI_AWLEN, S_AXI_AWBURST, S_AXI_AWSIZE,
				S_AXI_AWADDR,
				S_AXI_WVALID, S_AXI_WDATA, S_AXI_WSTRB,
				S_AXI_WLAST, S_AXI_BREADY,
				M_AXI_AWREADY, M_AXI_WREADY,
				M_AXI_BRESP, M_AXI_BVALID,
				*/
				rfifo_count, rfifo_full
				};
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		//
		// Formal properties, read half
		// {{{
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////
`ifdef	FORMAL
		// As with the write half, the following is a subset of the
		// formal properties used to verify this section of the core.
		// It may, or may not, be syntactically correct.  I don't
		// warrant this version of the design.
		//
		// Register declarations
		// {{{
		localparam	F_LGDEPTH = LGFIFO+1+8;

		wire	[F_LGDEPTH-1:0]		faxi_awr_nbursts;
		wire	[9-1:0]			faxi_wr_pending;
		wire	[F_LGDEPTH-1:0]		faxi_rd_nbursts;
		wire	[F_LGDEPTH-1:0]		faxi_rd_outstanding;

		//
		// ...
		//

		localparam	F_AXIL_LGDEPTH = F_LGDEPTH;
		wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
						faxil_wr_outstanding,
						faxil_awr_outstanding;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI channel properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxi_slave #(
			// {{{
			.C_AXI_ID_WIDTH(IW),
			.C_AXI_DATA_WIDTH(SLVDW),
			.C_AXI_ADDR_WIDTH(AW),
			.OPT_EXCLUSIVE(0)
			// ...
			// }}}
		) faxi(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address
			// {{{
			.i_axi_awvalid(1'b0),
			.i_axi_awready(1'b0),
			.i_axi_awid(   skids_arid),
			.i_axi_awaddr( skids_araddr),
			.i_axi_awlen(  8'h0),
			.i_axi_awsize( 3'h0),
			.i_axi_awburst(2'h0),
			.i_axi_awlock( 0),
			.i_axi_awcache(0),
			.i_axi_awprot( 0),
			.i_axi_awqos(  0),
			// }}}
			// Write data
			// {{{
			.i_axi_wvalid( 1'b0),
			.i_axi_wready( 1'b0),
			.i_axi_wdata(  {(C_S_AXI_DATA_WIDTH  ){1'b0}}),
			.i_axi_wstrb(  {(C_S_AXI_DATA_WIDTH/8){1'b0}}),
			.i_axi_wlast(  1'b0),
			// }}}
			// Write return response
			// {{{
			.i_axi_bvalid( 1'b0),
			.i_axi_bready( 1'b0),
			.i_axi_bid(    S_AXI_BID),
			.i_axi_bresp(  2'b00),
			// }}}
			// Read address
			// {{{
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
			// }}}
			// Read response
			// {{{
			.i_axi_rid(    S_AXI_RID),
			.i_axi_rresp(  S_AXI_RRESP),
			.i_axi_rvalid( S_AXI_RVALID),
			.i_axi_rdata(  S_AXI_RDATA),
			.i_axi_rlast(  S_AXI_RLAST),
			.i_axi_rready( S_AXI_RREADY),
			// }}}
			// Formal property data
			// {{{
			.f_axi_awr_nbursts(   faxi_awr_nbursts),
			.f_axi_wr_pending(    faxi_wr_pending),
			.f_axi_rd_nbursts(    faxi_rd_nbursts),
			.f_axi_rd_outstanding(faxi_rd_outstanding),
			//
			// ...
			//
			// }}}
			// }}}
		);

		always @(*)
		begin
			assert(faxi_awr_nbursts == 0);
			assert(faxi_wr_pending == 0);
			assert(faxi_wr_ckvalid == 0);
		end
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// AXI-lite properties
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//
		faxil_master #(
			// {{{
			.C_AXI_DATA_WIDTH(MSTDW),
			.C_AXI_ADDR_WIDTH(AW),
			.F_OPT_NO_RESET(1),
			.F_AXI_MAXWAIT(5),
			.F_AXI_MAXDELAY(4),
			.F_AXI_MAXRSTALL(0),
			.F_OPT_WRITE_ONLY(1'b0),
			.F_OPT_READ_ONLY(1'b1),
			.F_LGDEPTH(F_AXIL_LGDEPTH)
			// }}}
		) faxil(
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			// Write address channel
			// {{{
			.i_axi_awvalid(1'b0),
			.i_axi_awready(1'b0),
			.i_axi_awaddr( M_AXI_AWADDR),
			.i_axi_awprot( 3'h0),
			// }}}
			// Write data
			// {{{
			.i_axi_wvalid( 1'b0),
			.i_axi_wready( 1'b0),
			.i_axi_wdata(  {(C_M_AXI_DATA_WIDTH  ){1'b0}}),
			.i_axi_wstrb(  {(C_M_AXI_DATA_WIDTH/8){1'b0}}),
			// }}}
			// Write response
			// {{{
			.i_axi_bvalid( 1'b0),
			.i_axi_bready( 1'b0),
			.i_axi_bresp(  2'b00),
			// }}}
			// Read address
			// {{{
			.i_axi_arvalid(M_AXI_ARVALID),
			.i_axi_arready(M_AXI_ARREADY),
			.i_axi_araddr( M_AXI_ARADDR),
			.i_axi_arprot( M_AXI_ARPROT),
			// }}}
			// Read data return
			// {{{
			.i_axi_rvalid( skidm_rvalid),
			.i_axi_rready( skidm_rready),
			.i_axi_rdata(  skidm_rdata),
			.i_axi_rresp(  skidm_rresp),
			// }}}
			// Formal check variables
			// {{{
			.f_axi_rd_outstanding(faxil_rd_outstanding),
			.f_axi_wr_outstanding(faxil_wr_outstanding),
			.f_axi_awr_outstanding(faxil_awr_outstanding)
			// }}}
			// }}}
		);

		always @(*)
		begin
			assert(faxil_awr_outstanding == 0);
			assert(faxil_wr_outstanding == 0);
		end
		// }}}
`endif
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

		// Make Verilator happy
		// Verilator coverage_off
		// Verilator lint_off UNUSED
		wire	unused_read;
		assign	unused_read = &{ 1'b0, M_AXI_ARREADY, M_AXI_RVALID,
				M_AXI_RDATA, M_AXI_RRESP, S_AXI_RREADY,
				S_AXI_ARLEN, S_AXI_ARSIZE, S_AXI_ARBURST,
				S_AXI_ARADDR, S_AXI_ARVALID, S_AXI_ARID
				};
		// Verilator lint_on  UNUSED
		// Verilator coverage_on
		// }}}
	end end endgenerate
	// }}}
	// Minimal parameter validation
	// {{{
	initial begin
		if (SLVDW < MSTDW)
		begin
			$fatal;		// Fatal elaboration error
			$stop;		// Stop any simulation
		end
	end
	// }}}
	// Make Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0,
		S_AXI_AWLOCK, S_AXI_AWCACHE, S_AXI_AWPROT, S_AXI_AWQOS,
		// skids_wlast, wfifo_count, rfifo_count
		S_AXI_ARLOCK, S_AXI_ARCACHE, S_AXI_ARPROT, S_AXI_ARQOS
		};
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
	////////////////////////////////////////////////////////////////////////
	//
	// Assume that the two write channels stay within an appropriate
	// distance of each other.  This is to make certain that the property
	// file features are not violated, although not necessary true for
	// actual operation
	//

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
			assume(!S_AXI_AWVALID);
			assume(!S_AXI_WVALID);
			assert(!M_AXI_AWVALID);
			assert(!M_AXI_WVALID);
			assume(!M_AXI_BVALID);
			assert(!S_AXI_BVALID);
		end
	end endgenerate

	generate if (!OPT_READS)
	begin

		always @(*)
		begin
			assume(!S_AXI_ARVALID);
			assert(!M_AXI_ARVALID);
		end

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Lowpower assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_LOWPOWER)
	begin : F_LOWPOWER

		always @(*)
		if (S_AXI_ARESETN)
		begin
			if (!M_AXI_AWVALID)
			begin
				// Not supported.
				// assert(M_AXI_AWADDR == 0);
				// assert(M_AXI_AWPROT == 0);
			end

			if (!M_AXI_WVALID)
			begin
				// assert(M_AXI_WDATA == 0);
				// assert(M_AXI_WSTRB == 0);
			end

			if (!M_AXI_ARVALID)
			begin
				assert(M_AXI_ARADDR == 0);
				assert(M_AXI_ARPROT == 0);
			end

			if (!S_AXI_RVALID)
			begin
				// These items build over the course of a
				// returned burst, so they might not be
				// zero when RVALID is zero.
				//
				// assert(S_AXI_RLAST == 0);
				// assert(S_AXI_RDATA == 0);
				// assert(S_AXI_RID == 0);
			end
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

		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// }}}
`undef	BMC_ASSERT
`endif
// }}}
endmodule
