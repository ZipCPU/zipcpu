////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/axilite2axi.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
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
`default_nettype none
// }}}
module axilite2axi #(
		// {{{
		parameter	C_AXI_ID_WIDTH	= 4,
				C_AXI_ADDR_WIDTH= 32,
				C_AXI_DATA_WIDTH= 32,
		parameter [C_AXI_ID_WIDTH-1:0]	C_AXI_WRITE_ID = 0,
						C_AXI_READ_ID = 0
		// }}}
	) (
		// {{{
		input	wire				ACLK,
		input	wire				ARESETN,
		// Slave AXI interface
		// {{{
		// Slave write signals
		input	wire				S_AXI_AWVALID,
		output	wire				S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_AWADDR,
		// Verilator coverage_off
		input	wire	[3-1:0]			S_AXI_AWPROT,
		// Verilator coverage_on
		// Slave write data signals
		input	wire				S_AXI_WVALID,
		output	wire				S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0] S_AXI_WSTRB,
		// Slave return write response
		output	wire				S_AXI_BVALID,
		input	wire				S_AXI_BREADY,
		output	wire	[2-1:0]			S_AXI_BRESP,
		// Slave read signals
		input	wire				S_AXI_ARVALID,
		output	wire				S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]	S_AXI_ARADDR,
		input	wire	[3-1:0]			S_AXI_ARPROT,
		// Slave read data signals
		output	wire				S_AXI_RVALID,
		input	wire				S_AXI_RREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	S_AXI_RDATA,
		output	wire	[2-1:0]			S_AXI_RRESP,
		// }}}
		// Master AXI interface
		// {{{
		// Master interface write address
		output	wire				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		// Verilator coverage_off
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_AWID,
		// Verilator coverage_on
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		// Verilator coverage_off
		output	wire	[8-1:0]			M_AXI_AWLEN,
		output	wire	[3-1:0]			M_AXI_AWSIZE,
		output	wire	[2-1:0]			M_AXI_AWBURST,
		output	wire				M_AXI_AWLOCK,
		output	wire	[4-1:0]			M_AXI_AWCACHE,
		output	wire	[3-1:0]			M_AXI_AWPROT,
		output	wire	[4-1:0]			M_AXI_AWQOS,
		// Verilator coverage_on
		// Master write data
		output	wire				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	wire	[C_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		// Master write response
		input	wire				M_AXI_BVALID,
		output	wire				M_AXI_BREADY,
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_BID,
		// Verilator coverage_off
		input	wire	[1:0]			M_AXI_BRESP,
		// Verilator coverage_on
		// Master interface read address
		output	wire				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_ARID,
		output	wire	[C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		// Verilator coverage_off
		output	wire	[8-1:0]			M_AXI_ARLEN,
		output	wire	[3-1:0]			M_AXI_ARSIZE,
		output	wire	[2-1:0]			M_AXI_ARBURST,
		output	wire				M_AXI_ARLOCK,
		output	wire	[4-1:0]			M_AXI_ARCACHE,
		output	wire	[3-1:0]			M_AXI_ARPROT,
		output	wire	[4-1:0]			M_AXI_ARQOS,
		// Verilator coverage_on
		// Master interface read data return
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		// Verilator coverage_off
		input	wire	[C_AXI_ID_WIDTH-1:0]	M_AXI_RID,
		// Verilator coverage_on
		input	wire	[C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[2-1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3;
	assign	M_AXI_AWID    = C_AXI_WRITE_ID;
	assign	M_AXI_AWADDR  = S_AXI_AWADDR;
	assign	M_AXI_AWLEN   = 0;
	assign	M_AXI_AWSIZE  = ADDRLSB[2:0];
	assign	M_AXI_AWBURST = 0;
	assign	M_AXI_AWLOCK  = 0;
	assign	M_AXI_AWCACHE = 4'b0011; // As recommended by Xilinx UG1037
	assign	M_AXI_AWPROT  = S_AXI_AWPROT;
	assign	M_AXI_AWQOS   = 0;
	assign	M_AXI_AWVALID = S_AXI_AWVALID;
	assign	S_AXI_AWREADY = M_AXI_AWREADY;
	// Master write data
	assign	M_AXI_WDATA   = S_AXI_WDATA;
	assign	M_AXI_WLAST   = 1;
	assign	M_AXI_WSTRB   = S_AXI_WSTRB;
	assign	M_AXI_WVALID  = S_AXI_WVALID;
	assign	S_AXI_WREADY  = M_AXI_WREADY;
	// Master write response
	assign	S_AXI_BRESP   = M_AXI_BRESP;
	assign	S_AXI_BVALID  = M_AXI_BVALID;
	assign	M_AXI_BREADY  = S_AXI_BREADY;
	//
	//
	assign	M_AXI_ARID    = C_AXI_READ_ID;
	assign	M_AXI_ARADDR  = S_AXI_ARADDR;
	assign	M_AXI_ARLEN   = 0;
	assign	M_AXI_ARSIZE  = ADDRLSB[2:0];
	assign	M_AXI_ARBURST = 0;
	assign	M_AXI_ARLOCK  = 0;
	assign	M_AXI_ARCACHE = 4'b0011; // As recommended by Xilinx UG1037
	assign	M_AXI_ARPROT  = S_AXI_ARPROT;
	assign	M_AXI_ARQOS   = 0;
	assign	M_AXI_ARVALID = S_AXI_ARVALID;
	assign	S_AXI_ARREADY = M_AXI_ARREADY;
	//
	assign	S_AXI_RDATA   = M_AXI_RDATA;
	assign	S_AXI_RRESP   = M_AXI_RRESP;
	assign	S_AXI_RVALID  = M_AXI_RVALID;
	assign	M_AXI_RREADY  = S_AXI_RREADY;

	// Make Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ACLK, ARESETN, M_AXI_RLAST, M_AXI_RID, M_AXI_BID };
	// Verilator lint_on UNUSED
	// Verilator coverage_on
	// }}}

`ifdef	FORMAL
	//
	// The following are some of the properties used to verify this design
	//

	localparam	F_LGDEPTH = 10;

	wire	[F_LGDEPTH-1:0]	faxil_awr_outstanding,
				faxil_wr_outstanding, faxil_rd_outstanding;

	faxil_slave #(
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.F_LGDEPTH(10),
			.F_AXI_MAXRSTALL(4),
			.F_AXI_MAXWAIT(9),
			.F_AXI_MAXDELAY(0)
	) faxil(.i_clk(ACLK), .i_axi_reset_n(ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awprot( S_AXI_AWPROT),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata( S_AXI_WDATA),
		.i_axi_wstrb( S_AXI_WSTRB),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bresp( S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr( S_AXI_ARADDR),
		.i_axi_arprot( S_AXI_ARPROT),
		//
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rdata( S_AXI_RDATA),
		.i_axi_rresp( S_AXI_RRESP),
		//
		.f_axi_awr_outstanding(faxil_awr_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_rd_outstanding(faxil_rd_outstanding));

	//
	// ...
	//

	faxi_master #(
			.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
			.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
			.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
			.OPT_MAXBURST(0),
			.OPT_EXCLUSIVE(1'b0),
			.OPT_NARROW_BURST(1'b0),
			.F_OPT_NO_RESET(1'b1),
			.F_LGDEPTH(10),
			.F_AXI_MAXSTALL(4),
			.F_AXI_MAXRSTALL(0),
			.F_AXI_MAXDELAY(4)
	) faxi(.i_clk(ACLK), .i_axi_reset_n(ARESETN),
		//
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awid(   M_AXI_AWID),
		.i_axi_awaddr( M_AXI_AWADDR),
		.i_axi_awlen(  M_AXI_AWLEN),
		.i_axi_awsize( M_AXI_AWSIZE),
		.i_axi_awburst(M_AXI_AWBURST),
		.i_axi_awlock( M_AXI_AWLOCK),
		.i_axi_awcache(M_AXI_AWCACHE),
		.i_axi_awprot( M_AXI_AWPROT),
		.i_axi_awqos(  M_AXI_AWQOS),
		.i_axi_awvalid(M_AXI_AWVALID),
		//
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wlast( M_AXI_WLAST),
		.i_axi_wvalid(M_AXI_WVALID),
		//
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid(   M_AXI_BID),
		.i_axi_bresp( M_AXI_BRESP),
		.i_axi_bvalid(M_AXI_BVALID),
		//
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
		.i_axi_arvalid(M_AXI_ARVALID),
		//
		.i_axi_rid(   M_AXI_RID),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rresp( M_AXI_RRESP),
		.i_axi_rvalid(M_AXI_RVALID),
		//
		.f_axi_awr_nbursts(faxi_awr_nbursts),
		.f_axi_wr_pending(faxi_wr_pending),
		.f_axi_rd_nbursts(faxi_rd_nbursts),
		.f_axi_rd_outstanding(faxi_rd_outstanding)
		//
		// ...
		//
		);


	////////////////////////////////////////////////////////////////////////
	//
	// Induction rule checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	// First rule: the AXI solver isn't permitted to have any more write
	// bursts outstanding than the AXI-lite interface has.
	always @(*)
		assert(faxi_awr_nbursts == faxil_awr_outstanding);

	//
	// Second: Since our bursts are limited to one value each, and since
	// we can't send address bursts ahead of their data counterparts,
	// (AXI property limitation) faxi_wr_pending can only ever be one or
	// zero, and the counters must match
	always @(*)
	begin
		//
		// ...
		//

		if (faxil_awr_outstanding != 0)
		begin
			assert((faxil_awr_outstanding == faxil_wr_outstanding)
			||(faxil_awr_outstanding-1 == faxil_wr_outstanding));
		end

		if (faxil_awr_outstanding == 0)
			assert(faxil_wr_outstanding == 0);
	end

	//
	// ...
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Known "bugs"
	//
	////////////////////////////////////////////////////////////////////////
	//
	// These are really more limitations in the AXI properties than
	// bugs in the code, but they need to be documented here.
	//
	generate if (C_AXI_DATA_WIDTH > 8)
	begin
		// The AXI-lite property checker doesn't validate WSTRB
		// values like it should.  If we don't force the AWADDR
		// LSBs to zero, the solver will pick an invalid WSTRB.
		//
		always @(*)
			assume(S_AXI_AWADDR[$clog2(C_AXI_DATA_WIDTH)-3:0] == 0);
		always @(*)
			assert(faxi_wr_addr[$clog2(C_AXI_DATA_WIDTH)-3:0] == 0);
	end endgenerate

	//
	// The AXI solver can't handle write transactions without either a
	// concurrent or proceeding write address burst.  Here we make that
	// plain.  It's not likely to cause any problems, but still worth
	// noting.
	always @(*)
	if (faxil_awr_outstanding == faxil_wr_outstanding)
		assume(S_AXI_AWVALID || !S_AXI_WVALID);
	else if (faxil_awr_outstanding > faxil_wr_outstanding)
		assume(!S_AXI_AWVALID);

	//
	// We need to make certain that our counters never overflow.  This is
	// an assertion within the property checkers, so we need an appropriate
	// matching assumption here.  In practice, F_LGDEPTH could be set
	// so arbitrarily large that this assumption would never get hit,
	// but the solver doesn't know that.
	always @(*)
	if (faxil_rd_outstanding >= {{(F_LGDEPTH-1){1'b1}}, 1'b0 })
		assume(!S_AXI_ARVALID);

	always @(*)
	if (faxil_awr_outstanding >= {{(F_LGDEPTH-1){1'b1}}, 1'b0 })
		assume(!S_AXI_AWVALID);

`endif
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
