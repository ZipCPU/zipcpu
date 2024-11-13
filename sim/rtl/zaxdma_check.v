////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zaxdma_check.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA --
//
//
// Creator:	Dan Gisselquist, Ph.D.,
//		... based on work by Sukru Uzun
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
`timescale 1ns/1ps
`default_nettype none
// }}}
module	zaxdma_check #(
		parameter	ADDRESS_WIDTH = 30,
		parameter	BUS_WIDTH = 64,
		parameter	IW = 1,
		localparam	AW = ADDRESS_WIDTH,
		localparam	DW = BUS_WIDTH
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// High-speed, high width AXI test/data port
		// {{{
		input	wire		S_AXI_AWVALID,
		output	wire		S_AXI_AWREADY,
		input	wire [IW-1:0]	S_AXI_AWID,
		input	wire [AW-1:0]	S_AXI_AWADDR,
		input	wire [7:0]	S_AXI_AWLEN,
		input	wire [2:0]	S_AXI_AWSIZE,
		input	wire [1:0]	S_AXI_AWBURST,
		input	wire 		S_AXI_AWLOCK,
		input	wire [3:0]	S_AXI_AWCACHE,
		input	wire [2:0]	S_AXI_AWPROT,
		input	wire [3:0]	S_AXI_AWQOS,
		//
		input	wire		S_AXI_WVALID,
		output	wire		S_AXI_WREADY,
		input	wire [DW-1:0]	S_AXI_WDATA,
		input	wire [DW/8-1:0]	S_AXI_WSTRB,
		input	wire		S_AXI_WLAST,
		//
		output	wire		S_AXI_BVALID,
		input	wire		S_AXI_BREADY,
		output	wire [IW-1:0]	S_AXI_BID,
		output	wire	[1:0]	S_AXI_BRESP,
		//
		input	wire		S_AXI_ARVALID,
		output	wire		S_AXI_ARREADY,
		input	wire [IW-1:0]	S_AXI_ARID,
		input	wire [AW-1:0]	S_AXI_ARADDR,
		input	wire [7:0]	S_AXI_ARLEN,
		input	wire [2:0]	S_AXI_ARSIZE,
		input	wire [1:0]	S_AXI_ARBURST,
		input	wire 		S_AXI_ARLOCK,
		input	wire [3:0]	S_AXI_ARCACHE,
		input	wire [2:0]	S_AXI_ARPROT,
		input	wire [3:0]	S_AXI_ARQOS,
		//
		//
		output	wire		S_AXI_RVALID,
		input	wire		S_AXI_RREADY,
		output	wire [IW-1:0]	S_AXI_RID,
		output	wire [DW-1:0]	S_AXI_RDATA,
		output	wire	[1:0]	S_AXI_RRESP,
		output	wire		S_AXI_RLAST,
		// }}}
		// AXI-L status port
		// {{{
		input	wire		S_AXIL_AWVALID,
		output	wire		S_AXIL_AWREADY,
		input	wire	[2:0]	S_AXIL_AWADDR,
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
		input	wire	[2:0]	S_AXIL_ARADDR,
		input	wire	[2:0]	S_AXIL_ARPROT,
		//
		output	reg		S_AXIL_RVALID,
		input	wire		S_AXIL_RREADY,
		output	reg	[31:0]	S_AXIL_RDATA,
		output	reg	[1:0]	S_AXIL_RRESP
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	SR = 32;
	localparam [SR-1:0]	POLY = 32'hc000_0000;
	localparam		AXILSB = $clog2(BUS_WIDTH/8);

	integer		lfsrk, dk, wk, wkp, rk, rkp;
	reg [SR-1:0]	lfsr_state;
	reg	[DW-1:0]	read_data, nxt_rddata;
	wire		read_beat, write_beat;
	reg		err_flag;
	reg	[11:0]	rd_count, wr_count;
	reg	[11:0]	rd_count_reg, wr_count_reg;
	reg	[DW/8-1:0]	wrmatchb, rdmask;
	reg	[2*DW-1:0]	wide_state, shift_state;

	wire			awskd_valid, axi_write_ready;
	wire	[IW-1:0]	awskd_id;
	wire	[AW-1:0]	awskd_addr;
	wire	[7:0]		awskd_len;
	// wire	[7:0]	awskd_burst;
	// wire	[2:0]	awskd_size;
	// wire	[7:0]	awskd_lock;
	// wire	[2:0]	awskd_cache;
	// wire	[2:0]	awskd_prot;
	// wire	[2:0]	awskd_qos;

	wire			wskd_valid;
	wire	[DW-1:0]	wskd_data;
	wire	[DW/8-1:0]	wskd_strb;
	wire			wskd_last;

	reg			bvalid;
	reg	[IW-1:0]	bid;
	reg	[8:0]		wlen;

	wire			arskd_valid, axi_read_ready;
	wire	[IW-1:0]	arskd_id;
	wire	[AW-1:0]	arskd_addr;
	wire	[7:0]		arskd_len;
	wire	[1:0]	arskd_burst;
	wire	[2:0]	arskd_size;
	// wire	[7:0]	arskd_lock;
	// wire	[2:0]	arskd_cache;
	// wire	[2:0]	arskd_prot;
	// wire	[2:0]	arskd_qos;
	reg			rvalid, rlast;
	reg	[AW-1:0]	raddr, arbeat_addr;
	reg	[IW-1:0]	rid;
	reg	[7:0]		rlen;
	reg	[2:0]		rsize;
	wire	[2:0]		read_size;
	reg	[1:0]		rburst;


	wire		ctrl_awvalid, ctrl_write_ready;
	wire	[2:0]	ctrl_awaddr;

	wire		ctrl_wvalid;
	wire	[31:0]	ctrl_wdata;
	wire	[3:0]	ctrl_wstrb;

	wire		ctrl_arvalid, ctrl_read_ready;
	wire	[2:0]	ctrl_araddr;
	wire	[DW/8-1:0]	byte_mask, half_mask, word_mask, bus_mask;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Skidbuffers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		.OPT_OUTREG(1'b0), .DW(IW+8+AW)
	) u_awskd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data({ S_AXI_AWID, S_AXI_AWLEN, S_AXI_AWADDR }),
		.o_valid(awskd_valid), .i_ready(axi_write_ready),
			.o_data({ awskd_id, awskd_len, awskd_addr })
	);

	skidbuffer #(
		.OPT_OUTREG(1'b0), .DW(1+DW/8+DW)
	) u_wskd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WLAST, S_AXI_WSTRB, S_AXI_WDATA }),
		.o_valid(wskd_valid), .i_ready(write_beat),
			.o_data({ wskd_last, wskd_strb, wskd_data })
	);

	skidbuffer #(
		.OPT_OUTREG(1'b0), .DW(2+3+IW+8+AW)
	) u_arskd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data({ S_AXI_ARBURST, S_AXI_ARSIZE, S_AXI_ARID, S_AXI_ARLEN, S_AXI_ARADDR }),
		.o_valid(arskd_valid), .i_ready(axi_read_ready),
			.o_data({ arskd_burst, arskd_size, arskd_id, arskd_len, arskd_addr })
	);

	skidbuffer #(
		.OPT_OUTREG(1'b0), .DW(3)
	) u_ctrl_awskd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
			.i_data(S_AXIL_AWADDR),
		.o_valid(ctrl_awvalid), .i_ready(ctrl_write_ready),
			.o_data(ctrl_awaddr)
	);

	skidbuffer #(
		.OPT_OUTREG(1'b0), .DW(4+32)
	) u_ctrl_wskd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
			.i_data({ S_AXIL_WSTRB, S_AXIL_WDATA }),
		.o_valid(ctrl_wvalid), .i_ready(ctrl_write_ready),
			.o_data({ ctrl_wstrb, ctrl_wdata })
	);

	skidbuffer #(
		.OPT_OUTREG(1'b0), .DW(3)
	) u_ctrl_arskd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
			.i_data(S_AXIL_ARADDR),
		.o_valid(ctrl_arvalid), .i_ready(ctrl_read_ready),
			.o_data(ctrl_araddr)
	);
	// }}}
	// AXI Bus logic
	// {{{

	always @(posedge i_clk)
	if (i_reset)
		wlen <= 0;
	else if (axi_write_ready)
		wlen <= awskd_len + (wskd_valid ? 0:1);
	else if (write_beat && wlen > 0)
		wlen <= wlen - 1;

	always @(posedge i_clk)
	if (axi_write_ready)
		bid <= awskd_id;

	always @(posedge i_clk)
	if (i_reset)
		bvalid <= 0;
	else if (write_beat)
		bvalid <= wskd_last;
	else if (S_AXI_BREADY)
		bvalid <= 1'b0;

	assign	S_AXI_BVALID = bvalid;
	assign	S_AXI_BID    = bid;
	assign	S_AXI_BRESP  = 2'b00;

	assign	axi_write_ready = awskd_valid && (wlen == 0)&&(!bvalid || S_AXI_BREADY);
	assign	write_beat = wskd_valid && (axi_write_ready || wlen > 0);
	

	always @(posedge i_clk)
	if (i_reset)
		rvalid <= 0;
	else if (read_beat)
		rvalid <= 1;
	else if (S_AXI_RREADY)
		rvalid <= 0;

	always @(posedge i_clk)
	if (axi_read_ready)
	begin
		rid <= arskd_id;
		rburst <= arskd_burst;
		rsize <= arskd_size;
	end

	always @(posedge i_clk)
	if (i_reset)
		rlen <= 0;
	else if (axi_read_ready)
		rlen <= arskd_len;
	else if (read_beat)
		rlen <= rlen - 1;

	always @(*)
	begin
		wide_state = 0;
		wide_state[2*DW-1:2*DW-32]= lfsr_state;
		for(dk=1; dk<2*DW/32; dk=dk+1)
			wide_state[2*DW - 32 - (32*dk) +: 32]
				= advance_lfsr(wide_state[2*DW-(32*dk) +: 32]);
	end

	always @(posedge i_clk)
	if (i_reset)
		raddr <= 0;
	else if (arskd_valid && axi_read_ready)
	begin
		if (arskd_burst == 2'b00)
		begin // FIX addressing
			raddr <= arskd_addr;
			case(arskd_size)
			3'h0: begin end
			3'h1: raddr[0] <= 1'b0;
			3'h2: raddr[1:0] <= 2'b00;
			default: raddr[AXILSB-1:0] <= 0;
			endcase
		end else begin // if arskd_burst == 2'b01
			case(arskd_size)
			3'h0: raddr <= arskd_addr + 1;
			3'h1: begin
				raddr <= arskd_addr + 2;
				raddr[0] <= 1'b0;
				end
			3'h2: begin
				raddr <= arskd_addr + 4;
				raddr[1:0] <= 2'b00;
				end
			default: begin
				raddr[AW-1:AXILSB] <= arskd_addr[AW-1:AXILSB]+1;
				raddr[AXILSB-1:0] <= 0;
				end
			endcase
		end
	end else if (read_beat && rburst[0])
	begin
		case(rsize)
		3'h0: raddr <= raddr + 1;
		3'h1: raddr <= raddr + 2;
		3'h2: raddr <= raddr + 4;
		default: raddr <= raddr + (1<<AXILSB);
		endcase
	end

	assign	byte_mask = { {(BUS_WIDTH/8-1){1'b0}}, 1'b1 };
	assign	half_mask = { {(BUS_WIDTH/8-2){1'b0}}, 2'b11 };
	assign	word_mask = { {(BUS_WIDTH/8-4){1'b0}}, 4'hf };
	assign	bus_mask  =   {(BUS_WIDTH/8  ){1'b1}};

	assign	arbeat_addr = (arskd_valid && axi_read_ready) ? arskd_addr
				: raddr;
	always @(*)
	begin
		case(arskd_size)
		3'h0: rdmask = (byte_mask << arbeat_addr[AXILSB-1:0]);
		3'h1: rdmask = (half_mask <<(2*arbeat_addr[AXILSB-1:1]))
				& (half_mask << (arbeat_addr[AXILSB-1:0]));
		3'h2: if (AXILSB > 2)
			begin
				rdmask = (word_mask << (4*arbeat_addr[((AXILSB <= 2) ? 2:(AXILSB-1)):2]))
					& (word_mask << (arbeat_addr[AXILSB-1:0]));
			end else
				rdmask = word_mask << (arbeat_addr[1:0]);
		default: rdmask = bus_mask << arbeat_addr[AXILSB-1:0];
		endcase
	end

	always @(*)
	begin
		nxt_rddata = 0;
		rkp = 0;
		if (read_beat)
		for(rk=0; rk<DW/8; rk=rk+1)
		begin
			if (rdmask[rk])
				nxt_rddata[rk*8 +: 8]
					= lfsr_state[(2*DW-8)-8*rkp +: 8];
		end
	end

	always @(posedge i_clk)
	if (!S_AXI_RVALID || S_AXI_RREADY)
		read_data <= nxt_rddata;

	always @(posedge i_clk)
	if (axi_read_ready)
		rlast <= arskd_len == 0;
	else if (read_beat)
		rlast <= (arskd_len <= 1);

	assign	S_AXI_RVALID = rvalid;
	assign	S_AXI_RID    = rid;
	assign	S_AXI_RDATA  = read_data;
	assign	S_AXI_RLAST  = rlast;
	assign	S_AXI_RRESP  = 2'b00;

	assign	read_size = (axi_read_ready) ? arskd_size : rsize;

	assign	axi_read_ready = arskd_valid && (rlen == 0)
			&& (!S_AXI_RVALID || (S_AXI_RREADY && S_AXI_RLAST));
	assign	read_beat = (axi_read_ready || rlen != 0)
				&& (!S_AXI_RVALID || S_AXI_RREADY);
	// }}}
	// AXI-Lite Control Bus logic
	// {{{
	reg	ctrl_bvalid, ctrl_rvalid;

	assign	ctrl_write_ready = (!S_AXIL_BVALID || S_AXIL_BREADY)
					&& ctrl_awvalid && ctrl_wvalid;

	always @(posedge i_clk)
	if (i_reset)
		ctrl_bvalid <= 0;
	else if (ctrl_write_ready)
		ctrl_bvalid <= 1;
	else if (S_AXIL_BREADY)
		ctrl_bvalid <= 1'b0;

	assign	S_AXIL_BVALID = ctrl_bvalid;
	assign	S_AXIL_BRESP  = 2'b00;
		
	always @(posedge i_clk)
	if (i_reset)
		ctrl_rvalid <= 0;
	else if (ctrl_read_ready)
		ctrl_rvalid <= 1;
	else if (S_AXIL_RREADY)
		ctrl_rvalid <= 1'b0;

	assign	S_AXIL_RVALID = ctrl_rvalid;
	assign	S_AXIL_RRESP  = 2'b00;
	assign	ctrl_read_ready = (!S_AXIL_RVALID || S_AXIL_RREADY)
					&& ctrl_arvalid;
	// }}}

	// lfsr_state
	// {{{
	always @(*)
	if (read_beat)
		shift_state = wide_state >> ((2*DW-32)-(8*$countones(rdmask)));
	else
		shift_state = wide_state >> ((2*DW-32)-(8*$countones(wskd_strb)));
	always @(posedge i_clk)
	if (i_reset)
		lfsr_state <= 0; // initial state
	else if (ctrl_write_ready && ctrl_wstrb != 0)
	begin
		// set an initial per-test state
		lfsr_state <= 0;
		for (lfsrk = 0; lfsrk < 4; lfsrk = lfsrk + 1)
		if (ctrl_wstrb[lfsrk])
			lfsr_state[(DW-32) + (lfsrk*8) +: 8] <= ctrl_wdata[(lfsrk*8) +: 8];
	end else if (read_beat || write_beat)
		lfsr_state <= shift_state[SR-1:0];
	// }}}

	// rd_count, wr_count
	// {{{
	always @(*)
	begin
		rd_count = rd_count_reg;
		wr_count = wr_count_reg;

		// reset counter after lfsr initialization
		if (ctrl_write_ready && ctrl_wstrb != 0)
		begin
			rd_count = 0;
			wr_count = 0;
		end else begin
			if (write_beat)
			begin
				for (wk = 0; wk < DW/8; wk=wk+1)
				if (wskd_strb[wk])
				begin
					wr_count = wr_count + 1;
				end
			end

			if (read_beat)
			begin
				rd_count = rd_count_reg + (1 << read_size);
			end
		end
	end

	always @(posedge i_clk)
	if (i_reset)
	begin
		rd_count_reg <= 0;
		wr_count_reg <= 0;
	end else begin
		rd_count_reg <= rd_count;
		wr_count_reg <= wr_count;
	end
	// }}}

	// err_flag
	// {{{
	always @(*)
	begin
		wrmatchb = -1; wkp = 0;
		if (write_beat)
		for(wk=0; wk<DW/8; wk=wk+1)
		if (wskd_strb[wk])
		begin
			wrmatchb[wk] = (wskd_data[wk*8 +: 8]
					== wide_state[2*DW-8-(8*wkp) +: 8]);
			wkp = wkp+1;
		end
	end

	always @(posedge i_clk)
	if (i_reset)
		err_flag <= 1'b0;
	else if (ctrl_write_ready && ctrl_wstrb != 0)
		err_flag <= 1'b0;
	else if (write_beat)
		err_flag <= |wrmatchb;
	// }}}

	// S_AXIL_RDATA: Error detectıon (might need more error flags)
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		S_AXIL_RDATA <= 32'b0;
	else if (!S_AXIL_RVALID || S_AXIL_RREADY)
	begin
		S_AXIL_RDATA  <= 32'h0;

		case(ctrl_araddr[2])
		1'b0: begin
			S_AXIL_RDATA[15:4]  <= rd_count;
			S_AXIL_RDATA[31:20] <= wr_count;

			S_AXIL_RDATA[0] <= err_flag;
			end
		1'b1: S_AXIL_RDATA[SR-1:0] <= lfsr_state;
		endcase

		if (!ctrl_read_ready)
			S_AXIL_RDATA <= 0;
	end
	// }}}

	function automatic [SR-1:0] advance_lfsr(input [SR-1:0] istate);
		// {{{
		integer ak;
		reg	[SR-1:0]	fill;
	begin
		fill = istate;
		for(ak=0; ak<SR; ak=ak+1)
		begin
			if (^(fill & POLY))
				fill = { fill[SR-2:0], 1'b1 };
			else
				fill = { fill[SR-2:0], 1'b0 };
		end

		advance_lfsr = fill;
	end endfunction
	// }}}

	// Keep Verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, awskd_addr, arskd_addr,
			S_AXI_AWLOCK, S_AXI_AWBURST, S_AXI_AWCACHE, S_AXI_AWPROT, S_AXI_AWQOS, S_AXI_AWSIZE,
			S_AXI_ARLOCK, S_AXI_ARBURST, S_AXI_ARCACHE, S_AXI_ARPROT, S_AXI_ARQOS,
			S_AXIL_AWPROT, ctrl_awaddr[2:0],
			S_AXIL_ARPROT, ctrl_araddr[1:0],
			arbeat_addr[AW-1:AXILSB],
			rburst[1], shift_state[2*DW-1:SR] };
	// verilator lint_on UNUSED
	// verilator coverage_on
	// }}}
endmodule
