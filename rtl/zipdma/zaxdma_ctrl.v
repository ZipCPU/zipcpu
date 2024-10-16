////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zaxdma_ctrl.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Simply handles the control requests for the AXI
//		version of the ZipDMA.  Status reads and control writes using
//	an AXI-Lite bus interface are handled here.
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
module zaxdma_ctrl #(
		// {{{
		parameter	ADDRESS_WIDTH=30, LGMEMLEN = 10,
		parameter	SLV_WIDTH=32,
				// BUS_WIDTH=512,
		parameter	LGDMALENGTH = ADDRESS_WIDTH,
		parameter	ABORT_KEY = 32'h41425254,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
				// == { 8'd65, 8'd66, 8'd82, 8'd84 }, "ABRT",
		localparam	AW = ADDRESS_WIDTH
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		// Slave / control port
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
		// DMA control wires and feedback
		// {{{
		output	reg				o_dma_request,
		output	reg				o_dma_abort,
		input	wire				i_dma_busy, i_dma_err,
		output	reg	[AW-1:0]		o_src_addr,
		output	reg	[AW-1:0]		o_dst_addr,
		output	reg	[LGDMALENGTH-1:0]	o_length,
		output	reg	[LGMEMLEN:0]		o_transferlen,
		output	reg				o_mm2s_inc, o_s2mm_inc,
		output	reg	[1:0]			o_mm2s_size,o_s2mm_size,
		//
		output	reg				o_trigger,
		//
		input	wire	[AW-1:0]		i_current_src,
		input	wire	[AW-1:0]		i_current_dst,
		input	wire	[LGDMALENGTH-1:0]	i_remaining_len,
		// }}}
		input	wire	[31:0]	i_dma_int,
		output	reg		o_interrupt
		// }}}
	);

	// Local declarations
	// {{{
	reg		int_trigger, r_err, r_zero_len, r_busy;
	reg	[4:0]	int_sel;
	reg	[SLV_WIDTH-1:0]	next_src, next_dst, next_len, next_tlen,
			w_control_reg;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Skid buffers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	rvalid, bvalid;
	wire		skd_awvalid, skd_wvalid, skd_arvalid;
	wire		axil_write_ready, axil_read_ready;
	wire	[3:0]	skd_awaddr, skd_araddr;
	wire	[31:0]	skd_wdata;
	wire	[3:0]	skd_wstrb;
	reg	[31:0]	rd_data;

	skidbuffer #(
		.DW(4), .OPT_OUTREG(1'b0), .OPT_LOWPOWER(OPT_LOWPOWER)
	) u_awskd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXIL_AWVALID), .o_ready(S_AXIL_AWREADY),
			.i_data(S_AXIL_AWADDR[3:0]),
		//
		.o_valid(skd_awvalid), .i_ready(axil_write_ready),
		.o_data(skd_awaddr)
		// }}}
	);

	skidbuffer #(
		.DW(4+32), .OPT_OUTREG(1'b0), .OPT_LOWPOWER(OPT_LOWPOWER)
	) u_wskd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXIL_WVALID), .o_ready(S_AXIL_WREADY),
			.i_data({ S_AXIL_WSTRB, S_AXIL_WDATA }),
		//
		.o_valid(skd_wvalid), .i_ready(axil_write_ready),
			.o_data({ skd_wstrb, skd_wdata })
		// }}}
	);

	assign	axil_write_ready = (!S_AXIL_BVALID || S_AXIL_BREADY)
			&& skd_awvalid && skd_wvalid;

	always @(posedge i_clk)
	if (i_reset)
		bvalid <= 1'b0;
	else if (axil_write_ready)
		bvalid <= 1'b1;
	else if (S_AXIL_BREADY)
		bvalid <= 1'b0;

	assign	S_AXIL_BVALID = bvalid;
	assign	S_AXIL_BRESP  = 2'b00;

	skidbuffer #(
		.DW(4), .OPT_OUTREG(1'b0), .OPT_LOWPOWER(OPT_LOWPOWER)
	) u_arskd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_AXIL_ARVALID), .o_ready(S_AXIL_ARREADY),
			.i_data(S_AXIL_ARADDR[3:0]),
		//
		.o_valid(skd_arvalid), .i_ready(axil_read_ready),
		.o_data(skd_araddr)
		// }}}
	);

	assign	axil_read_ready = (!S_AXIL_RVALID || S_AXIL_RREADY) && skd_arvalid;

	always @(posedge i_clk)
	if (i_reset)
		rvalid <= 1'b0;
	else if (axil_read_ready)
		rvalid <= 1'b1;
	else if (S_AXIL_RREADY)
		rvalid <= 1'b0;
	assign	S_AXIL_RVALID = rvalid;
	assign	S_AXIL_RRESP  = 2'b00;
	// }}}

	// w_control_reg
	// {{{
	always @(*)
	begin
		w_control_reg = 0;
		w_control_reg[31]    = i_dma_busy;
		w_control_reg[30]    = r_err || i_dma_err;
		w_control_reg[29]    = int_trigger;
		w_control_reg[28:24] = int_sel;
		//
		w_control_reg[LGMEMLEN:0] = o_transferlen;
		//
		w_control_reg[22]    = !o_s2mm_inc;
		w_control_reg[21:20] =  o_s2mm_size;
		//
		w_control_reg[18]    = !o_mm2s_inc;
		w_control_reg[17:16] =  o_mm2s_size;
	end
	// }}}

	// S_AXIL_RDATA
	// {{{
	always @(posedge i_clk)
	if ((!S_AXIL_RVALID || S_AXIL_RREADY) && (!OPT_LOWPOWER || axil_read_ready))
	begin
		rd_data <= 0;
		case(skd_araddr[3:2])
		2'b00: rd_data <= w_control_reg;
		2'b01: rd_data[AW-1:0] <= (i_dma_busy) ? i_current_src : o_src_addr;
		2'b10: rd_data[AW-1:0] <= (i_dma_busy) ? i_current_dst : o_dst_addr;
		2'b11: rd_data[LGDMALENGTH-1:0] <= (i_dma_busy) ? i_remaining_len : o_length;
		endcase
	end
	assign	S_AXIL_RDATA = rd_data;
	// }}}

	// o_trigger
	// {{{
	always @(posedge i_clk)
	if (i_reset || o_dma_abort || i_dma_err || !i_dma_busy)
		o_trigger <= 1'b0;
	else if (!int_trigger)
		o_trigger <= 1'b1;
	else
		o_trigger <= i_dma_int[int_sel];
	// }}}

	// next_src
	// {{{
	always @(*)
	begin
		next_src = 32'h00;
		next_src[AW-1:0] = o_src_addr;

		if (skd_wstrb[0]) next_src[ 7: 0] = skd_wdata[ 7: 0];
		if (skd_wstrb[1]) next_src[15: 8] = skd_wdata[15: 8];
		if (skd_wstrb[2]) next_src[23:16] = skd_wdata[23:16];
		if (skd_wstrb[3]) next_src[31:24] = skd_wdata[31:24];
	end
	// }}}

	// next_dst
	// {{{
	always @(*)
	begin
		next_dst = 32'h00;
		next_dst[AW-1:0] = o_dst_addr;

		if (skd_wstrb[0]) next_dst[ 7: 0] = skd_wdata[ 7: 0];
		if (skd_wstrb[1]) next_dst[15: 8] = skd_wdata[15: 8];
		if (skd_wstrb[2]) next_dst[23:16] = skd_wdata[23:16];
		if (skd_wstrb[3]) next_dst[31:24] = skd_wdata[31:24];
	end
	// }}}

	// next_len
	// {{{
	always @(*)
	begin
		next_len = 32'h00;
		next_len[LGDMALENGTH-1:0] = o_length;

		if (skd_wstrb[0]) next_len[ 7: 0] = skd_wdata[ 7: 0];
		if (skd_wstrb[1]) next_len[15: 8] = skd_wdata[15: 8];
		if (skd_wstrb[2]) next_len[23:16] = skd_wdata[23:16];
		if (skd_wstrb[3]) next_len[31:24] = skd_wdata[31:24];
	end
	// }}}

	// next_tlen
	// {{{
	always @(*)
	begin
		next_tlen = 32'h00;
		next_tlen[LGMEMLEN-1:0] = o_transferlen[LGMEMLEN-1:0];

		if (skd_wstrb[0]) next_tlen[ 7: 0] = skd_wdata[ 7: 0];
		if (skd_wstrb[1]) next_tlen[15: 8] = skd_wdata[15: 8];
		if (skd_wstrb[2]) next_tlen[23:16] = skd_wdata[23:16];
		if (skd_wstrb[3]) next_tlen[31:24] = skd_wdata[31:24];

		next_tlen[SLV_WIDTH-1:LGMEMLEN] = 0;
		next_tlen[LGMEMLEN] = (next_tlen[LGMEMLEN-1:0] == 0);
	end
	// }}}

	// Process writes
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_src_addr    <= {(AW){1'b0}};
		o_dst_addr    <= {(AW){1'b0}};
		o_length      <= {(LGDMALENGTH){1'b0}};
		r_zero_len    <= 1'b1;
		o_transferlen <= { 1'b1, {(LGMEMLEN){1'b0}} };

		o_s2mm_inc    <= 1'b0;
		o_s2mm_size   <= 2'b0;

		o_mm2s_inc  <= 1'b0;
		o_mm2s_size <= 2'b0;

		int_trigger <= 1'b0;
		int_sel     <= 5'h0;
		// }}}
	end else if (axil_write_ready && !o_dma_request && !i_dma_busy)
	begin // Register write, DMA is idle
		// {{{
		case(skd_awaddr[3:2])
		2'b00: begin // Control registers
			// {{{
			o_transferlen[LGMEMLEN:0] <= next_tlen[LGMEMLEN:0];
			if (skd_wstrb[2])
			begin
				o_s2mm_inc  <= !skd_wdata[22];
				o_s2mm_size <=  skd_wdata[21:20];
				//
				o_mm2s_inc  <= !skd_wdata[18];
				o_mm2s_size <=  skd_wdata[17:16];
			end

			if (skd_wstrb[3])
			begin
				int_trigger <= skd_wdata[29];
				int_sel     <= skd_wdata[28:24];
			end end
			// }}}
		2'b01: o_src_addr <= next_src[AW-1:0];
		2'b10: o_dst_addr <= next_dst[AW-1:0];
		2'b11: begin // o_length
			// {{{
			o_length <= next_len[LGDMALENGTH-1:0];
			r_zero_len <= (next_len[LGDMALENGTH-1:0] == 0);
			end
			// }}}
		endcase
		// }}}
	end else if (i_dma_busy)
	begin
		o_src_addr <= i_current_src;
		o_dst_addr <= i_current_dst;
	end
	// }}}

	// o_dma_request, o_dma_abort, o_interrupt, r_err
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_dma_request <= 1'b0;
		o_dma_abort   <= 1'b0;

		r_err <= 1'b0;

		o_interrupt <= 1'b0;
		// }}}
	end else begin
		r_busy <= i_dma_busy;

		if (!i_dma_busy)
		begin
			o_dma_request <= 1'b0;
			o_dma_abort   <= 1'b0;
		end

		if (i_dma_err)
			r_err <= 1'b1;
		if (r_busy && (!i_dma_busy || i_dma_err))
			o_interrupt <= 1'b1;

		if (axil_write_ready && skd_awaddr[3:2] == 2'b00)
		begin
		// {{{
			if (o_dma_request || i_dma_busy)
			begin
				// Deal with abort requests
				if ((&skd_wstrb) && skd_wdata == ABORT_KEY)
					{ o_dma_request, o_dma_abort } <= 2'b01;

			end else if (skd_wstrb[3])
			begin
				// Clear interrupts, errors, and potentially
				// restart the DMA
				if (skd_wdata[29] || !skd_wdata[30])
					o_interrupt <= 1'b0;
				if (skd_wdata[30])
					r_err <= 1'b0;
				if (!skd_wdata[31] && (!r_err || skd_wdata[30]))
					o_dma_request <= !r_zero_len;
			end
		// }}}
		end
	end
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, next_tlen[SLV_WIDTH-1:LGMEMLEN],
			S_AXIL_AWPROT, S_AXIL_ARPROT,
			skd_awaddr[1:0], skd_araddr[1:0] };
	generate if (SLV_WIDTH > AW)
	begin : UNUSED_WIDE_ADDR
		wire	unused_addr;
		assign	unused_addr = &{ 1'b0,
				next_src[SLV_WIDTH-1:AW],
				next_dst[SLV_WIDTH-1:AW]
				};
	end if (SLV_WIDTH > LGDMALENGTH)
	begin : UNUSED_LEN
		wire	unused_len;
		assign	unused_len = &{ 1'b0,
				next_len[SLV_WIDTH-1:LGDMALENGTH]
				};
	end endgenerate
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
endmodule
