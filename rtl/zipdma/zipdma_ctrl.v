////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_ctrl.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA -- Simply handles the control requests for the ZipDMA.
//		Status reads and control writes using a 32-bit Wishbone bus
//	interface are handled here.
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
module zipdma_ctrl #(
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
		input	wire				i_cyc, i_stb, i_we,
		input	wire	[1:0]			i_addr,
		input	wire	[SLV_WIDTH-1:0]		i_data,
		input	wire [SLV_WIDTH/8-1:0]		i_sel,
		//
		output	wire				o_stall,
		output	reg				o_ack,
		output	reg	[SLV_WIDTH-1:0]		o_data,
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

	// o_ack
	// {{{
	initial	o_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_ack <= 1'b0;
	else
		o_ack <= i_stb;
	// }}}

	assign	o_stall = 1'b0;

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

	// o_data
	// {{{
	always @(posedge i_clk)
	if (!OPT_LOWPOWER || (i_stb && !o_stall && !i_we))
	begin
		o_data <= 0;
		case(i_addr)
		2'b00: o_data <= w_control_reg;
		2'b01: o_data[AW-1:0] <= (i_dma_busy) ? i_current_src : o_src_addr;
		2'b10: o_data[AW-1:0] <= (i_dma_busy) ? i_current_dst : o_dst_addr;
		2'b11: o_data[LGDMALENGTH-1:0] <= (i_dma_busy) ? i_remaining_len : o_length;
		endcase
	end
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

		if (i_sel[0]) next_src[ 7: 0] = i_data[ 7: 0];
		if (i_sel[1]) next_src[15: 8] = i_data[15: 8];
		if (i_sel[2]) next_src[23:16] = i_data[23:16];
		if (i_sel[3]) next_src[31:24] = i_data[31:24];
	end
	// }}}

	// next_dst
	// {{{
	always @(*)
	begin
		next_dst = 32'h00;
		next_dst[AW-1:0] = o_dst_addr;

		if (i_sel[0]) next_dst[ 7: 0] = i_data[ 7: 0];
		if (i_sel[1]) next_dst[15: 8] = i_data[15: 8];
		if (i_sel[2]) next_dst[23:16] = i_data[23:16];
		if (i_sel[3]) next_dst[31:24] = i_data[31:24];
	end
	// }}}

	// next_len
	// {{{
	always @(*)
	begin
		next_len = 32'h00;
		next_len[LGDMALENGTH-1:0] = o_length;

		if (i_sel[0]) next_len[ 7: 0] = i_data[ 7: 0];
		if (i_sel[1]) next_len[15: 8] = i_data[15: 8];
		if (i_sel[2]) next_len[23:16] = i_data[23:16];
		if (i_sel[3]) next_len[31:24] = i_data[31:24];
	end
	// }}}

	// next_tlen
	// {{{
	always @(*)
	begin
		next_tlen = 32'h00;
		next_tlen[LGMEMLEN-1:0] = o_transferlen[LGMEMLEN-1:0];

		if (i_sel[0]) next_tlen[ 7: 0] = i_data[ 7: 0];
		if (i_sel[1]) next_tlen[15: 8] = i_data[15: 8];
		if (i_sel[2]) next_tlen[23:16] = i_data[23:16];
		if (i_sel[3]) next_tlen[31:24] = i_data[31:24];

		next_tlen[SLV_WIDTH-1:LGMEMLEN] = 0;
		next_tlen[LGMEMLEN] = (next_tlen[LGMEMLEN-1:0] == 0);
	end
	// }}}

	// Process i_data writes
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
	end else if (i_stb && !o_stall && i_we && !o_dma_request && !i_dma_busy)
	begin // Register write, DMA is idle
		// {{{
		case(i_addr)
		2'b00: begin // Control registers
			// {{{
			o_transferlen[LGMEMLEN:0] <= next_tlen[LGMEMLEN:0];
			if (i_sel[2])
			begin
				o_s2mm_inc  <= !i_data[22];
				o_s2mm_size <=  i_data[21:20];
				//
				o_mm2s_inc  <= !i_data[18];
				o_mm2s_size <=  i_data[17:16];
			end

			if (i_sel[3])
			begin
				int_trigger <= i_data[29];
				int_sel     <= i_data[28:24];
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

		if (i_stb && !o_stall && i_we && i_addr == 2'b00)
		begin
		// {{{
			if (o_dma_request || i_dma_busy)
			begin
				// Deal with abort requests
				if ((&i_sel) && i_data == ABORT_KEY)
					{ o_dma_request, o_dma_abort } <= 2'b01;

			end else if (i_sel[3])
			begin
				// Clear interrupts, errors, and potentially
				// restart the DMA
				if (i_data[29] || !i_data[30])
					o_interrupt <= 1'b0;
				if (i_data[30])
					r_err <= 1'b0;
				if (!i_data[31] && (!r_err || i_data[30]))
					o_dma_request <= !r_zero_len;
			end
		// }}}
		end
	end
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_cyc, next_tlen[SLV_WIDTH-1:LGMEMLEN] };
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
	// }}}
endmodule
