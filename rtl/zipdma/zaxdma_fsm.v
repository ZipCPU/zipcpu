////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zaxdma_fsm.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA's control FSM
//
//	Since the Wishbone bus can only accommodate either a read or a write
//	transaction, large DMA transfers need to be broken up between reads
//	and writes.  This function accomplishes that purpose--issuing read
//	requests of the zipdma_mm2s controller, followed by write requests
//	of the zipdma_s2mm controller.
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
module	zaxdma_fsm #(
		// {{{
		parameter	ADDRESS_WIDTH = 32,	// Byte ADDR width
		parameter	LGDMALENGTH = ADDRESS_WIDTH,
		parameter	LGSUBLENGTH = 10
		// }}}
	) (
		// {{{
		input	wire				i_clk, i_reset,
		input	wire				i_soft_reset,
		// DMA control
		// {{{
		input	wire				i_dma_request,
		output	reg				o_dma_busy,
		output	reg				o_dma_err,
		input	wire	[ADDRESS_WIDTH-1:0]	i_src_addr,
		input	wire	[ADDRESS_WIDTH-1:0]	i_dst_addr,
		input	wire	[LGDMALENGTH-1:0]	i_length,
		input	wire	[LGSUBLENGTH:0]		i_transferlen,

		output	reg	[LGDMALENGTH-1:0]	o_remaining_len,
		// }}}
		input	wire				i_trigger,
		// MM2S control
		// {{{
		output	reg				o_mm2s_request,
		input	wire				i_mm2s_busy,
		input	wire				i_mm2s_err,
		input	wire				i_mm2s_inc,
		// input wire	[1:0]			i_mm2s_size,
		output	reg	[ADDRESS_WIDTH-1:0]	o_mm2s_addr,
		output	wire	[LGDMALENGTH-1:0]	o_mm2s_transferlen,
		// }}}
		// S2MM control
		// {{{
		output	reg				o_s2mm_request,
		input	wire				i_s2mm_busy,
		input	wire				i_s2mm_err,
		input	wire				i_s2mm_inc,
		// input wire	[1:0]			i_s2mm_size,
		output	reg	[ADDRESS_WIDTH-1:0]	o_s2mm_addr
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[1:0]	S_IDLE = 2'b00,
				S_WAIT = 2'b01,
				S_TRANSFER = 2'b10;

	reg	[LGDMALENGTH-1:0]	r_length;
	reg	[LGSUBLENGTH:0]		r_transferlen;
	reg	[1:0]			fsm_state;
	// }}}

	always @(posedge i_clk)
	if (i_reset || i_soft_reset || i_mm2s_err || i_s2mm_err)
	begin
		// {{{
		o_dma_busy     <= 0;
		r_length       <= 0;
		r_transferlen  <= 0;
		o_remaining_len <= 0;
		o_mm2s_request <= 0;
		o_s2mm_request <= 0;

		o_mm2s_addr <= 0;
		o_s2mm_addr <= 0;

		fsm_state   <= S_IDLE;
		// }}}
	end else if (!o_dma_busy)
	begin
		// {{{
		// state = S_IDLE
		o_dma_busy <= 1'b0;

		r_length <= 0;
		o_remaining_len <= 0;
		// Verilator lint_off WIDTH
		r_transferlen <= (i_length < i_transferlen) ? i_length
					: i_transferlen;
		// Verilator lint_on  WIDTH

		fsm_state <= S_IDLE;

		o_mm2s_request <= 0;
		o_s2mm_request <= 0;

		if (i_dma_request)
		begin
			o_dma_busy <= (i_length > 0);

			fsm_state      <= (i_trigger) ? S_TRANSFER : S_WAIT;
			o_mm2s_request <= i_trigger && (i_length > 0);
			o_s2mm_request <= i_trigger && (i_length > 0);

			o_mm2s_addr <= i_src_addr;
			o_s2mm_addr <= i_dst_addr;
			o_remaining_len <= i_length;
			r_length <= i_length;
		end
`ifdef	FORMAL
		assert(fsm_state == S_IDLE);
`endif
		// }}}
	end else case(fsm_state)
	S_WAIT: begin // Wait here for a trigger
		// {{{
		o_remaining_len <= r_length;
		o_mm2s_request <= 1'b0;
		o_s2mm_request <= 1'b0;

		if (r_length == 0)
			o_dma_busy <= 0;
		else if (i_trigger)
		begin
			fsm_state <= S_TRANSFER;
			o_mm2s_request <= 1'b1;
			o_s2mm_request <= 1'b1;

			if (r_transferlen[LGSUBLENGTH])
				r_length <= 0;
			// Verilator lint_off WIDTH
			else if (r_length > r_transferlen)
				r_length <= r_length - r_transferlen;
				// Verilator lint_on  WIDTH
			else
				r_length <= 0;
		end end
		// }}}
	S_TRANSFER: begin
		// {{{
		if (o_mm2s_request && !i_mm2s_busy)	// VALID && READY
			o_mm2s_request <= 1'b0;
		if (o_s2mm_request && !i_s2mm_busy)	// VALID && READY
			o_s2mm_request <= 1'b0;
		if (!i_mm2s_busy && !o_mm2s_request
			&& !i_s2mm_busy && !o_s2mm_request)
		begin
			fsm_state <= S_WAIT;

			// Verilator lint_off WIDTH
			if (i_mm2s_inc)
				o_mm2s_addr <= o_mm2s_addr + r_transferlen;

			if (i_s2mm_inc)
				o_s2mm_addr <= o_s2mm_addr + r_transferlen;
			// Verilator lint_on  WIDTH

			if (r_transferlen[LGSUBLENGTH])
			begin
				// {{{
				// We just accomplished the *entire* transfer
				if (i_mm2s_inc)
					o_mm2s_addr <= o_mm2s_addr + o_remaining_len;
				if (i_s2mm_inc)
					o_s2mm_addr <= o_s2mm_addr + o_remaining_len;
				// }}}
			end

			if (r_length == 0)
			begin
				fsm_state      <= S_IDLE;
				o_dma_busy     <= 1'b0;
			end
		end end
		// }}}
	// Verilator coverage_off
	default: begin
		fsm_state <= S_IDLE;
		o_dma_busy <= 1'b0;
		o_mm2s_request <= 1'b0;
		o_s2mm_request <= 1'b0;
		r_length <= 0;
		o_remaining_len <= 0;
		end
	// Verilator coverage_on
	endcase

	// Verilator lint_off WIDTH
	assign	o_mm2s_transferlen = r_transferlen[LGSUBLENGTH] ? o_remaining_len : r_transferlen;
	// Verilator lint_on  WIDTH

	// o_dma_err
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_soft_reset || !o_dma_busy)
		o_dma_err <= 1'b0;
	else
		o_dma_err <= (i_mm2s_busy && i_mm2s_err)
				|| (i_s2mm_busy && i_s2mm_err);
	// }}}
endmodule
