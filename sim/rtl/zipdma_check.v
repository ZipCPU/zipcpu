////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipdma_check.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	ZipDMA --
//
//
// Creator:	Sukru Uzun
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
`timescale 1ns/1ps
`default_nettype none

module zipdma_check #(
        parameter ADDRESS_WIDTH = 30,
        parameter BUS_WIDTH = 64
    ) (
        input   wire            i_clk, i_reset,
        // data
        input	wire		    i_wb_cyc, i_wb_stb,
		input	wire			i_wb_we,
		input	wire [AW-1:0]	i_wb_addr,
		input	wire [DW-1:0]	i_wb_data,
		input	wire [DW/8-1:0]	i_wb_sel,
		//
        output	reg	    		o_wb_stall,
		output	reg	    		o_wb_ack,
		output	reg [DW-1:0]	o_wb_data,
		output	reg 			o_wb_err,
        // status
        input	wire		    i_st_cyc, i_st_stb,
		input	wire			i_st_we,
		input	wire        	i_st_addr,
		input	wire [31:0]	    i_st_data,
		input	wire [3:0]	    i_st_sel,
		//
        output	reg	    		o_st_stall,
		output	reg	    		o_st_ack,
		output	reg [31:0]  	o_st_data,
		output	reg 			o_st_err
    );

    localparam	DW = BUS_WIDTH;
    localparam	AW = ADDRESS_WIDTH-$clog2(DW/8);
    localparam BW = DW/8;   // BIT_WIDTH

    reg [DW-1:0] lfsr_state;

    reg stb_reg;
    wire rd_data_en, wr_data_en;
    reg [11:0] rd_count, wr_count;
    reg [11:0] rd_count_reg, wr_count_reg;

    // rd_en, wr_en
    assign rd_data_en = i_wb_stb && !i_wb_we && (i_wb_sel != 0);
    assign wr_data_en = i_wb_stb && i_wb_we && (i_wb_sel != 0);

    // Wishbone outputs
    assign o_wb_stall = 1'b0;
    assign o_wb_err   = 1'b0;
    assign o_wb_data  = lfsr_state;

    assign o_st_stall = 1'b0;
    assign o_st_err   = 1'b0;

    // LFSR reset, o_st_ack
    always @(posedge i_clk) begin
        if (i_reset) begin
            o_st_ack <= 1'b0;
        end
        else begin
            o_st_ack <= 1'b0;
            if (i_st_stb) begin
                o_st_ack <= 1'b1;
            end
        end
    end

    // LFSR
    always @(posedge i_clk) begin
        if (i_reset)
            lfsr_state <= 0; // initial state
        else begin
            // set initial state
            if (i_st_stb && i_st_we && (i_st_sel != 0)) begin
                lfsr_state <= 0;
                for (int i = 0; i < 4; i++) begin
                    if (i_st_sel[i])
                        lfsr_state[(i*8)+:8] <= i_st_data[(i*8)+:8];
                end
            end

            // feedback
            if (rd_data_en)
                lfsr_state <= {lfsr_state[DW-2:0], lfsr_state[DW-1] ^ lfsr_state[DW-2]};
        end
    end

    // o_wb_ack
    initial	stb_reg = 1'b0;
    always @(posedge i_clk) begin
        if (i_reset)
            stb_reg <= 0;
        else
            stb_reg <= i_wb_stb && !o_wb_stall;
    end

	assign o_wb_ack = stb_reg;

    // rd_count, wr_count
    always @(*) begin
        rd_count = rd_count_reg;
        wr_count = wr_count_reg;

        // reset counter after lfsr initialization
        if (i_st_stb && i_st_we && (i_st_sel != 0)) begin
            rd_count = 0;
            wr_count = 0;
        end else begin
            for (int i = 0; i < BW; i++) begin
                if (i_wb_sel[i]) begin
                    rd_count = rd_count + (rd_data_en ? 1 : 0);
                    wr_count = wr_count + (wr_data_en ? 1 : 0);
                end
            end
        end
    end

    always @(posedge i_clk) begin
        if (i_reset) begin
            rd_count_reg <= 0;
            wr_count_reg <= 0;
        end else begin
            rd_count_reg <= rd_count;
            wr_count_reg <= wr_count;
        end
    end

    // o_wb_err
    // Error detectıon (might need more error flags)
    always @(posedge i_clk) begin
        if (i_reset) begin
            o_st_data <= 32'b0;
        end
        else begin
            o_st_data[15:4]  <= rd_count;
            o_st_data[31:20] <= wr_count;
            if (wr_data_en) begin
                for (int i = 0; i < BW; i++) begin
                    if (i_wb_sel[i]) begin
                        if (i_wb_data[(i*8)+:8] != lfsr_state[(i*8)+:8])
                            o_st_data[0] <= 1'b1;
                        else
                            o_st_data[0] <= 1'b0;
                    end
                end
            end

            if (i_st_stb && i_st_we)
                o_st_data[0] <= 1'b0;
        end
    end

    // verilator lint_off UNUSED
	wire unused;
	assign unused = &{ 1'b0, i_wb_cyc, i_st_cyc, i_st_addr, i_wb_addr };
	// verilator lint_on UNUSED

endmodule
