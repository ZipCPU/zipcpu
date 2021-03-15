////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axilops.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU based upon AXI-lite.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2021, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
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
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	axilops #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	C_AXI_ADDR_WIDTH = ADDRESS_WIDTH,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter [0:0]	SWAP_ENDIANNESS = 1'b0,
		parameter [0:0]	SWAP_WSTRB = 1'b1,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		//
		// AXI locks are a challenge, and require support from the
		// CPU.  Specifically, we have to be able to unroll and re-do
		// the load instruction on any atomic access failure.  For that
		// reason, we'll ignore the lock request initially.
		//
		// parameter [0:0]	IMPLEMENT_LOCK=1'b1,
		parameter [0:0]	OPT_ALIGNMENT_ERR = 1'b1,
		parameter [0:0]	OPT_ZERO_ON_IDLE = 1'b0,
		localparam	AXILLSB = $clog2(C_AXI_ADDR_WIDTH/8)
		// }}}
	) (
		// {{{
		input	wire				S_AXI_ACLK,
		input	wire				S_AXI_ARESETN,
		input	wire				i_cpu_reset,
		//
		// CPU interface
		// {{{
		input	wire				i_stb,
		input	wire				i_lock,
		input	wire	[2:0]			i_op,
		input	wire	[AW-1:0]		i_addr,
		input	wire	[31:0]			i_data,
		input	wire	[4:0]			i_oreg,
		output	reg				o_busy,
		output	reg				o_rdbusy,
		output	reg				o_valid,
		output	reg				o_err,
		output	reg	[4:0]			o_wreg,
		output	reg	[31:0]			o_result,
		// }}}
		// AXI-Lite bus interface
		//
		// Writes
		// {{{
		output	reg				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	reg [C_AXI_ADDR_WIDTH-1:0]	M_AXI_AWADDR,
		output	reg	[2:0]			M_AXI_AWPROT,
		//
		output	reg				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	reg [C_AXI_DATA_WIDTH-1:0]	M_AXI_WDATA,
		output	reg [C_AXI_DATA_WIDTH/8-1:0]	M_AXI_WSTRB,
		//
		input	wire				M_AXI_BVALID,
		output	reg				M_AXI_BREADY,
		input	wire [1:0]			M_AXI_BRESP,
		// }}}
		// Reads
		// {{{
		output	reg				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	reg [C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	reg	[2:0]			M_AXI_ARPROT,
		//
		input	wire				M_AXI_RVALID,
		output	reg				M_AXI_RREADY,
		input	wire [C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire [1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	wire	i_clk = S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;

	reg	misaligned_request, w_misaligned, misaligned_aw_request,
		misaligned_response_pending,pending_err, misaligned_read;
	reg	r_flushing;
	reg	[3:0]			r_op;
	reg	[C_AXI_DATA_WIDTH-1:0]	next_wdata;
	reg [C_AXI_DATA_WIDTH/8-1:0]	next_wstrb;
	reg	[31:0]			last_result;
	reg	[31:0]			endian_swapped_wdata;
	// reg	[31:0]			endian_swapped_result;
	reg [2*C_AXI_DATA_WIDTH/8-1:0]	shifted_wstrb_word,
					shifted_wstrb_halfword,
					shifted_wstrb_byte;
	reg [2*C_AXI_DATA_WIDTH/8-1:0]	swapped_wstrb_word,
					swapped_wstrb_halfword,
					swapped_wstrb_byte;
	reg	[C_AXI_DATA_WIDTH-1:0]	axi_wdata;
	reg [C_AXI_DATA_WIDTH/8-1:0]	axi_wstrb;
	// }}}

	initial	M_AXI_AWVALID = 1'b0;
	initial	M_AXI_WVALID = 1'b0;
	initial	M_AXI_ARVALID = 1'b0;
	initial	M_AXI_BREADY = 1'b0;
	initial	M_AXI_RREADY = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		M_AXI_AWVALID <= 1'b0;
		M_AXI_WVALID  <= 1'b0;
		M_AXI_ARVALID <= 1'b0;
		M_AXI_BREADY  <= 1'b0;
		M_AXI_RREADY  <= 1'b0;
		// }}}
	end else if (M_AXI_BREADY || M_AXI_RREADY)
	begin // Something is outstanding
		// {{{
		if (M_AXI_AWREADY)
			M_AXI_AWVALID <= M_AXI_AWVALID && misaligned_aw_request;
		if (M_AXI_WREADY)
			M_AXI_WVALID <= M_AXI_WVALID && misaligned_request;
		if (M_AXI_ARREADY)
			M_AXI_ARVALID <= M_AXI_ARVALID && misaligned_request;

		if ((M_AXI_BVALID || M_AXI_RVALID) && !misaligned_response_pending)
		begin
			M_AXI_BREADY <= 1'b0;
			M_AXI_RREADY <= 1'b0;
		end
		// }}}
	end else begin // New memory operation
		// {{{
		// Initiate a request
		M_AXI_AWVALID <=  i_op[0];
		M_AXI_WVALID  <=  i_op[0];
		M_AXI_ARVALID <= !i_op[0];

		M_AXI_BREADY  <=  i_op[0];
		M_AXI_RREADY  <= !i_op[0];

		if (i_cpu_reset || o_err || !i_stb
				|| (OPT_ALIGNMENT_ERR && w_misaligned))
		begin
			M_AXI_AWVALID <= 0;
			M_AXI_WVALID  <= 0;
			M_AXI_ARVALID <= 0;

			M_AXI_BREADY <= 0;
			M_AXI_RREADY <= 0;
		end
		// }}}
	end

	// r_flushing
	// {{{
	initial	r_flushing = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
		r_flushing <= 1'b0;
	else if (i_cpu_reset && o_busy)
		r_flushing <= misaligned_response_pending
				||(!M_AXI_BVALID && !M_AXI_RVALID);
	else if (M_AXI_BREADY || M_AXI_RREADY)
	begin
		if (M_AXI_BVALID || M_AXI_RVALID)
			r_flushing <= 1'b0;
		if (misaligned_response_pending)
			r_flushing <= r_flushing;
	end
	// }}}

	// M_AXI_AxADDR
	// {{{
	initial	M_AXI_AWADDR = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN && OPT_ZERO_ON_IDLE)
		M_AXI_AWADDR <= 0;
	else if (!M_AXI_BREADY && !M_AXI_RREADY)
	begin
		M_AXI_AWADDR <= (i_stb && OPT_ZERO_ON_IDLE) ? 0 : i_addr;

		if (OPT_ZERO_ON_IDLE && !i_stb)
			M_AXI_AWADDR <= 0;

		if (SWAP_WSTRB)
			M_AXI_AWADDR[1:0] <= 2'b00;

	end else if ((M_AXI_AWVALID && M_AXI_AWREADY)
			||(M_AXI_ARVALID && M_AXI_ARREADY))
	begin
		M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:AXILLSB]
			<= M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:AXILLSB] + 1;
		M_AXI_AWADDR[AXILLSB-1:0] <= 0;

		if (OPT_ZERO_ON_IDLE && ((M_AXI_RREADY && !misaligned_request)
			|| (M_AXI_BREADY && !misaligned_aw_request)))
			M_AXI_AWADDR <= 0;
	end

	always @(*)
		M_AXI_ARADDR = M_AXI_AWADDR;
	// }}}

	// AxPROT
	// {{{
	always @(*)
	begin
		M_AXI_AWPROT = 3'b000;
		M_AXI_ARPROT = 3'b000;
	end
	// }}}

	// shifted_wstrb_*
	// {{{
	always @(*)
		shifted_wstrb_word = { {(C_AXI_DATA_WIDTH/8-4){1'b0}},
						4'b1111} << i_addr[AXILLSB-1:0];

	always @(*)
		shifted_wstrb_halfword = { {(C_AXI_DATA_WIDTH/8-4){1'b0}},
						4'b0011} << i_addr[AXILLSB-1:0];

	always @(*)
		shifted_wstrb_byte = { {(C_AXI_DATA_WIDTH/8-4){1'b0}},
						4'b0001} << i_addr[AXILLSB-1:0];
	// }}}

	// Swapping WSTRB bits
	// {{{
	generate if (SWAP_WSTRB)
	begin : SWAPPING_WSTRB
		// {{{
		genvar	gw, gb;

		for(gw=0; gw<C_AXI_DATA_WIDTH/32; gw=gw+1)
		for(gb=0; gb<32/8; gb=gb+1)
		always @(*)
		begin
			swapped_wstrb_word[gw*4+gb]
					= shifted_wstrb_word[gw*4+(3-gb)];
			swapped_wstrb_halfword[gw*4+gb]
					= shifted_wstrb_halfword[gw*4+(3-gb)];
			swapped_wstrb_byte[gw*4+gb]
					= shifted_wstrb_byte[gw*4+(3-gb)];
		end
		// }}}
	end else begin : KEEP_WSTRB
		// {{{

		always @(*)
			swapped_wstrb_word = shifted_wstrb_word;

		always @(*)
			swapped_wstrb_halfword = shifted_wstrb_halfword;

		always @(*)
			swapped_wstrb_byte = shifted_wstrb_byte;
		// }}}
	end endgenerate
	// }}}

	// wdata, wstrb
	// {{{
	initial	axi_wdata = 0;
	initial	axi_wstrb = 0;
	initial	next_wdata  = 0;
	initial	next_wstrb  = 0;
	always @(posedge i_clk)
	if (OPT_ZERO_ON_IDLE && !S_AXI_ARESETN)
	begin
		// {{{
		axi_wdata <= 0;
		axi_wstrb <= 0;

		next_wdata  <= 0;
		next_wstrb  <= 0;

		r_op <= 0;
		// }}}
	end else if (i_stb)
	begin
		// {{{
		if (OPT_ZERO_ON_IDLE && SWAP_WSTRB)
		begin
			// {{{
			casez(i_op[2:1])
			2'b10: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-16){1'b0}},
				    i_data[15:0] } << (8*(3-i_addr[AXILLSB-1:0]));
			2'b11: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-8){1'b0}},
				    i_data[7:0] } << (8*(3-i_addr[AXILLSB-1:0]));
			default: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-32){1'b0}},
				    i_data } << (8*(3-i_addr[AXILLSB-1:0]));
			endcase
			// }}}
		end else if (OPT_ZERO_ON_IDLE && !SWAP_WSTRB)
		begin
			// {{{
			casez(i_op[2:1])
			2'b10: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-16){1'b0}},
				    i_data[15:0] } << (8*i_addr[AXILLSB-1:0]);
			2'b11: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-8){1'b0}},
				    i_data[7:0] } << (8*i_addr[AXILLSB-1:0]);
			default: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-32){1'b0}},
				    i_data } << (8*i_addr[AXILLSB-1:0]);
			endcase
			// }}}
		end else begin
			// {{{
			casez(i_op[2:1])
			2'b10: { next_wdata, axi_wdata }
				<= { (2*C_AXI_DATA_WIDTH/16){ i_data[15:0] } };
			2'b11: { next_wdata, axi_wdata }
				<= { (2*C_AXI_DATA_WIDTH/8){  i_data[7:0] } };
			default: { next_wdata, axi_wdata }
				<= { (2*C_AXI_DATA_WIDTH/32){ i_data } };
			endcase
			// }}}
		end

		// next_wstrb, axi_wstrb
		// {{{
		casez(i_op[2:1])
		2'b0?: { next_wstrb, axi_wstrb } <= swapped_wstrb_word;
		2'b10: { next_wstrb, axi_wstrb } <= swapped_wstrb_halfword;
		2'b11: { next_wstrb, axi_wstrb } <= swapped_wstrb_byte;
		endcase
		// }}}

		r_op <= { i_op[2:1] , i_addr[AXILLSB-1:0] };

		// On a read set everything to zero but only if OPT_ZERO_ON_IDLE
		// is set
		// {{{
		if (OPT_ZERO_ON_IDLE && !i_op[0])
			{ next_wstrb, next_wdata, axi_wstrb, axi_wdata } <= 0;

		if (OPT_ALIGNMENT_ERR)
			{ next_wstrb, next_wdata } <= 0;
		if (OPT_ZERO_ON_IDLE)
		begin
			if (OPT_ALIGNMENT_ERR && w_misaligned)
				{ axi_wdata, axi_wstrb } <= 0;
			if (o_err || i_cpu_reset)
				{ next_wdata, next_wstrb,
				axi_wdata, axi_wstrb } <= 0;
		end
		// }}}
		// }}}
	end else if ((M_AXI_WVALID && M_AXI_WREADY)
			|| (M_AXI_ARVALID && M_AXI_ARREADY))
	begin
		// {{{
		axi_wdata <= OPT_ALIGNMENT_ERR ? 0 : next_wdata;
		axi_wstrb <= OPT_ALIGNMENT_ERR ? 0 : next_wstrb;
		if (OPT_ZERO_ON_IDLE)
			{ next_wdata, next_wstrb } <= 0;
		// }}}
	end else if ((OPT_ZERO_ON_IDLE)&&(M_AXI_WREADY))
	begin
		// {{{
		axi_wdata <= 0;
		axi_wstrb <= 0;
		// }}}
	end
	// }}}

	// M_AXI_WDATA, M_AXI_WSTRB
	// {{{
	generate if (SWAP_ENDIANNESS)
	begin : SWAP_WRITE_DATA_STRB
		// {{{
		genvar	gw, gb;

		for(gw=0; gw<C_AXI_DATA_WIDTH/32; gw=gw+1)
		for(gb=0; gb<32/8; gb=gb+1)
		always @(*)
		begin
			M_AXI_WDATA[32*gw + 8*gb +: 8] = axi_wdata[32*gw+8*(3-gb) +: 8];
			M_AXI_WSTRB[4*gw + gb] = axi_wstrb[4*gw+(3-gb)];
		end
		// }}}
	end else begin : KEEP_WRITE_DATA_STRB
		// {{{
		always @(*)
			{ M_AXI_WSTRB, M_AXI_WDATA } = { axi_wstrb, axi_wdata };
		// }}}
	end endgenerate
	// }}}

	// w_misaligned
	// {{{
	always @(*)
	casez(i_op[2:1])
	// Full word
	2'b0?: w_misaligned = (i_addr[AXILLSB-1:0]+3) >= (1<<AXILLSB);
	// Half word
	2'b10: w_misaligned = (i_addr[AXILLSB-1:0]+1) >= (1<<AXILLSB);
	// Bytes are always aligned
	2'b11: w_misaligned = 1'b0;
	endcase
	// }}}

	// misaligned_[aw_|]request, pending_err, misaligned_response_pending
	// {{{
	generate if (OPT_ALIGNMENT_ERR)
	begin
		// {{{
		always @(*)
		begin
			misaligned_request = 1'b0;

			misaligned_aw_request = 1'b0;
			misaligned_response_pending = 1'b0;
			misaligned_read = 1'b0;
			pending_err = 1'b0;
		end
		// }}}
	end else begin
		// {{{
		initial	misaligned_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_request <= w_misaligned;
		else if ((M_AXI_WVALID && M_AXI_WREADY)
					|| (M_AXI_ARVALID && M_AXI_ARREADY))
			misaligned_request <= 1'b0;
	
		initial	misaligned_aw_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_aw_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_aw_request <= w_misaligned && i_op[0];
		else if (M_AXI_AWREADY)
			misaligned_aw_request <= 1'b0;

		initial	misaligned_response_pending = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_response_pending <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_response_pending <= w_misaligned;
		else if (M_AXI_BVALID || M_AXI_RVALID)
			misaligned_response_pending <= 1'b0;
	
		initial	misaligned_read = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_read <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_read <= w_misaligned && !i_op[0];
		else if (M_AXI_RVALID)
			misaligned_read <= (misaligned_response_pending);

		always @(posedge i_clk)
		if (!S_AXI_ARESETN || i_stb || (!M_AXI_BREADY && !M_AXI_RREADY)
				|| o_err || r_flushing || i_cpu_reset)
			pending_err <= 1'b0;
		else if ((M_AXI_BVALID && M_AXI_BRESP[1])
				|| (M_AXI_RVALID && M_AXI_RRESP[1]))
			pending_err <= 1'b1;
		// }}}
	end endgenerate
	// }}}

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || r_flushing || i_cpu_reset)
		o_valid <= 1'b0;
	else
		o_valid <= M_AXI_RVALID && !M_AXI_RRESP[1] && !pending_err
				&& !misaligned_response_pending;
	// }}}

	// o_err
	// {{{
	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (r_flushing || i_cpu_reset || o_err)
		o_err <= 1'b0;
	else if (OPT_ALIGNMENT_ERR && i_stb && w_misaligned)
		o_err <= 1'b1;
	else if ((M_AXI_BVALID || M_AXI_RVALID) && !misaligned_response_pending)
		o_err <= (M_AXI_BVALID && M_AXI_BRESP[1])
			|| (M_AXI_RVALID && M_AXI_RRESP[1])
			|| pending_err;
	else
		o_err <= 1'b0;
	// }}}

	// o_busy, o_rdbusy
	// {{{
	always @(*)
	begin
		o_busy   = M_AXI_BREADY || M_AXI_RREADY;
		o_rdbusy = M_AXI_RREADY && !r_flushing;
	end
	// }}}

	// o_wreg
	// {{{
	always @(posedge i_clk)
	if (i_stb)
		o_wreg    <= i_oreg;
	// }}}

	// last_result, o_result
	// {{{
	always @(posedge i_clk)
	if ((OPT_ZERO_ON_IDLE)&&(!M_AXI_RREADY || !S_AXI_ARESETN))
		{ last_result, o_result } <= 0;
	else if (M_AXI_RVALID)
	begin
		// {{{
		if (!misaligned_response_pending && OPT_ZERO_ON_IDLE)
			last_result <= 0;
		else
			last_result <= M_AXI_RDATA;

		if (OPT_ALIGNMENT_ERR)
			last_result <= 0;

		// Verilator lint_off WIDTH
		if (misaligned_read && !OPT_ALIGNMENT_ERR)
			o_result <= { M_AXI_RDATA, last_result }
						>> (8*r_op[AXILLSB-1:0]);
		else
			o_result <= { 32'h0, M_AXI_RDATA }
						>> (8*r_op[AXILLSB-1:0]);
		// Verilator lint_on WIDTH

		casez(r_op[AXILLSB +: 2])
		2'b10: o_result[31:16] <= 0;
		2'b11: o_result[31: 8] <= 0;
		default: begin end
		endcase
		// }}}
	end
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_lock, M_AXI_RRESP[0], M_AXI_BRESP[0] };
	// verilator lint_on  UNUSED
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
`define	ASSERT	assert
`ifdef	AXILOPS
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	localparam	F_LGDEPTH = 2;

	wire	[F_LGDEPTH-1:0]	faxil_rd_outstanding, faxil_wr_outstanding,
				faxil_awr_outstanding;
	wire			f_pc, f_gie, f_read_cycle;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;
	always @(*)
	if (!f_past_valid)
		`ASSUME(!S_AXI_ARESETN);

	faxil_master #(
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_OPT_ASSUME_RESET(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
	) faxil(.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awaddr( M_AXI_AWADDR),
		.i_axi_awcache(4'h0),
		.i_axi_awprot( M_AXI_AWPROT),
		.i_axi_awvalid(M_AXI_AWVALID),
		//
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wvalid(M_AXI_WVALID),
		//
		.i_axi_bresp( M_AXI_BRESP),
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		//
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arcache(4'h0),
		.i_axi_arprot( M_AXI_ARPROT),
		.i_axi_arvalid(M_AXI_ARVALID),
		//
		.i_axi_rresp( M_AXI_RRESP),
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rready(M_AXI_RREADY),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding));


	always @(*)
	begin
		if (misaligned_request)
			`ASSERT(M_AXI_WVALID || M_AXI_ARVALID);
		if (misaligned_aw_request)
			`ASSERT(M_AXI_AWVALID);
		if (!misaligned_response_pending)
		begin
			`ASSERT(faxil_rd_outstanding  <= (M_AXI_ARVALID ? 0:1));
			`ASSERT(faxil_wr_outstanding  <= (M_AXI_WVALID ? 0:1));
			`ASSERT(faxil_awr_outstanding <= (M_AXI_AWVALID ? 0:1));

			`ASSERT(!misaligned_request);
			`ASSERT(!misaligned_aw_request);
		end else if (M_AXI_RREADY)
			`ASSERT(misaligned_read);

		if (!M_AXI_RREADY)
		begin
			`ASSERT(!M_AXI_ARVALID);
			`ASSERT(faxil_rd_outstanding == 0);
			`ASSERT(misaligned_read == 1'b0);
		end else begin
			if (misaligned_request)
				`ASSERT(faxil_rd_outstanding <= 0);
			`ASSERT(faxil_rd_outstanding <= 1 + (misaligned_read ? 1:0));
			// `ASSERT(faxil_rd_outstanding ==
			//	(M_AXI_RREADY && misaligned_request) ? 1:0)
			//	((M_AXI_RREADY && !M_AXI_RVALID) ? 1:0)
			//	);
		end

		if (!M_AXI_BREADY)
		begin
			`ASSERT(!M_AXI_AWVALID);
			`ASSERT(!M_AXI_WVALID);
			`ASSERT(faxil_awr_outstanding == 0);
			`ASSERT(faxil_wr_outstanding  == 0);
		end else begin
			if (misaligned_request)
				`ASSERT(faxil_wr_outstanding <= 0);
			if (misaligned_aw_request)
				`ASSERT(faxil_awr_outstanding <= 0);
			`ASSERT(faxil_awr_outstanding <= 2);
			`ASSERT(faxil_wr_outstanding <= 2);

			case({misaligned_request,
					misaligned_aw_request,
					misaligned_response_pending})
			3'b000: begin
				`ASSERT(faxil_awr_outstanding<= (M_AXI_BREADY ? 1:0));
				`ASSERT(faxil_wr_outstanding <= (M_AXI_BREADY ? 1:0));
				end
			3'b001: begin
				`ASSERT(faxil_awr_outstanding<= 1 + (M_AXI_AWVALID ? 0:1));
				`ASSERT(faxil_wr_outstanding <= 1 + (M_AXI_WVALID ? 0:1));
				end
			3'b010: `ASSERT(0);
			3'b011: begin
				`ASSERT(faxil_wr_outstanding<= 1 + (M_AXI_WVALID ? 0:1));
				`ASSERT(faxil_awr_outstanding == 0);
				`ASSERT(M_AXI_AWVALID);
				end
			3'b100: `ASSERT(0);
			3'b101: begin
				`ASSERT(faxil_awr_outstanding<= 1 + (M_AXI_AWVALID ? 0:1));
				`ASSERT(faxil_wr_outstanding == 0);
				`ASSERT(M_AXI_WVALID);
				end
			3'b110: `ASSERT(0);
			3'b111: begin
				`ASSERT(faxil_awr_outstanding == 0);
				`ASSERT(faxil_wr_outstanding == 0);
				`ASSERT(M_AXI_AWVALID);
				`ASSERT(M_AXI_WVALID);
				end
			default: begin end
			endcase
		end


		// Rule: Only one of the two xREADY's may be valid, never both
		`ASSERT(!M_AXI_BREADY || !M_AXI_RREADY);

		// Rule: Only one of the two VALID's may be valid, never both
		`ASSERT(!M_AXI_RVALID || (!M_AXI_AWVALID && !M_AXI_WVALID));
	end

	always @(*)
	if (!o_busy)
		`ASSERT(!r_flushing);

	// Following any i_stb request, assuming we are idle, immediately
	// begin a bus transaction
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_stb && !o_err))
		&&(!$past(o_busy))&&($past(!i_cpu_reset)))
	begin
		`ASSERT(o_busy || (OPT_ALIGNMENT_ERR && o_err));
	end

	always @(*)
		`ASSERT(o_busy == (M_AXI_BREADY || M_AXI_RREADY));

	always @(*)
	if (o_busy && !misaligned_request && OPT_ZERO_ON_IDLE)
	begin
		assert(next_wdata == 0);
		assert(next_wstrb == 0);
	end

	// If a transaction ends in an error, send o_err on the output port.
	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if ($past(i_cpu_reset || r_flushing || o_err))
			`ASSERT(!o_err);
		else if ($past(M_AXI_BVALID && M_AXI_BRESP[1]))
		begin
			if ($past(misaligned_response_pending))
				`ASSERT((!o_err && pending_err) || r_flushing);
			else
				`ASSERT(o_err);
		end else if ($past(M_AXI_RVALID && M_AXI_RRESP[1]))
		begin
			if ($past(misaligned_response_pending))
				`ASSERT((!o_err && pending_err) || r_flushing);
			else
				`ASSERT(o_err);
		end else if (OPT_ALIGNMENT_ERR && $past(i_stb && w_misaligned))
			`ASSERT(o_err);
		else if (!$past(pending_err))
			`ASSERT(!o_err);
		//else if ($past(misaligned))
			//`ASSERT(o_err);
	end

	always @(*)
	if (o_busy && misaligned_response_pending)
		`ASSERT(!pending_err);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_cpu_reset))&&($past(i_stb)))
	begin
		// On a write, assert o_wb_we should be true
		assert($past(i_op[0] && !o_err
			&& (!OPT_ALIGNMENT_ERR || !w_misaligned))
				== (M_AXI_AWVALID && M_AXI_WVALID));
	end

	// The 3'b00? opcode isn't defined
	always @(*)
		`ASSUME(i_op[2:1] != 2'b00);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_cpu_reset)))
		`ASSUME(!i_stb);

	always @(*)
	if (!S_AXI_ARESETN)
		`ASSUME(i_cpu_reset);

	always @(*)
	if (o_busy)
	begin
		`ASSUME(!i_stb);
		`ASSERT(!o_valid);
		`ASSERT(!o_err);
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Zero on idle checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_ZERO_ON_IDLE)
	begin
		always @(*)
		if (!M_AXI_AWVALID && !M_AXI_ARVALID)
			`ASSERT(M_AXI_AWADDR == 0);

		always @(*)
		if (!M_AXI_WVALID)
		begin
			`ASSERT(M_AXI_WDATA == 0);
			`ASSERT(M_AXI_WSTRB == 0);

			`ASSERT(next_wdata == 0);
			`ASSERT(next_wstrb == 0);
		end

		// always @(*)
		// if (!o_valid)
		//	`ASSERT(o_result == 0);

	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire	[3:0]	cpu_outstanding;
	reg		f_done;
	wire	[4:0]	f_last_reg, f_addr_reg;
	(* anyseq *) reg [4:0]	f_areg;

	initial	f_done = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || r_flushing || i_cpu_reset)
		f_done <= 1'b0;
	else
		f_done <= (M_AXI_RVALID && !M_AXI_RRESP[1]
			|| M_AXI_BVALID && !M_AXI_BRESP[1]) && !pending_err
				&& !misaligned_response_pending;


	fmem
	fcheck(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_bus_reset(!S_AXI_ARESETN),
		.i_cpu_reset(i_cpu_reset),
		.i_stb(i_stb),
		.i_pipe_stalled(o_busy),
		.i_clear_cache(1'b0),
		.i_lock(i_lock), .i_op(i_op), .i_addr(i_addr),
		.i_data(i_data), .i_oreg(i_oreg), .i_busy(o_busy),
			.i_areg(f_areg),
		.i_rdbusy(o_rdbusy), .i_valid(o_valid), .i_done(f_done),
		.i_err(o_err), .i_wreg(o_wreg), .i_result(o_result),
		.f_outstanding(cpu_outstanding),
		.f_pc(f_pc),
		.f_gie(f_gie),
		.f_read_cycle(f_read_cycle),
		.f_last_reg(f_last_reg), .f_addr_reg(f_addr_reg)
		// }}}
	);

	always @(*)
	if (r_flushing)
		`ASSERT(cpu_outstanding <= 0);
	else begin
		`ASSERT(cpu_outstanding == (o_busy ? 1:0)
			+ ((f_done || o_err) ? 1 : 0));
	end

	always @(*)
	if (f_pc)
		assert(o_wreg[3:1] == 3'h7);
	else if (o_rdbusy)
		assert(o_wreg[3:1] != 3'h7);

	always @(*)
	if (cpu_outstanding > 0)
		assert(o_wreg == f_last_reg);

	always @(*)
	if (o_busy)
		assert(o_wreg[4] == f_gie);

	always @(*)
	if (M_AXI_RREADY)
		assert(f_read_cycle || r_flushing);
	else if (M_AXI_BREADY)
		assert(!f_read_cycle);

	// ????   Not written yet
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_writes, cvr_reads;

	initial	cvr_writes = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
		cvr_writes <= 0;
	else if (M_AXI_BVALID&& !misaligned_response_pending  && !cvr_writes[3])
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
		cvr_reads <= 0;
	else if (M_AXI_RVALID && !misaligned_response_pending && !cvr_reads[3])
		cvr_reads <= cvr_reads + 1;

	// Cover a write response
	always @(posedge i_clk)
		cover(M_AXI_BVALID && !M_AXI_BRESP[1]);
	always @(posedge i_clk)
		cover(M_AXI_BVALID &&  M_AXI_BRESP[1]);

	always @(posedge i_clk)
		cover(M_AXI_RVALID && !M_AXI_RRESP[1]);
	always @(posedge i_clk)
		cover(M_AXI_RVALID &&  M_AXI_RRESP[1]);


	always @(posedge i_clk)
		cover(cvr_writes > 3);

	always @(posedge i_clk)
		cover(cvr_reads > 3);
	// }}}
`endif
// }}}
endmodule
//
//
// Usage (from yosys):
//		(BFOR)	(!ZOI,ALIGN)	(ZOI,ALIGN)	(!ZOI,!ALIGN)
//	Cells	 230		226		281		225
//	  FDRE	 114		116		116		116
//	  LUT2	  17		 23		 76		 19
//	  LUT3	   9		 23		 17		 20
//	  LUT4	  15		  4		 11		 14
//	  LUT5	  18		 18		  7		 15
//	  LUT6	  33		 18		 54		 38
//	  MUX7	  16		 12		  		  2
//	  MUX8	   8		  1				  1
//
//
