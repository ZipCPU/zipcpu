////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axiops.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU based upon AXI4.  This is about
//		the simplest AXI4 interface I can design for this purpose.
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
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
// }}}
module	axiops #(
		// {{{
		parameter	ADDRESS_WIDTH=32,
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	C_AXI_ADDR_WIDTH = ADDRESS_WIDTH,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter [((C_AXI_ID_WIDTH > 0)? C_AXI_ID_WIDTH:1)-1:0]
					AXI_ID = 0,
		parameter [0:0]	SWAP_ENDIANNESS = 1'b0,
		parameter [0:0]	SWAP_WSTRB = 1'b0,
		parameter [3:0]	OPT_QOS = 0,
		localparam	IW = (C_AXI_ID_WIDTH > 0) ? 1:C_AXI_ID_WIDTH,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		//
		parameter [0:0]		OPT_LOCK=1'b1,
		parameter [0:0]		OPT_ALIGNMENT_ERR = 1'b0,
		parameter [0:0]		OPT_LOWPOWER = 1'b1,
		localparam	AXILSB = $clog2(C_AXI_DATA_WIDTH/8)
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
		input	wire	[AW-1:0]		i_restart_pc,
		input	wire	[31:0]			i_data,
		input	wire	[4:0]			i_oreg,
		output	reg				o_busy,
		output	reg				o_rdbusy,
		output	reg				o_valid,
		output	reg				o_err,
		output	reg	[4:0]			o_wreg,
		output	reg	[31:0]			o_result,
		// }}}
		// AXI4 bus interface
		//
		// Writes
		// {{{
		output	reg				M_AXI_AWVALID,
		input	wire				M_AXI_AWREADY,
		output	wire	[IW-1:0]		M_AXI_AWID,
		output	reg	[AW-1:0]		M_AXI_AWADDR,
		output	wire	[7:0]			M_AXI_AWLEN,
		output	reg 	[2:0]			M_AXI_AWSIZE,
		output	wire	[1:0]			M_AXI_AWBURST,
		output	wire				M_AXI_AWLOCK,
		output	wire	[3:0]			M_AXI_AWCACHE,
		output	wire	[2:0]			M_AXI_AWPROT,
		output	wire	[3:0]			M_AXI_AWQOS,
		//
		output	reg				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	reg	[DW-1:0]		M_AXI_WDATA,
		output	reg	[DW/8-1:0]		M_AXI_WSTRB,
		output	wire				M_AXI_WLAST,
		//
		input	wire				M_AXI_BVALID,
		output	reg				M_AXI_BREADY,
		input	wire	[IW-1:0]		M_AXI_BID,
		input	wire	[1:0]			M_AXI_BRESP,
		// }}}
		// Reads
		// {{{
		output	reg				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	wire	[IW-1:0]		M_AXI_ARID,
		output	reg	[AW-1:0]		M_AXI_ARADDR,
		output	wire	[7:0]			M_AXI_ARLEN,
		output	wire 	[2:0]			M_AXI_ARSIZE,
		output	wire	[1:0]			M_AXI_ARBURST,
		output	wire				M_AXI_ARLOCK,
		output	wire	[3:0]			M_AXI_ARCACHE,
		output	wire	[2:0]			M_AXI_ARPROT,
		output	wire	[3:0]			M_AXI_ARQOS,
		//
		input	wire				M_AXI_RVALID,
		output	reg				M_AXI_RREADY,
		input	wire	[IW-1:0]		M_AXI_RID,
		input	wire	[DW-1:0]		M_AXI_RDATA,
		input	wire				M_AXI_RLAST,
		input	wire	[1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam		CPU_DATA_WIDTH = 32;
	// Verilator lint_off WIDTH
	localparam	[2:0]	DSZ = $clog2(CPU_DATA_WIDTH/8);
	// Verilator lint_on  WIDTH
	localparam	[1:0]	AXI_INCR = 2'b01,
				OKAY   = 2'b00,
				EXOKAY = 2'b01;

	wire	i_clk = S_AXI_ACLK;
	// wire	i_reset = !S_AXI_ARESETN;

	reg	misaligned_request, w_misaligned, misaligned_aw_request,
		misaligned_response_pending,pending_err, misaligned_read,
		w_misalignment_err;
	reg	r_flushing;
	reg	[AW-1:0]		r_pc;
	reg	[3:0]			r_op;
	reg	[DW-1:0]		next_wdata;
	reg	[DW/8-1:0]		next_wstrb;
	reg	[31:0]			last_result;
	// reg	[31:0]			endian_swapped_wdata;
	// reg	[31:0]			endian_swapped_result;
	reg	[2*DW/8-1:0]		shifted_wstrb_word,
					shifted_wstrb_halfword,
					shifted_wstrb_byte;
	reg	[2*DW/8-1:0]		swapped_wstrb_word,
					swapped_wstrb_halfword,
					swapped_wstrb_byte;
	reg	[DW-1:0]		axi_wdata;
	reg	[DW/8-1:0]		axi_wstrb;
	reg				r_lock;
	reg	[AXILSB-1:0]		swapaddr;

	// }}}

	// xVALID, and xREADY
	// {{{
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
			M_AXI_WVALID  <= M_AXI_WVALID && misaligned_request;
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

		if (i_cpu_reset || o_err || !i_stb || w_misalignment_err)
		begin
			M_AXI_AWVALID <= 0;
			M_AXI_WVALID  <= 0;
			M_AXI_ARVALID <= 0;

			M_AXI_BREADY <= 0;
			M_AXI_RREADY <= 0;
		end
		// }}}
	end
	// }}}

	// r_lock
	// {{{
	initial	r_lock = 1'b0;
	always @(posedge i_clk)
	if (!OPT_LOCK || (!S_AXI_ARESETN && OPT_LOWPOWER))
	begin
		// {{{
		r_lock <= 1'b0;
		// }}}
	end else if (M_AXI_BREADY || M_AXI_RREADY)
	begin // Something is outstanding
		// {{{
		if (OPT_LOWPOWER && (M_AXI_BVALID || M_AXI_RVALID))
			r_lock <= 1'b0;
		// }}}
	end else begin // New memory operation
		// {{{
		// Initiate a request
		r_lock <= i_lock && i_stb;

		if (OPT_LOWPOWER && (i_cpu_reset || o_err || w_misaligned))
			r_lock <= 1'b0;
		// }}}
	end

	assign	M_AXI_AWLOCK = r_lock;
	assign	M_AXI_ARLOCK = r_lock;
	// }}}

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
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
		M_AXI_AWADDR <= 0;
	else if (!M_AXI_BREADY && !M_AXI_RREADY)
	begin // Initial address
		// {{{
		M_AXI_AWADDR <= i_addr;

		if (OPT_LOWPOWER && (i_cpu_reset || o_err || !i_stb || w_misalignment_err))
			M_AXI_AWADDR <= 0;

		if (SWAP_WSTRB)
			M_AXI_AWADDR[AXILSB-1:0] <= 0;
		// }}}
	end else if ((M_AXI_AWVALID && M_AXI_AWREADY)
			||(M_AXI_ARVALID && M_AXI_ARREADY))
	begin // Subsequent addresses
		// {{{
		M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:AXILSB]
			<= M_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:AXILSB] + 1;

		M_AXI_AWADDR[AXILSB-1:0] <= 0;

		if (OPT_LOWPOWER && ((M_AXI_RREADY && !misaligned_request)
			|| (M_AXI_BREADY && !misaligned_aw_request)))
			M_AXI_AWADDR <= 0;
		// }}}
	end

	always @(*)
		M_AXI_ARADDR = M_AXI_AWADDR;
	// }}}

	// M_AXI_AxSIZE
	// {{{
	reg	[2:0]	awsize;

	initial	awsize = 3'b010;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
		awsize <= 3'b010;
	else if (!M_AXI_BREADY && !M_AXI_RREADY && (!OPT_LOWPOWER || i_stb))
	begin
		casez(i_op[2:1])
		2'b0?: awsize <= 3'b010;
		2'b10: awsize <= 3'b001;
		2'b11: awsize <= 3'b000;
		// default: begin end
		endcase
	end

	assign	M_AXI_AWSIZE = awsize;
	assign	M_AXI_ARSIZE  = M_AXI_AWSIZE;
	// }}}

	// AxOTHER
	// {{{
	localparam [3:0]	AXI_NON_CACHABLE_BUFFERABLE = 4'h3;
	localparam [3:0]	OPT_CACHE = AXI_NON_CACHABLE_BUFFERABLE;
	localparam [2:0]	AXI_UNPRIVILEGED_NONSECURE_DATA_ACCESS = 3'h0;
	localparam [2:0]	OPT_PROT=AXI_UNPRIVILEGED_NONSECURE_DATA_ACCESS;

	assign	M_AXI_AWID    = AXI_ID;
	assign	M_AXI_AWLEN   = 0;
	assign	M_AXI_AWBURST = AXI_INCR;
	assign	M_AXI_AWCACHE = M_AXI_AWLOCK ? 0: OPT_CACHE;
	assign	M_AXI_AWPROT  = OPT_PROT;
	assign	M_AXI_AWQOS   = OPT_QOS;
	assign	M_AXI_WLAST   = 1;

	assign	M_AXI_ARID    = AXI_ID;
	assign	M_AXI_ARLEN   = 0;
	assign	M_AXI_ARBURST = AXI_INCR;
	assign	M_AXI_ARCACHE = M_AXI_ARLOCK ? 0: OPT_CACHE;
	assign	M_AXI_ARPROT  = OPT_PROT;
	assign	M_AXI_ARQOS   = OPT_QOS;
	// }}}

	// shifted_wstrb_*
	// {{{
	always @(*)
		shifted_wstrb_word = { {(2*DW/8-4){1'b0}},
						4'b1111} << i_addr[AXILSB-1:0];

	always @(*)
		shifted_wstrb_halfword = { {(2*DW/8-4){1'b0}},
						4'b0011} << i_addr[AXILSB-1:0];

	always @(*)
		shifted_wstrb_byte = { {(2*DW/8-4){1'b0}},
						4'b0001} << i_addr[AXILSB-1:0];
	// }}}

	// Swapping WSTRB bits
	// {{{
	generate if (SWAP_WSTRB)
	begin : SWAPPING_WSTRB
		// {{{
		genvar	gw, gb;

		for(gw=0; gw<2*DW/32; gw=gw+1)
		begin : FOREACH_32B_WORD
		for(gb=0; gb<32/8; gb=gb+1)
		begin : FOREACH_BYTE

		always @(*)
		begin
			swapped_wstrb_word[gw*4+gb]
					= shifted_wstrb_word[gw*4+(3-gb)];
			swapped_wstrb_halfword[gw*4+gb]
					= shifted_wstrb_halfword[gw*4+(3-gb)];
			swapped_wstrb_byte[gw*4+gb]
					= shifted_wstrb_byte[gw*4+(3-gb)];
		end end end
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
	always @(*)
	begin
		swapaddr = i_addr[AXILSB-1:0];
		if (SWAP_WSTRB)
			swapaddr[1:0] = 3 - i_addr[1:0];
	end

	initial	axi_wdata = 0;
	initial	axi_wstrb = 0;
	initial	next_wdata  = 0;
	initial	next_wstrb  = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
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
		if (OPT_LOWPOWER)
		begin
			// {{{
			casez(i_op[2:1])
			2'b10: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-16){1'b0}},
				    i_data[15:0] } << (8*swapaddr);
			2'b11: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-8){1'b0}},
				    i_data[7:0] } << (8*swapaddr);
			default: { next_wdata, axi_wdata }
				<= { {(2*C_AXI_DATA_WIDTH-32){1'b0}},
				    i_data } << (8*swapaddr);
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

		r_op <= { i_op[2:1] , i_addr[AXILSB-1:0] };

		// On a read set everything to zero but only if OPT_LOWPOWER
		// is set
		// {{{
		if (OPT_LOWPOWER && !i_op[0])
			{ next_wstrb, next_wdata, axi_wstrb, axi_wdata } <= 0;

		if (w_misalignment_err)
			{ next_wstrb, next_wdata } <= 0;
		if (OPT_LOWPOWER)
		begin
			if (w_misalignment_err)
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
		if (OPT_LOWPOWER)
			{ next_wdata, next_wstrb } <= 0;
		// }}}
	end else if (OPT_LOWPOWER && M_AXI_WREADY)
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
	2'b0?: w_misaligned = (i_addr[AXILSB-1:0]+3) >= (1<<AXILSB);
	// Half word
	2'b10: w_misaligned = (i_addr[AXILSB-1:0]+1) >= (1<<AXILSB);
	// Bytes are always aligned
	2'b11: w_misaligned = 1'b0;
	endcase
	// }}}

	// w_misalignment_err
	// {{{
	always @(*)
	begin
		w_misalignment_err = OPT_ALIGNMENT_ERR && w_misaligned;
		if (OPT_LOCK && i_lock)
		begin
			casez(i_op[2:1])
			2'b0?: w_misalignment_err = (|i_addr[1:0]);
			2'b10: w_misalignment_err = i_addr[0];
			default:
				w_misalignment_err = 1'b0;
			endcase
		end
	end
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

		// misaligned_request
		// {{{
		initial	misaligned_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_request <= w_misaligned
						&& !w_misalignment_err;
		else if ((M_AXI_WVALID && M_AXI_WREADY)
					|| (M_AXI_ARVALID && M_AXI_ARREADY))
			misaligned_request <= 1'b0;
		// }}}

		// misaligned_aw_request
		// {{{	
		initial	misaligned_aw_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_aw_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_aw_request <= w_misaligned && i_op[0]
					&& !w_misalignment_err;
		else if (M_AXI_AWREADY)
			misaligned_aw_request <= 1'b0;
		// }}}

		// misaligned_response_pending
		// {{{
		initial	misaligned_response_pending = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_response_pending <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_response_pending <= w_misaligned
						&& !w_misalignment_err;
		else if (M_AXI_BVALID || M_AXI_RVALID)
			misaligned_response_pending <= 1'b0;
		// }}}

		// misaligned_read
		// {{{
		initial	misaligned_read = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_read <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			misaligned_read <= w_misaligned && !i_op[0]
						&& !w_misalignment_err;
		else if (M_AXI_RVALID)
			misaligned_read <= (misaligned_response_pending);
		// }}}

		// pending_err
		// {{{
		always @(posedge i_clk)
		if (!S_AXI_ARESETN || i_stb || (!M_AXI_BREADY && !M_AXI_RREADY)
				|| o_err || r_flushing || i_cpu_reset)
			pending_err <= 1'b0;
		else if ((M_AXI_BVALID && M_AXI_BRESP[1])
				|| (M_AXI_RVALID && M_AXI_RRESP[1]))
			pending_err <= 1'b1;
		// }}}

		// }}}
	end endgenerate
	// }}}

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || r_flushing || i_cpu_reset)
		o_valid <= 1'b0;
	else if (r_lock)
		o_valid <= (M_AXI_RVALID && M_AXI_RRESP == EXOKAY)
				|| (M_AXI_BVALID && M_AXI_BRESP == OKAY);
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
	else if (i_stb && w_misalignment_err)
		o_err <= 1'b1;
	else if (r_lock)
	begin
		o_err <= (M_AXI_BVALID && M_AXI_BRESP[1])
			 || (M_AXI_RVALID && M_AXI_RRESP != EXOKAY);
	end else if ((M_AXI_BVALID || M_AXI_RVALID)
						&& !misaligned_response_pending)
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
		o_rdbusy = (M_AXI_BREADY && r_lock)
			|| (M_AXI_RREADY && !r_flushing);
		if (r_flushing)
			o_rdbusy <= 1'b0;
	end
	// }}}

	// o_wreg
	// {{{
	always @(posedge i_clk)
	if (i_stb)
	begin
		o_wreg    <= i_oreg;
		if (OPT_LOCK && i_stb && i_lock && i_op[0])
			o_wreg[3:0] <= 4'hf;
	end
	// }}}

	// r_pc
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!OPT_LOCK)
		r_pc <= 0;
	else if (i_stb && i_lock && !i_op[0])
		r_pc <= i_restart_pc;
	// }}}

	// last_result, o_result
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER &&(!M_AXI_RREADY || !S_AXI_ARESETN))
		{ last_result, o_result } <= 0;
	else begin
		// {{{
		if (M_AXI_BVALID && (!OPT_LOWPOWER
					|| (r_lock && M_AXI_BRESP == OKAY)))
		begin
			o_result <= 0;
			o_result[AW-1:0] <= r_pc;
		end

		if (M_AXI_RVALID)
		begin
			// {{{
			if (!misaligned_response_pending && OPT_LOWPOWER)
				last_result <= 0;
			else
				last_result <= M_AXI_RDATA;

			if (OPT_ALIGNMENT_ERR)
				last_result <= 0;

			// Verilator lint_off WIDTH
			if (misaligned_read && !OPT_ALIGNMENT_ERR)
				o_result <= { M_AXI_RDATA, last_result }
						>> (8*r_op[AXILSB-1:0]);
			else
				o_result <= { 32'h0, M_AXI_RDATA }
						>> (8*r_op[AXILSB-1:0]);
			// Verilator lint_on WIDTH

			casez(r_op[AXILSB +: 2])
			2'b10: o_result[31:16] <= 0;
			2'b11: o_result[31: 8] <= 0;
			default: begin end
			endcase
			// }}}
		end
		// }}}
	end
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXI_BID, M_AXI_RID, M_AXI_RLAST };
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
	// Local declarations
	// {{{
`define	ASSERT	assert
`ifdef	AXIOPS
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	localparam	F_LGDEPTH = 10;

	wire	[F_LGDEPTH-1:0]	faxi_awr_nbursts,
				faxi_rd_nbursts, faxi_rd_outstanding;
	wire	[8:0]		faxi_wr_pending;
	wire	[IW-1:0]	faxi_wr_checkid;
	wire			faxi_wr_ckvalid;
	wire	[F_LGDEPTH-1:0]	faxi_wrid_nbursts;
	wire	[AW-1:0]	faxi_wr_addr;
	wire	[7:0]		faxi_wr_incr;
	wire	[1:0]		faxi_wr_burst;
	wire	[2:0]		faxi_wr_size;
	wire	[7:0]		faxi_wr_len;
	wire			faxi_wr_lockd;
	//
	wire	[IW-1:0]	faxi_rd_checkid;
	wire			faxi_rd_ckvalid;
	wire	[8:0]		faxi_rd_cklen;
	wire	[AW-1:0]	faxi_rd_ckaddr;
	wire	[7:0]		faxi_rd_ckincr;
	wire	[1:0]		faxi_rd_ckburst;
	wire	[2:0]		faxi_rd_cksize;
	wire	[7:0]		faxi_rd_ckarlen;
	wire			faxi_rd_cklockd;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_nbursts, faxi_rdid_outstanding;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_ckign_nbursts, faxi_rdid_ckign_outstanding;

	wire	[1:0]		faxi_ex_state;
	wire			faxi_ex_checklock;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_bursts_to_lock;
	wire	[F_LGDEPTH-1:0]	faxi_wrid_bursts_to_exwrite;
	(* anyseq *)	wire	f_active_lock;
	reg	[AW-1:0]	f_exlock_addr;
	wire	[AW-1:0]	faxi_exreq_addr;
	wire	[7:0]		f_exlock_len, faxi_exreq_len;
	wire	[1:0]		f_exlock_burst, faxi_exreq_burst;
	wire	[2:0]		faxi_exreq_size;
	reg	[2:0]		f_exlock_size;
	wire			faxi_exlock_return;

	wire			f_pc, f_gie, f_read_cycle, f_exwrite_cycle;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;
	always @(*)
	if (!f_past_valid)
		`ASSUME(!S_AXI_ARESETN);
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	
	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.OPT_EXCLUSIVE(OPT_LOCK),
		.F_OPT_ASSUME_RESET(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxi(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_axi_reset_n(S_AXI_ARESETN),
		//
		// Write address channel
		// {{{
		.i_axi_awvalid(M_AXI_AWVALID),
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
		// }}}
		// Write data
		// {{{
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wlast( M_AXI_WLAST),
		// }}}
		// Write return
		// {{{
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid( M_AXI_BID),
		.i_axi_bresp( M_AXI_BRESP),
		// }}}
		// Read address
		// {{{
		.i_axi_arvalid(M_AXI_ARVALID),
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
		// }}}
		// Read return
		// {{{
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rid(   M_AXI_RID),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rlast( M_AXI_RLAST),
		.i_axi_rresp( M_AXI_RRESP),
		// }}}
		// Induction values
		// {{{
		.f_axi_awr_nbursts(faxi_awr_nbursts),
		.f_axi_wr_pending(faxi_wr_pending),
		.f_axi_rd_nbursts(faxi_rd_nbursts),
		.f_axi_rd_outstanding(faxi_rd_outstanding),
		// Write counters
		// {{{
		.f_axi_wr_checkid(faxi_wr_checkid),
		.f_axi_wr_ckvalid(faxi_wr_ckvalid),
		.f_axi_wrid_nbursts(faxi_wrid_nbursts),
		.f_axi_wr_addr(faxi_wr_addr),
		.f_axi_wr_incr(faxi_wr_incr),
		.f_axi_wr_burst(faxi_wr_burst),
		.f_axi_wr_size(faxi_wr_size),
		.f_axi_wr_len(faxi_wr_len),
		.f_axi_wr_lockd(faxi_wr_lockd),
		// }}}
		// Read counters
		// {{{
		.f_axi_rd_checkid(faxi_rd_checkid),
		.f_axi_rd_ckvalid(faxi_rd_ckvalid),
		.f_axi_rd_cklen(faxi_rd_cklen),
		.f_axi_rd_ckaddr(faxi_rd_ckaddr),
		.f_axi_rd_ckincr(faxi_rd_ckincr),
		.f_axi_rd_ckburst(faxi_rd_ckburst),
		.f_axi_rd_cksize(faxi_rd_cksize),
		.f_axi_rd_ckarlen(faxi_rd_ckarlen),
		.f_axi_rd_cklockd(faxi_rd_cklockd),
		.f_axi_rdid_nbursts(faxi_rdid_nbursts),
		.f_axi_rdid_outstanding(faxi_rdid_outstanding),
		.f_axi_rdid_ckign_nbursts(faxi_rdid_ckign_nbursts),
		.f_axi_rdid_ckign_outstanding(faxi_rdid_ckign_outstanding),
		// }}}
		// Exclusive access checks
		// {{{
		.f_axi_ex_state(faxi_ex_state),
		.f_axi_ex_checklock(faxi_ex_checklock),
		.f_axi_rdid_bursts_to_lock(faxi_rdid_bursts_to_lock),
		.f_axi_wrid_bursts_to_exwrite(faxi_wrid_bursts_to_exwrite),
		.i_active_lock( f_active_lock),
		.i_exlock_addr( f_exlock_addr),
		.i_exlock_len(  f_exlock_len),
		.i_exlock_burst(f_exlock_burst),
		.i_exlock_size( f_exlock_size),
		.f_axi_exreq_addr( faxi_exreq_addr),
		.f_axi_exreq_len(  faxi_exreq_len),
		.f_axi_exreq_burst(faxi_exreq_burst),
		.f_axi_exreq_size( faxi_exreq_size),
		.f_axi_exreq_return( faxi_exlock_return)
		// }}}
		// }}}
		// }}}
	);

	always @(*)
	begin
		assert(faxi_wrid_nbursts == faxi_awr_nbursts);
		assert(faxi_rdid_nbursts == faxi_rd_nbursts);
		assert(faxi_rdid_outstanding == faxi_rd_outstanding);
		assert(faxi_rd_nbursts == faxi_rd_outstanding);

		assume(faxi_rd_checkid == faxi_wr_checkid);
		assume(faxi_rd_checkid == AXI_ID);

		if (faxi_wr_ckvalid)
		begin
			assert(faxi_wr_burst == M_AXI_AWBURST);
			// assert(faxi_wr_size  == M_AXI_AWSIZE);
			assert(faxi_wr_len   == M_AXI_AWLEN);	// == 0
			assert(faxi_wr_lockd == r_lock);
		end

		if (faxi_rd_ckvalid)
		begin
			assert(faxi_rd_ckburst == M_AXI_ARBURST);
			// assert(faxi_rd_cksize  == M_AXI_ARSIZE);
			assert(faxi_rd_ckarlen == M_AXI_ARLEN);	// == 0
			assert(faxi_rd_cklockd == r_lock);
		end

		if (misaligned_request)
			`ASSERT(M_AXI_WVALID || M_AXI_ARVALID);
		if (misaligned_aw_request)
			`ASSERT(M_AXI_AWVALID);

		if (!misaligned_response_pending)
		begin
			`ASSERT(faxi_rd_outstanding  <= (M_AXI_ARVALID ? 0:1));
			// `ASSERT(faxi_wr_outstanding  <= (M_AXI_WVALID ? 0:1));
			`ASSERT(faxi_awr_nbursts <= (M_AXI_AWVALID ? 0:1));

			`ASSERT(!misaligned_request);
			`ASSERT(!misaligned_aw_request);
		end else if (M_AXI_RREADY)
			`ASSERT(misaligned_read);

		if (!M_AXI_RREADY)
		begin
			`ASSERT(!M_AXI_ARVALID);
			`ASSERT(faxi_rd_outstanding == 0);
			`ASSERT(misaligned_read == 1'b0);
		end else begin
			if (misaligned_request)
				`ASSERT(faxi_rd_outstanding <= 0);
			`ASSERT(faxi_rd_outstanding <= 1 + (misaligned_read ? 1:0));
			// `ASSERT(faxi_rd_outstanding ==
			//	(M_AXI_RREADY && misaligned_request) ? 1:0)
			//	((M_AXI_RREADY && !M_AXI_RVALID) ? 1:0)
			//	);
		end

		if (!M_AXI_BREADY)
		begin
			`ASSERT(!M_AXI_AWVALID);
			`ASSERT(!M_AXI_WVALID);
			`ASSERT(faxi_awr_nbursts == 0);
			`ASSERT(faxi_wr_pending  == 0);
		end else begin
			if (misaligned_request)
				`ASSERT(faxi_wr_pending == (((!M_AXI_AWVALID || !misaligned_aw_request) && M_AXI_WVALID) ? 1:0));

			if (misaligned_aw_request)
			begin
				`ASSERT(faxi_awr_nbursts == 0);
				`ASSERT(misaligned_request);
				`ASSERT(M_AXI_AWVALID);
				`ASSERT(M_AXI_WVALID);
			end
			`ASSERT(!M_AXI_AWVALID || M_AXI_WVALID);
			`ASSERT(faxi_awr_nbursts <= 2);
			`ASSERT(faxi_wr_pending <= 2);

			case({misaligned_request,
					misaligned_aw_request,
					misaligned_response_pending})
			3'b000: begin
				`ASSERT(faxi_awr_nbursts<= (M_AXI_BREADY ? 1:0));
				`ASSERT(faxi_wr_pending <= (M_AXI_BREADY ? 1:0));
				end
			3'b001: begin
				`ASSERT(faxi_awr_nbursts<= 1 + (M_AXI_AWVALID ? 0:1));
				`ASSERT(faxi_wr_pending <= 1 + (M_AXI_WVALID ? 0:1));
				end
			3'b010: `ASSERT(0);
			3'b011: begin
				`ASSERT(faxi_wr_pending<= 1 + (M_AXI_WVALID ? 0:1));
				`ASSERT(faxi_awr_nbursts == 0);
				`ASSERT(M_AXI_AWVALID);
				end
			3'b100: `ASSERT(0);
			3'b101: begin
				`ASSERT(faxi_awr_nbursts<= 1 + (M_AXI_AWVALID ? 0:1));
				// `ASSERT(faxi_wr_pending == 0);
				`ASSERT(M_AXI_WVALID);
				end
			3'b110: `ASSERT(0);
			3'b111: begin
				`ASSERT(faxi_awr_nbursts == 0);
				// `ASSERT(faxi_wr_pending == 0);
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

	// f_exlock_*
	// {{{
	initial	f_exlock_size = 3'b010;
	always @(posedge i_clk)
	if (M_AXI_ARVALID && M_AXI_ARREADY && M_AXI_ARLOCK)
	begin
		f_exlock_addr <= M_AXI_ARADDR;
		f_exlock_size <= M_AXI_ARSIZE;
	end

	assign	f_exlock_len = 0;
	assign	f_exlock_burst = M_AXI_AWBURST;
	// }}}

	always @(*)
	if (!o_busy)
		`ASSERT(!r_flushing);

	// Following any i_stb request, assuming we are idle, immediately
	// begin a bus transaction
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_stb && !o_err))
		&&(!$past(o_busy))&&($past(!i_cpu_reset)))
	begin
		`ASSERT(o_busy || ($past(w_misalignment_err) && o_err));
	end

	always @(*)
		`ASSERT(o_busy == (M_AXI_BREADY || M_AXI_RREADY));

	always @(*)
	if (o_busy && !misaligned_request && OPT_LOWPOWER)
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
			begin
				`ASSERT((!o_err && pending_err) || r_flushing);
			end else
				`ASSERT(o_err);
		end else if ($past(M_AXI_RVALID && M_AXI_RRESP[1]
				|| (M_AXI_RVALID && r_lock && M_AXI_RRESP != EXOKAY)))
		begin
			if ($past(misaligned_response_pending))
			begin
				`ASSERT((!o_err && pending_err) || r_flushing);
			end else
				`ASSERT(o_err);
		end else if ($past(i_stb && w_misalignment_err))
		begin
			`ASSERT(o_err);
		end else if (!$past(pending_err))
			`ASSERT(!o_err);
		//else if ($past(misaligned))
			//`ASSERT(o_err);
	end

	always @(*)
	if (misaligned_response_pending || misaligned_aw_request
				|| misaligned_read || misaligned_request)
		assert(!r_lock);

	always @(*)
	if (o_busy && misaligned_response_pending)
		`ASSERT(!pending_err);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_cpu_reset))&&($past(i_stb)))
	begin
		// On a write, assert o_wb_we should be true
		assert($past(i_op[0] && !o_err && !w_misalignment_err)
				== (M_AXI_AWVALID && M_AXI_WVALID));
	end

	always @(*)
	if (r_lock && M_AXI_BREADY)
		assert(o_wreg[3:0] == 4'hf);

	// }}}

/*
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
*/
	////////////////////////////////////////////////////////////////////////
	//
	// Zero on idle checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_LOWPOWER)
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
	// }}}
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
	else begin
		f_done <= (M_AXI_RVALID && !M_AXI_RRESP[1]
			|| M_AXI_BVALID && !M_AXI_BRESP[1]);
		if (pending_err || misaligned_response_pending)
			f_done <= 0;
	end

	fmem #(
		// {{{
		.IMPLEMENT_LOCK(OPT_LOCK),
		.OPT_AXI_LOCK(1)
		// }}}
	) fcheck(
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
		.f_axi_write_cycle(f_exwrite_cycle),
		.f_last_reg(f_last_reg), .f_addr_reg(f_addr_reg)
		// }}}
	);

	always @(*)
	if (r_flushing)
	begin
		`ASSERT(cpu_outstanding <= 0);
	end else begin
		`ASSERT(cpu_outstanding == (o_busy ? 1:0)
			+ ((f_done || o_err) ? 1 : 0));
	end

	always @(*)
	if (o_rdbusy && M_AXI_BREADY)
	begin
		assert(f_exwrite_cycle);
		assert(r_lock);
	end else if (M_AXI_RREADY)
		assert(!f_exwrite_cycle);

	always @(*)
	if (M_AXI_BREADY && (M_AXI_AWLOCK || f_exwrite_cycle || r_lock))
	begin
		assert(!pending_err);
		assert(!misaligned_response_pending);
		assert(M_AXI_AWLOCK && f_exwrite_cycle && r_lock);
		if (f_active_lock)
			assert((M_AXI_AWVALID || M_AXI_WVALID) || faxi_ex_state == 2'b11);
	end else
		assert(faxi_ex_state != 2'b11);

	always @(*)
	if (M_AXI_RREADY && !r_flushing)
		assert(f_last_reg == o_wreg);

	always @(*)
	if (f_pc || (r_lock && M_AXI_BREADY))
	begin
		assert(o_wreg[3:1] == 3'h7);
	end else if (o_rdbusy)
		assert(o_wreg[3:1] != 3'h7);

//	always @(*)
//	if (cpu_outstanding > 0 && (M_AXI_RREADY || (!r_lock && !o_err)))
//		assert(o_wreg == f_last_reg);

	always @(*)
	if (o_busy)
		assert(o_wreg[4] == f_gie);

	always @(*)
	if (M_AXI_RREADY)
	begin
		assert(f_read_cycle || r_flushing);
	end else if (M_AXI_BREADY)
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

	generate if (OPT_LOCK)
	begin : COVER_LOCK

		always @(posedge i_clk)
			cover(r_lock);

		always @(posedge i_clk)
			cover(o_valid && $past(r_lock && M_AXI_RVALID));

		always @(posedge i_clk)
			cover(!o_valid && !o_err && faxi_ex_state == 2'b10);

		always @(posedge i_clk)
			cover(i_stb && i_op[0] && i_lock && faxi_ex_state == 2'b10);

		always @(posedge i_clk)
			cover(i_stb && i_op[0] && i_lock && faxi_ex_state == 2'b10 && !w_misalignment_err);
		always @(posedge i_clk)
		if (S_AXI_ARESETN && $past(S_AXI_ARESETN)
			&& !i_cpu_reset && !$past(i_cpu_reset))
			cover($past(i_stb && i_op[0] && i_lock && faxi_ex_state == 2'b10 && !w_misalignment_err));

		always @(posedge i_clk)
			cover(M_AXI_AWVALID && M_AXI_AWLOCK);
		always @(posedge i_clk)
			cover(M_AXI_BVALID && r_lock);

		always @(posedge i_clk)
			cover(o_valid && $past(r_lock && M_AXI_BVALID));

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (i_stb && i_op[0] && i_lock)
	begin
		assume(i_addr == f_exlock_addr);
		assume(faxi_ex_state == 2'b10);

		casez(i_op[2:1])
		2'b0?: assume(f_exlock_size == 3'b010);
		2'b10: assume(f_exlock_size == 3'b001);
		2'b11: assume(f_exlock_size == 3'b000);
		endcase
	end

	always @(*)
	if (faxi_ex_state == 2'b10)
	begin
		assert(f_exlock_addr  == faxi_exreq_addr);
		assert(f_exlock_len   == faxi_exreq_len);
		assert(f_exlock_size  == faxi_exreq_size);
		assert(f_exlock_burst == faxi_exreq_burst);
	end

	always @(*)
	if (i_stb && i_lock)
		assume(!i_cpu_reset);

always @(*)
assume(S_AXI_ARESETN != i_cpu_reset);
	// }}}
`endif
// }}}
endmodule
// yosys -p 'read -sv axiops.v ; synth_xiling -flatten -top axiops'
//
// Usage (from yosys):
//			(!ZOI)		(ZOI)
//	Cells		 877		1029
//	  FDRE,FDSE	 216		 209
//	  LUT1		   5		   2
//	  LUT2		  33		  42
//	  LUT3		  84		  11
//	  LUT4		  45		  30
//	  LUT5		  54		  92
//	  LUT6		  35		 158
//	  MUX7		  29		  34
//	  MUX8		   8
//	Estimated LCs:	 218		 292
//
//