////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axilops.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU based upon AXI-lite.  This is
//		a very basic memory unit designed to be low on logic and yet
//	to still support a lot of options.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
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
module	axilops #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	C_AXI_ADDR_WIDTH = ADDRESS_WIDTH,
		parameter	C_AXI_DATA_WIDTH = 32,
		//
		// SWAP_ENDIANNESS
		// {{{
		// The ZipCPU was designed to be a big endian machine.  With
		// no other adjustments, this design will make the ZipCPU
		// *little* endian, for the simple reason that the AXI bus is
		// a little endian bus.  However, if SWAP_ENDIANNESS is set,
		// the bytes within 32-bit words on the AXI bus will be swapped.
		// This will return the CPU to being a big endian CPU on a
		// little endian bus.  It will also break any design that
		// assumes the bus is presented to it in its proper order.
		// Simple things like counters or interrupt controllers will
		// therefore cease to work with this option unless they also
		// swap the endianness of the words they are given.
		parameter [0:0]	SWAP_ENDIANNESS = 1'b0,
		// }}}
		// SWAP_WSTRB
		// {{{
		// SWAP_WSTRB represents a second attempt to fix the endianness
		// issue.  It is incompatible with the SWAP_ENDIANNESS option
		// above.  If SWAP_WSTRB is set, then half words and words will
		// be placed on the bus in little endian order, but at big
		// endian addresses.  Words written to the bus will be written
		// in little endian order.  Halfwords written to the bus at
		// address 2 will be written to address 0, halfwords written to
		// address 0 will be written to address 2.  Bytes written to the
		// but at address 3 will be written to address 0, address 2
		// will be written to address 1, address 1 to address 2, and
		// address 3 to address 0.
		//
		// This may just be a half baked attempt to solve this problem,
		// since it will fail if you ever trie to access bytes or
		// halfwords at other than their intended widths.
		parameter [0:0]	SWAP_WSTRB = 1'b0,
		// }}}
		// OPT_SIGN_EXTEND
		// {{{
		// Some CPU's want memory accesses to be sign extended upon
		// return.  The ZipCPU is not one of those CPU's.  However,
		// since it's fairly easy to do so, we'll implement this logic
		// if ever OPT_SIGN_EXTEND is true so you can see how it would
		// be done if necessary.
		parameter [0:0]	OPT_SIGN_EXTEND = 1'b0,
		// }}}
		// OPT_ALIGNMENT_ERR
		// {{{
		// If set, OPT_ALIGNMENT_ERR will generate an alignment error
		// on any attempt to write to or read from an unaligned word.
		// If not set, unaligned reads (or writes) will be expanded into
		// pairs so as to still accomplish the action requested.  The
		// bus does not guarantee protection, however, that these two
		// writes or two reads will proceed uninterrupted.  Since
		// unaligned writes and unaligned reads are no longer
		// guaranteed to be atomic by the AXI bus, it is possible that
		// any unaligned operations might yield an incoherent result.
		parameter [0:0]		OPT_ALIGNMENT_ERR = 1'b1,
		// }}}
		// OPT_LOWPOWER
		// {{{
		// If set, the design will use extra logic to guarantee that any
		// unused registers are kept at zero until they are used.  This
		// will help to guarantee the design (ideally) has fewer
		// transitions and therefore uses lower power.
		parameter [0:0]		OPT_LOWPOWER = 1'b0,
		// }}}
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
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
		output	reg	[AW-1:0]		M_AXI_AWADDR,
		// verilator coverage_off
		output	wire	[2:0]			M_AXI_AWPROT,
		// verilator coverage_on
		//
		output	reg				M_AXI_WVALID,
		input	wire				M_AXI_WREADY,
		output	reg	[DW-1:0]		M_AXI_WDATA,
		output	reg	[DW/8-1:0]		M_AXI_WSTRB,
		//
		input	wire				M_AXI_BVALID,
		output	reg				M_AXI_BREADY,
		input	wire	[1:0]			M_AXI_BRESP,
		// }}}
		// Reads
		// {{{
		output	reg				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	reg	[AW-1:0]		M_AXI_ARADDR,
		// verilator coverage_off
		output	wire	[2:0]			M_AXI_ARPROT,
		// verilator coverage_on
		//
		input	wire				M_AXI_RVALID,
		output	reg				M_AXI_RREADY,
		input	wire	[DW-1:0]		M_AXI_RDATA,
		input	wire	[1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	wire	i_clk = S_AXI_ACLK;
	// wire	i_reset = !S_AXI_ARESETN;

	reg	w_misaligned, w_misalignment_err;
	wire	misaligned_request, misaligned_aw_request,
		misaligned_response_pending, pending_err, misaligned_read;
	reg	r_flushing;
	reg	[AXILSB+1:0]		r_op;
	reg	[DW-1:0]		next_wdata;
	reg	[DW/8-1:0]		next_wstrb;
	reg	[DW-1:0]		last_result;
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
	reg	[AXILSB-1:0]		swapaddr;
	wire	[DW-1:0]		endian_swapped_rdata;
	reg	[31:0]			pre_result;
	reg	[2*DW-1:0]		wide_return;

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
		M_AXI_AWVALID <=  i_op[0];	// Write request
		M_AXI_WVALID  <=  i_op[0];	// Write request
		M_AXI_ARVALID <= !i_op[0];	// Read request

		// Set BREADY or RREADY to accept the response.  These will
		// remain ready until the response is returned.
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

	// r_flushing
	// {{{
	initial	r_flushing = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
		// If everything is reset, then we don't need to worry about
		// or wait for any pending returns--they'll be canceled by the
		// global reset.
		r_flushing <= 1'b0;
	else if (M_AXI_BREADY || M_AXI_RREADY)
	begin
		if (i_cpu_reset)
			// If only the CPU is reset, however, we have a problem.
			// The bus hasn't been reset, and so it is still active.
			// We can't respond to any new requests from the CPU
			// until we flush any transactions that are currently
			// active.
			r_flushing <= 1'b1;
		if (M_AXI_BVALID || M_AXI_RVALID)
			// A request just came back, therefore we can clear
			// r_flushing
			r_flushing <= 1'b0;
		if (misaligned_response_pending)
			// ... unless we're in the middle of a misaligned
			// request.  In that case, there will be a second
			// return that we still need to wait for.  This request,
			// though, will clear misaligned_response_pending.
			r_flushing <= r_flushing || i_cpu_reset;
	end else
		// If nothing is active, we don't care about the CPU reset.
		// Flushing just stays at zero.
		r_flushing <= 1'b0;
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

		if (SWAP_ENDIANNESS || SWAP_WSTRB)
		begin
			// When adjusting endianness, reads (or writes) are
			// always full words.  This is important since the
			// the bytes at issues may (or may not) be in their
			// expected locations
			if (OPT_ALIGNMENT_ERR)
				M_AXI_AWADDR[AXILSB-1:0] <= 0;
			else
				M_AXI_AWADDR[1:0] <= 0;
		end
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

	// AxPROT
	// {{{
	localparam [2:0]	AXI_UNPRIVILEGED_NONSECURE_DATA_ACCESS = 3'h0;
	localparam [2:0]	OPT_PROT=AXI_UNPRIVILEGED_NONSECURE_DATA_ACCESS;

	assign	M_AXI_AWPROT  = OPT_PROT;
	assign	M_AXI_ARPROT  = OPT_PROT;
	// }}}

	// shifted_wstrb_*
	// {{{
	generate if (SWAP_WSTRB)
	begin : BIG_ENDIAN_WSTRB
		always @(*)
			shifted_wstrb_word = { 4'b1111, {(2*DW/8-4){1'b0}} }
						>> i_addr[AXILSB-1:0];

		always @(*)
			shifted_wstrb_halfword = { 2'b11, {(2*DW/8-2){1'b0}} }
						>> i_addr[AXILSB-1:0];

		always @(*)
			shifted_wstrb_byte = { 1'b1, {(2*DW/8-1){1'b0}} }
						>> i_addr[AXILSB-1:0];
	end else begin : NORMAL_SHIFTED_WSTRB
		always @(*)
		shifted_wstrb_word = { {(2*DW/8-4){1'b0}},
						4'b1111} << i_addr[AXILSB-1:0];

		always @(*)
		shifted_wstrb_halfword = { {(2*DW/8-4){1'b0}},
						4'b0011} << i_addr[AXILSB-1:0];

		always @(*)
		shifted_wstrb_byte = { {(2*DW/8-4){1'b0}},
						4'b0001} << i_addr[AXILSB-1:0];
	end endgenerate
	// }}}

	// Swapping WSTRB bits
	// {{{
	generate if (SWAP_ENDIANNESS)
	begin : SWAPPING_ENDIANNESS
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
		swapaddr = i_addr[AXILSB-1:0];

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
		if (SWAP_WSTRB)
		begin
			casez(i_op[2:1])
			2'b10: { axi_wdata, next_wdata }
				<= { i_data[15:0], {(2*C_AXI_DATA_WIDTH-16){1'b0}} }
					>> (8*swapaddr);
			2'b11: { axi_wdata, next_wdata }
				<= { i_data[7:0], {(2*C_AXI_DATA_WIDTH-8){1'b0}} }
					>> (8*swapaddr);
			default: { axi_wdata, next_wdata }
				<= { i_data, {(2*C_AXI_DATA_WIDTH-32){1'b0}} }
					>> (8*swapaddr);
			endcase
		end else begin
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
		end

		// next_wstrb, axi_wstrb
		// {{{
		if (SWAP_WSTRB)
		begin
			casez(i_op[2:1])
			2'b0?: { axi_wstrb, next_wstrb } <= swapped_wstrb_word;
			2'b10: { axi_wstrb, next_wstrb } <= swapped_wstrb_halfword;
			2'b11: { axi_wstrb, next_wstrb } <= swapped_wstrb_byte;
			endcase
		end else begin
			casez(i_op[2:1])
			2'b0?: { next_wstrb, axi_wstrb } <= swapped_wstrb_word;
			2'b10: { next_wstrb, axi_wstrb } <= swapped_wstrb_halfword;
			2'b11: { next_wstrb, axi_wstrb } <= swapped_wstrb_byte;
			endcase
		end
		// }}}

		r_op <= { i_op[2:1] , i_addr[AXILSB-1:0] };

		// On a read set everything to zero but only if OPT_LOWPOWER
		// is set
		// {{{
		if (OPT_LOWPOWER && !i_op[0])
			{ next_wstrb, next_wdata, axi_wstrb, axi_wdata } <= 0;

		if (OPT_ALIGNMENT_ERR)
			{ next_wstrb, next_wdata } <= 0;
		if (OPT_LOWPOWER)
		begin
			if (w_misalignment_err)
				{ axi_wdata, axi_wstrb, r_op } <= 0;
			if (o_err || i_cpu_reset)
				{ next_wdata, next_wstrb,
					axi_wdata, axi_wstrb, r_op } <= 0;
		end
		// }}}
		// }}}
	end else if ((misaligned_request || !OPT_LOWPOWER) && M_AXI_WREADY)
	begin
		// {{{
		axi_wdata <= next_wdata;
		axi_wstrb <= next_wstrb;
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
	2'b0?: w_misaligned = ((i_addr[AXILSB-1:0]+3) >= (1<<AXILSB));
	// Half word
	2'b10: w_misaligned = ((i_addr[AXILSB-1:0]+1) >= (1<<AXILSB));
	// Bytes are always aligned
	2'b11: w_misaligned = 1'b0;
	endcase
	// }}}

	// w_misalignment_err
	// {{{
	always @(*)
	begin
		w_misalignment_err = OPT_ALIGNMENT_ERR && w_misaligned;
	end
	// }}}

	// misaligned_[aw_|]request, pending_err, misaligned_response_pending
	// {{{
	generate if (OPT_ALIGNMENT_ERR)
	begin : GEN_ALIGNMENT_ERR
		// {{{
		assign	misaligned_request = 1'b0;

		assign	misaligned_aw_request = 1'b0;
		assign	misaligned_response_pending = 1'b0;
		assign	misaligned_read = 1'b0;
		assign	pending_err = 1'b0;
		// }}}
	end else begin : GEN_REALIGNMENT
		// {{{
		reg	r_misaligned_request, r_misaligned_aw_request,
			r_misaligned_response_pending, r_misaligned_read,
			r_pending_err;

		// misaligned_request
		// {{{
		initial	r_misaligned_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			r_misaligned_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			r_misaligned_request <= w_misaligned
						&& !w_misalignment_err;
		else if ((M_AXI_WVALID && M_AXI_WREADY)
					|| (M_AXI_ARVALID && M_AXI_ARREADY))
			r_misaligned_request <= 1'b0;

		assign	misaligned_request = r_misaligned_request;
		// }}}

		// misaligned_aw_request
		// {{{
		initial	r_misaligned_aw_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			r_misaligned_aw_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			r_misaligned_aw_request <= w_misaligned && i_op[0]
					&& !w_misalignment_err;
		else if (M_AXI_AWREADY)
			r_misaligned_aw_request <= 1'b0;

		assign	misaligned_aw_request = r_misaligned_aw_request;
		// }}}

		// misaligned_response_pending
		// {{{
		initial	r_misaligned_response_pending = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			r_misaligned_response_pending <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			r_misaligned_response_pending <= w_misaligned
						&& !w_misalignment_err;
		else if (M_AXI_BVALID || M_AXI_RVALID)
			r_misaligned_response_pending <= 1'b0;

		assign	misaligned_response_pending
					= r_misaligned_response_pending;
		// }}}

		// misaligned_read
		// {{{
		initial	r_misaligned_read = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			r_misaligned_read <= 0;
		else if (i_stb && !o_err && !i_cpu_reset)
			r_misaligned_read <= w_misaligned && !i_op[0]
						&& !w_misalignment_err;
		else if (M_AXI_RVALID)
			r_misaligned_read <= (misaligned_response_pending);

		assign	misaligned_read = r_misaligned_read;
		// }}}

		// pending_err
		// {{{
		initial	r_pending_err = 1'b0;
		always @(posedge i_clk)
		if (i_cpu_reset || (!M_AXI_BREADY && !M_AXI_RREADY)
				|| r_flushing)
			r_pending_err <= 1'b0;
		else if ((M_AXI_BVALID && M_AXI_BRESP[1])
				|| (M_AXI_RVALID && M_AXI_RRESP[1]))
			r_pending_err <= 1'b1;

		assign	pending_err = r_pending_err;
		// }}}

		// }}}
	end endgenerate
	// }}}

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || r_flushing)
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
	else if (i_stb && w_misalignment_err)
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
	if (OPT_LOWPOWER && (!S_AXI_ARESETN || i_cpu_reset || o_err || (i_stb && w_misalignment_err)))
		o_wreg <= 0;
	else if (i_stb && (!OPT_LOWPOWER || !i_op[0]))
		o_wreg    <= i_oreg;
	else if (OPT_LOWPOWER && (o_valid || o_err))
		o_wreg <= 0;
	// }}}

	// endian_swapped_rdata
	// {{{
	generate if (SWAP_ENDIANNESS)
	begin : SWAP_RDATA_ENDIANNESS
		genvar	gw, gb;

		for(gw=0; gw<C_AXI_DATA_WIDTH/32; gw=gw+1)
		for(gb=0; gb<32/8; gb=gb+1)
			assign	endian_swapped_rdata[gw*32+gb*8 +: 8]
					= M_AXI_RDATA[gw*32+(3-gb)*8 +: 8];
	end else begin : KEEP_RDATA
		assign	endian_swapped_rdata = M_AXI_RDATA;
	end endgenerate
	// }}}

	// pre_result
	// {{{
	// The purpose of the pre-result is to guarantee that the synthesis
	// tool knows we want a shift of the full 2*DW width.
	always @(*)
	begin
		if (SWAP_WSTRB)
		begin
			if (misaligned_read && !OPT_ALIGNMENT_ERR)
				wide_return={ last_result, endian_swapped_rdata }
						<< (8*r_op[AXILSB-1:0]);
			else
				wide_return = { endian_swapped_rdata, {(DW){1'b0}} }
						<< (8*r_op[AXILSB-1:0]);

		end else begin
			if (misaligned_read && !OPT_ALIGNMENT_ERR)
				wide_return={ endian_swapped_rdata, last_result }
						>> (8*r_op[AXILSB-1:0]);
			else
				wide_return = { {(DW){1'b0}}, endian_swapped_rdata }
						>> (8*r_op[AXILSB-1:0]);
		end

		if (OPT_LOWPOWER && (!M_AXI_RVALID || M_AXI_RRESP[1]))
			wide_return = 0;
	end

	always @(*)
	begin
		if (SWAP_WSTRB)
		begin
			pre_result = 0;
			casez(r_op[AXILSB +: 2])
			2'b10: pre_result[15:0] = wide_return[(2*DW)-1:(2*DW)-16];
			2'b11: pre_result[7:0] = wide_return[(2*DW)-1:(2*DW)-8];
			default: pre_result[31:0] = wide_return[(2*DW-1):(2*DW-32)];
			endcase

		end else
			pre_result = wide_return[31:0];
	end

	// }}}
	// last_result, o_result
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER &&(!M_AXI_RREADY
			|| !S_AXI_ARESETN || r_flushing || i_cpu_reset))
		{ last_result, o_result } <= 0;
	else begin
		// {{{
		if (OPT_LOWPOWER)
			o_result <= 0;

		if (M_AXI_RVALID)
		begin
			// {{{
			if (OPT_LOWPOWER && (M_AXI_RRESP[1] || !misaligned_response_pending))
				last_result <= 0;
			else
				last_result <= endian_swapped_rdata;

			o_result <= pre_result[31:0];

			if (OPT_SIGN_EXTEND)
			begin
				// {{{
				// verilator coverage_off
				// Optionally sign extend the return result.
				//   ... would violate ZipCPU ISA
				casez(r_op[AXILSB +: 2])
				2'b10: o_result[31:16] <= {(16){pre_result[15]}};
				2'b11: o_result[31: 8] <= {(24){pre_result[7]}};
				default: begin end
				endcase
				// verilator coverage_on
				// }}}
			end else begin
				// Fill unused return bits with zeros
				casez(r_op[AXILSB +: 2])
				2'b10: o_result[31:16] <= 0;
				2'b11: o_result[31: 8] <= 0;
				default: begin end
				endcase
			end

			if (OPT_LOWPOWER && M_AXI_RRESP[1])
				o_result <= 0;
			// }}}
		end

		if (OPT_ALIGNMENT_ERR)
			last_result <= 0;

		if (OPT_LOWPOWER && (pending_err || misaligned_response_pending))
			o_result <= 0;
		// }}}
	end
	// }}}

	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_lock, M_AXI_RRESP[0], M_AXI_BRESP[0] };

	generate if (SWAP_WSTRB)
	begin : GEN_UNUSED_SWAP
		wire	wide_unused;

		if (SWAP_WSTRB)
		begin : UNUSED_SWAP_WSTRB
			assign	wide_unused = &{ 1'b0,
					wide_return[2*DW-32-1:0] };
		end else begin : UNUSED_NO_SWAP
			assign	wide_unused = &{ 1'b0, wide_return[2*DW-1:32] };
		end
	end endgenerate
	// verilator lint_on  UNUSED
	// verilator coverage_on
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
`ifdef	AXILOPS
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	localparam	F_LGDEPTH = 2;

	reg			f_misaligned;
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
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Bus property checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxil_master #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_OPT_ASSUME_RESET(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(M_AXI_AWVALID),
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awaddr( M_AXI_AWADDR),
		.i_axi_awprot( M_AXI_AWPROT),
		//
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		//
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bresp( M_AXI_BRESP),
		//
		.i_axi_arvalid(M_AXI_ARVALID),
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arprot( M_AXI_ARPROT),
		//
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rresp( M_AXI_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
	);


	always @(*)
	begin
		if (misaligned_request)
			`ASSERT(M_AXI_WVALID || M_AXI_ARVALID);
		if (misaligned_aw_request)
			`ASSERT(M_AXI_AWVALID);
		if (!misaligned_response_pending)
		begin
			`ASSERT(faxil_awr_outstanding <= (M_AXI_AWVALID ? 0:1));
			`ASSERT(faxil_wr_outstanding  <= (M_AXI_WVALID ? 0:1));
			`ASSERT(faxil_rd_outstanding  <= (M_AXI_ARVALID ? 0:1));

			`ASSERT(!misaligned_request);
			`ASSERT(!misaligned_aw_request);
		end else if (M_AXI_RREADY)
			`ASSERT(misaligned_read);

		if (!M_AXI_RREADY)
		begin
			`ASSERT(!M_AXI_ARVALID);
			`ASSERT(faxil_rd_outstanding == 0);
			// `ASSERT(misaligned_read == 1'b0);
		end else begin
			if (misaligned_request)
				`ASSERT(faxil_rd_outstanding == 0);
			`ASSERT(faxil_rd_outstanding <= 1 + (misaligned_read ? 1:0));
		end

		if (!M_AXI_BREADY)
		begin
			`ASSERT(!M_AXI_AWVALID);
			`ASSERT(!M_AXI_WVALID);
			`ASSERT(faxil_awr_outstanding == 0);
			`ASSERT(faxil_wr_outstanding  == 0);
		end else begin
			if (misaligned_request)
				`ASSERT(faxil_wr_outstanding == 0);
			if (misaligned_aw_request)
				`ASSERT(faxil_awr_outstanding == 0);
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
	end

	// f_misaligned
	// {{{
	always @(*)
	begin
		f_misaligned = 0;
		case(r_op[AXILSB +: 2])
		2'b01: f_misaligned = ((r_op[AXILSB-1:0] + 3) >= (1<<AXILSB));
		2'b10: f_misaligned = ((r_op[AXILSB-1:0] + 1) >= (1<<AXILSB));
		default: f_misaligned = 0;
		endcase

		if (!M_AXI_BREADY && !M_AXI_RREADY)
			f_misaligned = 0;
	end
	// }}}

	always @(*)
	if (!M_AXI_RREADY && !M_AXI_BREADY)
	begin
		// {{{
		assert(!misaligned_aw_request);
		assert(!misaligned_request);
		assert(!misaligned_response_pending);
		assert(faxil_awr_outstanding == 0);
		assert(faxil_wr_outstanding  == 0);
		assert(faxil_rd_outstanding  == 0);
		// }}}
	end else if (f_misaligned)
	begin
		// {{{
		assert(!OPT_ALIGNMENT_ERR);

		if (misaligned_aw_request || misaligned_request)
		begin
			// {{{
			if (misaligned_aw_request)
			begin
				assert(faxil_awr_outstanding == 0);
			end else if (M_AXI_BREADY)
			begin
				assert(faxil_awr_outstanding
					== (M_AXI_AWVALID ? 0:1)
						+ (misaligned_response_pending ? 1:0));
			end else
				assert(faxil_awr_outstanding == 0);

			if (misaligned_request && M_AXI_BREADY)
			begin
				assert(faxil_wr_outstanding  == 0);
				assert(faxil_rd_outstanding == 0);
			end else if (M_AXI_RREADY)
			begin
				assert(faxil_rd_outstanding
					== (M_AXI_ARVALID ? 0:1)
						+ (!misaligned_request && misaligned_response_pending ? 1:0));
				assert(faxil_wr_outstanding == 0);
			end else begin
				assert(faxil_wr_outstanding
					== (M_AXI_WVALID ? 0:1)
						+ (misaligned_response_pending ? 1:0));
				assert(faxil_rd_outstanding == 0);
			end
			// }}}
		end else if (M_AXI_BREADY)
		begin
			// {{{
			assert(faxil_awr_outstanding
				== (M_AXI_AWVALID ? 0:1)
					+ (misaligned_response_pending ? 1:0));
			assert(faxil_wr_outstanding
				== (M_AXI_WVALID ? 0:1)
					+ (misaligned_response_pending ? 1:0));
			// }}}
		end else begin // Read cycle
			// {{{
			assert(M_AXI_RREADY);
			assert(faxil_rd_outstanding
				== (M_AXI_ARVALID ? 0:1)
					+ (misaligned_response_pending ? 1:0));
			// }}}
		end
		// }}}
	end else if (M_AXI_BREADY)
	begin
		// {{{
		assert(!misaligned_aw_request);
		assert(!misaligned_request);
		assert(!misaligned_response_pending);
		assert(!pending_err);
		assert(faxil_awr_outstanding == (M_AXI_AWVALID ? 0:1));
		assert(faxil_wr_outstanding  == (M_AXI_WVALID  ? 0:1));
		assert(faxil_rd_outstanding  == 0);
		assert(!misaligned_read);
		// }}}
	end else begin
		// {{{
		assert(M_AXI_RREADY);
		assert(!misaligned_aw_request);
		assert(!misaligned_request);
		assert(!misaligned_response_pending);
		assert(!misaligned_read);
		assert(!pending_err);
		assert(faxil_awr_outstanding == 0);
		assert(faxil_wr_outstanding  == 0);
		assert(faxil_rd_outstanding  == (M_AXI_ARVALID ? 0:1));
		// }}}
	end
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
		`ASSERT(o_busy || (OPT_ALIGNMENT_ERR && o_err));
	end

	always @(*)
		`ASSERT(o_busy == (M_AXI_BREADY || M_AXI_RREADY));
	always @(*)
		`ASSERT(o_rdbusy == (M_AXI_RREADY && !r_flushing));

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
		begin
			`ASSERT(!o_err);
		end else if ($past(M_AXI_BVALID && M_AXI_BRESP[1]))
		begin
			if ($past(misaligned_response_pending))
			begin
				`ASSERT((!o_err && pending_err) || r_flushing);
			end else
				`ASSERT(o_err);
		end else if ($past(M_AXI_RVALID && M_AXI_RRESP[1]))
		begin
			if ($past(misaligned_response_pending))
			begin
				`ASSERT((!o_err && pending_err) || r_flushing);
			end else
				`ASSERT(o_err);
		end else if (OPT_ALIGNMENT_ERR && $past(i_stb && w_misaligned))
		begin
			`ASSERT(o_err);
		end else if (!$past(pending_err))
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

	////////////////////////////////////////////////////////////////////////
	//
	// OPT_LOWPOWER / Zero on idle checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_LOWPOWER)
	begin
		genvar	fb;

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

		always @(*)
		if (S_AXI_ARESETN && !o_valid)
			`ASSERT(o_result == 0);

		always @(*)
		if (S_AXI_ARESETN && (!o_valid && !o_err) && (!M_AXI_RREADY || r_flushing))
			`ASSERT(o_wreg == 0);

		always @(*)
		if (S_AXI_ARESETN && (OPT_ALIGNMENT_ERR || !M_AXI_RREADY
					|| misaligned_response_pending))
			`ASSERT(last_result == 0);

		for(fb=0; fb<C_AXI_DATA_WIDTH/8; fb=fb+1)
		begin
			always @(*)
			if (S_AXI_ARESETN && !M_AXI_WSTRB[fb])
				`ASSERT(M_AXI_WDATA[fb*8 +: 8] == 8'h0);

			always @(*)
			if (S_AXI_ARESETN && !next_wstrb[fb])
				`ASSERT(next_wdata[fb*8 +: 8] == 8'h0);
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
	else
		f_done <= (M_AXI_RVALID && !M_AXI_RRESP[1]
			|| M_AXI_BVALID && !M_AXI_BRESP[1]) && !pending_err
				&& !misaligned_response_pending;


	fmem
	fcheck(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_sys_reset(!S_AXI_ARESETN),
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
	begin
		`ASSERT(cpu_outstanding == 0);
	end else
		`ASSERT(cpu_outstanding == (o_busy ? 1:0)
			+ ((f_done || o_err) ? 1 : 0));

	always @(*)
	if (f_pc)
	begin
		assert(o_wreg[3:1] == 3'h7 || (OPT_LOWPOWER && o_err));
	end else if (o_rdbusy)
		assert(o_wreg[3:1] != 3'h7);

	always @(*)
	if (cpu_outstanding > 0 && (!OPT_LOWPOWER || (f_read_cycle && !o_err)))
		assert(o_wreg == f_last_reg);

	always @(*)
	if (o_busy && (!OPT_LOWPOWER || (M_AXI_RREADY && !r_flushing)))
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
