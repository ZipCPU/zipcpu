////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axilfetch.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a very simple instruction fetch approach based around
//		AXI-lite.
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	axilfetch #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 64,
		parameter	DATA_WIDTH=32,
		parameter	FETCH_LIMIT=16,
		parameter [0:0]	SWAP_ENDIANNESS = 1'b1,
		localparam	AW=C_AXI_ADDR_WIDTH
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		//
		// CPU interaction wires
		// {{{
		input	wire			i_cpu_reset,
		input	wire			i_new_pc,
		input	wire			i_clear_cache,
		input	wire			i_ready,
		input	wire	[AW-1:0]	i_pc,	// Ignd unls i_new_pc
		output	wire [DATA_WIDTH-1:0]	o_insn,	// Insn read from bus
		output	reg	[AW-1:0]	o_pc,	// Addr of that insn
		output	reg			o_valid,	// If valid
		output	reg			o_illegal,	// Bus error
		// }}}
		// AXI-lite bus interface
		// {{{
		output	reg				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	reg [C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		output	wire	[2:0]			M_AXI_ARPROT,
		//
		input	wire				M_AXI_RVALID,
		output	wire				M_AXI_RREADY,
		input	wire [C_AXI_DATA_WIDTH-1:0]	M_AXI_RDATA,
		input	wire [1:0]			M_AXI_RRESP
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam	AXILLSB = $clog2(C_AXI_DATA_WIDTH/8);
	localparam	INSNS_PER_WORD = C_AXI_DATA_WIDTH / DATA_WIDTH;
	localparam	LGDEPTH = $clog2(FETCH_LIMIT)+4;
	localparam	LGFIFO = $clog2(FETCH_LIMIT);
	localparam	W = LGDEPTH;
	localparam	FILLBITS = $clog2(INSNS_PER_WORD);
			// ($clog2(INSNS_PER_WORD) > 0)
			//			? $clog2(INSNS_PER_WORD) : 1);

	reg	[W:0]			new_flushcount, outstanding,
					next_outstanding, flushcount;
	reg				flushing, flush_request, full_bus;
	reg	[((AXILLSB>2)?(AXILLSB-3):0):0]	shift;
	wire				fifo_reset, fifo_wr, fifo_rd;
	wire				ign_fifo_full, fifo_empty;
	wire	[LGFIFO:0]		ign_fifo_fill;
	wire	[C_AXI_DATA_WIDTH:0]	fifo_data;
	reg				pending_new_pc;
	reg	[C_AXI_ADDR_WIDTH-1:0]	pending_pc;
	reg	[W-1:0]			fill;
	reg [FILLBITS:0]	out_fill;
	reg	[C_AXI_DATA_WIDTH-1:0]	out_data;
	reg	[C_AXI_DATA_WIDTH-1:0]	endian_swapped_rdata;
	// }}}

	assign	fifo_reset = i_cpu_reset || i_clear_cache || i_new_pc;
	assign	fifo_wr = M_AXI_RVALID && !flushing;


	// ARPROT = 3'b100 for an unprivileged, secure instruction access
	// (not sure what unprivileged or secure mean--even after reading the
	//  spec)
	assign	M_AXI_ARPROT = 3'b100;

	// next_outstanding
	// {{{
	always @(*)
	begin
		next_outstanding = outstanding;

		case({ M_AXI_ARVALID && M_AXI_ARREADY, M_AXI_RVALID })
		2'b10: next_outstanding = outstanding + 1;
		2'b01: next_outstanding = outstanding - 1;
		default: begin end
		endcase
	end
	// }}}

	// outstanding, full_bus
	// {{{
	initial	outstanding = 0;
	initial	full_bus    = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		outstanding <= 0;
		full_bus <= 0;
	end else begin
		outstanding <= next_outstanding;
		full_bus <= (next_outstanding
			// + (((M_AXI_ARVALID && !M_AXI_ARREADY) ? 1:0)
						>= (1<<LGDEPTH)-1);
	end
	// }}}

	// fill
	// {{{
	initial	fill = 0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		fill <= 0;
	// else if (fo_reset || flushing)
	//	fill <= 0;
	else case({ M_AXI_ARVALID && M_AXI_ARREADY && !flush_request,
				fifo_rd && !fifo_empty })
	2'b10: fill <= fill + 1;
	2'b01: fill <= fill - 1;
	default: begin end
	endcase
	// }}}

	// new_flushcount
	// {{{
	always @(*)
		new_flushcount = outstanding + (M_AXI_ARVALID ? 1:0)
				- (M_AXI_RVALID ? 1:0);
	// }}}

	// flushcount, flushing, flush_request
	// {{{
	initial	flushcount = 0;
	initial	flushing   = 0;
	initial	flush_request = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		flushcount <= 0;
		flushing   <= 0;
		flush_request <= 0;
	end else if (fifo_reset)
	begin
		flushcount <= new_flushcount;
		flushing   <= (new_flushcount > 0);
		flush_request <= (M_AXI_ARVALID && !M_AXI_ARREADY);
	end else begin
		if (M_AXI_RVALID && flushcount > 0)
		begin
			flushcount <= flushcount - 1;
			// Verilator lint_off CMPCONST
			flushing   <= (flushcount > 1);
			// Verilator lint_on  CMPCONST
		end

		if (M_AXI_ARREADY)
			flush_request <= 0;
	end
	// }}}

	// M_AXI_ARVALID
	// {{{
	initial	M_AXI_ARVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXI_ARVALID <= 1'b0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		M_AXI_ARVALID <= 1;
		if (i_new_pc || pending_new_pc)
			M_AXI_ARVALID <= 1'b1;

		//
		// Throttle the number of requests we make
		// Verilator lint_off CMPCONST
		//	out_fill will only capture 0 or 1 if DATA_WIDTH == 32
		if (fill + (M_AXI_ARVALID ? 1:0)
				+ ((o_valid &&(!i_ready || out_fill > 1)) ? 1:0)
				>= FETCH_LIMIT)
			M_AXI_ARVALID <= 1'b0;
		// Verilator lint_on  CMPCONST
		if (i_cpu_reset || i_clear_cache || full_bus)
			M_AXI_ARVALID <= 1'b0;
	end
	// }}}

	assign	M_AXI_RREADY = 1'b1;

	// pending_new_pc
	// {{{
	initial	pending_new_pc = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_clear_cache)
		pending_new_pc <= 1'b0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		pending_new_pc <= 1'b0;
	else if (i_new_pc)
		pending_new_pc <= 1'b1;
	// }}}

	// pending_pc
	// {{{
	initial	pending_pc = 0;
	always @(posedge S_AXI_ACLK)
	if (i_new_pc)
		pending_pc <= i_pc;
	// }}}

	// M_AXI_ARADDR
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		if (i_new_pc)
			M_AXI_ARADDR <= i_pc;
		else if (pending_new_pc)
			M_AXI_ARADDR <= pending_pc;
		else if (M_AXI_ARVALID)
		begin
			M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:AXILLSB]
				<= M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:AXILLSB] +1;
			M_AXI_ARADDR[AXILLSB-1:0] <= 0;
		end
	end
	// }}}

	// o_pc
	// {{{
	initial	o_pc = 0;
	always @(posedge S_AXI_ACLK)
	if (i_new_pc)
		o_pc <= i_pc;
	else if (o_valid && i_ready && !o_illegal)
	begin
		o_pc[AW-1:2] <= o_pc[AW-1:2] + 1;
		o_pc[1:0] <= 2'b00;
	end
	// }}}

	generate if (AXILLSB > 2)
	begin : BIG_WORD
		// {{{
		always @(*)
		begin
			shift = o_pc[AXILLSB-1:2];

			if (FETCH_LIMIT > 0 && o_valid)
				shift = 0;
		end
		// }}}
	end else begin : NO_SHIFT
		// {{{
		always @(*)
			shift = 0;
		// }}}
	end endgenerate

	generate if (SWAP_ENDIANNESS)
	begin : SWAPPED_ENDIANNESS
		// {{{
		genvar	gw, gb;	// Word count, byte count

		for(gw=0; gw<C_AXI_DATA_WIDTH/32; gw=gw+1) // For each bus word
		for(gb=0; gb<4; gb=gb+1) // For each bus byte
		always @(*)
			endian_swapped_rdata[gw*32+(3-gb)*8 +: 8]
				= M_AXI_RDATA[gw*32+gb*8 +: 8];
		// }}}
	end else begin : NO_ENDIAN_SWAP
		// {{{
		always @(*)
			endian_swapped_rdata = M_AXI_RDATA;
		// }}}
	end endgenerate

	generate if (FETCH_LIMIT <= 1)
	begin : NOCACHE
		// {{{
		// No cache

		// assign	fifo_rd    = fifo_wr;
		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		assign	fifo_empty = !fifo_wr; //(out_fill <= (i_aready ? 1:0));
		assign	fifo_data  = { M_AXI_RRESP[1], endian_swapped_rdata };

		assign	ign_fifo_fill = 1'b0;
		assign	ign_fifo_full = 1'b0;
`ifdef	FORMAL
		always @(*)
		if (M_AXI_RVALID || M_AXI_ARVALID || outstanding > 0)
			assert(!o_valid);
`endif
		// }}}
	end else if (FETCH_LIMIT == 2)
	begin : DBLFETCH
		// {{{
		// Single word cache
		reg				cache_valid;
		reg	[C_AXI_DATA_WIDTH:0]	cache_data;

		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		assign	fifo_empty =(!M_AXI_RVALID && !cache_valid) || flushing;
		assign	fifo_data = cache_valid ? cache_data
					: ({ M_AXI_RRESP[1], endian_swapped_rdata });


		assign	ign_fifo_fill = cache_valid ? 1 : 0;
		assign	ign_fifo_full = cache_valid;

		initial	cache_valid = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (fifo_reset)
			cache_valid <= 1'b0;
		else if (M_AXI_RVALID && o_valid && !fifo_rd)
			cache_valid <= 1;
		else if (fifo_rd)
			cache_valid <= 1'b0;

		always @(posedge S_AXI_ACLK)
		if (M_AXI_RVALID)
			cache_data <= { M_AXI_RRESP[1], endian_swapped_rdata };
		// }}}
	end else begin : FIFO_FETCH
		// {{{
		// FIFO cache

		// Verilator lint_off CMPCONST
		//	out_fill will only capture 0 or 1 if DATA_WIDTH == 32
		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		// Verilator lint_on  CMPCONST

		sfifo #(.BW(1+C_AXI_DATA_WIDTH), .LGFLEN(LGFIFO))
		fcache(.i_clk(S_AXI_ACLK), .i_reset(fifo_reset),
			.i_wr(fifo_wr),
			.i_data({M_AXI_RRESP[1], endian_swapped_rdata }),
			.o_full(ign_fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(fifo_rd),.o_data(fifo_data),.o_empty(fifo_empty));
		// }}}
	end endgenerate

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		o_valid <= 1'b0;
	else if (!o_valid || i_ready)
		o_valid <= (fifo_rd && !fifo_empty)
			|| out_fill > (o_valid ? 1:0);
	// }}}

	// out_fill
	// {{{
	initial	out_fill = 0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		out_fill <= 0;
	else if (fifo_rd)
		// Verilator lint_off WIDTH
		out_fill <= (fifo_empty) ? 0: (INSNS_PER_WORD - shift);
		// Verilator lint_on  WIDTH
	else if (i_ready && out_fill > 0)
		out_fill <= out_fill - 1;
	// }}}

	// out_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (fifo_rd)
		out_data <= fifo_data[C_AXI_DATA_WIDTH-1:0]>>(DATA_WIDTH*shift);
	else if (i_ready)
		out_data <= out_data >> DATA_WIDTH;
	// }}}

	assign	o_insn = out_data[DATA_WIDTH-1:0];

	// o_illegal
	// {{{
	initial	o_illegal = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		o_illegal <= 1'b0;
	else if (!o_illegal && fifo_rd && !fifo_empty)
		o_illegal <= fifo_data[C_AXI_DATA_WIDTH];
	// }}}
	
	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = & { 1'b0, M_AXI_RRESP[0], ign_fifo_full, ign_fifo_fill };
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
	// Declarations
	// {{{
	localparam	DW=DATA_WIDTH;
	localparam	F_LGDEPTH=LGDEPTH+2;
	reg	f_past_valid;
	wire	[(F_LGDEPTH-1):0]	faxil_outstanding;
	reg	[(AW-1):0]	f_last_pc;
	reg			f_last_pc_valid;
	//
	reg	[AW-1:0]	fc_pc, f_address;
	reg			fc_illegal;
	reg [DATA_WIDTH-1:0]	fc_insn;
	//}}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generic setup
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Keep track of a flag telling us whether or not $past()
	// will return valid results
	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid = 1'b1;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Assume we start from a reset condition
	// {{{
	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(*)
	if (!S_AXI_ARESETN)
		assume(i_cpu_reset);
	// }}}

	//
	//
	// Let's make some assumptions about how long it takes our
	// phantom bus and phantom CPU to respond.
	//
	// These delays need to be long enough to flush out any potential
	// errors, yet still short enough that the formal method doesn't
	// take forever to solve.
	//
	localparam	F_CPU_DELAY = 4;
	reg	[$clog2(F_CPU_DELAY):0]	f_cpu_delay;
	// First, let's assume that any response from the bus comes back
	// within F_WB_DELAY clocks

		// Here's our delay assumption: We'll assume that the
	// wishbone will always respond within F_WB_DELAY clock ticks
	// of the beginning of any cycle.
	//
	// This includes both dropping the stall line, as well as
	// acknowledging any request.  While this may not be
	// a reasonable assumption for a piped master, it should
	// work here for us.

	// Count the number of clocks it takes the CPU to respond to our
	// instruction.
	always @(posedge S_AXI_ACLK)
	// If no instruction is ready, then keep our counter at zero
	if (i_cpu_reset|| !o_valid || i_ready)
		f_cpu_delay <= 0;
	else
		// Otherwise, count the clocks the CPU takes to respond
		f_cpu_delay <= f_cpu_delay + 1'b1;

`ifdef	PREFETCH
	// Only *assume* that we are less than F_CPU_DELAY if we are not
	// integrated into the CPU
	always @(posedge S_AXI_ACLK)
		assume(f_cpu_delay < F_CPU_DELAY);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxil_master #(
		// {{{
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.F_OPT_READ_ONLY(1'b1),
		.F_OPT_COVER_BURST(5),
		.F_OPT_ASSUME_RESET(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		// Unused write interface
		// {{{
		.i_axi_awvalid(1'b0), .i_axi_awready(1'b1),
		.i_axi_wvalid(1'b0), .i_axi_wready(1'b1),
		.i_axi_bvalid(1'b0), .i_axi_bready(1'b1),
		// }}}
		// Read address channel
		// {{{
		.i_axi_arvalid(M_AXI_ARVALID),
		.i_axi_arready(M_AXI_ARREADY),
		.i_axi_araddr( M_AXI_ARADDR),
		.i_axi_arprot( 3'h0),
		// }}}
		// Read return / data interface
		// {{{
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rdata(M_AXI_RDATA),
		.i_axi_rresp(M_AXI_RRESP),
		// }}}
		.f_axi_rd_outstanding(faxil_outstanding)
		// }}}
	);


	always @(*)
		assert(full_bus == (outstanding >= (1<<LGDEPTH)-1));

	always @(*)
		assert(flushing == (flushcount > 0));

	always @(*)
		assert(flushcount <= outstanding + (flush_request ? 1:0));

	always @(posedge S_AXI_ACLK)
	if (flush_request && !i_clear_cache && !i_cpu_reset)
		assert(pending_new_pc || i_new_pc);

	always @(*)
	if (!M_AXI_ARVALID || !flushing)
		assert(!flush_request);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Subword return
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[W:0]			f_word_count;
	reg	[AW-1:0]		f_return_addr;
	reg	[AW-1:0]		f_out_addr, f_subout_addr;
	reg	[C_AXI_ADDR_WIDTH-1:0]	f_req_addr, f_ret_addr;
	reg	[W:0]			f_req_offset, f_ret_offset;


	always @(*)
	begin
		f_req_offset = f_word_count;
		if (flushing)
			f_req_offset = f_req_offset - flushcount;
		if (M_AXI_ARVALID && f_req_offset > 0)
			f_req_offset = f_req_offset - 1;

		f_req_addr = f_out_addr + (f_req_offset << AXILLSB);
		if (f_req_offset == 0)
			f_req_addr[AXILLSB-1:0] = o_pc[AXILLSB-1:0];

		///////////////

		f_ret_offset = o_valid ? 1:0;
		f_ret_offset = f_ret_offset + ign_fifo_fill;

		f_ret_addr = f_out_addr + (f_ret_offset << AXILLSB);
		if (f_ret_offset == 0)
			f_ret_addr[AXILLSB-1:0] = o_pc[AXILLSB-1:0];
	end

	always @(*)
		assert(f_req_offset <= f_word_count);

	always @(*)
		assert(f_req_offset == fill + (o_valid ? 1:0));

	always @(*)
		assert(f_ret_offset <= f_req_offset);

	always @(*)
	if (!i_cpu_reset && !i_new_pc && !i_clear_cache
			&& !pending_new_pc && M_AXI_ARADDR != o_pc)
		assert(M_AXI_ARADDR[AXILLSB-1:0] == 0);

	always @(*)
	if (!flushing)
		assert(f_word_count <= FETCH_LIMIT);
	else
		assert(f_word_count - flushcount <= FETCH_LIMIT);

	always @(*)
	if (!i_cpu_reset && !i_new_pc && !i_clear_cache && !flush_request)
	begin
		if (!o_illegal)
			assert(f_req_addr[AXILLSB-1:0] == M_AXI_ARADDR[AXILLSB-1:0]);
		assert(f_req_addr[C_AXI_ADDR_WIDTH-1:AXILLSB]
			== M_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:AXILLSB]);
	end

	always @(*)
	if (S_AXI_ARESETN && !i_cpu_reset && !i_new_pc && !i_clear_cache
			&& !flushing && !o_illegal)
		assert(f_ret_addr[C_AXI_ADDR_WIDTH-1:AXILLSB]
			== f_return_addr[C_AXI_ADDR_WIDTH-1:AXILLSB]);

	always @(*)
	begin
		f_word_count = faxil_outstanding;
		if (M_AXI_ARVALID)
			f_word_count = f_word_count + 1;
		f_word_count = f_word_count + ign_fifo_fill;
		if (o_valid)
			f_word_count = f_word_count + 1;
	end


	generate if (FETCH_LIMIT <= 1)
	begin : F_NO_CACHE

	end else if (FETCH_LIMIT == 2)
	begin : F_DBLFETCH

	end else begin : F_FIFO_CACHE

	end endgenerate

	always @(*)
	begin
		assert(faxil_outstanding + (M_AXI_ARVALID ? 1:0)<=(1<<LGDEPTH));

		assert(faxil_outstanding == outstanding);
		assert(flushcount <= outstanding + (M_AXI_ARVALID ? 1:0));

		assert(flushing == (flushcount != 0));
	end

	always @(*)
	if (flushing)
		assert(!o_valid);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// I-Fetch contract w/ CPU
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	ffetch #(.ADDRESS_WIDTH(C_AXI_ADDR_WIDTH-2), .OPT_ALIGNED(1'b0))
	ffetchi(S_AXI_ACLK, i_cpu_reset,
		i_new_pc, i_clear_cache, i_pc,
		o_valid, i_ready, o_pc, o_insn, o_illegal,
		fc_pc, fc_illegal, fc_insn, f_address);

	always @(*)
	if (!i_cpu_reset && !i_new_pc && !i_clear_cache && !o_illegal)
		assert(o_pc == f_address);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// If we just got a valid instruction from the wishbone, assert that
	// the instruction is listed as valid on the next instruction cycle
	always @(posedge S_AXI_ACLK)
	if ((f_past_valid)&&(!$past(fifo_reset))
		&&($past(o_valid && !i_ready)))
	begin
		assert(o_valid);
		assert($stable(o_illegal));
		assert($stable(o_insn));
		assert($stable(o_pc));
	end

	always @(posedge S_AXI_ACLK)
	if ((f_past_valid)&&($past(i_clear_cache)))
		assert(!o_valid);

	always @(*)
		assert(out_fill <= INSNS_PER_WORD);

	always @(*)
		assert(o_valid == (out_fill >0));

	//
	// Assertions about our return responses
	// {{{
	// While the below assertions (currently) appear to just copy the logic
	// above, they still have a purpose--they'll help us guarantee that the
	// logic above will never change without also requiring a change here.
	//
	generate if (SWAP_ENDIANNESS)
	begin : CHECK_SWAPPED_ENDIANNESS
		// {{{
		genvar	gw, gb;	// Word count, byte count

		for(gw=0; gw<C_AXI_DATA_WIDTH/32; gw=gw+1) // For each bus word
		for(gb=0; gb<4; gb=gb+1) // For each bus byte
		always @(*)
			assert(endian_swapped_rdata[gw*32+(3-gb)*8 +: 8]
				== M_AXI_RDATA[gw*32+gb*8 +: 8]);
		// }}}
	end else begin : CHECK_NO_ENDIAN_SWAP
		// {{{
		always @(*)
			assert(endian_swapped_rdata == M_AXI_RDATA);
		// }}}
	end endgenerate
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`define	CHECK_CONTRACT
`ifdef	CHECK_CONTRACT
	(* anyconst *) reg	[AW:0]		const_addr;
	(* anyconst *) reg	[DW-1:0]	const_insn;

	wire	[DATA_WIDTH-1:0]	f_bus_word, f_out_data;

	initial	f_out_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (i_new_pc)
		f_out_addr <= { i_pc[AW-1:AXILLSB], {(AXILLSB){1'b0}} };
	else if (o_valid && i_ready && out_fill == 1)
		f_out_addr[AW-1:AXILLSB] <= f_out_addr[AW-1:AXILLSB] + 1;

	always @(*)
		f_subout_addr = f_out_addr
			+ ((INSNS_PER_WORD-out_fill) << $clog2(DATA_WIDTH/8));

	always @(*)
		assert(f_out_addr[AXILLSB-1:0] == 0);

	always @(*)
	if (o_valid && !o_illegal)
	begin
		assert(f_out_addr[AW-1:AXILLSB] == o_pc[AW-1:AXILLSB]);
		assert(f_subout_addr[AW-1:2] == o_pc[AW-1:2]);
	end else if (!i_cpu_reset && !i_clear_cache && !pending_new_pc && !i_new_pc && !o_illegal)
	begin
		assert(f_out_addr[AW-1:AXILLSB] == o_pc[AW-1:AXILLSB]);
		// assert(f_subout_addr[AW-1:2] == o_pc[AW-1:2]);
	end

	always @(*)
	begin
		f_return_addr={ M_AXI_ARADDR[AW-1:AXILLSB], {(AXILLSB){1'b0}} };
		f_return_addr = f_return_addr
				- ((outstanding - flushcount)<<AXILLSB);
	end

	//
	//
	// Step 1. Assume any return matches the contract
	//
	//

	generate if (DATA_WIDTH == C_AXI_DATA_WIDTH)
	begin : F_BUSWORD
		// {{{
		assign	f_bus_word = endian_swapped_rdata;
		// }}}
	end else begin : BUSWORD_SHIFT
		// {{{
		reg	[$clog2(INSNS_PER_WORD)-1:0]	shift;

		always @(*)
			shift = fc_pc[AXILLSB-1:2];

		assign	f_bus_word = endian_swapped_rdata >> (shift * DATA_WIDTH);
		// }}}
	end endgenerate

	always @(*)
	if (M_AXI_RVALID && f_return_addr[AW-1:AXILLSB] == fc_pc[AW-1:AXILLSB])
	begin
		assume(M_AXI_RRESP[1] == fc_illegal);
		assume(f_bus_word == fc_insn);
	end

	//
	//
	// Step 2: Assert that any value in our cache meets the contract
	//
	//
	generate if (DATA_WIDTH == C_AXI_DATA_WIDTH)
	begin : F_OUTDATA
		// {{{
		assign	f_out_data = out_data;
		// }}}
	end else begin : F_OUTDATA_SHIFT
		// {{{
		reg	[$clog2(INSNS_PER_WORD)-1:0]	shift;

		always @(*)
			shift = (fc_pc - f_subout_addr) >> $clog2(DATA_WIDTH/8);

		assign	f_out_data = out_data >> (shift * DATA_WIDTH);
		// }}}
	end endgenerate

	generate if (FETCH_LIMIT == 1)
	begin : F_SINGLE
	end else if (FETCH_LIMIT == 2)
	begin : F_CACHE_CHECK
		// {{{
		reg	[AW-1:0]		f_cache_addr;
		wire	[C_AXI_DATA_WIDTH-1:0]	f_cache_data;
		wire				f_cache_illegal;
		reg				f_cache_check;

		always @(*)
		begin
			f_cache_addr = 0;
			f_cache_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB]+1;

			f_cache_check = (fc_pc[AW-1:AXILLSB]
						== f_cache_addr[AW-1:AXILLSB]);
			if (!DBLFETCH.cache_valid)
				f_cache_check = 1'b0;
		end

		if (DATA_WIDTH == C_AXI_DATA_WIDTH)
		begin : F_CACHEDATA

			assign f_cache_data=DBLFETCH.cache_data[DATA_WIDTH-1:0];
			assign f_cache_illegal= DBLFETCH.cache_data[DATA_WIDTH];

		end else begin : F_CACHEDATA_SHIFT

			reg	[$clog2(INSNS_PER_WORD)-1:0]	shift;

			always @(*)
				shift = (fc_pc - f_cache_addr) >> $clog2(DATA_WIDTH/8);

			assign	f_cache_data = DBLFETCH.cache_data >> (shift * DATA_WIDTH);
			assign f_cache_illegal= DBLFETCH.cache_data[C_AXI_DATA_WIDTH];
		end

		always @(*)
		if (f_cache_check && !o_illegal)
		begin
			assert(f_cache_data[DATA_WIDTH-1:0] == fc_insn);
			assert(f_cache_illegal == fc_illegal);
		end
		// }}}
	end else begin : F_FIFO_CHECK
		// {{{
		reg	[AW-1:0]		f_cache_addr, f_fifo_addr;
		reg	[C_AXI_DATA_WIDTH-1:0]	f_cache_data, f_cache_subdata,
						f_fifo_subdata;
		reg				f_cache_illegal;
		reg				f_cache_check, f_cache_valid;
		reg	[LGFIFO:0]		f_cache_distance;
		reg				f_cache_assume;


		always @(*)
			{ f_cache_illegal, f_cache_data }
						= { FIFO_FETCH.fcache.f_first_data };

		always @(*)
			f_cache_distance = FIFO_FETCH.fcache.f_distance_to_first;

		always @(*)
			f_cache_valid = FIFO_FETCH.fcache.f_first_in_fifo;

		always @(*)
		begin
			f_cache_addr = 0;
			f_cache_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB]
					+ (o_valid ? 1:0)
					+ f_cache_distance;

			f_cache_check = (fc_pc[AW-1:AXILLSB]
						== f_cache_addr[AW-1:AXILLSB]);
			if (!f_cache_valid)
				f_cache_check = 1'b0;
		end

		if (DATA_WIDTH == C_AXI_DATA_WIDTH)
		begin : F_CACHEDATA

			always @(*)
				f_cache_subdata = f_cache_data;

			always @(*)
				f_fifo_subdata = fifo_data[DATA_WIDTH-1:0];

		end else begin : F_CACHEDATA_SHIFT

			reg	[$clog2(INSNS_PER_WORD)-1:0]	shift;

			always @(*)
				shift = (fc_pc - f_cache_addr) >> $clog2(DATA_WIDTH/8);

			always @(*)
				f_cache_subdata = f_cache_data >> (shift * DATA_WIDTH);
			always @(*)
				f_fifo_subdata = fifo_data >> (shift * DATA_WIDTH);
		end

		always @(*)
		begin
			f_fifo_addr = 0;
			f_fifo_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB]
				+ (o_valid ? 1:0);
		end

		always @(*)
		if (f_cache_check && !o_illegal)
		begin
			assert(f_cache_subdata[DATA_WIDTH-1:0] == fc_insn);
			assert(f_cache_illegal == fc_illegal);
		end

		always @(*)
		begin
			f_cache_assume = 0;
			if (ign_fifo_fill != 0 && (f_fifo_addr[AW-1:AXILLSB]
						== fc_pc[AW-1:AXILLSB]))
			begin
				if (!f_cache_check || o_illegal)
					f_cache_assume = 1;
				if (f_cache_addr[AW-1:AXILLSB]
						!= f_fifo_addr[AW-1:AXILLSB])
					f_cache_assume = 1;
			end
		end

		always @(*)
		if (f_cache_assume)
		begin
			assume(f_fifo_subdata[DATA_WIDTH-1:0] == fc_insn);
			assume(fifo_data[C_AXI_DATA_WIDTH] == fc_illegal);
		end
		// }}}
	end endgenerate

	//
	// Check the final output word
	//
	always @(*)
	if ((out_fill > 0) && (fc_pc[AW-1:AXILLSB] == f_out_addr[AW-1:AXILLSB])
		&&(fc_pc >= f_subout_addr))
	begin
		if (fc_illegal)
			assert(o_illegal);
		else if (!o_illegal)
			assert(f_out_data == fc_insn);
	end

	always @(*)
	if (pending_new_pc)
		assert(i_new_pc || flush_request);

	always @(*)
	if (pending_new_pc)
		assert(o_pc == pending_pc);

	always @(*)
	if (flush_request)
		assert(flushcount == faxil_outstanding + 1);

	always @(*)
	if (flushing)
		assert(!o_illegal);

	always @(*)
	if (flush_request && !i_cpu_reset && !i_new_pc && !i_clear_cache)
	begin
		assert(f_out_addr[C_AXI_ADDR_WIDTH-1:AXILLSB] == pending_pc[C_AXI_ADDR_WIDTH-1:AXILLSB]);
		assert(o_pc == pending_pc);
	end
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_returns;
	(* anyconst *) reg	cvr_always_ready;

	always @(*)
	if (cvr_always_ready)
		assume(M_AXI_ARREADY);

	initial	cvr_returns = 0;
	always @(posedge S_AXI_ACLK)
	if (i_cpu_reset || i_new_pc || i_clear_cache || o_illegal)
		cvr_returns <= 0;
	else if (o_valid && i_ready && !cvr_returns[3])
		cvr_returns <= cvr_returns + 1;

	always @(*)
	begin
		cover(cvr_returns == 4'b0100);
		cover(cvr_returns == 4'b0101);
		cover(cvr_returns == 4'b0110 && cvr_always_ready);
	end
	// }}}
`endif
// }}}
endmodule
