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
		parameter	INSN_WIDTH=32,
		parameter	FETCH_LIMIT=16,
		parameter [0:0]	SWAP_ENDIANNESS = 1'b0,
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
		output	wire [INSN_WIDTH-1:0]	o_insn,	// Insn read from bus
		output	reg	[AW-1:0]	o_pc,	// Addr of that insn
		output	reg			o_valid,	// If valid
		output	reg			o_illegal,	// Bus error
		// }}}
		// AXI-lite bus interface
		// {{{
		output	reg				M_AXI_ARVALID,
		input	wire				M_AXI_ARREADY,
		output	reg [C_AXI_ADDR_WIDTH-1:0]	M_AXI_ARADDR,
		// Verilator coverage_off
		output	wire	[2:0]			M_AXI_ARPROT,
		// Verilator coverage_on
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
	localparam	INSNS_PER_WORD = C_AXI_DATA_WIDTH / INSN_WIDTH;
	localparam	INSN_LSB = $clog2(INSN_WIDTH/8);
	localparam	LGDEPTH = $clog2(FETCH_LIMIT)+4;
	localparam	LGFIFO = $clog2(FETCH_LIMIT);
	localparam	W = LGDEPTH;
	localparam	FILLBITS = $clog2(INSNS_PER_WORD);
			// ($clog2(INSNS_PER_WORD) > 0)
			//			? $clog2(INSNS_PER_WORD) : 1);

	reg	[W:0]			new_flushcount, outstanding,
					next_outstanding, flushcount;
	reg				flushing, flush_request, full_bus;
	wire	[((AXILLSB>INSN_LSB) ? (AXILLSB-INSN_LSB-1):0):0]	shift;
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
`ifdef	FORMAL
	wire				f_cache_valid;
	wire	[C_AXI_DATA_WIDTH-1:0]	f_cache_data;
	wire				f_cache_illegal;
	wire	[LGFIFO:0]		f_cache_distance;
`endif
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
		// Verilator lint_off WIDTH
		//	out_fill will only capture 0 or 1 if DATA_WIDTH == 32
		if (fill + (M_AXI_ARVALID ? 1:0)
				+ ((o_valid &&(!i_ready || out_fill > 1)) ? 1:0)
				>= FETCH_LIMIT)
			M_AXI_ARVALID <= 1'b0;
		// Verilator lint_on  WIDTH
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
		o_pc <= 0;
		o_pc[AW-1:INSN_LSB] <= o_pc[AW-1:INSN_LSB] + 1;
	end
	// }}}

	generate if (AXILLSB > INSN_LSB)
	begin : BIG_WORD
		// {{{
		assign	shift = o_pc[AXILLSB-1:INSN_LSB];
		// }}}
	end else begin : NO_SHIFT
		// {{{
		assign	shift = 0;
		// }}}
	end endgenerate

	generate if (SWAP_ENDIANNESS)
	begin : SWAPPED_ENDIANNESS
		// {{{
		genvar	gw, gb;	// Word count, byte count

		for(gw=0; gw<C_AXI_DATA_WIDTH/INSN_WIDTH; gw=gw+1) // For each bus word
		begin : FOR_INSN_WORD
			for(gb=0; gb<(INSN_WIDTH/8); gb=gb+1) // For each bus byte
			begin : FOR_INSN_BYTE
				always @(*)
					endian_swapped_rdata[gw*INSN_WIDTH
						+ ((INSN_WIDTH/8)-1-gb)*8 +: 8]
				= M_AXI_RDATA[gw*INSN_WIDTH+gb*8 +: 8];
			end
		end
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
		// Verilator lint_off CMPCONST
		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		// Verilator lint_on  CMPCONST
		assign	fifo_empty = !fifo_wr; //(out_fill <= (i_aready ? 1:0));
		assign	fifo_data  = { M_AXI_RRESP[1], endian_swapped_rdata };

		assign	ign_fifo_fill = 1'b0;
		assign	ign_fifo_full = 1'b0;
`ifdef	FORMAL
		always @(*)
		if (M_AXI_RVALID || M_AXI_ARVALID || outstanding > 0)
			assert(!o_valid);

		assign	f_cache_valid   = 1'b0;
		assign	f_cache_data    = 0;
		assign	f_cache_illegal = 1'b0;
		assign	f_cache_distance= 0;
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
`ifdef	FORMAL
		assign	f_cache_valid = cache_valid;
		assign	{ f_cache_illegal, f_cache_data }  = cache_data;
		assign	f_cache_distance= 0;
`endif
		// }}}
	end else begin : FIFO_FETCH
		// {{{
		// FIFO cache
`ifdef	FORMAL
		wire	[LGFIFO:0]	f_first_addr;
		wire	[LGFIFO:0]	f_second_addr;
		wire	[C_AXI_DATA_WIDTH:0]	f_first_data, f_second_data;

		wire			f_first_in_fifo,
					f_second_in_fifo;
		wire	[LGFIFO:0]	f_distance_to_first,
					f_distance_to_second;
`endif


		// Verilator lint_off CMPCONST
		//	out_fill will only capture 0 or 1 if DATA_WIDTH == 32
		assign	fifo_rd = !o_valid || (i_ready && (out_fill <= 1));
		// Verilator lint_on  CMPCONST

		sfifo #(
			// {{{
			.BW(1+C_AXI_DATA_WIDTH), .LGFLEN(LGFIFO)
			// }}}
		) fcache(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(fifo_reset),
			.i_wr(fifo_wr),
			.i_data({M_AXI_RRESP[1], endian_swapped_rdata }),
			.o_full(ign_fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(fifo_rd),.o_data(fifo_data),.o_empty(fifo_empty)
`ifdef	FORMAL
			// {{{
			, .f_first_addr(f_first_addr),
			.f_second_addr(f_second_addr),
			.f_first_data(f_first_data),
			.f_second_data(f_second_data),

			.f_first_in_fifo(f_first_in_fifo),
			.f_second_in_fifo(f_second_in_fifo),
			.f_distance_to_first(f_distance_to_first),
			.f_distance_to_second(f_distance_to_second)
			// }}}
`endif
			// }}}
		);

`ifdef	FORMAL
		assign	{ f_cache_illegal, f_cache_data } = f_first_data;
		assign	f_cache_distance = f_distance_to_first;
		assign	f_cache_valid = f_first_in_fifo;
`endif
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
	// == number of instructions in the fifo_data word that have not (yet)
	//	been accepted by the CPU.
	// == 0 when no data is available
	// == INSN_PER_WORD on the first instruction of any word
	// == 1 on the last instruction of any word
	initial	out_fill = 0;
	always @(posedge S_AXI_ACLK)
	if (fifo_reset)
		out_fill <= 0;
	else if (fifo_rd)
	begin
		if (fifo_empty)
			out_fill <= 0;
		else if (o_valid)
			out_fill <= INSNS_PER_WORD[FILLBITS:0];
		else
			// Verilator lint_off WIDTH
			out_fill <= (INSNS_PER_WORD[FILLBITS:0] - shift);
			// Verilator lint_on  WIDTH
	end else if (i_ready && out_fill > 0)
		out_fill <= out_fill - 1;
	// }}}

	// out_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (fifo_rd)
	begin
		if (o_valid || (INSN_WIDTH == C_AXI_DATA_WIDTH))
			out_data <= fifo_data[C_AXI_DATA_WIDTH-1:0];
		else
		out_data <= fifo_data[C_AXI_DATA_WIDTH-1:0]>>(INSN_WIDTH*shift);
	end else if (i_ready)
		out_data <= out_data >> INSN_WIDTH;
	// }}}

	assign	o_insn = out_data[INSN_WIDTH-1:0];

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
	// Verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = & { 1'b0, M_AXI_RRESP[0], ign_fifo_full, ign_fifo_fill };
	// verilator lint_on  UNUSED
	// Verilator coverage_on
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
	localparam	DW=INSN_WIDTH;
	localparam	F_LGDEPTH=LGDEPTH+2;
	reg	f_past_valid;
	wire	[(F_LGDEPTH-1):0]	faxil_outstanding;
	// Verilator lint_off UNUSED
	wire	[(F_LGDEPTH-1):0]	faxil_awr_outstanding,
					faxil_wr_outstanding;
	// Verilator lint_on  UNUSED
	reg	[(AW-1):0]	f_last_pc;
	reg			f_last_pc_valid;
	//
	reg	[AW-1:0]	fc_pc, f_address;
	reg			fc_illegal;
	reg [INSN_WIDTH-1:0]	fc_insn;
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
		f_past_valid <= 1'b1;
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
			.i_axi_awaddr( {(AW){1'b0}}),
			.i_axi_awprot( 3'h0),
		.i_axi_wvalid(1'b0), .i_axi_wready(1'b1),
			.i_axi_wdata({(C_AXI_DATA_WIDTH){1'b0}}),
			.i_axi_wstrb({(C_AXI_DATA_WIDTH/8){1'b0}}),
		.i_axi_bvalid(1'b0), .i_axi_bready(1'b1),
			.i_axi_bresp(2'b00),
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
		.f_axi_awr_outstanding(faxil_awr_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
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
	reg	[W:0]		f_word_count;
	reg	[AW-1:0]	f_return_addr;
	reg	[AW-1:0]	f_out_addr, f_subout_addr;
	reg	[AW-1:0]	f_req_addr, f_ret_addr;
	reg	[W:0]		f_req_offset, f_ret_offset;


	always @(*)
	begin
		f_req_offset = f_word_count;
		if (flushing)
			f_req_offset = f_req_offset - flushcount;
		if (M_AXI_ARVALID && f_req_offset > 0)
			f_req_offset = f_req_offset - 1;

		// Verilator lint_off WIDTH
		f_req_addr = 0;
		f_req_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB]
				+ f_req_offset;

		///////////////

		f_ret_offset = o_valid ? 1:0;
		f_ret_offset = f_ret_offset + ign_fifo_fill;

		f_ret_addr = 0;
		f_ret_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB] + f_ret_offset;
	end

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(f_req_offset <= f_word_count);

		assert(f_req_offset == fill + (o_valid ? 1:0));

		assert(f_ret_offset <= f_req_offset);
	end

	always @(*)
	if (!i_cpu_reset && !i_new_pc && !i_clear_cache
			&& !pending_new_pc && M_AXI_ARADDR != o_pc)
		assert(M_AXI_ARADDR[AXILLSB-1:0] == 0);

	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (!flushing)
		begin
			assert(f_word_count <= FETCH_LIMIT);
		end else
			assert(f_word_count - flushcount <= FETCH_LIMIT);
	end

	always @(*)
	if (!i_cpu_reset && !i_new_pc && !i_clear_cache && !flush_request)
	begin
	//	if (!o_illegal)
	//		assert(f_req_addr[AXILLSB-1:0] == M_AXI_ARADDR[AXILLSB-1:0]);
		assert(f_req_addr[AW-1:AXILLSB] == M_AXI_ARADDR[AW-1:AXILLSB]);
	end

	always @(*)
	if (S_AXI_ARESETN && !i_cpu_reset && !i_new_pc && !i_clear_cache
			&& !flushing && !o_illegal)
		assert(f_ret_addr[AW-1:AXILLSB] == f_return_addr[AW-1:AXILLSB]);

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

		assert(faxil_outstanding == { 1'b0, outstanding });
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

	ffetch #(
		// {{{
		.ADDRESS_WIDTH(C_AXI_ADDR_WIDTH-INSN_LSB),
		.OPT_ALIGNED(1'b0)
		// }}}
	) ffetchi(
		// {{{
		S_AXI_ACLK, i_cpu_reset,
		i_new_pc, i_clear_cache, i_pc,
		o_valid, i_ready, o_pc, o_insn, o_illegal,
		fc_pc, fc_illegal, fc_insn, f_address
		// }}}
	);

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

	generate if (AXILLSB != INSN_LSB)
	begin : OUTFILL_CHK
		always @(*)
		if (o_valid && !o_illegal)
			assert(out_fill == INSNS_PER_WORD - o_pc[AXILLSB-1:INSN_LSB]);
	end else begin
		always @(*)
		if (S_AXI_ARESETN)
			assert(out_fill <= 1);
	end endgenerate

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

		for(gw=0; gw<C_AXI_DATA_WIDTH/INSN_WIDTH; gw=gw+1) // For each bus word
		begin : FOR_INSN_WORD
		for(gb=0; gb<(INSN_WIDTH/8); gb=gb+1) // For each bus byte
		begin : FOR_INSN_BYTE
		always @(*)
			assert(endian_swapped_rdata[gw*INSN_WIDTH+((INSN_WIDTH/8)-1-gb)*8 +: 8]
				== M_AXI_RDATA[gw*INSN_WIDTH+gb*8 +: 8]);
		end end
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

	wire	[INSN_WIDTH-1:0]	f_bus_word, f_out_data;

	initial	f_out_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (i_new_pc)
		f_out_addr <= { i_pc[AW-1:INSN_LSB], {(INSN_LSB){1'b0}} };
	else if (o_valid && i_ready && out_fill == 1)
	begin
		f_out_addr <= 0;
		f_out_addr[AW-1:AXILLSB] <= f_out_addr[AW-1:AXILLSB] + 1;
	end

	always @(*)
	if (out_fill == 0 || out_fill == INSNS_PER_WORD)
		f_subout_addr = f_out_addr;
	else begin
		f_subout_addr = 0;
		f_subout_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB];
		f_subout_addr = f_subout_addr
			+ ((INSNS_PER_WORD-out_fill) << INSN_LSB);
	end

	always @(*)
		assert(f_out_addr[INSN_LSB-1:0] == 0);

	always @(*)
	if (S_AXI_ARESETN && pending_new_pc)
		assert(f_out_addr[AW-1:INSN_LSB] == pending_pc[AW-1:INSN_LSB]);

	always @(*)
	if (o_valid && !o_illegal)
	begin
		assert(f_out_addr[AW-1:AXILLSB] == o_pc[AW-1:AXILLSB]);
		assert(f_subout_addr[AW-1:INSN_LSB] == o_pc[AW-1:INSN_LSB]);
	end else if (!i_cpu_reset && !i_clear_cache
				&& !pending_new_pc && !i_new_pc && !o_illegal)
	begin
		assert(f_out_addr[AW-1:INSN_LSB] == o_pc[AW-1:INSN_LSB]);
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

	generate if (INSN_WIDTH == C_AXI_DATA_WIDTH)
	begin : F_BUSWORD
		// {{{
		assign	f_bus_word = endian_swapped_rdata;
		// }}}
	end else begin : BUSWORD_SHIFT
		// {{{
		reg	[$clog2(INSNS_PER_WORD)-1:0]	bshift;

		// Verilator lint_off WIDTH
		always @(*)
			bshift = fc_pc[AXILLSB-1:INSN_LSB];

		assign	f_bus_word = endian_swapped_rdata >> (bshift * INSN_WIDTH);
		// Verilator lint_on  WIDTH
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
	generate if (INSN_WIDTH == C_AXI_DATA_WIDTH)
	begin : F_OUTDATA
		// {{{
		assign	f_out_data = out_data;
		// }}}
	end else begin : F_OUTDATA_SHIFT
		// {{{
		reg	[$clog2(INSNS_PER_WORD)-1:0]	ashift;

		// Verilator lint_off WIDTH
		always @(*)
			ashift = (fc_pc - f_subout_addr) >> INSN_LSB;

		assign	f_out_data = out_data >> (ashift * INSN_WIDTH);
		// Verilator lint_on  WIDTH
		// }}}
	end endgenerate

	generate if (FETCH_LIMIT == 1)
	begin : F_SINGLE
	end else if (FETCH_LIMIT == 2)
	begin : F_CACHE_CHECK
		// {{{
		reg	[AW-1:0]		f_cache_addr;
		wire	[C_AXI_DATA_WIDTH-1:0]	f_cache_insn;
		// wire				f_cache_illegal;
		reg				f_cache_check;

		always @(*)
		begin
			f_cache_addr = 0;
			f_cache_addr[AW-1:AXILLSB] = f_out_addr[AW-1:AXILLSB]+1;

			f_cache_check = (fc_pc[AW-1:AXILLSB]
						== f_cache_addr[AW-1:AXILLSB]);
			if (!f_cache_valid)
				f_cache_check = 1'b0;
		end

		if (INSN_WIDTH == C_AXI_DATA_WIDTH)
		begin : F_CACHEDATA

			assign	f_cache_insn = f_cache_data;

		end else begin : F_CACHEDATA_SHIFT

			reg	[$clog2(INSNS_PER_WORD)-1:0]	ashift;

			always @(*)
				ashift = (fc_pc - f_cache_addr) >> INSN_LSB;

			assign	f_cache_insn = f_cache_data >> (ashift * INSN_WIDTH);
		end

		always @(*)
		if (f_cache_check && !o_illegal)
		begin
			assert(f_cache_insn[INSN_WIDTH-1:0] == fc_insn);
			assert(f_cache_illegal == fc_illegal);
		end
		// }}}
	end else begin : F_FIFO_CHECK
		// {{{
		reg	[AW-1:0]		f_cache_addr, f_fifo_addr;
		reg	[C_AXI_DATA_WIDTH-1:0]	f_cache_subdata,
						f_fifo_subdata;
		reg				f_cache_check;
		// reg	[LGFIFO:0]		f_cache_distance;
		reg				f_cache_assume;


		/*
		always @(*)
			{ f_cache_illegal, f_cache_data }
						= { FIFO_FETCH.fcache.f_first_data };

		always @(*)
			f_cache_distance = FIFO_FETCH.fcache.f_distance_to_first;

		always @(*)
			f_cache_valid = FIFO_FETCH.fcache.f_first_in_fifo;
		*/

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

		if (INSN_WIDTH == C_AXI_DATA_WIDTH)
		begin : F_CACHEDATA

			always @(*)
				f_cache_subdata = f_cache_data;

			always @(*)
				f_fifo_subdata = fifo_data[INSN_WIDTH-1:0];

		end else begin : F_CACHEDATA_SHIFT

			reg	[$clog2(INSNS_PER_WORD)-1:0]	ashift;

			// Verilator lint_off WIDTH
			always @(*)
				ashift = (fc_pc - f_cache_addr) >> INSN_LSB;
			// Verilator lint_on  WIDTH

			always @(*)
				f_cache_subdata = f_cache_data >> (ashift * INSN_WIDTH);
			always @(*)
				f_fifo_subdata = fifo_data >> (ashift * INSN_WIDTH);
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
			assert(f_cache_subdata[INSN_WIDTH-1:0] == fc_insn);
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
			assume(f_fifo_subdata[INSN_WIDTH-1:0] == fc_insn);
			assume(fifo_data[C_AXI_DATA_WIDTH] == fc_illegal);
		end
		// }}}
	end endgenerate

	//
	// Check the final output word
	// This checks all instruction positions within that word
	always @(*)
	if ((out_fill > 0)
		&& (fc_pc[AW-1:AXILLSB] == f_out_addr[AW-1:AXILLSB]))
	begin
		if (fc_illegal)
		begin
			assert(o_illegal);
		end else if (!o_illegal && fc_pc >= f_subout_addr)
			assert(f_out_data == fc_insn);
	end

	always @(*)
	if (pending_new_pc)
		assert(i_new_pc || flush_request);

	always @(*)
	if (pending_new_pc)
		assert(o_pc == pending_pc);

	// Verilator lint_off WIDTH
	always @(*)
	if (flush_request)
		assert(flushcount == faxil_outstanding + 1);
	// Verilator lint_on  WIDTH

	always @(*)
	if (flushing)
		assert(!o_illegal);

	always @(*)
	if (flush_request && !i_cpu_reset && !i_new_pc && !i_clear_cache)
	begin
		assert(f_out_addr[AW-1:AXILLSB] == pending_pc[AW-1:AXILLSB]);
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
	// Verilator lint_off UNDRIVEN
	(* anyconst *) reg	cvr_always_ready;
	// Verilator lint_on  UNDRIVEN
	reg	[3:0]	cvr_returns;

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

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_ret_addr[AXILLSB-1:0] };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
