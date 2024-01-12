////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axidcache.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A data cache built using AXI as the underlying protocol
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
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype none
// }}}
module	axidcache #(
		// {{{
		// AXI Setup: address width, data width, ID width, and ID
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 32,
		parameter	C_AXI_DATA_WIDTH = 64,
		parameter	C_AXI_ID_WIDTH = 1,
		parameter [C_AXI_ID_WIDTH-1:0]	AXI_ID = 0,
		// }}}
		// LGCACHELEN
		// {{{
		// The log (base 2) of the cache size in bytes.
		parameter	LGCACHELEN = 8 + $clog2(C_AXI_DATA_WIDTH/8),
		localparam LGCACHEWORDS= LGCACHELEN-$clog2(C_AXI_DATA_WIDTH/8),
		// }}}
		// LGNLINES
		// {{{
		// The log (base 2) of the number of cache lines.  A cache line
		// is the minimum amount of data read on a miss.  Each cache
		// line has a valid signal and a tag associated with it.
		parameter	LGNLINES = (LGCACHEWORDS-3),
		// }}}
		parameter [0:0]	SWAP_WSTRB = 1'b0,
		// OPT_SIGN_EXTEND: When returning values to the CPU that are
		// {{{
		// less than word sized in length, if OPT_SIGN_EXTEND is true
		// these values will be sign extended.
		parameter [0:0]	OPT_SIGN_EXTEND = 1'b0,
		// }}}
		parameter	NAUX = 5,
		// OPT_PIPE: Set to 1 to allow multiple outstanding transactions
		// {{{
		// This is primarily used by write requests.  Read requests
		// will only ever read one cache line at a time.  Non-cache
		// reads are only ever done (at present) as singletons.
		parameter [0:0]	OPT_PIPE = 1'b0,
		// }}}
		// OPT_WRAP: True if using AXI WRAP mode.  With AXI WRAP mode,
		// {{{
		// a cache read result will return its value before the entire
		// cache line read has been completed
		parameter [0:0]	OPT_WRAP     = 1'b0,
		// }}}
		// OPT_LOWPOWER: If true, sets unused AXI values to all zeros,
		// {{{
		// or, in the case of AxSIZE, to 3'd2.  This is to keep things
		// from toggling if they don't need to.
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		// }}}
		// OPT_LOCK: Set to 1 in order to support exclusive access.
		// {{{
		parameter [0:0]	OPT_LOCK = 1'b0,
		// }}}
		// Local parameters, mostly abbreviations
		// {{{
		// Verilator lint_off UNUSED
		localparam	LGPIPE = (OPT_PIPE) ? 4:2,
		// Verilator lint_on  UNUSED
		localparam [0:0]	OPT_DUAL_READ_PORT = 1'b1,
		localparam [1:0]	DC_IDLE  = 2'b00,
					DC_WRITE = 2'b01,
					DC_READS = 2'b10,
					DC_READC = 2'b11,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		localparam	IW = C_AXI_ID_WIDTH,
		localparam	AXILSB = $clog2(C_AXI_DATA_WIDTH/8),
		localparam	CS = LGCACHELEN - AXILSB, // Cache size, in wrds
		localparam	LS = CS-LGNLINES,	// Cache lines, lg_2
		localparam	TW = AW-(CS+AXILSB)	// Tag width
		// }}}
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		input	wire		i_cpu_reset, i_clear,
		// Interface from the CPU
		// {{{
		input	wire		i_pipe_stb, i_lock,
		input	wire	[2:0]	i_op,
		input	wire [AW-1:0]	i_addr,
		input	wire [AW-1:0]	i_restart_pc,
		input	wire [31:0]	i_data,
		input	wire [NAUX-1:0]	i_oreg,
		// Outputs, going back to the CPU
		output	reg 		o_busy, o_rdbusy,
		output	wire 		o_pipe_stalled,
		output	reg 		o_valid, o_err,
		output	reg [NAUX-1:0]	o_wreg,
		output	reg [31:0]	o_data,
		// }}}
		// AXI bus interface
		// {{{
		// Write address
		// {{{
		output	wire		M_AXI_AWVALID,
		input	wire		M_AXI_AWREADY,
		// verilator coverage_off
		output	wire [IW-1:0]	M_AXI_AWID,	// = constant
		// verilator coverage_on
		output	wire [AW-1:0]	M_AXI_AWADDR,
		// verilator coverage_off
		output	wire [7:0]	M_AXI_AWLEN,	// = const 0
		// verilator coverage_on
		output	wire [2:0]	M_AXI_AWSIZE,
		output	wire [1:0]	M_AXI_AWBURST,
		output	wire 		M_AXI_AWLOCK,
		output	wire [3:0]	M_AXI_AWCACHE,
		// verilator coverage_off
		output	wire [2:0]	M_AXI_AWPROT,
		output	wire [3:0]	M_AXI_AWQOS,
		// verilator coverage_on
		// }}}
		// Write data
		// {{{
		output	wire		M_AXI_WVALID,
		input	wire		M_AXI_WREADY,
		output	wire [DW-1:0]	M_AXI_WDATA,
		output	wire [DW/8-1:0]	M_AXI_WSTRB,
		output	wire 		M_AXI_WLAST,
		// }}}
		// Write return
		// {{{
		input	wire		M_AXI_BVALID,
		output	wire		M_AXI_BREADY,
		// verilator coverage_off
		input	wire [IW-1:0]	M_AXI_BID,
		// verilator coverage_on
		input	wire	[1:0]	M_AXI_BRESP,
		// }}}
		// Read address
		// {{{
		output	wire		M_AXI_ARVALID,
		input	wire		M_AXI_ARREADY,
		// verilator coverage_off
		output	wire [IW-1:0]	M_AXI_ARID,
		// verilator coverage_on
		output	wire [AW-1:0]	M_AXI_ARADDR,
		output	wire [7:0]	M_AXI_ARLEN,
		output	wire [2:0]	M_AXI_ARSIZE,
		output	wire [1:0]	M_AXI_ARBURST,
		output	wire 		M_AXI_ARLOCK,
		output	wire [3:0]	M_AXI_ARCACHE,
		// verilator coverage_off
		output	wire [2:0]	M_AXI_ARPROT,
		output	wire [3:0]	M_AXI_ARQOS,
		// verilator coverage_on
		// }}}
		// Read data returned
		// {{{
		input	wire		M_AXI_RVALID,
		output	wire		M_AXI_RREADY,
		// verilator coverage_off
		input	wire [IW-1:0]	M_AXI_RID,
		// verilator coverage_on
		input	wire [DW-1:0]	M_AXI_RDATA,
		input	wire		M_AXI_RLAST,
		input	wire	[1:0]	M_AXI_RRESP
		// }}}
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam	[1:0]	INCR = 2'b01,
				WRAP = 2'b10;
	localparam	[1:0]	OKAY = 2'b00,
				EXOKAY = 2'b01;
	// Verilator lint_off UNUSED
	localparam		DSZ = 2;
	// Verilator lint_on  UNUSED

	// The cache itself
	// {{{
	reg	[(1<<(CS-LS))-1:0]	cache_valid;
	reg	[TW-1:0]	cache_tag	[0:(1<<LGNLINES)-1];
	reg	[DW-1:0]	cache_mem	[0:(1<<CS)-1];
	reg	[DW-1:0]	cached_iword, cached_rword;
	// }}}

	reg			misaligned;

	wire			cache_miss_inow, address_is_cachable;
	wire			cachable_request, cachable_read_request;

	wire			i_read, i_write;
	reg	[AW-AXILSB-1:0]	r_addr;
	wire	[CS-LS-1:0]	i_cline, r_cline;
	wire	[CS-1:0]	i_caddr, r_caddr;
	reg	[TW-1:0]	last_tag, r_itag, r_rtag, w_tag;
	reg	[CS-LS-1:0]	last_tag_line;
	wire	[TW-1:0]	r_ctag, i_ctag, axi_tag;
	wire	[CS-LS-1:0]	axi_line;

	reg			r_iv, r_rv, r_check, w_v, set_vflag;
	reg			zero_noutstanding, last_ack, full_pipe,
				nearly_full_pipe;
	wire			w_pipe_stalled;
	reg	[LGPIPE-1:0]	noutstanding;
	reg	[CS-1:0]	wcache_addr;
	reg	[DW-1:0]	wcache_data;
	reg	[DW/8-1:0]	wcache_strb;
	reg	[TW-1:0]	wcache_tag;
	integer			ik;

	reg			good_cache_read;
	reg	[1:0]		state;

	reg			r_dvalid, r_svalid, r_cachable,
				r_cache_miss, flushing, r_rd_pending,
				last_tag_valid, w_cache_miss;
	reg	[DW-1:0]	pre_data, shifted_data;
	reg	[AXILSB+1:0]	req_data;
	wire	[AXILSB-1:0]	req_lsb;
	wire	[1:0]		req_op;

	reg	[1:0]		suppress_miss;
	reg	[CS-1:0]	read_addr;

	assign	i_write = i_op[0];
	assign	i_read  = !i_op[0];

	// AXI registers
	// {{{
	reg			axi_awvalid, axi_wvalid;
	reg	[AW-1:0]	axi_awaddr;
	reg	[2:0]		axi_awsize;
	reg	[DW-1:0]	axi_wdata;
	reg	[DW/8-1:0]	axi_wstrb;
	wire	[DW-1:0]	axi_rdata;
	wire			axi_awlock;

	reg			axi_arvalid;
	reg	[AW-1:0]	axi_araddr;
	reg	[7:0]		axi_arlen;
	reg	[2:0]		axi_arsize;
	wire	[1:0]		axi_arburst;
	wire			axi_arlock;
	// }}}

	// LOCK handling declarations
	// {{{
	wire	[AW-1:0]	restart_pc;
	wire			locked_write_in_progress,
				locked_read_in_progress,
				locked_read_in_cache;
	// }}}
	// }}}

	// Fixed AXI outputs that aren't changing
	// {{{
	assign	M_AXI_AWID = AXI_ID;
	assign	M_AXI_ARID = AXI_ID;
	assign	M_AXI_AWLEN = 0;	// All writes are one beat only

	assign	M_AXI_AWBURST = INCR;	// INCR addressing only
	assign	M_AXI_ARBURST = axi_arburst;

	assign	M_AXI_AWLOCK = OPT_LOCK && axi_awlock;
	assign	M_AXI_ARLOCK = OPT_LOCK && axi_arlock;

	assign	M_AXI_AWCACHE = M_AXI_AWLOCK ? 0 : 4'b011;
	assign	M_AXI_ARCACHE = M_AXI_ARLOCK ? 0 : 4'b011;

	assign	M_AXI_AWPROT = 3'b0;	// == 3'b001 if GIE is clear, 3'b000 if
	assign	M_AXI_ARPROT = 3'b0;	// not

	assign	M_AXI_AWQOS = 0;
	assign	M_AXI_ARQOS = 0;

	assign	M_AXI_WLAST = 1;

	assign	M_AXI_BREADY = 1;
	assign	M_AXI_RREADY = 1;
	// }}}

	// Misalignment detection
	// {{{
	always @(*)
	begin
		misaligned = checklsb(i_op[2:1], i_addr[1:0]);
	end

	function checklsb;
		input	[1:0]	op;
		input	[1:0]	addr;

		casez(op[1:0])
		2'b0?:	checklsb = (addr[1:0] != 2'b00); // 32'bit words
		2'b10:	checklsb = addr[0];	// 16-bit words
		2'b11:	checklsb = 1'b0;	// Bytes are never misaligned
		endcase
	endfunction
	// }}}

	// Address decoding
	//  {{{
	assign	i_cline = i_addr[LS+AXILSB +: (CS-LS)];	// Cache line
	assign	i_caddr = i_addr[AXILSB +: CS];		// Cache address
	assign	i_ctag  = i_addr[AW-1:CS+AXILSB];	// Associated tag

	// Unlike i_addr, r_addr doesn't include the AXI LSB's
	assign	r_cline = r_addr[CS-1:LS];	// Cache line
	assign	r_caddr = r_addr[CS-1:0];	// Cache address
	assign	r_ctag  = r_addr[AW-AXILSB-1 : CS];	// Associated tag

	assign	cache_miss_inow = (!last_tag_valid
			|| last_tag != i_ctag
			|| last_tag_line != i_cline);
	// }}}

	// Cache lookup
	// {{{
	always @(posedge S_AXI_ACLK)
		r_check <= i_pipe_stb;

	always @(posedge S_AXI_ACLK)
	if (i_pipe_stb)
		r_itag  <= cache_tag[i_cline];

	always @(posedge S_AXI_ACLK)
	if (o_pipe_stalled)
		r_rtag  <= cache_tag[r_cline];

	always @(posedge S_AXI_ACLK)
	if (i_pipe_stb)
		r_iv  <= cache_valid[i_cline];

	always @(posedge S_AXI_ACLK)
		r_rv  <= cache_valid[r_cline] && r_rd_pending;

	always @(*)
		w_v = (r_check) ? r_iv : r_rv;

	always @(*)
		w_tag = (r_check) ? r_itag : r_rtag;

	// Cachability checking
	// {{{
	// Note that the correct address width must be built-in to the
	// iscachable routine.  It is *not* parameterizable.  iscachable must
	// be rewritten if the address width changes because, of necessity, that
	// also means the address map is changing and therefore what is and
	// isn't cachable.  etc.
	iscachable chkaddress(
		i_addr[AW-1:0], address_is_cachable
	);
	// }}}

	// Locked requests are *not* cachable, but *must* go to the bus
	assign	cachable_request = address_is_cachable&& (!OPT_LOCK || !i_lock);
	assign	cachable_read_request = i_pipe_stb && i_read
						&& cachable_request;

	initial	r_rd_pending = 0;
	initial	r_cache_miss = 0;
	initial	last_tag_valid = 0;
	initial	r_dvalid = 0;
	always @(posedge S_AXI_ACLK)
	begin
		r_svalid <= cachable_read_request && !misaligned
			&& !cache_miss_inow && (wcache_strb == 0);

		if (!o_pipe_stalled)
			r_addr <= i_addr[AW-1:AXILSB];

		if (!o_pipe_stalled && !r_rd_pending)
		begin
			r_cachable <= cachable_read_request;
			r_rd_pending <= cachable_read_request
					&& !misaligned
					&& (cache_miss_inow || (|wcache_strb));
		end else if (r_rd_pending)
		begin
			r_rd_pending <= (w_tag != r_ctag || !w_v);
			if (OPT_WRAP && M_AXI_RVALID)
				r_rd_pending <= 0;
		end

		if (M_AXI_RVALID && M_AXI_RRESP[1])
			r_rd_pending <= 1'b0;

		// r_rd <= (i_pipe_stb && !i_read);

		r_dvalid <= !r_svalid && !r_dvalid
				&& (w_tag == r_ctag) && w_v
				&& r_cachable && r_rd_pending;

		if (w_tag == r_ctag && w_v && r_cachable && r_rd_pending)
		begin
			last_tag_valid <= 1'b1;
			last_tag_line <= r_cline;
			last_tag      <= r_ctag;
		end else if (state == DC_READC)
			//	&& (last_tag == r_ctag)
			//	&& (M_AXI_RVALID))
			last_tag_valid <= 1'b0;

		r_cache_miss <= (r_cachable && !r_svalid
				&& (r_rd_pending && !r_svalid)
				&& (w_tag != r_ctag || !w_v));

		if (i_clear)
			last_tag_valid <= 0;
		if (OPT_PIPE && M_AXI_BVALID && M_AXI_BRESP[1])
			last_tag_valid <= 0;

		if (!S_AXI_ARESETN || i_cpu_reset)
		begin
			r_cachable <= 1'b0;
			r_svalid <= 1'b0;
			r_dvalid <= 1'b0;
			r_cache_miss <= 1'b0;
			r_rd_pending <= 0;
			last_tag_valid <= 0;
		end
	end
	// }}}

	// Transaction counting
	// {{{
	initial	noutstanding = 0;
	initial	zero_noutstanding = 1;
	initial	nearly_full_pipe = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		noutstanding <= 0;
		zero_noutstanding <= 1;
		nearly_full_pipe <= 0;
	end else case( { ((M_AXI_AWVALID && M_AXI_AWREADY)
					||(M_AXI_ARVALID && M_AXI_ARREADY)),
			((M_AXI_RVALID && M_AXI_RLAST) || M_AXI_BVALID)
			})
	2'b10: begin
		noutstanding <= noutstanding + 1;
		zero_noutstanding <= 1'b0;
		nearly_full_pipe <= (noutstanding >= (1<<LGPIPE)-3);
		end
	2'b01: begin
		noutstanding <= noutstanding - 1;
		zero_noutstanding <= (noutstanding == 1);
		nearly_full_pipe <= (&noutstanding);
		end
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	begin
		assert(zero_noutstanding == (noutstanding == 0));
		assert(nearly_full_pipe == (noutstanding >= (1<<LGPIPE)-2));
	end
`endif

	always @(*)
	begin
		full_pipe = 1'b0;
		if (nearly_full_pipe)
			full_pipe = noutstanding[0]
					|| (M_AXI_AWVALID || M_AXI_WVALID);
	end

	always @(*)
		last_ack = (noutstanding <= 1)&&(!M_AXI_ARVALID && !M_AXI_AWVALID);

	initial	flushing = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		flushing <= 0;
	else if (flushing)
	begin // Can we clear flushing?
		if (zero_noutstanding)
			flushing <= 1'b0;
		if (last_ack && (M_AXI_BVALID
				|| (M_AXI_RVALID && M_AXI_RLAST)))
			flushing <= 1'b0;
		if (M_AXI_AWVALID || M_AXI_ARVALID || M_AXI_WVALID)
			flushing <= 1'b1;
	end else if (i_cpu_reset
			|| (M_AXI_RVALID && M_AXI_RRESP[1])
			|| (M_AXI_BVALID && M_AXI_BRESP[1])
			|| (OPT_PIPE && i_pipe_stb && misaligned))
	begin // Flushing causes
		flushing <= 1'b0;
		if (M_AXI_ARVALID || M_AXI_AWVALID || M_AXI_WVALID)
			flushing <= 1'b1;
		if (!last_ack)
			flushing <= 1'b1;
		if ((noutstanding >= 1) && !M_AXI_BVALID
					&& (!M_AXI_RVALID || !M_AXI_RLAST))
			flushing <= 1'b1;
	end
	// }}}

	// Read handling
	// {{{
	// Read state machine
	// {{{
	initial	state = DC_IDLE;
	initial	set_vflag = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		cache_valid <= 0;
		// end_of_line <= 1'b0;
		// last_line_stb <= 1'b0;
		state <= DC_IDLE;
		set_vflag <= 1'b0;
		// }}}
	end else begin
		// {{{
		set_vflag <= 1'b0;
		if (set_vflag)
			cache_valid[r_cline] <= 1'b1;

		case(state)
		DC_IDLE: begin
			// {{{
			good_cache_read <= 1'b1;
			if (i_pipe_stb && i_write && !misaligned)
				state <= DC_WRITE;
			else if (w_cache_miss)
				state <= DC_READC;
			else if (i_pipe_stb && i_read && !cachable_request
					&& !misaligned)
				state <= DC_READS;

			if (i_cpu_reset)
				state <= DC_IDLE;
			end
			// }}}
		DC_READC: begin	// Read cache line
			// {{{
			if (M_AXI_RVALID)
			begin
				good_cache_read
					<= good_cache_read && !M_AXI_RRESP[1];
				cache_valid[r_cline] <= 1'b0;
			end
			if (M_AXI_RVALID && M_AXI_RLAST)
			begin
				state <= DC_IDLE;
				set_vflag <= !i_cpu_reset && !i_clear && !flushing && !M_AXI_RRESP[1] && good_cache_read;
			end end
			// }}}
		DC_READS: begin	// Read single value
			// {{{
			if (M_AXI_RVALID && last_ack)
				state <= DC_IDLE;
			end
			// }}}
		DC_WRITE: begin
			// {{{
			if (M_AXI_BVALID && M_AXI_BREADY
				&& (!OPT_PIPE || (last_ack && !i_pipe_stb)))
				state <= DC_IDLE;
			end
			// }}}
		endcase

		if (i_clear || i_cpu_reset)
			cache_valid <= 0;
		if (OPT_PIPE && M_AXI_BVALID && M_AXI_BRESP[1])
			cache_valid <= 0;
		// }}}
	end
	// }}}

	// axi_axlock
	// {{{
	generate if (OPT_LOCK)
	begin : GEN_AXLOCK

		reg		r_arlock, r_awlock;
		reg	[2:0]	r_read_in_cache;

		initial	r_arlock = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_arlock <= 1'b0;
		else if (i_pipe_stb)
		begin
			r_arlock <= i_lock;

			if (misaligned || i_write)
				r_arlock <= 1'b0;
		end else if (M_AXI_RVALID)
			r_arlock <= 1'b0;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || r_rd_pending || M_AXI_RVALID)
			r_read_in_cache <= 3'b00;
		else if (i_pipe_stb)
		begin
			r_read_in_cache <= 3'b00;
			r_read_in_cache[0] <= address_is_cachable && i_read && i_lock;
		end else if (r_read_in_cache != 0)
		begin
			r_read_in_cache[2:1] <= { r_read_in_cache[1:0] };
			if (r_read_in_cache[1] && ((w_tag != r_ctag) || !w_v))
				r_read_in_cache <= 0;
				// && (w_tag == r_ctag) && w_v
		end

		initial	r_awlock = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			r_awlock <= 1'b0;
		else if (i_pipe_stb)
		begin
			r_awlock <= i_lock;

			if (misaligned || i_read)
				r_awlock <= 1'b0;
		end else if (M_AXI_BVALID)
			r_awlock <= 1'b0;

		assign	locked_write_in_progress = r_awlock;
		assign	locked_read_in_progress  = r_arlock;
		assign	locked_read_in_cache = r_read_in_cache[2];
		assign	axi_awlock = r_awlock;
		assign	axi_arlock = r_arlock;
	end else begin : NO_LOCK
		assign	axi_awlock = 1'b0;
		assign	axi_arlock = 1'b0;
		assign	locked_write_in_progress = 1'b0;
		assign	locked_read_in_progress  = 1'b0;
		assign	locked_read_in_cache = 1'b0;
	end endgenerate
	// }}}

	// M_AXI_ARVALID, axi_arvalid
	// {{{
	always @(posedge S_AXI_ACLK)
		suppress_miss <= { suppress_miss[0] || set_vflag, set_vflag };
	always @(*)
		w_cache_miss = r_cache_miss && state == DC_IDLE
				&& !r_dvalid && !o_err
				&& wcache_strb == 0 && !suppress_miss[1];

	initial	axi_arvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_arvalid <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		axi_arvalid <= 1'b0;
		if (i_pipe_stb && i_read && !misaligned
			&& ((OPT_LOCK && i_lock) || !address_is_cachable))
			axi_arvalid <= 1;
		if (w_cache_miss)
			axi_arvalid <= 1;
		if (i_cpu_reset)
			axi_arvalid <= 0;
	end

	assign	M_AXI_ARVALID = axi_arvalid;
	// }}}

	// M_AXI_ARADDR, M_AXI_ARSIZE, M_AXI_ARLEN
	// {{{
	initial	axi_araddr = 0;
	initial	axi_arsize = 3'd2;
	initial	axi_arlen  = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
	begin
		// {{{
		axi_araddr <= 0;
		axi_arsize <= 3'd2;
		axi_arlen  <= 0;
		// }}}
	end else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		axi_arlen  <= 0;
		if (r_cache_miss)
		begin
			// {{{
			if (OPT_WRAP)
				axi_araddr <= { r_ctag, r_caddr[CS-1:0],
							{(AXILSB){1'b0}} };
			else
				axi_araddr <= { r_ctag, r_cline, {(LS+AXILSB){1'b0}} };
			axi_arlen  <= (1 << LS) - 1;
			axi_arsize <= AXILSB[2:0];
			// }}}
		end else begin
			// {{{
			axi_araddr <= i_addr;
			axi_arlen  <= 0;
			casez(i_op[2:1])
			2'b0?: axi_arsize <= 3'd2;
			2'b10: axi_arsize <= 3'd1;
			2'b11: axi_arsize <= 3'd0;
			// default:  axi_arsize <= 3'd2; (Messes w/ coverage)
			endcase

			if (SWAP_WSTRB)
			begin
				// axi_araddr[AXILSB-1:0] <= ~i_addr[AXILSB-1:0];
				axi_araddr[1:0] <= 0;
				axi_arsize <= 3'b010;
			end
			// }}}
		end

		if (OPT_LOWPOWER && (i_cpu_reset || (!w_cache_miss
			&& (!i_pipe_stb || i_op[0] || misaligned
					|| (address_is_cachable && !i_lock)))))
		begin
			// {{{
			axi_araddr <= 0;
			axi_arlen  <= 0;
			axi_arsize <= 3'd2;
			// }}}
		end
	end

	assign	axi_tag  = axi_araddr[AW-1:AW-TW];
	assign	axi_line = axi_araddr[AXILSB+LS +: CS-LS];

	assign	M_AXI_ARADDR = axi_araddr;
	assign	M_AXI_ARLEN  = axi_arlen;
	assign	M_AXI_ARSIZE = axi_arsize;
	// }}}

	// M_AXI_ARBURST
	// {{{
	generate if (OPT_WRAP)
	begin : GEN_ARBURST
		reg	r_wrap;

		initial	r_wrap = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (OPT_LOWPOWER && !S_AXI_ARESETN)
		begin
			// {{{
			r_wrap <= 1'b0;
			// }}}
		end else if (!M_AXI_ARVALID || M_AXI_ARREADY)
		begin
			// {{{
			r_wrap <= 1'b0;
			if (r_cache_miss)
				r_wrap <= 1'b1;
			// }}}
		end

		assign	axi_arburst = r_wrap ? WRAP : INCR;

	end else begin : NO_WRAPBURST

		assign	axi_arburst = INCR;
	end endgenerate

	// }}}
	// }}}

	// Writes always go straight to the bus
	// {{{

	// M_AXI_AWVALID, axi_awvalid
	// {{{
	initial	axi_awvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_awvalid <= 1'b0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		axi_awvalid <= i_pipe_stb && i_op[0] && !misaligned;
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			axi_awvalid <= 1'b0;
		if (i_cpu_reset || flushing)
			axi_awvalid <= 1'b0;
	end

	assign	M_AXI_AWVALID = axi_awvalid;
	// }}}

	// M_AXI_AWADDR
	// {{{
	initial	axi_awaddr = 0;
	initial	axi_awsize = 3'd2;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
	begin
		axi_awaddr <= 0;
		axi_awsize <= 3'd2;
	end else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		axi_awaddr <= i_addr;

		casez(i_op[2:1])
		2'b0?: axi_awsize <= 3'd2;
		2'b10: axi_awsize <= 3'd1;
		2'b11: axi_awsize <= 3'd0;
		// default:  axi_awsize <= 3'd2;	(Unused, messes w/ covr)
		endcase


		if (SWAP_WSTRB)
		begin
			// axi_awaddr[AXILSB-1:0] <= ~i_addr[AXILSB-1:0];
			axi_awaddr[1:0] <= 0;
			axi_awsize <= 3'd2;
		end

		if (OPT_LOWPOWER && (!i_pipe_stb || !i_op[0] || misaligned
				|| i_cpu_reset || flushing
				|| (M_AXI_BVALID && M_AXI_BRESP[1])))
		begin
			axi_awaddr <= 0;
			axi_awsize <= 3'd2;
		end
	end

	assign	M_AXI_AWADDR = axi_awaddr;
	assign	M_AXI_AWSIZE = axi_awsize;
	// }}}

	// M_AXI_WVALID
	// {{{
	initial	axi_wvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_wvalid <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		axi_wvalid <= i_pipe_stb && i_op[0] && !misaligned;
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			axi_wvalid <= 1'b0;
		if (i_cpu_reset || flushing)
			axi_wvalid <= 1'b0;
	end

	assign	M_AXI_WVALID = axi_wvalid;
	// }}}

	// M_AXI_WDATA, M_AXI_WSTRB
	// {{{
	initial	axi_wdata = 0;
	initial	axi_wstrb = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN && OPT_LOWPOWER)
	begin
		axi_wdata <= 0;
		axi_wstrb <= 0;
	end else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin

		// WDATA
		// {{{
		if (SWAP_WSTRB)
		begin
			// {{{
			casez(i_op[2:1])
			// Write a 16b half-word
			2'b10: axi_wdata <= { i_data[15:0],
				{(C_AXI_DATA_WIDTH-16){1'b0}} }
				>> (8*i_addr[AXILSB-1:0]);
			// Write an 8b half-word
			2'b11: axi_wdata <= { i_data[7:0],
					{(C_AXI_DATA_WIDTH-8){1'b0}} }
				>> (8*i_addr[AXILSB-1:0]);
			default: axi_wdata <= { i_data,
					{(C_AXI_DATA_WIDTH-32){1'b0}} }
				>> (8*i_addr[AXILSB-1:0]);
			endcase
			// }}}
		end else begin
			// {{{
			casez(i_op[2:1])
			// Write a 16b half-word
			2'b10: axi_wdata <= { {(C_AXI_DATA_WIDTH-16){1'b0}},
				i_data[15:0] } << (8*i_addr[AXILSB-1:0]);
			// Write an 8b half-word
			2'b11: axi_wdata <= { {(C_AXI_DATA_WIDTH-8){1'b0}},
				i_data[7:0] } << (8*i_addr[AXILSB-1:0]);
			default: axi_wdata <= { {(C_AXI_DATA_WIDTH-32){1'b0}},
				i_data } << (8*i_addr[AXILSB-1:0]);
			endcase
			// }}}
		end
		// }}}

		// WSTRB
		// {{{
		if (SWAP_WSTRB)
		begin
			// {{{
			casez(i_op[2:1])
			// Write a 16b half-word
			2'b10: axi_wstrb <= { 2'b11,
				{(C_AXI_DATA_WIDTH/8-2){1'b0}} }
				>> (i_addr[AXILSB-1:0]);
			// Write an 8b half-word
			2'b11: axi_wstrb <= { 1'b1,
				{(C_AXI_DATA_WIDTH/8-1){1'b0}} }
				>> (i_addr[AXILSB-1:0]);
			default: axi_wstrb <= { 4'b1111,
					{(C_AXI_DATA_WIDTH/8-4){1'b0}} }
					>> (i_addr[AXILSB-1:0]);
			endcase
			// }}}
		end else begin
			// {{{
			casez(i_op[2:1])
			// Write a 16b half-word
			2'b10: axi_wstrb <= { {(C_AXI_DATA_WIDTH/8-4){1'b0}},
				4'b0011 } << (i_addr[AXILSB-1:0]);
			// Write an 8b half-word
			2'b11: axi_wstrb <= { {(C_AXI_DATA_WIDTH/8-4){1'b0}},
				4'b0001 } << (i_addr[AXILSB-1:0]);
			default: axi_wstrb <= { {(C_AXI_DATA_WIDTH/8-4){1'b0}},
					4'b1111 } << (i_addr[AXILSB-1:0]);
			endcase
			// }}}
		end
		// }}}

		// OPT_LOWPOWER: Clear if nothing is being used
		// {{{
		if (OPT_LOWPOWER && ((!i_pipe_stb || !i_op[0] || misaligned)
			|| (M_AXI_BVALID && M_AXI_BRESP[1])
			|| (i_cpu_reset || flushing)))
		begin
			axi_wdata <= 0;
			axi_wstrb <= 0;
		end
		// }}}
	end

	genvar	gk;
	generate if (!SWAP_WSTRB)
	begin : NO_SWAP_WSTRB
		assign	M_AXI_WDATA = axi_wdata;
		assign	M_AXI_WSTRB = axi_wstrb;

		assign	axi_rdata   = M_AXI_RDATA;
	end else begin : J
	for(gk=0; gk<C_AXI_DATA_WIDTH/32; gk=gk+1)
	begin : GEN_SWAP_WSTRB
		assign	M_AXI_WDATA[32*gk +: 32] = axi_wdata[C_AXI_DATA_WIDTH - (gk+1)*32 +: 32];
		assign	M_AXI_WSTRB[ 4*gk +:  4] = axi_wstrb[C_AXI_DATA_WIDTH/8 - (gk+1)*4 +: 4];

		assign	axi_rdata[32*gk +: 32] = M_AXI_RDATA[C_AXI_DATA_WIDTH - (gk+1)*32 +: 32];
	end end endgenerate
	// }}}
	// }}}

	// Writes take a clock to go to the cache
	// {{{
	reg	[AW-1:0]	rev_addr;
	always @(*)
	begin
		rev_addr = i_addr;
		/*
		if (SWAP_WSTRB && C_AXI_DATA_WIDTH != 32)
		begin
			rev_addr[AXILSB-1:0] = ~i_addr[AXILSB-1:0];
			rev_addr[1:0] = i_addr[1:0];
		end
		*/
	end

	always @(posedge S_AXI_ACLK)
	begin
		wcache_strb <= 0;

		if (i_pipe_stb && (!OPT_LOWPOWER || i_read))
		begin
			if (i_lock && OPT_LOCK)
				read_addr <= i_addr[LGCACHELEN-1:AXILSB];
			else if (OPT_WRAP)
				read_addr <= i_addr[LGCACHELEN-1:AXILSB];
			else
				read_addr <= { i_addr[LGCACHELEN-1:AXILSB+LS], {(LS){1'b0}} };
		end

		if (state == DC_READC)
		begin
			// {{{
			// Write returning read data to the cache
			if (M_AXI_RVALID)
				read_addr[LS-1:0]
					<= read_addr[LS-1:0] + 1;
			read_addr[CS-1:LS] <= r_cline;
			wcache_addr <= read_addr;
			wcache_data <= axi_rdata;
			wcache_strb <= -1;
			if (!M_AXI_RVALID || flushing || i_cpu_reset
				|| M_AXI_RRESP[1])
				wcache_strb <= 0;
			wcache_tag  <= w_tag;
			// }}}
		end else begin
			// {{{
			if (i_pipe_stb)
				{ wcache_tag, wcache_addr } <= i_addr[AW-1:AXILSB];
			else if (locked_read_in_progress)
				wcache_addr <= read_addr;
			else
				wcache_addr[LS-1:0] <= 0;

			// wcache_data
			// {{{
			if (SWAP_WSTRB)
			begin
				casez(i_op[2:1])
				// Write a 16b half-word
				2'b10: wcache_data <= { i_data[15:0],
							{(DW-16){1'b0}} }
					>> (8*i_addr[AXILSB-1:0]);
				// Write an 8b half-word
				2'b11: wcache_data <= { i_data[7:0],
							{(DW-8){1'b0}} }
					>> (8*i_addr[AXILSB-1:0]);
				default: wcache_data <= { i_data,
							{(DW-32){1'b0}} }
					>> (8*i_addr[AXILSB-1:0]);
				endcase
			end else begin
				casez(i_op[2:1])
				// Write a 16b half-word
				2'b10: wcache_data <= { {(DW-16){1'b0}},
					i_data[15:0] } << (8*i_addr[AXILSB-1:0]);
				// Write an 8b half-word
				2'b11: wcache_data <= { {(DW-8){1'b0}},
					i_data[7:0] } << (8*i_addr[AXILSB-1:0]);
				default: wcache_data <= { {(DW-32){1'b0}},
					i_data } << (8*i_addr[AXILSB-1:0]);
				endcase
			end

			if (locked_read_in_progress)
				wcache_data <= axi_rdata;
			// }}}

			// wcache_strb
			// {{{
			if (SWAP_WSTRB)
			begin
				case(i_op[2:1])
				// Write a 16b half-word
				2'b10: wcache_strb<=
					{ 2'h3, {(C_AXI_DATA_WIDTH/8-2){1'b0}} }
						>> (i_addr[AXILSB-1:0]);
				// Write an 8b byte
				2'b11: wcache_strb<=
					{ 1'b1, {(C_AXI_DATA_WIDTH/8-1){1'b0}} }
						>> (i_addr[AXILSB-1:0]);
				default: wcache_strb<=
					{ 4'hf, {(C_AXI_DATA_WIDTH/8-4){1'b0}} }
						>> (i_addr[AXILSB-1:0]);
				endcase
			end else begin
				case(i_op[2:1])
				// Write a 16b half-word
				2'b10: wcache_strb<=
					{ {(C_AXI_DATA_WIDTH/8-4){1'b0}}, 4'h3 }
						<< (i_addr[AXILSB-1:0]);
				// Write an 8b byte
				2'b11: wcache_strb<=
					{ {(C_AXI_DATA_WIDTH/8-4){1'b0}}, 4'h1 }
						<< (i_addr[AXILSB-1:0]);
				default: wcache_strb<=
					{{(C_AXI_DATA_WIDTH/8-4){1'b0}}, 4'hf }
						<< (i_addr[AXILSB-1:0]);
				endcase
			end
			// }}}

			if (locked_read_in_progress)
			begin
				if (!locked_read_in_cache || !M_AXI_RVALID
						|| M_AXI_RRESP != EXOKAY)
					wcache_strb <= 0;
			end else if (!i_pipe_stb || !i_op[0] || misaligned)
				wcache_strb <= 0;
			// }}}
		end
	end
	// }}}

	// Actually write to the cache
	// {{{
	always @(posedge S_AXI_ACLK)
	if (state != DC_WRITE || (r_iv && wcache_tag == r_itag))
	begin
		for(ik=0; ik<DW/8; ik=ik+1)
		if (wcache_strb[ik])
			cache_mem[wcache_addr][8*ik +: 8] <= wcache_data[8*ik +: 8];
	end
	// }}}

	// Update the cache tag
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!flushing && M_AXI_RVALID && state == DC_READC)
		cache_tag[r_cline] <= r_ctag;
	// }}}

	// o_busy
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_busy <= 1'b0;
	else if (flushing || (i_pipe_stb && !misaligned))
		o_busy <= 1'b1;
	else if (state  == DC_READS && M_AXI_RVALID && last_ack)
		o_busy <= 1'b0;
	else if (OPT_WRAP
			// && state  == DC_READC && M_AXI_RVALID && M_AXI_RLAST
			&& state == DC_IDLE && !r_rd_pending)
		o_busy <= 1'b0;
	else if ((r_dvalid || r_svalid) && (!OPT_WRAP || state == DC_IDLE))
		o_busy <= 1'b0;
	else if (M_AXI_BVALID && last_ack && (!OPT_PIPE || !i_pipe_stb))
		o_busy <= 1'b0;
	// }}}

	// o_rdbusy
	// {{{
	initial	o_rdbusy = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_rdbusy <= 1'b0;
	else if (i_cpu_reset)
		o_rdbusy <= 1'b0;
	else if (i_pipe_stb && (i_read || (i_lock && OPT_LOCK))&& !misaligned)
		o_rdbusy <= 1'b1;
	else if (state == DC_READS && M_AXI_RVALID)
		o_rdbusy <= 1'b0;
	else if (state == DC_READC && M_AXI_RVALID && (OPT_WRAP || M_AXI_RRESP[1]))
		o_rdbusy <= 1'b0;
	else if (locked_write_in_progress && M_AXI_BVALID)
		o_rdbusy <= 1'b0;
	else if (r_svalid || r_dvalid)
		o_rdbusy <= 1'b0;
	// }}}

	// o_pipe_stalled
	// {{{
	generate if (OPT_PIPE)
	begin : GEN_PIPE_STALL
		reg	r_pipe_stalled, pipe_stalled;
		(* keep *) reg	[3:0]	r_pipe_code;

	// else case( { ((M_AXI_AWVALID && M_AXI_AWREADY)
	//				||(M_AXI_ARVALID && M_AXI_ARREADY)),
	//		((M_AXI_RVALID && M_AXI_RLAST) || M_AXI_BVALID)
	//		})
	// 2'b10: noutstanding <= noutstanding + 1;
	// 2'b01: noutstanding <= noutstanding - 1;

		initial	r_pipe_stalled = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			r_pipe_stalled <= 1'b0;
			r_pipe_code <= 4'h0;
		end else begin
			// Clear any stall on the last outstanding bus response
			if ((!OPT_WRAP && r_dvalid)
				// || (OPT_WRAP && state == DC_READC
				//		&& M_AXI_RVALID && M_AXI_RLAST)
				|| (OPT_WRAP && state == DC_IDLE && !r_rd_pending))
			begin
				r_pipe_stalled <= 1'b0;
				r_pipe_code  <= 4'h1;
			end
			if (r_svalid)
			begin
				r_pipe_stalled <= 1'b0;
				r_pipe_code  <= 4'h2;
			end
			if (last_ack && (M_AXI_BVALID
				||(OPT_WRAP && state == DC_IDLE && !r_rd_pending)
				||(state  == DC_READS && M_AXI_RVALID
								&& last_ack)
				||(!OPT_WRAP && !r_rd_pending
					&& M_AXI_RVALID && M_AXI_RLAST)))
			begin
				r_pipe_stalled <= 1'b0;
				r_pipe_code <= 4'h3;
			end

			// If we have to start flushing, then we have to stall
			// while flushing

			if (i_cpu_reset
			|| (M_AXI_RVALID && M_AXI_RRESP[1])
			|| (M_AXI_BVALID && M_AXI_BRESP[1])
			|| (i_pipe_stb && misaligned))
			begin
			// {{{
			r_pipe_stalled <= 1'b0;
			r_pipe_code <= 4'ha;

			// Always stall if we have to start flushing
			if (M_AXI_ARVALID || M_AXI_AWVALID || M_AXI_WVALID)
			begin
				r_pipe_stalled <= 1'b1;
				r_pipe_code <= 4'h4;
			end
			if (!last_ack)
			begin
				r_pipe_stalled <= 1'b1;
				r_pipe_code <= 4'h5;
			end
			if ((noutstanding >= 1) && !M_AXI_BVALID
						&& (!M_AXI_RVALID || !M_AXI_RLAST))
			begin
				r_pipe_stalled <= 1'b1;
				r_pipe_code <= 4'h6;
			end
			// }}}
			end

			// All cachable read requests will stall our pipeline
			if (!i_cpu_reset && i_pipe_stb && i_read && !misaligned)
			begin
				r_pipe_stalled <= 1'b1;
				r_pipe_code <= 4'h7;
			end
			if (!i_cpu_reset && i_pipe_stb && i_lock && !misaligned)
			begin
				r_pipe_stalled <= 1'b1;
				r_pipe_code <= 4'h8;
			end

			if (flushing && (M_AXI_AWVALID || M_AXI_ARVALID || M_AXI_WVALID))
			begin
				r_pipe_stalled <= 1'b1;
				r_pipe_code <= 4'h9;
			end
		end

		always @(*)
		if (r_pipe_stalled)
			pipe_stalled = 1'b1;
		else if (M_AXI_AWVALID && !M_AXI_AWREADY)
			pipe_stalled = 1'b1;
		else if (M_AXI_WVALID && !M_AXI_WREADY)
			pipe_stalled = 1'b1;
		else if (full_pipe)
			pipe_stalled = 1'b1;
		else
			pipe_stalled = 1'b0;

		assign	w_pipe_stalled = r_pipe_stalled;
		assign	o_pipe_stalled = pipe_stalled;

		// Verilator lint_off UNUSED
		wire	unused_pipe;
		assign	unused_pipe = &{ 1'b0, r_pipe_code };
		// Verilator lint_on  UNUSED
`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN && locked_write_in_progress)
		begin
			assert(r_pipe_stalled);
		end
`endif
	end else begin : PIPE_STALL_ON_BUSY
		assign	w_pipe_stalled = 1'b0;
		assign	o_pipe_stalled = o_busy;

		// Verilator lint_off UNUSED
		wire	unused_pipe;
		assign	unused_pipe = &{ 1'b0, full_pipe };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// o_wreg
	// {{{
	// generate if (!OPT_PIPE)
	always @(posedge S_AXI_ACLK)
	if (i_pipe_stb)
	begin
		o_wreg <= i_oreg;
		if (OPT_LOCK && i_lock && i_op[0])
			o_wreg <= { i_oreg[4], 4'hf };
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && locked_write_in_progress)
		assert(o_wreg[3:0] == 4'hf);
`endif
	// }}}

	// restart_pc
	// {{{
	generate if (OPT_LOCK)
	begin : GEN_RESTART_PC
		reg	[AW-1:0]	r_pc;

		always @(posedge S_AXI_ACLK)
		if (i_pipe_stb && i_lock && i_op[0])
			r_pc <= i_restart_pc;

		assign	restart_pc = r_pc;

	end else begin : NO_RESTART_PC
		assign	restart_pc = 0;

		// Verilator lint_off UNUSED
		wire	unused_restart_pc;
		assign	unused_restart_pc = &{ 1'b0, i_restart_pc };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// req_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (i_pipe_stb)
		req_data <= { i_op[2:1], rev_addr[AXILSB-1:0] };

	assign	req_lsb = req_data[AXILSB-1:0];
	assign	req_op  = req_data[AXILSB +: 2];
	// }}}

	// o_err
	// {{{
	initial	o_err = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_err <= 1'b0;
	else if (i_cpu_reset || flushing)
		o_err <= 1'b0;
	else begin
		o_err <= 1'b0;
		if (M_AXI_RVALID && M_AXI_RRESP[1] && o_rdbusy && !r_dvalid)
			o_err <= 1'b1;
		if (M_AXI_RVALID && locked_read_in_progress
						&& M_AXI_RRESP != EXOKAY)
			o_err <= 1'b1;
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			o_err <= 1'b1;
		if (i_pipe_stb && misaligned)
			o_err <= 1'b1;
	end
	// }}}

	// Read from the cache
	// {{{
	generate if (OPT_DUAL_READ_PORT)
	begin : GEN_DUALREAD
		always @(posedge S_AXI_ACLK)
		if (!OPT_LOWPOWER || (i_pipe_stb && !i_op[0]))
			cached_iword <= cache_mem[i_caddr];

		always @(posedge S_AXI_ACLK)
		if (!OPT_LOWPOWER || o_rdbusy)
			cached_rword <= cache_mem[r_caddr];
	end else begin : GEN_SINGLE_READ_PORT

		always @(posedge S_AXI_ACLK)
			cached_rword <= cache_mem[(o_busy) ? r_caddr : i_caddr];

		always @(*)
			cached_iword = cached_rword;
	end endgenerate
	// }}}

	// o_data, pre_data
	// {{{
	always @(*)
	if (r_svalid)
		pre_data = cached_iword;
	else if (state == DC_READS || (OPT_WRAP && state == DC_READC))
		pre_data = axi_rdata;
	else
		pre_data = cached_rword;

	always @(*)
	if (SWAP_WSTRB)
	begin
		shifted_data = pre_data << (8*req_lsb);

		casez(req_op)
		2'b10: shifted_data[31:0] = { 16'h0, shifted_data[DW-1:DW-16] };
		2'b11: shifted_data[31:0] = { 24'h0, shifted_data[DW-1:DW- 8] };
		default: shifted_data[31:0] = shifted_data[DW-1:DW-32];
		endcase
	end else
		shifted_data = pre_data >> (8*req_lsb);

	// o_data
	always @(posedge S_AXI_ACLK)
	begin
		o_data <= shifted_data[31:0];
		if (OPT_SIGN_EXTEND)
		begin
			// verilator coverage_off
			// Unused, would violate ZipCPU ISA
			casez(req_op)
			2'b10: o_data[31:16] <= {(16){shifted_data[15]}};
			2'b11: o_data[31: 8] <= {(24){shifted_data[ 7]}};
			default: begin end
			endcase
			// verilator coverage_on
		end else begin
			casez(req_op)
			2'b10: o_data[31:16] <= 0;
			2'b11: o_data[31: 8] <= 0;
			default: begin end
			endcase
		end

		if (locked_write_in_progress)
		begin
			o_data <= 0;
			o_data[AW-1:0] <= restart_pc;
		end
	end
	// }}}

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_cpu_reset || flushing)
		o_valid <= 1'b0;
	else if (state == DC_READS)
	begin
		o_valid <= M_AXI_RVALID && !M_AXI_RRESP[1];
		if (OPT_LOCK && locked_read_in_progress && M_AXI_RRESP != EXOKAY)
			o_valid <= 0;
	end else if (locked_write_in_progress && M_AXI_BVALID
						&& M_AXI_BRESP == OKAY)
		o_valid <= 1'b1;
	else if (OPT_WRAP && r_rd_pending && state == DC_READC)
		o_valid <= M_AXI_RVALID  && !M_AXI_RRESP[1];
	else
		o_valid <= r_svalid || r_dvalid;
	// }}}

	// Make Verilator happy
	// {{{
	// verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXI_BID, M_AXI_RID, r_addr, M_AXI_RRESP[0],
				M_AXI_BRESP[0], i_lock, shifted_data,
				w_pipe_stalled, axi_tag, axi_line,
				rev_addr[C_AXI_ADDR_WIDTH-1:AXILSB] };
	// Verilator lint_on UNUSED
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
	// Declarations
	// {{{
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
	wire			faxi_rd_checkid;
	wire			faxi_rd_ckvalid;
	wire	[8:0]		faxi_rd_cklen;
	wire	[AW-1:0]	faxi_rd_ckaddr;
	reg	[AW-1:0]	faxi_rd_lastaddr;
	wire	[7:0]		faxi_rd_ckincr;
	wire	[1:0]		faxi_rd_ckburst;
	wire	[2:0]		faxi_rd_cksize;
	wire	[7:0]		faxi_rd_ckarlen;
	wire			faxi_rd_cklockd;
	//
	wire	[F_LGDEPTH-1:0]	faxi_rdid_nbursts;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_outstanding;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_ckign_nbursts;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_ckign_outstanding;

	// Verilator lint_off UNDRIVEN
	// Verilator lint_off UNUSED
	wire	[1:0]		faxi_ex_state;
	wire			faxi_ex_checklock;
	wire	[F_LGDEPTH-1:0]	faxi_rdid_bursts_to_lock;
	wire	[F_LGDEPTH-1:0]	faxi_wrid_bursts_to_exwrite;
	wire			faxi_active_lock;
	wire	[AW-1:0]	faxi_exreq_addr;
	wire	[7:0]		faxi_exlock_len,   faxi_exreq_len;
	wire	[1:0]		faxi_exlock_burst, faxi_exreq_burst;
	wire	[2:0]		faxi_exreq_size;
	reg	[AW-1:0]	faxi_exlock_addr;
	reg	[2:0]		faxi_exlock_size;
	wire			faxi_exreq_return;
	// Verilator lint_on  UNUSED
	// Verilator lint_on  UNDRIVEN

	wire	[LGPIPE:0]	cpu_outstanding;
	wire			cpu_pc;
	wire			cpu_gie;
	wire			cpu_read_cycle, cpu_lockd_write_cycle;
	wire	[4:0]		cpu_last_reg;
	wire	[4:0]		cpu_addr_reg;
	reg			f_done;
	reg			f_was_locked_write;
	// Verilator lint_off UNDRIVEN
	(* anyseq *) reg [4:0]	f_areg;
	// Verilator lint_on  UNDRIVEN
	wire	[1:0]		req_size;

	assign	req_size = req_data[AXILSB +: 2];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxi_master #(
		// {{{
		.C_AXI_ID_WIDTH(IW),
		.C_AXI_ADDR_WIDTH(AW),
		.C_AXI_DATA_WIDTH(DW),
		.OPT_EXCLUSIVE(OPT_LOCK),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxi (
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		// AW*
		// {{{
		.i_axi_awvalid(M_AXI_AWVALID),
		.i_axi_awready(M_AXI_AWREADY),
		.i_axi_awid(M_AXI_AWID),
		.i_axi_awaddr(M_AXI_AWADDR),
		.i_axi_awlen(M_AXI_AWLEN),
		.i_axi_awsize(M_AXI_AWSIZE),
		.i_axi_awburst(M_AXI_AWBURST),
		.i_axi_awlock(M_AXI_AWLOCK),
		.i_axi_awcache(M_AXI_AWCACHE),
		.i_axi_awprot(M_AXI_AWPROT),
		.i_axi_awqos(M_AXI_AWQOS),
		// }}}
		// W*
		// {{{
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata(M_AXI_WDATA),
		.i_axi_wstrb(M_AXI_WSTRB),
		.i_axi_wlast(M_AXI_WLAST),
		// }}}
		// B*
		// {{{
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid(M_AXI_RID),
		.i_axi_bresp(M_AXI_BRESP),
		// }}}
		// AR*
		// {{{
		.i_axi_arvalid(	M_AXI_ARVALID),
		.i_axi_arready(	M_AXI_ARREADY),
		.i_axi_arid(	M_AXI_ARID),
		.i_axi_araddr(	M_AXI_ARADDR),
		.i_axi_arlen(	M_AXI_ARLEN),
		.i_axi_arsize(	M_AXI_ARSIZE),
		.i_axi_arburst(	M_AXI_ARBURST),
		.i_axi_arlock(	M_AXI_ARLOCK),
		.i_axi_arcache(	M_AXI_ARCACHE),
		.i_axi_arprot(	M_AXI_ARPROT),
		.i_axi_arqos(	M_AXI_ARQOS),
		// }}}
		// R*
		// {{{
		.i_axi_rvalid(	M_AXI_RVALID),
		.i_axi_rready(	M_AXI_RREADY),
		.i_axi_rid(	M_AXI_RID),
		.i_axi_rdata(	M_AXI_RDATA),
		.i_axi_rlast(	M_AXI_RLAST),
		.i_axi_rresp(	M_AXI_RRESP),
		// }}}
		// Induction
		// {{{
		.f_axi_awr_nbursts(faxi_awr_nbursts),
		.f_axi_wr_pending(faxi_wr_pending),
		.f_axi_rd_nbursts(faxi_rd_nbursts),
		.f_axi_rd_outstanding(faxi_rd_outstanding),
		// Write checking
		// {{{
		.f_axi_wr_checkid(	faxi_wr_checkid),
		.f_axi_wr_ckvalid(	faxi_wr_ckvalid),
		.f_axi_wrid_nbursts(	faxi_wrid_nbursts),
		.f_axi_wr_addr(		faxi_wr_addr),
		.f_axi_wr_incr(		faxi_wr_incr),
		.f_axi_wr_burst(	faxi_wr_burst),
		.f_axi_wr_size(		faxi_wr_size),
		.f_axi_wr_len(		faxi_wr_len),
		.f_axi_wr_lockd(	faxi_wr_lockd),
		// }}}
		// Read checking
		// {{{
		.f_axi_rd_checkid(	faxi_rd_checkid),
		.f_axi_rd_ckvalid(	faxi_rd_ckvalid),
		.f_axi_rd_cklen(	faxi_rd_cklen),
		.f_axi_rd_ckaddr(	faxi_rd_ckaddr),
		.f_axi_rd_ckincr(	faxi_rd_ckincr),
		.f_axi_rd_ckburst(	faxi_rd_ckburst),
		.f_axi_rd_cksize(	faxi_rd_cksize),
		.f_axi_rd_ckarlen(	faxi_rd_ckarlen),
		.f_axi_rd_cklockd(	faxi_rd_cklockd),
		//
		.f_axi_rdid_nbursts(		faxi_rdid_nbursts),
		.f_axi_rdid_outstanding(	faxi_rdid_outstanding),
		.f_axi_rdid_ckign_nbursts(	faxi_rdid_ckign_nbursts),
		.f_axi_rdid_ckign_outstanding(	faxi_rdid_ckign_outstanding),
		// }}}
		// Exclusive access checking
		// {{{
		.f_axi_ex_state(faxi_ex_state),
		.f_axi_ex_checklock(faxi_ex_checklock),
		.f_axi_rdid_bursts_to_lock(faxi_rdid_bursts_to_lock),
		.f_axi_wrid_bursts_to_exwrite(faxi_wrid_bursts_to_exwrite),
		.i_active_lock( faxi_active_lock),
		.i_exlock_addr( faxi_exlock_addr),
		.i_exlock_len(  faxi_exlock_len),
		.i_exlock_burst(faxi_exlock_burst),
		.i_exlock_size( faxi_exlock_size),
		.f_axi_exreq_addr(faxi_exreq_addr),
		.f_axi_exreq_len(faxi_exreq_len),
		.f_axi_exreq_burst(faxi_exreq_burst),
		.f_axi_exreq_size(faxi_exreq_size),
		.f_axi_exreq_return(faxi_exreq_return)
		// }}}
		// }}}
		// }}}
	);

	// ID checking
	// {{{
	always @(*)
	begin
		assume(faxi_rd_checkid == AXI_ID);
		assert(faxi_rdid_nbursts == faxi_rd_nbursts);
		assert(faxi_rdid_outstanding == faxi_rd_outstanding);

		assume(faxi_wr_checkid == AXI_ID);
		assert(faxi_wrid_nbursts == faxi_awr_nbursts);
	end
	// }}}

	// Never both reads and writes outstanding
	// {{{
	always @(*)
	if (faxi_rd_outstanding > 0)
	begin
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(faxi_awr_nbursts == 0);
		assert(o_busy);
		if (r_rd_pending)
		begin
			assert(o_rdbusy);
		end
		if (flushing)
			assert(!o_rdbusy);
		assert(!locked_write_in_progress);
	end else if (faxi_awr_nbursts > 0)
	begin
		assert(!locked_read_in_progress);
		assert(o_busy);
		if (locked_write_in_progress)
		begin
			assert(o_rdbusy);
		end else
			assert(!o_rdbusy);	// || OPT_LOCK && LOCKD WRITE
		assert(!M_AXI_ARVALID);
		// assert(f_wr_pending == (M_AXI_WVALID ? 1:0));
	end
	// }}}

	// Read count checking
	// {{{
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (state == DC_READC)
		begin
			assert(faxi_rd_nbursts == (M_AXI_ARVALID ? 0:1));
		end else if (state == DC_READS)
		begin
			assert(faxi_rd_nbursts == faxi_rd_outstanding);
			if (!OPT_PIPE)
				assert(faxi_rd_nbursts == (M_AXI_ARVALID ? 0:1));
		end else
			assert(faxi_rd_nbursts == 0);
	end
	// }}}

	// Write packet checking
	// {{{
	always @(*)
	if (faxi_wr_ckvalid)
	begin
		assert(faxi_wr_burst == M_AXI_AWBURST);
		assert(faxi_wr_len == 8'h00);
		assert(faxi_wr_lockd == locked_write_in_progress);
		//
		if (SWAP_WSTRB)
			assert(faxi_wr_size == 3'd2);
		else casez(f_op[AXILSB+1:AXILSB])
		2'b0?: assert(faxi_wr_size == 3'd2);
		2'b10: assert(faxi_wr_size == 3'd1);
		2'b11: assert(faxi_wr_size == 3'd0);
		endcase
	end
	// }}}

	// CPU matching -- write cycle
	// {{{
	always @(*)
	if (!cpu_read_cycle)
	begin
		if (OPT_WRAP && state == DC_READC)
		begin
			assert(!r_rd_pending);
			assert(faxi_rd_nbursts == (M_AXI_ARVALID ? 0:1));
			assert(faxi_awr_nbursts == 0);
		end else begin
			assert(flushing || (faxi_rd_nbursts == 0));
			// Verilator lint_off WIDTH
			assert(flushing || o_err
				|| (cpu_outstanding == faxi_awr_nbursts
					+ ((OPT_LOCK && f_was_locked_write
						&& !locked_write_in_progress) ? 1:0)
					+ (M_AXI_AWVALID ? 1:0)));
			// Verilator lint_on  WIDTH
		end
	end else // if (!flushing)
		assert(faxi_awr_nbursts == 0);
	// }}}

	// Read request checking
	// {{{
	always @(*)
	if (!S_AXI_ARESETN)
	begin end
	else if (state == DC_IDLE || state == DC_WRITE)
	begin
		assert(!M_AXI_ARVALID);
		assert(flushing || faxi_rd_outstanding == 0);
	end else if (M_AXI_ARVALID && !flushing)
	begin
		assert(faxi_rd_outstanding == 0);
		if (state == DC_READC)
		begin
			assert(M_AXI_ARBURST == (OPT_WRAP) ? WRAP : INCR);
			assert(!M_AXI_ARLOCK);
			assert(M_AXI_ARLEN == (1 << LS) - 1);
			if (!OPT_LOWPOWER || M_AXI_ARVALID)
			begin
				assert(M_AXI_ARADDR[AW-1:CS+AXILSB] == r_ctag);
				assert(axi_tag == r_ctag);
				assert(M_AXI_ARADDR[CS+AXILSB-1:LS+AXILSB] == r_cline);
				assert(axi_line == r_cline);
			end
			assert(M_AXI_ARADDR[AXILSB-1:0] == 0);
			if (!OPT_WRAP)
			begin
				assert(read_addr[LS-1:0] == 0);
			end
			assert((OPT_LOWPOWER && !M_AXI_ARVALID)
				|| M_AXI_ARADDR[AXILSB +: CS] == read_addr);
		end else begin
			assert(state == DC_READS);
			assert(M_AXI_ARBURST == INCR);
			assert(M_AXI_ARLEN   == 0);
			assert(M_AXI_ARLOCK == locked_read_in_progress);
			if (locked_read_in_progress || OPT_WRAP)
				assert((OPT_LOWPOWER && !M_AXI_ARVALID)
					||M_AXI_ARADDR[AXILSB +: CS] == read_addr);
		end
	end
	// }}}

	// Read packet checking
	// {{{
	always @(*)
	begin
		faxi_rd_lastaddr = faxi_rd_ckaddr;
		// Verilator lint_off WIDTH
		faxi_rd_lastaddr = faxi_rd_ckaddr
				+ ((faxi_rd_cklen - 1) << faxi_rd_cksize);
		// Verilator lint_on  WIDTH
	end

	always @(*)
	if (faxi_rd_ckvalid)
	begin
		// .f_axi_rd_cklen(	faxi_rd_cklen),
		// .f_axi_rd_ckaddr(	faxi_rd_ckaddr),
		if (state == DC_READC)
		begin
			// Read to cache
			assert(faxi_rd_ckarlen == (1 << LS) - 1);
			assert(faxi_rd_nbursts == 1);
			assert(faxi_rd_cksize  == AXILSB[2:0]);
			if (!OPT_WRAP)
			begin
				assert(faxi_rd_lastaddr[AXILSB-1:0] == 0);
				assert(&faxi_rd_lastaddr[AXILSB +: LS]);
			end
			assert(last_ack == (axi_arvalid ? 0:1));
			assert(r_ctag == faxi_rd_ckaddr[AW-1:CS+AXILSB]);
			assert(!faxi_rd_cklockd);
			assert(faxi_rd_ckburst == (OPT_WRAP) ? WRAP : INCR);
			// Need to verify wcache_addr
		end else begin
			// Single, uncachable reads
			// assert(!w_v || wcache_tag != r_ctag);
			assert(faxi_rd_ckarlen == 0);
			assert(locked_read_in_progress == faxi_rd_cklockd);
			assert(faxi_rd_ckburst == INCR);
			if (SWAP_WSTRB)
			begin
				assert(faxi_rd_cksize == 3'b010);
			end else case(req_size)
			2'b10: assert(faxi_rd_cksize  == 3'd1);
			2'b11: assert(faxi_rd_cksize  == 3'd0);
			default: assert(faxi_rd_cksize  == 3'd2);
			endcase
		end
	end
	// }}}

	always @(*)
	if (S_AXI_ARESETN && (state != DC_WRITE || !OPT_LOCK))
		assert(!locked_write_in_progress);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CPU/memory interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fmem #(
		// {{{
		.OPT_LOCK(OPT_LOCK),
		.OPT_AXI_LOCK(OPT_LOCK),
		.F_LGDEPTH(LGPIPE+1),
		.OPT_MAXDEPTH((OPT_PIPE) ? ((1<<LGPIPE)-1) : 1)
		// }}}
	) fmemp (
		// {{{
		.i_clk(S_AXI_ACLK), .i_sys_reset(!S_AXI_ARESETN),
			.i_cpu_reset(i_cpu_reset),
		.i_stb(i_pipe_stb),
			.i_pipe_stalled(o_pipe_stalled),
		.i_clear_cache(i_clear),
			.i_lock(i_lock),
		.i_op(i_op),
			.i_addr(i_addr),
			.i_data(i_data),
			.i_oreg(i_oreg),
			.i_areg(f_areg),
		//
			.i_busy(o_busy),
			.i_rdbusy(o_rdbusy),
		.i_valid(o_valid),
			.i_done(f_done),
			.i_err(o_err),
			.i_wreg(o_wreg),
			.i_result(o_data),
		//
		.f_outstanding(cpu_outstanding),
		.f_pc(cpu_pc),
		.f_gie(cpu_gie),
		.f_read_cycle(cpu_read_cycle),
		.f_axi_write_cycle(cpu_lockd_write_cycle),
		.f_last_reg(cpu_last_reg),
		.f_addr_reg(cpu_addr_reg)
		// }}}
	);

	always @(*)
	if (o_rdbusy)
		assert(cpu_outstanding <= 1);

	always @(*)
	if (o_rdbusy && (cpu_outstanding == 1 + ((f_done || o_err) ? 1:0))
			&& (r_rd_pending))
		assert(o_pipe_stalled);

	initial	f_was_locked_write = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !OPT_LOCK)
		f_was_locked_write <= 1'b0;
	else
		f_was_locked_write <= locked_write_in_progress;

	always @(*)
	begin
		f_done = 0;
		if (M_AXI_BVALID && !flushing && !M_AXI_BRESP[1]
				&& (!OPT_LOCK || !locked_write_in_progress))
			f_done = 1'b1;
		if (OPT_LOCK && f_was_locked_write && !locked_write_in_progress)
			f_done = 1'b1;
		if (cpu_read_cycle && (o_valid || o_err))
			f_done = 1'b1;

		if (flushing)
			assert(!o_rdbusy);
	end

	always @(*)
	if (!OPT_LOCK)
		assert(!cpu_lockd_write_cycle);

	always @(*)
	if (o_rdbusy)
		assert(cpu_gie == o_wreg[4]);

	always @(*)
	if (o_rdbusy && !locked_write_in_progress)
	begin
		assert(cpu_gie == o_wreg[4]);
		if (locked_write_in_progress)
		begin
			assert(o_wreg[3:0] == 4'hf);
		end else
			assert(cpu_last_reg == o_wreg);
	end

	always @(*)
	if (S_AXI_ARESETN
		&& (locked_write_in_progress || locked_read_in_progress))
	begin
		assert(OPT_LOCK);
		assert(o_pipe_stalled);
	end

	always @(*)
	if (S_AXI_ARESETN && OPT_PIPE
		&& (locked_write_in_progress || locked_read_in_progress))
	begin
		assert(w_pipe_stalled);
	end

	always @(*)
	if (OPT_PIPE && state == DC_READC)
		assert(w_pipe_stalled);

	always @(*)
	if (OPT_PIPE && flushing)
		assert(w_pipe_stalled);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && OPT_PIPE && $past(S_AXI_ARESETN))
	begin
		if ($past(!i_cpu_reset && i_pipe_stb && i_read && !misaligned))
			assert(w_pipe_stalled);
		else if (M_AXI_ARVALID)
			assert(o_pipe_stalled);
		else if ((faxi_rd_nbursts == 0) && (faxi_awr_nbursts == 0)
				&& !r_rd_pending && !r_svalid && !r_dvalid
				&& (!M_AXI_AWVALID && !M_AXI_WVALID))
		begin
			if ($past(state) != DC_READC)
				assert(!w_pipe_stalled);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// State checking
	// {{{
	always @(*)
	if (S_AXI_ARESETN)
	case(state)
	DC_IDLE: begin
		// {{{
		assert(!flushing);
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(!M_AXI_ARVALID);
		assert(faxi_rd_nbursts  == 0);
		assert(faxi_awr_nbursts == 0);
		assert(noutstanding == 0);
		assert(cpu_outstanding <= 1);
		if (r_rd_pending)
			assert(o_rdbusy);
		if (cpu_outstanding > 0)
		begin
			if (r_svalid || r_dvalid || o_valid || o_err)
				assert(!r_rd_pending);
			if (!r_rd_pending)
				assert(f_done || o_err || r_svalid || r_dvalid);
			// else
			//	assert(r_svalid || r_dvalid || o_valid || o_err);
			//
			// Older logic
			// if (r_svalid || r_dvalid || o_valid || o_err)
			//	assert(!r_rd_pending);
			// if (!r_svalid && !r_dvalid && !o_err && !o_valid && !f_done)
			//	assert(cpu_outstanding == (r_rd_pending ? 1:0));
		end else
			assert(!r_rd_pending);
		/*
		if (cpu_read_cycle && !o_err && o_busy)
		begin
			assert(o_rdbusy || o_valid);
			assert(o_valid || r_rd_pending);
		// assert(!r_cache_miss);
		end
		*/
		end
		// }}}
	DC_WRITE: begin
		// {{{
		assert(!M_AXI_ARVALID);
		assert(noutstanding == faxi_awr_nbursts);
		if (!OPT_PIPE)
		begin
			assert(faxi_awr_nbursts == (M_AXI_AWVALID ? 0:1));
			assert(noutstanding == (M_AXI_AWVALID ? 0:1));
		end else begin
			assert(faxi_awr_nbursts == noutstanding);
		end
		assert(o_rdbusy == locked_write_in_progress);
		assert(!cpu_read_cycle);
		assert(o_busy);
		assert(!r_rd_pending);
		assert(!r_cache_miss);
		assert(faxi_wr_pending
			== ((M_AXI_WVALID && !M_AXI_AWVALID) ? 1:0));
		if (flushing)
			assert(o_err || cpu_outstanding == 0);
		end
		// }}}
	DC_READC: begin
		// {{{
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		if (M_AXI_ARVALID)
			assert(M_AXI_ARLEN == (1 << LS) - 1);
		// assert(!M_AXI_ARVALID);
		// assert(faxi_rd_nbursts == 0);
		assert(noutstanding == (M_AXI_ARVALID ? 0:1));
		assert(faxi_awr_nbursts == 0);
		assert(flushing || (OPT_WRAP || o_rdbusy));
		assert(o_busy);
		assert(faxi_rd_nbursts == (M_AXI_ARVALID ? 0:1));
		assert(faxi_rd_outstanding <= (1<<LS));
		assert(OPT_WRAP || r_cache_miss || flushing);
		assert(OPT_WRAP || !r_dvalid);
		assert(!r_svalid);
		assert(good_cache_read || flushing);
		assert(wcache_addr[CS-1:LS] == r_cline);
		assert(read_addr[CS-1:LS] == r_cline);
		if (!OPT_WRAP)
			assert(r_rd_pending || flushing);
		if (flushing)
		begin
			assert(!r_rd_pending);
			assert(cpu_outstanding == (o_err ? 1:0));
		end else
			assert(OPT_WRAP || r_rd_pending);
		end
		// }}}
	DC_READS: begin
		// {{{
		assert(!M_AXI_AWVALID);
		assert(!M_AXI_WVALID);
		assert(noutstanding == (M_AXI_ARVALID ? 0:1));
		assert(faxi_awr_nbursts == 0);
		// assert(!M_AXI_ARVALID);
		assert(faxi_rd_nbursts == faxi_rd_outstanding);
		assert(faxi_rd_nbursts == noutstanding);
		assert(flushing || o_rdbusy);
		assert(o_busy);
		assert(!r_rd_pending);
		assert(!r_cache_miss);
		if (flushing)
		begin
			assert(!o_rdbusy);
			assert(cpu_outstanding == (o_err ? 1:0));
		end end
		// }}}
	endcase
	// }}}

	/*

	// Issues with the following:
	//   1. Can't handle errors
	//   2. Can't handle the wrong cache read ...
	//
	*/
	reg	[3:0]	f_read_state;
	(* anyconst *) reg f_never_err;

	always @(*)
	if (f_never_err)
	begin
		assume(!M_AXI_RVALID || !M_AXI_RRESP[1]);
		// assume(!M_AXI_BVALID || !M_AXI_BRESP[1]);
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN) // || !f_never_err)
		f_read_state <= 0;
	else if (i_cpu_reset)
		f_read_state <= 0;
	else case(f_read_state)
	4'h0: begin // Idle.  What operation do we start?
		// {{{
		assert(!r_rd_pending);
		assert(!set_vflag);
		if (!flushing)
		begin
			assert(state == DC_IDLE || state == DC_WRITE);
			assert(faxi_rd_nbursts == 0);
			if (i_pipe_stb && i_read && !misaligned)
			begin
				if (cachable_read_request)
					f_read_state <= 4'h1;
				else
					f_read_state <= 4'h6;
			end
		end end
		// }}}
	4'h1: begin // Cachable read request, checking if its in the cache
		// {{{
		assert(r_svalid ^ r_rd_pending);
		assert(state == DC_IDLE);
		assert(r_check);
		assert(!set_vflag);
		assert(o_rdbusy);
		assert(o_busy);
		if (r_svalid)
			f_read_state <= 4'h7;
		else
			f_read_state <= 4'h2;
		end
		// }}}
	4'h2: begin // Cachable read, checking in the cache step #2
		// {{{
		assert(!flushing);
		assert(r_cachable);
		assert(r_rd_pending ^ r_dvalid);
		assert(o_rdbusy);
		assert(!r_check);
		assert(state == DC_IDLE);
		assert(!set_vflag);
		assert(o_busy);
		if (r_dvalid)
			f_read_state <= 4'h7;
		else begin
			assert(!r_rv || r_rtag != r_ctag);	// !!!
			f_read_state <= 4'h3;
		end end
		// }}}
	4'h3: begin // Cachable read, now starting the read operation
		// {{{
		assert(faxi_rd_nbursts == (M_AXI_ARVALID ? 0:1));
		assert(!flushing);
		assert(!r_svalid);
		assert(!r_dvalid);
		assert(!r_check);
		assert(!r_rv || r_rtag != r_ctag);
		assert(r_rd_pending);
		assert(r_cachable);
		assert(state == DC_READC);
		assert(good_cache_read);
		assert(!set_vflag);
		assert(o_busy);
		if (OPT_WRAP && M_AXI_RVALID)
			f_read_state <= M_AXI_RLAST ? 4'h9 : 4'h8;
		if (!OPT_WRAP && M_AXI_RVALID && M_AXI_RLAST)
			f_read_state <= 4'h4;
		if (M_AXI_RVALID && M_AXI_RRESP[1])
			f_read_state <= 4'h0;
		end
		// }}}
	4'h4: begin // Completed the cachable read operation into the cache
		// {{{
		assert(!OPT_WRAP);
		assert(!flushing);
		assert(!r_svalid);
		assert(r_cachable);
		assert(r_rd_pending);
		assert(r_rtag == r_ctag);
		assert(state == DC_IDLE);
		assert(set_vflag);
		assert(o_busy);
		f_read_state <= 4'h5;

		// r_dvalid <= !r_svalid && !r_dvalid
		//		&& (w_tag == r_ctag) && w_v

		end
		// }}}
	4'h5: begin // Final step of the cachable read
		// {{{
		assert(!OPT_WRAP);
		assert(!flushing);
		assert(r_cachable);
		assert(r_rd_pending != r_dvalid);
		// assert(w_v && w_tag == r_ctag);
		// assert(r_dvalid == $stable(f_read_state));
		assert(state == DC_IDLE);
		assert(!set_vflag);
		if (r_dvalid)
			f_read_state <= 4'h7;
		end
		// }}}
	4'h6: begin // Read single state
		// {{{
		assert(!flushing);
		assert(faxi_rd_nbursts == (M_AXI_ARVALID ? 0:1));
		assert(faxi_rd_outstanding == (M_AXI_ARVALID ? 0:1));
		assert(!flushing);
		assert(state == DC_READS);
		if (M_AXI_RVALID)
			f_read_state <= 4'h7;
		end
		// }}}
	4'h7: begin
		// {{{
		assert(faxi_rd_outstanding == 0);
		// assert(r_rd_pending);
		assert(o_valid || o_err);
		f_read_state <= 4'h000;
		if (!flushing && i_pipe_stb && !i_op[0] && !misaligned)
		begin
			if (address_is_cachable && (!OPT_LOCK || !i_lock))
				f_read_state <= 4'h1;
			else
				f_read_state <= 4'h6;
		end end
		// }}}
	4'h8: begin // WRAP Read
		// {{{
		assert(OPT_WRAP);
		assert(!flushing);
		assert(faxi_rd_nbursts == 1);
		assert(!r_rd_pending);
		assert(!set_vflag);
		assert(o_busy);
		if (M_AXI_RVALID && M_AXI_RLAST)
			f_read_state <= 4'h9;
		end
		// }}}
	4'h9: begin // Concluding WRAP read
		// {{{
		assert(OPT_WRAP);
		assert(faxi_rd_nbursts == 0);
		assert(!r_rd_pending);
		assert(!flushing);
		assert(state == DC_IDLE);
		assert(o_busy);
		if (!$past(i_clear))
			assert(set_vflag || !good_cache_read);
		f_read_state <= 4'h0;
		if (!flushing && i_pipe_stb && i_read && !misaligned)
		begin
			if (address_is_cachable && (!OPT_LOCK || !i_lock))
				f_read_state <= 4'h1;
			else
				f_read_state <= 4'h6;
		end end
		// }}}
	default: assert(0);
	endcase

	always @(*)
	if (S_AXI_ARESETN && faxi_rd_outstanding > 0 && !flushing)
		assert(f_read_state != 0);

	always @(*)
	if (S_AXI_ARESETN && (state == DC_READS || state == DC_READC))
	begin
		assert(flushing || (f_read_state != 0));
	end

	// DC_READC checks
	// {{{
	always @(posedge S_AXI_ACLK)
	if (state == DC_READC)
	begin
		assert(read_addr[CS-1:LS] == r_cline);
		if (M_AXI_ARVALID)
		begin
			assert(axi_araddr[AW-1:AXILSB+LS] == { r_ctag, r_cline });
			if (!OPT_WRAP)
			begin
				assert(axi_araddr[AXILSB+LS-1:0] == 0);
			end
			assert(axi_araddr[AXILSB +: CS] == read_addr[CS-1:0]);
			// read_addr <= { i_addr[LGCACHELEN-1:AXILSB+LS], {(LS){1'b0}} };
			if (!OPT_WRAP)
				assert(read_addr[LS-1:0] == 0);
		end else if (faxi_rd_ckvalid)
		begin
			assert(faxi_rd_ckaddr[AW-1:AXILSB+LS] == { r_ctag, r_cline });
			assert(faxi_rd_ckaddr[AXILSB-1:0] == 0);
			assert(faxi_rd_ckaddr[AXILSB +: CS] == read_addr[CS-1:0]);
		end
	end
	// }}}

	// last_tag_valid checking
	// {{{
	always @(*)
	if (last_tag_valid)
	begin
		assert(cache_tag[last_tag_line] == last_tag);
		assert(cache_valid[last_tag_line]);
	end
	// }}}

	always @(*)
	if (!cpu_read_cycle && S_AXI_ARESETN && !flushing && !o_err)
	case(state)
	DC_WRITE: begin
		if (locked_write_in_progress)
		begin
			assert(cpu_outstanding == faxi_awr_nbursts
				+ ((o_valid || f_done) ? 1:0)
				+ (M_AXI_AWVALID ? 1:0));
		end else begin
			assert(cpu_outstanding == faxi_awr_nbursts
				+ (o_valid ? 1:0)
				+ (M_AXI_AWVALID ? 1:0));
		end end
	default:
		assert(cpu_outstanding == ((o_valid || o_err || f_done) ? 1:0));
	endcase

	always @(*)
	if (S_AXI_ARESETN && !flushing && (!f_done && !o_valid && !o_err))
		assert(cpu_lockd_write_cycle == locked_write_in_progress);

	always @(*)
	if (S_AXI_ARESETN && locked_write_in_progress)
	begin
		assert(state == DC_WRITE);
		assert(faxi_awr_nbursts + (M_AXI_AWVALID ? 1:0) == 1);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Lowpower checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_LOWPOWER)
	begin : F_LOWPOWER

		always @(*)
		if (S_AXI_ARESETN && !M_AXI_AWVALID)
		begin
			assert(axi_awaddr == 0);
		end

		always @(*)
		if (S_AXI_ARESETN && !M_AXI_WVALID)
		begin
			assert(axi_wdata == 0);
			assert(axi_wstrb == 0);
		end

		always @(*)
		if (S_AXI_ARESETN && !M_AXI_ARVALID)
		begin
			assert(axi_araddr == 0);
			assert(axi_arlen == 0);
			assert(axi_arsize == 3'd2);
		end

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg	[AW-1:0]	f_const_addr;
	(* anyconst *)	reg			f_const_err;
			reg	[DW-1:0]	f_mem_data;
			wire	[DW-1:0]	f_word_swapped_mem_data;
	wire	[TW-1:0]	f_const_tag;
	wire	[CS-LS-1:0]	f_const_line;
	wire	[LS-1:0]	f_const_caddr;
	reg			f_this_return, f_this_line;
	reg	[AW-1:0]	f_request_addr;
	reg			f_simple_return;
	reg	[31:0]		f_return;
	reg	[DW-1:0]	f_wide_return;
	reg	[AXILSB+1:0]	f_op;
	wire			f_special_valid;
	wire	[DW-1:0]	f_special_cached_data;
	wire	[TW-1:0]	f_special_tag;
	reg	[CS-1:0]	f_wcache_addr_diff;


	always @(*)
		assume(f_const_addr[AXILSB-1:0] == 0);

	assign	{ f_const_tag, f_const_line, f_const_caddr }
				= f_const_addr[AW-1:AXILSB];

	// f_this_return
	// {{{
	always @(*)
	begin
		f_this_return = r_rd_pending && M_AXI_RVALID;
		if (OPT_WRAP)
			f_this_return = (state == DC_READC && M_AXI_RVALID);
		if (read_addr[CS-1:LS] != f_const_line)
			f_this_return = 0;
		if ({ r_ctag, r_cline } != { f_const_tag, f_const_line })
			f_this_return = 0;
		if (faxi_rd_ckvalid)
		begin
			if (faxi_rd_ckaddr[AW-1:AXILSB] != f_const_addr[AW-1:AXILSB])
				f_this_return = 0;
		end else begin
			if (read_addr[CS-1:0] != f_const_addr[AXILSB +: CS])
				f_this_return = 0;
		end
		if (state != DC_READC)
			f_this_return = 0;
	end
	// }}}

	// f_simple_return, f_request_addr
	// {{{
	initial	f_simple_return = 0;
	always @(posedge S_AXI_ACLK)
	begin
		if (i_pipe_stb)
		begin
			f_request_addr <= rev_addr;
			f_simple_return = (f_const_addr[AW-1:AXILSB]
							== i_addr[AW-1:AXILSB]);
			if (misaligned || i_op[0])
				f_simple_return <= 1'b0;
			if (address_is_cachable && (!OPT_LOCK || !i_lock))
				f_simple_return <= 1'b0;
		end else if (M_AXI_RVALID)
			f_simple_return <= 1'b0;

		if (state == DC_READC)
		begin
			assert(read_addr[CS-1:LS] == f_request_addr[AXILSB +LS
							+: (CS-LS)]);
			if (M_AXI_ARVALID)
			begin
				if (!OPT_WRAP)
				begin
					assert({ f_request_addr[AW-1:AXILSB+LS], {(LS){1'b0}}, {(AXILSB){1'b0}} } == M_AXI_ARADDR);
					assert(read_addr[LS-1:0] == 0);
					assert(axi_araddr == { f_request_addr[AW-1:AXILSB+LS],
							{(LS+AXILSB){1'b0}} });
				end else begin
					assert({ f_request_addr[AW-1:AXILSB], {(AXILSB){1'b0}} } == M_AXI_ARADDR);
					assert(read_addr[LS-1:0] == M_AXI_ARADDR[AXILSB+LS-1:AXILSB]);
				end
			end else if (faxi_rd_ckvalid)
				assert(faxi_rd_ckaddr[AW-1:AXILSB+LS]
					== f_request_addr[AW-1:AXILSB+LS]);
		end else if (state == DC_READS)
			assert(read_addr[CS-1:LS] == f_request_addr[AXILSB+LS +: (CS-LS)]);

		if (i_cpu_reset)
			f_simple_return <= 0;
	end
	// }}}

	// f_this_line
	// {{{
	always @(*)
		f_this_line = (f_request_addr[AW-1:AXILSB+LS] == f_const_addr[AW-1:AXILSB+LS]);
	// }}}

	// f_op
	// {{{
	always @(posedge S_AXI_ACLK)
	if (i_pipe_stb)
		f_op <= { i_op[2:1], rev_addr[AXILSB-1:0] };

	always @(*)
	if (cpu_outstanding > 0)
		assert(f_op == req_data);

	always @(*)
	if (cpu_outstanding > 0 && !o_err)
	begin
		assert(!checklsb(f_op[AXILSB+1:AXILSB], f_op[1:0]));
		assert(f_op[AXILSB-1:0] == f_request_addr[AXILSB-1:0]);
		if (!OPT_PIPE)
			assert(f_request_addr[AW-1:AXILSB] == r_addr);
	end
	// }}}

	// Check f_simple_return and f_request_addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (flushing)
	begin
		assert(!f_simple_return);
	end else if (state != DC_READS)
	begin
		assert(!f_simple_return);
	end else if (f_simple_return)
	begin
		assert(f_request_addr[AW-1:AXILSB]== f_const_addr[AW-1:AXILSB]);
	end else
		assert(f_request_addr[AW-1:AXILSB]!= f_const_addr[AW-1:AXILSB]);
	// }}}

	// Update f_mem_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (M_AXI_AWVALID && M_AXI_WVALID
		&& M_AXI_AWADDR[AW-1:AXILSB] == f_const_addr[AW-1:AXILSB])
	begin
		for(ik=0; ik<DW/8; ik=ik+1)
		if (M_AXI_WSTRB[ik])
			f_mem_data[ik*8 +: 8] <= M_AXI_WDATA[ik*8 +: 8];
	end

	generate if (!SWAP_WSTRB)
	begin
		assign	f_word_swapped_mem_data = f_mem_data;

	end else for(gk=0; gk<C_AXI_DATA_WIDTH/32; gk=gk+1)
	begin
		assign	f_word_swapped_mem_data[32*gk +: 32]
				=f_mem_data[C_AXI_DATA_WIDTH - (gk+1)*32 +: 32];
	end endgenerate
	// }}}

	// Property #1: Assume a known return
	// {{{
	always @(*)
	if (M_AXI_RVALID && (f_simple_return || f_this_return))
	begin
		assume(M_AXI_RRESP[1] == f_const_err);
		if (!f_const_err)
			assume(M_AXI_RDATA == f_mem_data);
	end else if (M_AXI_RVALID && f_this_line)
	begin
		if (!f_const_err)
			assume(!M_AXI_RRESP[1]);
	end

	always @(*)
	if (M_AXI_BVALID && (f_request_addr[AW-1:AXILSB] == f_const_addr[AW-1:AXILSB]))
		assume(M_AXI_BRESP[1] == f_const_err);
	// }}}

	// Check good_cache_read
	// {{{
	always @(*)
	if (state == DC_READC && f_this_line)
	begin
		if (!f_const_err)
		begin
			assert(good_cache_read);
		end else if (!OPT_WRAP && read_addr[LS-1:0] > f_const_addr[LS+AXILSB-1:AXILSB])
			assert(flushing);
	end
	// }}}

	// f_wide_return, f_return
	// {{{
	always @(*)
	if (SWAP_WSTRB)
	begin
		f_wide_return = f_word_swapped_mem_data << (8*f_op[AXILSB-1:0]);
		casez(f_op[AXILSB +: 2])
		2'b0?:	f_wide_return[31:0] = f_wide_return[DW-1:DW-32];
		2'b10:	f_wide_return[31:0] = { 16'h0, f_wide_return[DW-1:DW-16] };
		2'b11:	f_wide_return[31:0] = { 24'h0, f_wide_return[DW-1:DW- 8] };
		endcase
	end else
		f_wide_return = f_mem_data >> (8*f_op[AXILSB-1:0]);

	always @(*)
	begin
		casez(f_op[AXILSB +: 2])
		2'b0?:	f_return = f_wide_return[31:0];
		2'b10:	f_return = { 16'h0, f_wide_return[15:0] };
		2'b11:	f_return = { 24'h0, f_wide_return[ 7:0] };
		endcase

		if (OPT_SIGN_EXTEND)
		casez(f_op[AXILSB +: 2])
		2'b0?:	begin end
		2'b10:	f_return[31:16] = {(16){f_wide_return[15]}};
		2'b11:	f_return[31:24] = {(24){f_wide_return[ 7]}};
		endcase
	end
	// }}}

	// Property #2: Assert a known response
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && !OPT_PIPE
		&& (!OPT_LOCK || !f_was_locked_write)
		&& (f_request_addr[AW-1:AXILSB] == f_const_addr[AW-1:AXILSB]))
	begin
		if (o_valid)
		begin
			assert(!f_const_err);
			assert(f_return == o_data);
		end else if (o_err)
		begin
			if (!OPT_LOCK)
				assert(f_const_err || $past(misaligned));
			// else if OPT_LOCK
			//
			// We might also produce an error if the value isn't
			// lockable
		end
	end
	// }}}

	// Property #3: Assert valid cache
	// {{{
	assign	f_special_valid = cache_valid[f_const_line]
				&& (cache_tag[f_const_line] == f_const_tag);
	assign	f_special_tag = cache_tag[f_const_line];
	assign	f_special_cached_data = cache_mem[{ f_const_line, f_const_caddr }];

	always @(*)
	if (S_AXI_ARESETN // && (!OPT_PIPE || (!flushing && !o_err))
			&& f_special_valid)
	begin
		assert(f_special_cached_data == f_word_swapped_mem_data);// !!!
		assert(!f_const_err);
	end

	always @(*)
	if (!OPT_PIPE && last_tag_valid && last_tag_line == f_const_line && last_tag == f_const_tag)
		assert(!f_const_err);

	always @(*)
		f_wcache_addr_diff = wcache_addr - f_const_addr[LGCACHELEN-1:AXILSB];

	always @(*)
	if (S_AXI_ARESETN && !OPT_PIPE && !flushing && (state == DC_READC
			|| (state == DC_IDLE && !set_vflag && r_rd_pending
				&& r_ctag == f_const_tag
				&& (r_dvalid || r_svalid)))
		&& f_this_line
		&& !f_wcache_addr_diff[CS-1] && f_wcache_addr_diff != 0)
	begin
		// The cache read is in progress.  Verify any partial results
		if (f_const_err)
		begin
			assert(OPT_WRAP || (!good_cache_read && !r_rd_pending));
		end else if (!flushing)
			assert(OPT_WRAP || (f_special_cached_data == f_word_swapped_mem_data));
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Exclusive access
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	faxi_exlock_len = 0;
	assign	faxi_exlock_burst = INCR;

	always @(posedge S_AXI_ACLK)
	if (M_AXI_ARVALID && M_AXI_ARREADY && M_AXI_ARLOCK)
	begin
		faxi_exlock_addr <= M_AXI_ARADDR;
		faxi_exlock_size <= M_AXI_ARSIZE;
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg		cvr_idle;
	reg	[3:0]	cvr_cache_reads, cvr_cache_writes, cvr_cache_misses,
			cvr_simple_reads, cvr_simple_writes;

	// cvr_idle
	// {{{
	always @(*)
	begin
		cvr_idle = 1;
		if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
			cvr_idle = 0;
		if (M_AXI_RVALID || M_AXI_BVALID)
			cvr_idle = 0;
		if (faxi_awr_nbursts > 0)
			cvr_idle = 0;
		if (faxi_rd_nbursts > 0)
			cvr_idle = 0;
		if (o_busy || f_done)
			cvr_idle = 0;
		if (i_pipe_stb)
			cvr_idle = 0;
	end
	// }}}

	// cvr_simple_writes
	// {{{
	initial	cvr_simple_writes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_cpu_reset)
		cvr_simple_writes <= 0;
	else if (wcache_strb != 0 && w_v && wcache_tag == r_ctag)
		cvr_simple_writes <= 0;
	else if (M_AXI_BVALID && !(&cvr_simple_writes))
		cvr_simple_writes <= cvr_simple_writes + 1;

	always @(*)
	begin
		// cover(cvr_idle && cvr_simple_writes > 0);
		// cover(cvr_idle && cvr_simple_writes > 1);
		cover(cvr_idle && cvr_simple_writes > 4);
	end
	// }}}

	// cvr_simple_reads
	// {{{
	initial	cvr_simple_reads = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || o_err || i_cpu_reset)
		cvr_simple_reads <= 0;
	else if (i_pipe_stb && !i_op[0] && !misaligned && !address_is_cachable
			&& !(&cvr_simple_reads))
		cvr_simple_reads <= cvr_simple_reads + 1;

	always @(*)
	begin
		// cover(cvr_idle && cvr_simple_reads > 0);
		// cover(cvr_idle && cvr_simple_reads > 1);
		cover(cvr_idle && cvr_simple_reads > 4);
	end
	// }}}

	// cvr_cache_misses
	// {{{
	initial	cvr_cache_misses = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || state == DC_READS || i_cpu_reset)
		cvr_cache_misses <= 0;
	else if (M_AXI_ARVALID && M_AXI_ARREADY &&
				(state == DC_READC) && !(&cvr_cache_misses))
		cvr_cache_misses <= cvr_cache_misses + 1;

	always @(*)
	begin
		// cover(cvr_idle && cvr_cache_misses > 0);
		// cover(cvr_idle && cvr_cache_misses > 1);
		cover(cvr_idle && cvr_cache_misses > 2);
	end
	// }}}

	// cvr_cache_reads
	// {{{
	initial	cvr_cache_reads = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || M_AXI_ARVALID || M_AXI_RVALID || i_cpu_reset)
		cvr_cache_reads <= 0;
	else if (o_valid && $past(r_dvalid || r_svalid) && !(&cvr_cache_reads))
		cvr_cache_reads <= cvr_cache_reads + 1;

	always @(*)
	begin
		// cover(cvr_idle && cvr_cache_reads > 0);
		// cover(cvr_idle && cvr_cache_reads > 1);
		cover(cvr_idle && cvr_cache_reads > 4);
	end
	// }}}

	// cvr_cache_writes
	// {{{
	initial	cvr_cache_writes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || M_AXI_ARVALID || M_AXI_RVALID || i_cpu_reset)
		cvr_cache_writes <= 0;
	else if (!(&cvr_cache_writes) && state == DC_WRITE
			&& w_v && wcache_tag == r_ctag && wcache_strb != 0)
		cvr_cache_writes <= cvr_cache_writes + 1;

	always @(*)
	begin
		// cover(cvr_idle && cvr_cache_writes > 0);
		// cover(cvr_idle && cvr_cache_writes > 1);
		cover(cvr_idle && cvr_cache_writes > 4);
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" constraining assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (i_pipe_stb && i_write && i_lock)
	begin
		assume(i_addr == faxi_exlock_addr);
		assume(faxi_ex_state == 2'b10);

		if (SWAP_WSTRB)
		begin
			assert(faxi_exlock_size == DSZ);
		end else casez(i_op[2:1])
		2'b0?: assume(faxi_exlock_size == 3'b010); // Word
		2'b10: assume(faxi_exlock_size == 3'b001); // Half-word
		2'b11: assume(faxi_exlock_size == 3'b000); // Byte
		endcase
	end

	always @(*)
	casez(faxi_ex_state)
	2'b01: begin
		assert(faxi_exreq_len == 0);
		assert(faxi_exreq_size <= 3'd2);

		if (faxi_exreq_addr[0])
		begin
			assert(faxi_exreq_size == 3'd0);
		end else if (faxi_exreq_addr[1])
			assert(faxi_exreq_size <= 3'd1);

		if (SWAP_WSTRB)
			assert(faxi_exreq_size == 3'd2);
		// assert(faxi_exlock_size  == faxi_exreq_size);
		end
	2'b1?: begin
		assert(faxi_exlock_addr  == faxi_exreq_addr);
		assert(faxi_exlock_len   == faxi_exreq_len);
		assert(faxi_exlock_size  == faxi_exreq_size);
		assert(faxi_exlock_burst == faxi_exreq_burst);
		assert(faxi_exlock_size <= 3'd2);

		if (SWAP_WSTRB)
			assert(faxi_exlock_size == 3'd2);
		if (faxi_exlock_addr[0])
		begin
			assert(faxi_exlock_size == 3'd0);
		end else if (faxi_exlock_addr[1])
			assert(faxi_exlock_size <= 3'd1);
		end
	default: begin end
	endcase

	always @(*)
	if (i_pipe_stb && i_lock)
		assume(!i_cpu_reset);

	always @(posedge S_AXI_ACLK)
	if ($past(i_cpu_reset))
		assume((faxi_ex_state == 2'b00) || (faxi_ex_state == 2'b01));

	always @(*)
	if (OPT_WRAP && S_AXI_ARESETN && !i_cpu_reset
		&& !r_rd_pending && state == DC_READC && M_AXI_RVALID)
		assume(M_AXI_RRESP[1] == !good_cache_read);

	always @(*)
	if (S_AXI_ARESETN && OPT_LOCK && cpu_outstanding > 0)
		assume(!i_pipe_stb || !i_lock);
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, cpu_pc,
			faxi_rdid_ckign_nbursts, faxi_rdid_ckign_outstanding,
			faxi_wr_incr, faxi_wr_pending, faxi_wr_addr,
			cpu_addr_reg, faxi_rd_ckincr,
			faxi_rd_lastaddr };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
