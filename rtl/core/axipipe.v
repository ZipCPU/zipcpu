////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axipipe.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A memory unit to support a CPU based upon AXI-lite.  Unlike the
//		axilops core, this one will permit multiple requests to be
//	outstanding at any given time.
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
module	axipipe #(
		// {{{
		parameter	C_AXI_ADDR_WIDTH = 30,
		parameter	C_AXI_DATA_WIDTH = 32,
		parameter	C_AXI_ID_WIDTH = 1,
		parameter	[((C_AXI_ID_WIDTH>0)? C_AXI_ID_WIDTH:1)-1:0]
				AXI_ID = 0,
		localparam	AW = C_AXI_ADDR_WIDTH,
		localparam	DW = C_AXI_DATA_WIDTH,
		localparam	IW =(C_AXI_ID_WIDTH > 0) ? C_AXI_ID_WIDTH : 1,
		//
		// parameter [0:0]	SWAP_ENDIANNESS = 1'b0,
		parameter [0:0]	SWAP_WSTRB = 1'b0,
		parameter [0:0]	OPT_SIGN_EXTEND = 1'b0,
		// AXI locks are a challenge, and require support from the
		// CPU.  Specifically, we have to be able to unroll and re-do
		// the load instruction on any atomic access failure.  For that
		// reason, we'll ignore the lock request initially.
		parameter [0:0]	OPT_LOCK=1'b1,
		parameter [0:0]	OPT_ALIGNMENT_ERR = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b1,
		parameter [3:0]	OPT_QOS = 0
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
		output	reg				o_pipe_stalled,
		output	reg				o_rdbusy,
		output	reg				o_valid,
		output	reg				o_err,
		output	reg	[4:0]			o_wreg,
		output	reg	[31:0]			o_result,
		// }}}
		//
		// AXI4 bus interface
		// {{{
		// Writes
		// {{{
		output	reg			M_AXI_AWVALID,
		input	wire			M_AXI_AWREADY,
		// verilator coverage_off
		output	wire	[IW-1:0]	M_AXI_AWID,
		// verilator coverage_on
		output	reg	[AW-1:0]	M_AXI_AWADDR,
		// verilator coverage_off
		output	wire	[7:0]		M_AXI_AWLEN,	// == 0
		// verilator coverage_on
		output	wire	[2:0]		M_AXI_AWSIZE,
		output	wire	[1:0]		M_AXI_AWBURST,
		output	wire			M_AXI_AWLOCK,
		output	wire	[3:0]		M_AXI_AWCACHE,
		// verilator coverage_off
		output	wire	[2:0]		M_AXI_AWPROT,
		output	wire	[3:0]		M_AXI_AWQOS,
		// verilator coverage_on
		//
		output	reg			M_AXI_WVALID,
		input	wire			M_AXI_WREADY,
		output	reg	[DW-1:0]	M_AXI_WDATA,
		output	reg	[DW/8-1:0]	M_AXI_WSTRB,
		output	wire			M_AXI_WLAST,
		//
		input	wire			M_AXI_BVALID,
		// verilator coverage_off
		input	wire	[IW-1:0]	M_AXI_BID,
		// verilator coverage_on
		output	wire			M_AXI_BREADY,
		input	wire [1:0]		M_AXI_BRESP,
		// }}}
		// Reads
		// {{{
		output	reg			M_AXI_ARVALID,
		input	wire			M_AXI_ARREADY,
		// verilator coverage_off
		output	wire	[IW-1:0]	M_AXI_ARID,
		// verilator coverage_on
		output	reg	[AW-1:0]	M_AXI_ARADDR,
		// verilator coverage_off
		output	wire	[7:0]		M_AXI_ARLEN,	// == 0
		// verilator coverage_on
		output	wire	[2:0]		M_AXI_ARSIZE,
		output	wire	[1:0]		M_AXI_ARBURST,
		output	wire			M_AXI_ARLOCK,
		output	wire	[3:0]		M_AXI_ARCACHE,
		// verilator coverage_off
		output	wire	[2:0]		M_AXI_ARPROT,
		output	wire	[3:0]		M_AXI_ARQOS,
		// verilator coverage_on
		//
		input	wire			M_AXI_RVALID,
		output	wire			M_AXI_RREADY,
		// verilator coverage_off
		input	wire	[IW-1:0]	M_AXI_RID,
		// verilator coverage_on
		input	wire	[DW-1:0]	M_AXI_RDATA,
		input	wire			M_AXI_RLAST,
		input	wire	[1:0]		M_AXI_RRESP
		// }}}
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam	AXILSB = $clog2(C_AXI_DATA_WIDTH/8);
	localparam [2:0] DSZ = AXILSB[2:0];
	localparam	LGPIPE = 4;
	localparam	FIFO_WIDTH = AXILSB+1+2+4 + 1;
	localparam	[1:0]	AXI_INCR = 2'b01,
				OKAY = 2'b00,
				EXOKAY = 2'b01;
			//	SLVERR
			//	DECERR

	wire	i_clk = S_AXI_ACLK;

	reg	w_misaligned;
	wire	misaligned_request, misaligned_aw_request, pending_err;
	reg	w_misalignment_err;
	reg	[C_AXI_DATA_WIDTH-1:0]	next_wdata;
	reg [C_AXI_DATA_WIDTH/8-1:0]	next_wstrb;

	reg	[AW-1:0]		r_pc;
	reg				r_lock;
	reg	[2:0]			axi_size;

	reg				none_outstanding, bus_abort,
					read_abort, write_abort;
	reg	[LGPIPE:0]		beats_outstanding;
	reg				r_flushing, flush_request,
					r_pipe_stalled;
	reg	[LGPIPE:0]		flushcount, new_flushcount;
	reg	[LGPIPE:0]		wraddr, rdaddr;
	reg	[3:0]			ar_oreg;
	reg	[1:0]			ar_op;
	reg	[AXILSB-1:0]		adr_lsb;
	reg	[FIFO_WIDTH-1:0]	fifo_data	[0:((1<<LGPIPE)-1)];
	reg	[FIFO_WIDTH-1:0]	fifo_read_data;
	wire				fifo_read_op, fifo_misaligned;
	reg				fifo_gie;
	wire	[1:0]			fifo_op;
	wire	[3:0]			fifo_return_reg;
	wire	[AXILSB-1:0]		fifo_lsb;
	reg [2*C_AXI_DATA_WIDTH-1:0]	wide_return, wide_wdata;
	reg	[31:0]			pre_result;
	reg [2*C_AXI_DATA_WIDTH/8-1:0]	wide_wstrb;
	reg	[C_AXI_DATA_WIDTH-1:0]	misdata;


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Transaction issue
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// AWVALID
	// {{{
	initial	M_AXI_AWVALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXI_AWVALID <= 0;
	else if (!M_AXI_AWVALID || M_AXI_AWREADY)
	begin
		if (i_stb && i_op[0])
			M_AXI_AWVALID <= !w_misalignment_err;
		else
			M_AXI_AWVALID <= M_AXI_AWVALID && misaligned_aw_request;

		if (write_abort && !misaligned_aw_request)
			M_AXI_AWVALID <= 0;
	end
	// }}}

	// WVALID
	// {{{
	initial	M_AXI_WVALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXI_WVALID <= 0;
	else if (!M_AXI_WVALID || M_AXI_WREADY)
	begin
		if (i_stb && i_op[0])
			M_AXI_WVALID <= !w_misalignment_err;
		else
			M_AXI_WVALID <= M_AXI_WVALID && misaligned_request;

		if (write_abort && !misaligned_request)
			M_AXI_WVALID <= 0;
	end
	// }}}

	// ARVALID
	// {{{
	initial	M_AXI_ARVALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXI_ARVALID <= 0;
	else if (!M_AXI_ARVALID || M_AXI_ARREADY)
	begin
		if (i_stb && !i_op[0])
			M_AXI_ARVALID <= !w_misalignment_err;
		else
			M_AXI_ARVALID <= M_AXI_ARVALID && misaligned_request;

		if (read_abort && !misaligned_request)
			M_AXI_ARVALID <= 0;
	end
	// }}}

	// r_lock, M_AXI_AxLOCK
	// {{{
	initial	r_lock = 1'b0;
	always @(posedge i_clk)
	if (!OPT_LOCK || !S_AXI_ARESETN)
		r_lock <= 1'b0;
	else if ((!M_AXI_ARVALID || M_AXI_ARREADY)
			&&(!M_AXI_AWVALID || M_AXI_AWREADY))
	begin
		if (!M_AXI_AWVALID && !M_AXI_ARVALID && !M_AXI_WVALID
				&& beats_outstanding <= ((M_AXI_RVALID||M_AXI_BVALID)? 1:0))
			r_lock <= 1'b0;
		if (i_stb)
			r_lock <= i_lock && !w_misalignment_err;
		if (i_cpu_reset || r_flushing)
			r_lock <= 1'b0;
	end

	assign	M_AXI_AWLOCK = r_lock;
	assign	M_AXI_ARLOCK = r_lock;
	// }}}

	// axi_size, M_AXI_AxSIZE
	// {{{
	initial	axi_size = DSZ;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_size <= DSZ;
	else if (i_stb)
	begin
		if (SWAP_WSTRB)
			axi_size <= AXILSB[2:0];
		else begin
			casez(i_op[2:1])
			2'b0?: begin
				axi_size <= 3'b010;
				if ((|i_addr[1:0]) && !w_misaligned)
					axi_size <= AXILSB[2:0];
				end
			2'b10: begin
				axi_size <= 3'b001;
				if (i_addr[0] && !w_misaligned)
					axi_size <= AXILSB[2:0];
				end
			2'b11: axi_size <= 3'b000;
			// default: begin end
			endcase
		end
	end

	assign	M_AXI_AWSIZE = axi_size;
	assign	M_AXI_ARSIZE = axi_size;
	// }}}

	// o_busy,
	// {{{
	// True if the bus is busy doing ... something, whatever it might be.
	// If the bus is busy, the CPU will avoid issuing further interactions
	// to the bus other than pipelined interactions.
	initial	o_busy = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_busy <= 0;
	else if (i_stb && !w_misalignment_err && !bus_abort)
		o_busy <= 1;
	else if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
		o_busy <= 1;
	else if (beats_outstanding > ((M_AXI_RVALID || M_AXI_BVALID) ? 1:0))
		o_busy <= 1;
	else
		o_busy <= 0;
`ifdef	FORMAL
	always @(*)
		assert(o_busy == (!none_outstanding || M_AXI_ARVALID
				|| M_AXI_AWVALID || M_AXI_WVALID));
`endif
	// }}}

	// Read busy
	// {{{
	// True if the CPU should expect some kind of pending response from a
	// read, and so should stall for that purpose.  False otherwise.
	initial	o_rdbusy = 0;
	always @(posedge S_AXI_ACLK)
	if (i_cpu_reset || r_flushing)
		o_rdbusy <= 0;
	else if ((i_stb && w_misalignment_err) || bus_abort)
		o_rdbusy <= 0;
	else if (i_stb && (!i_op[0] || (OPT_LOCK && i_lock)))
		o_rdbusy <= 1;
	else if (OPT_LOCK)
	begin
		if (M_AXI_AWVALID || M_AXI_ARVALID || M_AXI_WVALID)
			o_rdbusy <= o_rdbusy;
		else if (o_rdbusy)
			o_rdbusy <= (beats_outstanding > ((M_AXI_RVALID||M_AXI_BVALID) ? 1:0));
	end else if (o_rdbusy && !M_AXI_ARVALID)
		o_rdbusy <= (beats_outstanding > (M_AXI_RVALID ? 1:0));

`ifdef	FORMAL
	reg	writing;

	always @(posedge S_AXI_ACLK)
	if (i_stb && !o_busy)
		writing <= i_op[0];

	always @(*)
	if (r_flushing)
	begin
		assert(!o_rdbusy);
	end else begin
		if (writing && r_lock && (M_AXI_AWVALID || M_AXI_WVALID || (beats_outstanding > 0)))
		begin
			assert(o_rdbusy);
		end else if (writing)
		begin
			assert(!o_rdbusy);
		end

		if (!o_busy)
			assert(!o_rdbusy);
	end
`endif
	// }}}

	// o_pipe_stalled, r_pipe_stalled
	// {{{
	// True if the CPU should expect some kind of pending response from a
	// read, and so should stall for that purpose.  False otherwise.
	generate if (OPT_ALIGNMENT_ERR)
	begin : FULL_PIPE_STALL
		// {{{
		// Here, we stall if the FIFO is ever full.  In this case,
		// any new beat will count as only one item to the FIFO, and
		// so we can run all the way to full.
		reg	[LGPIPE:0]		beats_committed;

		always @(*)
			beats_committed = beats_outstanding
				+ ((i_stb && !w_misalignment_err) ? 1:0)
				+ ((M_AXI_AWVALID || M_AXI_WVALID
						|| M_AXI_ARVALID) ? 1:0);

		initial	r_pipe_stalled = 0;
		always @(posedge S_AXI_ACLK)
		if (i_cpu_reset)
			r_pipe_stalled <= 0;
		else if (M_AXI_RVALID || M_AXI_BVALID)
			r_pipe_stalled <= 0;
		else if (i_stb && i_lock && !w_misalignment_err)
			r_pipe_stalled <= 1;
		else if (OPT_LOCK && r_lock)
			r_pipe_stalled <= (beats_committed > 0);
		else
			r_pipe_stalled <= (beats_committed >= (1<<LGPIPE));

`ifdef	FORMAL
		always @(*)
		if (r_flushing)
		begin
			assert(o_pipe_stalled);
		end else if (beats_outstanding + ((M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) ? 1:0) >= (1<<LGPIPE))
		begin
			assert(r_pipe_stalled);
		end else if (beats_outstanding + (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) < (1<<LGPIPE)-1)
			assert(r_lock || !r_pipe_stalled);

		always @(*)
		if (r_lock && !r_flushing)
		begin
			if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
			begin
				assert(r_pipe_stalled);
			end else if (beats_outstanding >= 1)
			begin
				assert(r_pipe_stalled);
			end else
				assert(!r_pipe_stalled && !OPT_LOWPOWER);
		end
`endif
		// }}}
	end else begin : PENULTIMATE_FULL_STALL
		// {{{
		// If we allow for misaligned reads and writes, than we have
		// to stall the CPU just before the FIFO is full, lest the
		// CPU send us a value that needs two items to be placed into
		// the FIO.
		reg	[LGPIPE:0]		beats_committed;

		always @(*)
		begin
			beats_committed = beats_outstanding + (i_stb ? 1:0)
				+ ((M_AXI_AWVALID || M_AXI_WVALID
						|| M_AXI_ARVALID) ? 1:0)
				- ((M_AXI_BVALID || M_AXI_RVALID) ? 1:0);
		end

		initial	r_pipe_stalled = 0;
		always @(posedge S_AXI_ACLK)
		if (i_cpu_reset || bus_abort)
			r_pipe_stalled <= 0;
		else begin
			r_pipe_stalled <= 0;
			if (r_lock && (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID))
				r_pipe_stalled <= 1;
			if (r_lock && (beats_outstanding > ((M_AXI_RVALID || M_AXI_BVALID) ? 1:0)))
				r_pipe_stalled <= 1;
			if (i_stb && (w_misaligned && !w_misalignment_err) && !o_pipe_stalled)
				r_pipe_stalled <= 1'b1;
			if (misaligned_request && (M_AXI_WVALID && !M_AXI_WREADY))
				r_pipe_stalled <= 1'b1;
			if (misaligned_request && (M_AXI_ARVALID && !M_AXI_ARREADY))
				r_pipe_stalled <= 1'b1;
			if (misaligned_aw_request && (M_AXI_AWVALID && !M_AXI_AWREADY))
				r_pipe_stalled <= 1'b1;
			if (beats_committed >= (1<<LGPIPE)-2)
				r_pipe_stalled <= 1'b1;
			if (i_stb && i_lock && !w_misalignment_err)
				r_pipe_stalled <= 1'b1;
		end

`ifdef	FORMAL
		always @(*)
		if (!r_flushing && (beats_outstanding
				+ ((M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) ? 1:0)
				+ ((misaligned_aw_request || misaligned_request) ? 1:0)
				>= (1<<LGPIPE)))
		begin
			assert(r_pipe_stalled);
		end else if (r_lock && !r_flushing)
		begin
			assert(r_pipe_stalled == o_busy);
		end else if (!r_flushing && !o_err
				&& !M_AXI_AWVALID && !M_AXI_WVALID
				&& !M_AXI_ARVALID
				&& beats_outstanding <= ((1<<LGPIPE)-4))
			assert(!r_pipe_stalled);

		always @(*)
			assert(beats_committed
				+ ((i_stb && w_misaligned && !r_pipe_stalled) ? 1:0)
				<= (1<<LGPIPE));
`endif
		// }}}
	end endgenerate

	always @(*)
	begin
		o_pipe_stalled = r_pipe_stalled || r_flushing;
		// if (r_lock && o_busy) o_pipe_stalled = 1;
		if (M_AXI_AWVALID && (!M_AXI_AWREADY || misaligned_aw_request))
			o_pipe_stalled = 1;
		if (M_AXI_WVALID && (!M_AXI_WREADY || misaligned_request))
			o_pipe_stalled = 1;
		if (M_AXI_ARVALID && (!M_AXI_ARREADY || misaligned_request))
			o_pipe_stalled = 1;
	end
`ifdef	FORMAL
	always @(*)
	if (misaligned_request)
		assert(M_AXI_WVALID || M_AXI_ARVALID);

	always @(*)
	if (misaligned_aw_request)
		assert(M_AXI_AWVALID);

	always @(*)
	if (r_lock && o_busy)
		assert(o_pipe_stalled);
`endif
	// }}}

	// Count the number of outstanding beats
	// {{{
	// This is the true count.  It is not affected by the number of
	// items the CPU believes is on the bus or not.
	initial	beats_outstanding = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		beats_outstanding <= 0;
	else casez({M_AXI_AWVALID && M_AXI_AWREADY,
		M_AXI_WVALID && M_AXI_WREADY,
		M_AXI_ARVALID && M_AXI_ARREADY,
		M_AXI_RVALID || M_AXI_BVALID})
	4'b0001: beats_outstanding <= beats_outstanding - 1;
	4'b??10: beats_outstanding <= beats_outstanding + 1;
	4'b1100: beats_outstanding <= beats_outstanding + 1;
	4'b1000: if (!M_AXI_WVALID || (misaligned_aw_request && !misaligned_request))
			beats_outstanding <= beats_outstanding + 1;
	4'b0100: if (!M_AXI_AWVALID || (misaligned_request && !misaligned_aw_request))
			beats_outstanding <= beats_outstanding + 1;
	4'b10?1: if ((M_AXI_WVALID && (OPT_ALIGNMENT_ERR
				|| (misaligned_request == misaligned_aw_request)))
			|| (!misaligned_aw_request && misaligned_request))
			beats_outstanding <= beats_outstanding - 1;
	4'b0101: if ((M_AXI_AWVALID && (OPT_ALIGNMENT_ERR
				|| (misaligned_request == misaligned_aw_request)))
			|| (!misaligned_request && misaligned_aw_request))
			beats_outstanding <= beats_outstanding - 1;
	default: begin end
	endcase

	initial	none_outstanding = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		none_outstanding <= 1;
	else casez({M_AXI_AWVALID && M_AXI_AWREADY,
		M_AXI_WVALID && M_AXI_WREADY,
		M_AXI_ARVALID && M_AXI_ARREADY,
		M_AXI_RVALID || M_AXI_BVALID})
	4'b0001: none_outstanding <= (beats_outstanding <= 1);
	4'b??10: none_outstanding <= 0;
	4'b1100: none_outstanding <= 0;
	4'b1000: if (!M_AXI_WVALID || (misaligned_aw_request && !misaligned_request))
			none_outstanding <= 0;
	4'b0100: if (!M_AXI_AWVALID || (misaligned_request && !misaligned_aw_request))
			none_outstanding <= 0;
	4'b10?1: if ((M_AXI_WVALID && (OPT_ALIGNMENT_ERR
				|| (misaligned_request == misaligned_aw_request)))
			|| (!misaligned_aw_request && misaligned_request))
			none_outstanding <= (beats_outstanding <= 1);
	4'b0101: if ((M_AXI_AWVALID && (OPT_ALIGNMENT_ERR
				|| (misaligned_request == misaligned_aw_request)))
			|| (!misaligned_request && misaligned_aw_request))
			none_outstanding <= (beats_outstanding <= 1);
	default: begin end
	endcase
`ifdef	FORMAL
	always @(*)
		assert(none_outstanding == (beats_outstanding == 0));
`endif
	// }}}

	// bus_abort
	// {{{
	// When do we abandon everything and start aborting bus transactions?
	always @(*)
	begin
		bus_abort = 0;
		if (i_cpu_reset || o_err)
			bus_abort = 1;
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			bus_abort = 1;
		if (M_AXI_RVALID && M_AXI_RRESP[1])
			bus_abort = 1;

		write_abort = 0;
		if (i_cpu_reset || o_err)
			write_abort = 1;
		if (M_AXI_BVALID && M_AXI_BRESP[1])
			write_abort = 1;

		read_abort = 0;
		if (i_cpu_reset || o_err)
			read_abort = 1;
		if (M_AXI_RVALID && M_AXI_RRESP[1])
			read_abort = 1;
	end
	// }}}

	// Flushing
	// {{{

	// new_flushcount
	// {{{
	always @(*)
	begin
		case({((M_AXI_AWVALID || M_AXI_WVALID) || M_AXI_ARVALID),
			(M_AXI_BVALID || M_AXI_RVALID) })
		2'b01: new_flushcount = beats_outstanding - 1;
		2'b10: new_flushcount = beats_outstanding + 1;
		default: new_flushcount = beats_outstanding;
		endcase

		if (!OPT_ALIGNMENT_ERR && (misaligned_request || misaligned_aw_request))
			new_flushcount = new_flushcount + 1;
	end
	// }}}

	initial	r_flushing    = 1'b0;
	initial	flushcount    = 0;
	initial	flush_request = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		r_flushing <= 1'b0;
		flush_request <= 0;
		flushcount    <= 0;
		// }}}
	end else if (i_cpu_reset || bus_abort || (i_stb && w_misalignment_err))
	begin
		// {{{
		r_flushing <= (new_flushcount != 0);
		flushcount <= new_flushcount;
		flush_request <= (M_AXI_ARVALID && (!M_AXI_ARREADY || misaligned_request))
			|| (M_AXI_AWVALID && (!M_AXI_AWREADY || misaligned_aw_request))
			|| (M_AXI_WVALID && (!M_AXI_WREADY || misaligned_request));
		// }}}
	end else if (r_flushing)
	begin
		// {{{
		if (M_AXI_BVALID || M_AXI_RVALID)
		begin
			flushcount <= flushcount - 1;
			r_flushing <= (flushcount > 1);
		end

		casez({M_AXI_AWVALID && (M_AXI_AWREADY && !misaligned_aw_request),
				(M_AXI_WVALID && M_AXI_WREADY && !misaligned_request),
				(M_AXI_ARVALID && M_AXI_ARREADY && !misaligned_request) })
		3'b001: flush_request <= 0;
		3'b10?: flush_request <= M_AXI_WVALID;
		3'b01?: flush_request <= M_AXI_AWVALID;
		3'b11?: flush_request <= 0;
		default: begin end
		endcase
		// }}}
	end
`ifdef	FORMAL
	always @(*)
	begin
		assert(r_flushing == (flushcount > 0));
		if (!r_flushing)
		begin
			assert(!flush_request);
		end else
			assert(flush_request == (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID));
		if (r_flushing && !flush_request)
		begin
			assert(!misaligned_request);
			assert(!misaligned_aw_request);
		end

		if (flush_request)
		begin
			assert(flushcount == beats_outstanding + 1
				+ ((misaligned_request
				|| misaligned_aw_request) ? 1:0));
		// else if (faxil_rd_outstanding > 0 || M_AXI_ARVALID)
		end else if (r_flushing)
		begin
			assert(beats_outstanding == flushcount);
		end else
			assert(beats_outstanding >= flushcount);
	end
`endif
	// }}}

	// Bus addressing
	// {{{
	initial	M_AXI_AWADDR = 0;
	always @(posedge i_clk)
	if (i_stb)
	begin
		M_AXI_AWADDR <= i_addr[AW-1:0];
		if (SWAP_WSTRB)
			M_AXI_AWADDR[AXILSB-1:0] <= 0;
	end else if (!OPT_ALIGNMENT_ERR
		&& ((M_AXI_AWVALID && M_AXI_AWREADY) // && misaligned_aw_request
		|| (M_AXI_ARVALID && M_AXI_ARREADY))) // && misaligned_request))
	begin
		M_AXI_AWADDR[AW-1:AXILSB] <= M_AXI_AWADDR[AW-1:AXILSB] + 1;
		M_AXI_AWADDR[AXILSB-1:0] <= 0;
	end

	always @(*)
		M_AXI_ARADDR = M_AXI_AWADDR;
	// }}}

	// Is this request misaligned?
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

	always @(*)
	begin
		w_misalignment_err = w_misaligned && OPT_ALIGNMENT_ERR;
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

	// wide_wdata, wide_wstrb
	// {{{
	always @(*)
	if (SWAP_WSTRB)
	begin : BACKWARDS_ORDER
		// {{{
		casez(i_op[2:1])
		2'b10: wide_wdata
			= { i_data[15:0], {(2*C_AXI_DATA_WIDTH-16){1'b0}} }
				>> (i_addr[AXILSB-1:0] * 8);
		2'b11: wide_wdata
			= { i_data[7:0], {(2*C_AXI_DATA_WIDTH-8){1'b0}} }
				>> (i_addr[AXILSB-1:0] * 8);
		default: wide_wdata
			= ({ i_data, {(2*C_AXI_DATA_WIDTH-32){ 1'b0 }} }
				>> (i_addr[AXILSB-1:0] * 8));
		endcase

		casez(i_op[2:1])
		2'b0?: wide_wstrb
			= { 4'b1111, {(2*C_AXI_DATA_WIDTH/8-4){1'b0}} } >> i_addr[AXILSB-1:0];
		2'b10: wide_wstrb
			= { 2'b11, {(2*C_AXI_DATA_WIDTH/8-2){1'b0}} } >> i_addr[AXILSB-1:0];
		2'b11: wide_wstrb
			= { 1'b1, {(2*C_AXI_DATA_WIDTH/8-1){1'b0}} } >> i_addr[AXILSB-1:0];
		endcase
		// }}}
	end else begin : LITTLE_ENDIAN_DATA
		// {{{
		casez(i_op[2:1])
		2'b10: wide_wdata
			= { {(2*C_AXI_DATA_WIDTH-16){1'b0}}, i_data[15:0] }
					<< (8*i_addr[AXILSB-1:0]);
		2'b11: wide_wdata
			= { {(2*C_AXI_DATA_WIDTH-8){1'b0}}, i_data[7:0] }
					<< (8*i_addr[AXILSB-1:0]);
		default: wide_wdata
			= { {(2*C_AXI_DATA_WIDTH-32){1'b0}}, i_data }
					<< (8*i_addr[AXILSB-1:0]);
		endcase

		casez(i_op[2:1])
		2'b0?: wide_wstrb
			= { {(2*C_AXI_DATA_WIDTH/8-4){1'b0}}, 4'b1111} << i_addr[AXILSB-1:0];
		2'b10: wide_wstrb
			= { {(2*C_AXI_DATA_WIDTH/8-4){1'b0}}, 4'b0011} << i_addr[AXILSB-1:0];
		2'b11: wide_wstrb
			= { {(2*C_AXI_DATA_WIDTH/8-4){1'b0}}, 4'b0001} << i_addr[AXILSB-1:0];
		endcase
		// }}}
	end
	// }}}

	// WDATA and WSTRB
	// {{{
	initial	M_AXI_WDATA = 0;
	initial	M_AXI_WSTRB = 0;
	initial	next_wdata  = 0;
	initial	next_wstrb  = 0;
	always @(posedge i_clk)
	if (i_stb)
	begin
		if (SWAP_WSTRB)
		begin : BACKWARDS_ORDER_REG
			// {{{
			{ M_AXI_WDATA, next_wdata } <= wide_wdata;
			{ M_AXI_WSTRB, next_wstrb } <= wide_wstrb;
			// }}}
		end else begin
			// {{{
			{ next_wdata, M_AXI_WDATA } <= wide_wdata;
			{ next_wstrb, M_AXI_WSTRB } <= wide_wstrb;
			// }}}
		end

		if (OPT_ALIGNMENT_ERR)
			{ next_wstrb, next_wdata } <= 0;

	end else if ((OPT_LOWPOWER || !OPT_ALIGNMENT_ERR) && M_AXI_WREADY)
	begin
		M_AXI_WDATA <= next_wdata;
		M_AXI_WSTRB <= next_wstrb;
		if (OPT_LOWPOWER)
			{ next_wdata, next_wstrb } <= 0;
	end
	// }}}

	generate if (OPT_ALIGNMENT_ERR)
	begin : GEN_ALIGNMENT_ERR
		// {{{
		// Generate an error on any misaligned request
		assign	misaligned_request = 1'b0;

		assign	misaligned_aw_request = 1'b0;
		assign	pending_err = 1'b0;
		// }}}
	end else begin : GEN_REALIGNMENT
		// {{{
		reg	r_misaligned_request, r_misaligned_aw_request,
			r_pending_err;

		// misaligned_request
		// {{{
		initial	r_misaligned_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			r_misaligned_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset && !bus_abort)
			r_misaligned_request <= w_misaligned && !w_misalignment_err;
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
		else if (i_stb && !o_err && !i_cpu_reset && !write_abort)
			r_misaligned_aw_request <= w_misaligned && i_op[0] && !w_misalignment_err;
		else if (M_AXI_AWREADY)
			r_misaligned_aw_request <= 1'b0;

		assign	misaligned_aw_request = r_misaligned_aw_request;
		// }}}

		// pending_err
		// {{{
		initial	r_pending_err = 1'b0;
		always @(posedge i_clk)
		if (i_cpu_reset || i_stb || o_err || r_flushing)
			r_pending_err <= 1'b0;
		else if ((M_AXI_BVALID && M_AXI_BRESP[1])
				|| (M_AXI_RVALID && M_AXI_RRESP[1]))
			r_pending_err <= 1'b1;

		assign	pending_err = r_pending_err;
		// }}}

`ifdef	FORMAL
		always @(*)
		if (pending_err)
			assert(r_flushing || o_err);
`endif
		// }}}
	end endgenerate

	// AxOTHER
	// {{{
	localparam [3:0]	AXI_NON_CACHABLE_BUFFERABLE = 4'h3;
	localparam [3:0]	OPT_CACHE = AXI_NON_CACHABLE_BUFFERABLE;
	localparam [2:0]	AXI_UNPRIVILEGED_NONSECURE_DATA_ACCESS = 3'h0;
	localparam [2:0]	OPT_PROT=AXI_UNPRIVILEGED_NONSECURE_DATA_ACCESS;

	assign	M_AXI_AWID    = AXI_ID;
	assign	M_AXI_AWLEN   = 0;
	assign	M_AXI_AWBURST = AXI_INCR;
	assign	M_AXI_AWCACHE = M_AXI_AWLOCK ? 0:OPT_CACHE;
	assign	M_AXI_AWPROT  = OPT_PROT;
	assign	M_AXI_AWQOS   = OPT_QOS;
	assign	M_AXI_WLAST   = 1;

	assign	M_AXI_ARID    = AXI_ID;
	assign	M_AXI_ARLEN   = 0;
	assign	M_AXI_ARBURST = AXI_INCR;
	assign	M_AXI_ARCACHE = M_AXI_ARLOCK ? 0:OPT_CACHE;
	assign	M_AXI_ARPROT  = OPT_PROT;
	assign	M_AXI_ARQOS   = OPT_QOS;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read transaction FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// wraddr
	// {{{
	initial	wraddr = 0;
	always @(posedge S_AXI_ACLK)
	if (bus_abort || flush_request)	// bus_abort includes i_cpu_reset
		wraddr <= 0;
	else if ((M_AXI_ARVALID && M_AXI_ARREADY) || (M_AXI_WVALID && M_AXI_WREADY))
		wraddr <= wraddr + 1;
	// }}}

	// rdaddr
	// {{{
	initial	rdaddr = 0;
	always @(posedge S_AXI_ACLK)
	if (bus_abort || r_flushing)
		rdaddr <= 0;
	else if (M_AXI_RVALID||M_AXI_BVALID)
		rdaddr <= rdaddr + 1;
	// }}}

	// ar_oreg, ar_op, adr_lsb
	// {{{
	always @(posedge S_AXI_ACLK)
	if (i_stb)
		{ fifo_gie, ar_oreg, ar_op, adr_lsb } <= { i_oreg, i_op[2:1], i_addr[AXILSB-1:0] };
	else if ((M_AXI_ARVALID && M_AXI_ARREADY)||(M_AXI_WVALID && M_AXI_WREADY))
		adr_lsb <= 0;
	// }}}

	// fifo_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if ((M_AXI_ARVALID && M_AXI_ARREADY) || (M_AXI_WVALID && M_AXI_WREADY))
		fifo_data[wraddr[LGPIPE-1:0]] <= { M_AXI_ARVALID, ar_oreg,ar_op,
				misaligned_request, adr_lsb };

	always @(*)
		fifo_read_data = fifo_data[rdaddr[LGPIPE-1:0]];

	assign	{ fifo_read_op, fifo_return_reg, fifo_op,
			fifo_misaligned, fifo_lsb } = fifo_read_data;
	// }}}

	// r_pc
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!OPT_LOCK)
		r_pc <= 0;
	else if (i_stb && i_lock && !i_op[0])
		r_pc <= i_restart_pc;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read return generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || r_flushing)
		o_valid <= 1'b0;
	else if (OPT_LOCK && r_lock)
		o_valid <= (M_AXI_RVALID && M_AXI_RRESP == EXOKAY)
			||(M_AXI_BVALID && M_AXI_BRESP == OKAY);
	else if (OPT_ALIGNMENT_ERR && i_stb && w_misaligned)
		o_valid <= 1'b0;
	else
		o_valid <= M_AXI_RVALID && !M_AXI_RRESP[1] // && !pending_err
				&& !fifo_misaligned;
	// }}}

	// o_wreg
	// {{{
	always @(posedge i_clk)
	begin
		o_wreg <= { fifo_gie, fifo_return_reg };
		if (OPT_LOCK && r_lock && M_AXI_BVALID)
			o_wreg[3:0] <= 4'hf;
	end
	// }}}

	// o_result, misdata
	// {{{
	// Need to realign any returning data
	// wide_return
	// {{{
	always @(*)
	begin
		if (SWAP_WSTRB)
		begin
			if (fifo_misaligned && !OPT_ALIGNMENT_ERR)
				wide_return = { misdata, M_AXI_RDATA }
							<< (8*fifo_lsb);
			else
				wide_return = { M_AXI_RDATA, {(DW){1'b0}} }
							<< (8*fifo_lsb);

		end else begin
			if (fifo_misaligned && !OPT_ALIGNMENT_ERR)
				wide_return = { M_AXI_RDATA, misdata } >> (8*fifo_lsb);
			else
				wide_return = { {(C_AXI_DATA_WIDTH){1'b0}}, M_AXI_RDATA }
					>> (8*fifo_lsb);
		end

		if (OPT_LOWPOWER && (!M_AXI_RVALID || M_AXI_RRESP[1]))
			wide_return = 0;
	end

	always @(*)
	begin
		if (SWAP_WSTRB)
		begin

			pre_result = 32'h0;
			casez(fifo_op)
			2'b10: pre_result[15:0] = {
					wide_return[(2*DW)-1:(2*DW)-16] };
			2'b11: pre_result[7:0] = {
					wide_return[(2*DW)-1:(2*DW)-8] };
			default: pre_result[31:0] = wide_return[(2*DW-1):(2*DW-32)];
			endcase

		end else
			pre_result = wide_return[31:0];
	end
	// }}}

	// misdata
	// {{{
	always @(posedge i_clk)
	if (OPT_ALIGNMENT_ERR)
		misdata <= 0;
	else if (M_AXI_RVALID)
	begin
		if (fifo_misaligned)
			misdata <= M_AXI_RDATA;
		else
			misdata <= 0;
	end
	// }}}

	// o_result
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (!S_AXI_ARESETN || r_flushing || i_cpu_reset))
	begin
		o_result <= 0;
	end else if (OPT_LOCK && M_AXI_BVALID && (!OPT_LOWPOWER || (r_lock && M_AXI_BRESP == OKAY)))
	begin
		o_result <= 0;
		o_result[AW-1:0] <= r_pc;
	end else if (!OPT_LOWPOWER || M_AXI_RVALID)
	begin

		o_result <= pre_result[31:0];

		if (OPT_SIGN_EXTEND)
		begin
			// {{{
			// verilator coverage_off
			// Optionally sign extend the return result.
			//   This would be contrary to the ZipCPU ISA
			case(fifo_op)
			2'b10: o_result[31:16] <= {(16){pre_result[15]}};
			2'b11: o_result[31: 8] <= {(24){pre_result[7]}};
			default: begin end
			endcase
			// verilator coverage_on
			// }}}
		end else if (fifo_op[1])
		begin
			// {{{
			if (fifo_op[0])
				o_result[31: 8] <= 0;
			else
				o_result[31:16] <= 0;
			// }}}
		end

	end
	// }}}
	// }}}

	// o_err - report bus errors back to the CPU
	// {{{
	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || r_flushing || o_err)
		o_err <= 1'b0;
	else if (i_stb && w_misalignment_err)
		o_err <= 1'b1;
	else if (OPT_LOCK && r_lock)
		o_err <= (M_AXI_BVALID && M_AXI_BRESP[1])
			||(M_AXI_RVALID && M_AXI_RRESP != EXOKAY);
	else if (M_AXI_BVALID || M_AXI_RVALID)
		o_err <= (M_AXI_BVALID && M_AXI_BRESP[1])
			|| (M_AXI_RVALID && M_AXI_RRESP[1]);
	else
		o_err <= 1'b0;
	// }}}

	// Return xREADY -- always ready
	// {{{
	assign	M_AXI_RREADY = 1;
	assign	M_AXI_BREADY = 1;
	// }}}

	// }}}

	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXI_RRESP[0], M_AXI_BRESP[0],
			M_AXI_BID, M_AXI_RID, M_AXI_RLAST,
			// i_addr[31:C_AXI_ADDR_WIDTH],
			(&i_addr),
			// wide_return[2*C_AXI_DATA_WIDTH-1:32],
			pending_err, fifo_read_op,
			none_outstanding };

	generate if (SWAP_WSTRB)
	begin : GEN_UNUSED
		wire	wide_unused;

		if (SWAP_WSTRB)
		begin : GEN_UNUSED_SWAP
			assign	wide_unused = &{ 1'b0,
					wide_return[2*DW-32-1:0] };
		end else begin : GEN_UNUSED_WIDE
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
// Formal property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Declarations
	// {{{
`define	ASSERT		assert
`ifndef	BMC_ASSERT
`define	BMC_ASSERT	assume
`endif
`ifdef	AXILPIPE
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
	localparam	F_LGDEPTH = (LGPIPE > 9) ? (LGPIPE+1) : 10;
	// Verilator lint_off UNDRIVEN
	(* anyseq *)	wire	f_active_lock;
	(* anyconst *)	reg	[LGPIPE:0]		f_first_addr;
	(* anyseq *) reg [4:0]	f_areg;
	// Verilator lint_on  UNDRIVEN
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
	reg	[AW-1:0]	f_exlock_addr;
	wire	[AW-1:0]	faxi_exreq_addr;
	wire	[7:0]		f_exlock_len, faxi_exreq_len;
	wire	[1:0]		f_exlock_burst, faxi_exreq_burst;
	wire	[2:0]		faxi_exreq_size;
	reg	[2:0]		f_exlock_size;
	// Verilator lint_off UNUSED
	wire			faxi_exlock_return;
	// Verilator lint_on  UNUSED
	reg	[LGPIPE:0]	f_fifo_fill;

	reg		f_clrfifo, f_wrfifo, f_rdfifo;
	wire		misaligned_response_pending;
	reg	[1:0]	f_fsmfifo;
			reg	[LGPIPE:0]		f_next_addr,
				f_penu_addr, f_last_written,
				f_distance_to_first, f_distance_to_next;
	reg	[FIFO_WIDTH-1:0]	f_first_data, f_next_data, f_penu_data;
	reg	[4:0]	f_first_return_reg, f_next_return_reg, f_return_reg,
			f_penu_return_reg;
	reg		f_first_in_fifo,	f_next_in_fifo,
			f_first_misaligned,	f_next_misaligned,
			f_this_misaligned,	f_penu_misaligned,
			f_first_read_cycle,	f_next_read_cycle,
			f_this_read_cycle,	f_penu_read_cycle;


	wire	[LGPIPE:0]	cpu_outstanding;
	wire			cpu_gie, cpu_pc, cpu_read_cycle;
	wire	[4:0]		cpu_last_reg, cpu_addr_reg;
	reg	[4:0]		f_ar_areg;

	reg			f_done;


	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		`ASSUME(!S_AXI_ARESETN);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus property checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxi_master #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
		.OPT_MAXBURST(8'h0),
		.OPT_EXCLUSIVE(OPT_LOCK),
		.F_OPT_ASSUME_RESET(1'b1),
		.F_LGDEPTH(F_LGDEPTH)
		// }}}
	) faxi (
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		// Write interface
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
		//
		.i_axi_wvalid(M_AXI_WVALID),
		.i_axi_wready(M_AXI_WREADY),
		.i_axi_wdata( M_AXI_WDATA),
		.i_axi_wstrb( M_AXI_WSTRB),
		.i_axi_wlast( M_AXI_WLAST),
		//
		.i_axi_bvalid(M_AXI_BVALID),
		.i_axi_bready(M_AXI_BREADY),
		.i_axi_bid(   M_AXI_BID),
		.i_axi_bresp( M_AXI_BRESP),
		// }}}
		// Read interface
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
		//
		.i_axi_rvalid(M_AXI_RVALID),
		.i_axi_rready(M_AXI_RREADY),
		.i_axi_rid(   M_AXI_RID),
		.i_axi_rdata( M_AXI_RDATA),
		.i_axi_rresp( M_AXI_RRESP),
		.i_axi_rlast( M_AXI_RLAST),
		// }}}
		// Induction information
		// 
		.f_axi_awr_nbursts(faxi_awr_nbursts),
		.f_axi_wr_pending(faxi_wr_pending),
		.f_axi_rd_nbursts(faxi_rd_nbursts),
		.f_axi_rd_outstanding(faxi_rd_outstanding),
		// WR_COUNT
		// {{{
		.f_axi_wr_checkid(  faxi_wr_checkid),
		.f_axi_wr_ckvalid(  faxi_wr_ckvalid),
		.f_axi_wrid_nbursts(faxi_wrid_nbursts),
		.f_axi_wr_addr(     faxi_wr_addr),
		.f_axi_wr_incr(     faxi_wr_incr),
		.f_axi_wr_burst(    faxi_wr_burst),
		.f_axi_wr_size(     faxi_wr_size),
		.f_axi_wr_len(      faxi_wr_len),
		.f_axi_wr_lockd(    faxi_wr_lockd),
		// }}}
		// RD_COUNT
		// {{{
		.f_axi_rd_checkid(faxi_rd_checkid),
		.f_axi_rd_ckvalid(faxi_rd_ckvalid),
		.f_axi_rd_cklen(  faxi_rd_cklen),
		.f_axi_rd_ckaddr( faxi_rd_ckaddr),
		.f_axi_rd_ckincr( faxi_rd_ckincr),
		.f_axi_rd_ckburst(faxi_rd_ckburst),
		.f_axi_rd_cksize( faxi_rd_cksize),
		.f_axi_rd_ckarlen(faxi_rd_ckarlen),
		.f_axi_rd_cklockd(faxi_rd_cklockd),
		//
		.f_axi_rdid_nbursts(faxi_rdid_nbursts),
		.f_axi_rdid_outstanding(faxi_rdid_outstanding),
		.f_axi_rdid_ckign_nbursts(faxi_rdid_ckign_nbursts),
		.f_axi_rdid_ckign_outstanding(faxi_rdid_ckign_outstanding),
		// }}}
		// Exclusive access handling
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
		// 
		// }}}
	);


	always @(*)
		f_fifo_fill = wraddr - rdaddr;

	always @(*)
	begin
		if (misaligned_request)
			`ASSERT(M_AXI_WVALID || M_AXI_ARVALID);
		if (misaligned_aw_request)
			`ASSERT(M_AXI_AWVALID);

		if (M_AXI_ARVALID || faxi_rd_outstanding > 0)
		begin
			assert(faxi_awr_nbursts == 0);
			assert(!M_AXI_AWVALID);
			assert(!M_AXI_WVALID);
		end

		if (faxi_awr_nbursts > 0 || M_AXI_AWVALID || M_AXI_WVALID)
		begin
			assert(faxi_rd_outstanding == 0);
			assert(!M_AXI_ARVALID);
		end

		// Rule: Only one of the two VALID's may be valid, never both
		`ASSERT(!M_AXI_RVALID || (!M_AXI_AWVALID && !M_AXI_WVALID));

		assert({ 5'h0, beats_outstanding }
			+ ((misaligned_request && !misaligned_aw_request && M_AXI_WVALID) ? 1:0)
			+ ((M_AXI_WVALID && !M_AXI_AWVALID) ? 1:0)
			== faxi_rd_outstanding + faxi_awr_nbursts);

		/*
		assert(beats_outstanding
			+ ((misaligned_aw_request && !misaligned_request) ? 1:0)
			+ ((M_AXI_AWVALID && !M_AXI_WVALID) ? 1:0)
			== faxi_rd_outstanding + faxi_awr_nbursts);
		*/

		if (OPT_ALIGNMENT_ERR && !r_flushing
				&& (faxi_rd_outstanding > 0 || M_AXI_ARVALID))
		begin
			assert({ 5'h0, f_fifo_fill } == faxi_rd_outstanding);
		end else if (OPT_ALIGNMENT_ERR && !r_flushing
				&& (faxi_awr_nbursts > 0))
		begin
			if (M_AXI_WVALID == M_AXI_AWVALID)
			begin
				assert({ 5'h0, f_fifo_fill } == faxi_awr_nbursts);
			end else if (M_AXI_WVALID)
				assert({ 5'h0, f_fifo_fill } == faxi_awr_nbursts-1);
		end

		if (faxi_rd_outstanding == 0 && faxi_awr_nbursts == 0)
			assert(f_fifo_fill == 0);
	end

	// Internal write checks
	// {{{
	always @(*)
	begin
		if (faxi_wr_checkid == AXI_ID)
		begin
			assert(faxi_wrid_nbursts == faxi_awr_nbursts);
		end else
			assert(faxi_wrid_nbursts == 0);

		if (M_AXI_AWVALID)
		begin
			assert(M_AXI_WVALID);
			if (!misaligned_aw_request && misaligned_request)
			begin
				assert(faxi_wr_pending == 1);
			end else
				assert(faxi_wr_pending == 0);
		end

		if (faxi_wr_ckvalid)
		begin
			assert(faxi_wr_pending == (M_AXI_WVALID ? 1:0));
			// assert(faxi_wr_addr == );
			// assert(faxi_wr_incr == );
			assert(faxi_wr_burst == AXI_INCR);
			// assert(faxi_wr_size  == AXI_INCR);
			assert(faxi_wr_len  == 0);
			assert(r_flushing || faxi_wr_lockd == r_lock);
		end
	end
	// }}}

	// Internal read checks
	// {{{
	always @(*)
	begin
		if (faxi_rd_ckvalid)
		begin
			assert(faxi_rd_checkid == AXI_ID);
			// assert(faxi_rd_cklen == AXI_ID);
			// assert(faxi_rd_ckaddr == AXI_ID);
			// assert(faxi_rd_ckincr == AXI_INCR);
			assert(faxi_rd_ckburst == AXI_INCR);
			// assert(faxi_rd_cksize  == AXI_INCR);
			assert(faxi_rd_ckarlen == 8'h00);
			assert(r_flushing || faxi_rd_cklockd == r_lock);
		end

		if (faxi_rd_checkid == AXI_ID)
		begin
			assert(faxi_rd_nbursts == faxi_rdid_nbursts);
		end else
			assert(faxi_rdid_nbursts == 0);

		assert(faxi_rd_nbursts == faxi_rd_outstanding);
		assert(faxi_rdid_nbursts == faxi_rdid_outstanding);

		if (faxi_rd_nbursts > 1)
			assert(!r_lock);
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
		if (OPT_LOCK && $past(w_misalignment_err))
		begin
			`ASSERT(o_err && !o_busy);
		end else
			`ASSERT(o_busy || (OPT_ALIGNMENT_ERR && o_err));
	end

	always @(*)
	if (o_busy && !misaligned_request && OPT_LOWPOWER)
	begin
		assert(next_wdata == 0);
		assert(next_wstrb == 0);
	end

	// o_err checking
	// {{{
	// If a transaction ends in an error, send o_err on the output port.
	always @(posedge i_clk)
	if (f_past_valid)
	begin
		if ($past(i_cpu_reset || r_flushing || o_err))
		begin
			`ASSERT(!o_err);
		end else if ($past(M_AXI_BVALID && M_AXI_BRESP[1]))
		begin
			`ASSERT(o_err);
		end else if ($past(M_AXI_RVALID && M_AXI_RRESP[1]))
		begin
			`ASSERT(o_err);
		end else if ($past(r_lock && M_AXI_RVALID && M_AXI_RRESP != EXOKAY))
		begin
			`ASSERT(o_err);
		end else if ($past(i_stb && w_misalignment_err))
		begin
			`ASSERT(o_err);
		end else if (!$past(pending_err))
			`ASSERT(!o_err);
	end
	// }}}

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_cpu_reset))&&($past(i_stb)))
	begin
		// On a write, assert o_wb_we should be true
		assert($past(i_op[0] && !o_err
			&& (!M_AXI_BVALID || !M_AXI_BRESP[1])
			&& (!w_misalignment_err))
				== (M_AXI_AWVALID && M_AXI_WVALID));
	end

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_cpu_reset)))
		`ASSUME(!i_stb);

	always @(*)
	if (!S_AXI_ARESETN)
		`ASSUME(i_cpu_reset);

	// misaligned_response_pending
	// {{{
	generate if (OPT_ALIGNMENT_ERR)
	begin : NO_MISALIGNED_RESPONSES

		assign	misaligned_response_pending = 0;

	end else begin : MISALIGNED_RESPONSE_PENDING
		reg	r_misaligned_response_pending;

		always @(*)
		begin
			r_misaligned_response_pending = fifo_misaligned;
			if (wraddr == rdaddr)
				r_misaligned_response_pending = 0;
		end

		assign	misaligned_response_pending
				= r_misaligned_response_pending;
	end endgenerate
	// }}}


	always @(*)
	if (o_busy)
	begin
		cover(i_stb);
		cover(o_valid);
		cover(o_err);
	end else begin
		cover(o_valid);
		cover(o_err);
	end
	// }}}
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

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FIFO property checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		// {{{
		f_next_addr = f_first_addr + 1;
		f_last_written = wraddr - 1;

		f_penu_addr = rdaddr + 1;
		f_penu_data = fifo_data[f_penu_addr[LGPIPE-1:0]];

		f_clrfifo = (!S_AXI_ARESETN || bus_abort || flush_request);
		f_wrfifo = (!f_clrfifo) && ((M_AXI_ARVALID && M_AXI_ARREADY)
				|| (M_AXI_WVALID && M_AXI_WREADY));
		f_rdfifo = (!f_clrfifo) && ((M_AXI_RVALID && M_AXI_RREADY)
				|| (M_AXI_BVALID && M_AXI_BREADY));

		f_distance_to_first = f_first_addr - rdaddr;
		f_distance_to_next  = f_next_addr  - rdaddr;

		f_first_in_fifo = (f_distance_to_first < f_fifo_fill) && (f_fifo_fill > 0);
		f_next_in_fifo  = (f_distance_to_next < f_fifo_fill) && (f_fifo_fill > 0);

		f_return_reg = { fifo_gie, fifo_return_reg };

		f_first_return_reg = { fifo_gie, f_first_data[AXILSB+3 +: 4] };
		f_next_return_reg  = { fifo_gie, f_next_data[AXILSB+3 +: 4] };
		f_penu_return_reg  = { fifo_gie, f_penu_data[AXILSB+3 +: 4] };

		f_first_misaligned = f_first_data[AXILSB];
		f_next_misaligned = f_next_data[AXILSB];
		f_this_misaligned = fifo_read_data[AXILSB];
		f_penu_misaligned = f_penu_data[AXILSB];

		f_first_read_cycle = f_first_data[FIFO_WIDTH-1];
		f_next_read_cycle = f_next_data[FIFO_WIDTH-1];
		f_this_read_cycle = fifo_read_data[FIFO_WIDTH-1];
		f_penu_read_cycle = f_penu_data[FIFO_WIDTH-1];
		// }}}
	end

	always @(*)
	if (r_flushing && !f_clrfifo)
		assert(rdaddr == wraddr);

	always @(*)
	if (!f_clrfifo)
	begin
		if (f_first_in_fifo)
			`ASSERT(f_first_data == fifo_data[f_first_addr[LGPIPE-1:0]]);
		if (f_next_in_fifo)
			`ASSERT(f_next_data == fifo_data[f_next_addr[LGPIPE-1:0]]);
	end

	always @(posedge S_AXI_ACLK)
	if (f_wrfifo && wraddr == f_first_addr)
		f_first_data <= { M_AXI_ARVALID, ar_oreg, ar_op, misaligned_request, adr_lsb };

	always @(posedge S_AXI_ACLK)
	if (f_wrfifo && wraddr == f_next_addr)
		f_next_data <= { M_AXI_ARVALID, ar_oreg, ar_op, misaligned_request, adr_lsb };

	// f_fsmfifo
	// {{{
	initial	f_fsmfifo = 2'b00;
	always @(posedge S_AXI_ACLK)
	if (f_clrfifo)
		f_fsmfifo <= 2'b00;
	else case(f_fsmfifo)
	2'b00: if (f_wrfifo && wraddr == f_first_addr)
		f_fsmfifo <= 2'b01;
	2'b01: if (f_rdfifo && rdaddr == f_first_addr)
		f_fsmfifo <= 2'b00;
		else if (f_wrfifo && wraddr == f_next_addr)
		f_fsmfifo <= 2'b10;
	2'b10: if (f_rdfifo && rdaddr == f_first_addr)
		f_fsmfifo <= 2'b11;
	2'b11: if (f_rdfifo)
		f_fsmfifo <= 2'b00;
	endcase

	always @(*)
	if (!f_clrfifo)
	case(f_fsmfifo)
	2'b00: begin
		// {{{
		`ASSERT(!f_first_in_fifo);
		end
		// }}}
	2'b01: begin
		// {{{
		`ASSERT(f_fifo_fill >= 1);
		`ASSERT(f_first_in_fifo);
		end
		// }}}
	2'b10: begin
		// {{{
		`ASSERT(f_fifo_fill >= 2);
		`ASSERT(f_first_in_fifo);
		`ASSERT(f_next_in_fifo);
		end
		// }}}
	2'b11: begin
		// {{{
		`ASSERT(f_fifo_fill >= 1);
		`ASSERT(f_next_in_fifo);
		`ASSERT(rdaddr == f_next_addr);
		end
		// }}}
	endcase
	// }}}

	// { ar_oreg, ar_op, misaligned_request, M_AXI_ARADDR[AXILSB-1:0] };

	// cpu_gie checks
	// {{{
	always @(*)
	if (M_AXI_ARVALID)
		`ASSERT(cpu_gie == fifo_gie);

	always @(*)
	if (!f_clrfifo && f_fifo_fill != 0)
	begin
		if (M_AXI_ARVALID || M_AXI_WVALID || M_AXI_AWVALID)
			`ASSERT(cpu_gie == fifo_gie);

		if ((!f_first_in_fifo || rdaddr != f_first_addr)
				&& (!f_next_in_fifo || rdaddr != f_next_addr)
				&& (f_fifo_fill > 0))
			`ASSUME(cpu_gie == f_return_reg[4]);

		if (f_first_in_fifo)
			`ASSERT(cpu_gie == f_first_return_reg[4]);
		if (f_next_in_fifo)
			`ASSERT(cpu_gie == f_next_return_reg[4]);
	end
	// }}}

	// cpu_pc checks
	// {{{
	always @(*)
	if (M_AXI_ARVALID)
		`ASSERT(cpu_pc == ((&ar_oreg[3:1]) && (o_err || !flush_request)));

	always @(*)
	if (!f_clrfifo && f_fifo_fill != 0)
	begin
		if ((M_AXI_ARVALID || (rdaddr != f_last_written)))
		begin
			`ASSERT(f_this_misaligned || !cpu_read_cycle || !(&f_return_reg[3:1]));
		end else if (f_fifo_fill > 0 && !M_AXI_ARVALID)
			`ASSERT(f_this_misaligned || !cpu_read_cycle || cpu_pc == (&f_return_reg[3:1]));

		if ((!f_first_in_fifo || rdaddr != f_first_addr)
			&& (!f_next_in_fifo || rdaddr != f_next_addr)
			&& cpu_read_cycle)
		begin
			if (M_AXI_ARVALID) // && (&ar_oreg[3:1]))
			begin
				`ASSUME(!(&f_return_reg[3:1]));
			end else if (rdaddr != f_last_written)
			begin
				`ASSUME(!(&f_return_reg[3:1]));
			end else if (!M_AXI_ARVALID && !o_err)
				`ASSUME(cpu_pc == (&f_return_reg[3:1])); // Not last written
		end

		if (f_first_in_fifo && cpu_read_cycle)
		begin
			if (!cpu_pc || M_AXI_ARVALID
					|| (f_last_written != f_first_addr))
			begin
				`ASSERT(f_first_misaligned || !cpu_read_cycle || !(&f_first_return_reg[3:1]));
			end else if (!M_AXI_ARVALID && !o_err)
				`ASSERT(&f_first_return_reg[3:1]);
		end

		if (f_next_in_fifo && cpu_read_cycle)
		begin
			if (!cpu_pc || M_AXI_ARVALID
					|| (f_last_written != f_next_addr))
			begin
				`ASSERT(f_next_misaligned || !(&f_next_return_reg[3:1]));
			end else if (!M_AXI_ARVALID && !o_err)
				`ASSERT(&f_next_return_reg[3:1]);
		end

		if (M_AXI_ARVALID)
			`ASSERT(cpu_pc == (&ar_oreg[3:1]));
	end
	// }}}

	always @(*)
	if (cpu_read_cycle && !r_flushing)
		assert(o_rdbusy==((rdaddr != wraddr)||(M_AXI_ARVALID)));

	always @(*)
	if (cpu_read_cycle)
		assert(!M_AXI_AWVALID && !M_AXI_WVALID&& faxi_awr_nbursts == 0);

	// Verifying the alignment flags
	// {{{
	always @(*)
	if (M_AXI_ARVALID && OPT_ALIGNMENT_ERR)
		assert(!misaligned_request);

	always @(*)
	if (!f_clrfifo && f_fifo_fill != 0)
	begin
		if (OPT_ALIGNMENT_ERR)
		begin
			// {{{
			if (f_first_in_fifo)
				`ASSERT(!f_first_misaligned);
			if (f_next_in_fifo)
				`ASSERT(!f_next_misaligned);
			if ((!f_first_in_fifo || rdaddr != f_first_addr)
				&& (!f_next_in_fifo || rdaddr != f_next_addr))
				`ASSUME(!f_this_misaligned);
			// }}}
		end else begin
			// {{{
			if (f_first_in_fifo && f_first_misaligned)
			begin
				if (f_next_in_fifo)
				begin
					`ASSERT(!f_next_misaligned);
				end else begin
					`ASSERT(!misaligned_request);
					`ASSERT(M_AXI_ARVALID || M_AXI_WVALID);
				end
			end

			if (misaligned_response_pending
				&& (!f_first_in_fifo || rdaddr != f_first_addr))
			begin
				if (f_fifo_fill > 1)
				begin
					`BMC_ASSERT(!f_penu_misaligned);
				end else if (f_fifo_fill == 1)
				begin
					`BMC_ASSERT(!misaligned_request);
				end
			end
			// }}}
		end
	end
	// }}}

	// Verifying unaligned registers remain the same
	// {{{
	always @(*)
	if (!f_clrfifo && f_fifo_fill != 0 && !OPT_ALIGNMENT_ERR)
	begin
		if (f_first_in_fifo && f_first_misaligned)
		begin
			if (f_next_in_fifo)
			begin
				`ASSERT(f_first_return_reg == f_next_return_reg);
			end else begin
				`ASSERT(M_AXI_ARVALID || M_AXI_WVALID);
				`ASSERT(!misaligned_request);
				`ASSERT(f_first_return_reg == { fifo_gie, ar_oreg });
			end
		end

		if (misaligned_response_pending
			&& (!f_first_in_fifo || rdaddr != f_first_addr))
		begin
			if (f_fifo_fill == 1)
			begin
				`BMC_ASSERT(M_AXI_ARVALID || M_AXI_WVALID);
				`BMC_ASSERT(!misaligned_request);
				`BMC_ASSERT(f_first_return_reg == { fifo_gie, ar_oreg });
			end else
				`BMC_ASSERT({ fifo_gie, fifo_return_reg } == f_penu_return_reg);
		end
	end
	// }}}

	always @(*)
		assert(f_fifo_fill <= (1<<LGPIPE));

	always @(*)
		assert(beats_outstanding <= (1<<LGPIPE));

	// Verifying the cpu_read_cycle flags
	// {{{
	always @(*)
	if (!r_flushing && f_fifo_fill > 0)
	begin
		if (f_first_in_fifo)
			`ASSERT(cpu_read_cycle == f_first_read_cycle);
		if (f_next_in_fifo)
			`ASSERT(cpu_read_cycle == f_next_read_cycle);

		if (// f_fifo_fill > 0 && // Redundant
			   (!f_first_in_fifo || rdaddr != f_first_addr)
			&& (!f_next_in_fifo  || rdaddr != f_next_addr))
		begin
			`BMC_ASSERT(cpu_read_cycle == f_this_read_cycle);
		end
		
		if (f_fifo_fill > 1
			&& (!f_first_in_fifo || f_penu_addr != f_first_addr)
			&& (!f_next_in_fifo  || f_penu_addr != f_next_addr))
		begin
			`BMC_ASSERT(cpu_read_cycle == f_penu_read_cycle);
		end

		if (cpu_read_cycle)
		begin
			`ASSERT(!M_AXI_AWVALID && !M_AXI_WVALID);
			`ASSERT(faxi_awr_nbursts == 0);
		end
	end
	// }}}

	// Verifying the cpu_last_reg
	// {{{
	always @(*)
	if (M_AXI_WVALID || M_AXI_ARVALID)
	begin
		if (cpu_axi_write_cycle)
		begin
			assert(cpu_last_reg == { fifo_gie, 4'hf });
		end else if (!r_flushing)
			assert(cpu_last_reg == { fifo_gie, ar_oreg });
	end else if (!f_clrfifo && f_fifo_fill > 0)
	begin
		if (cpu_axi_write_cycle)
		begin
			assert(cpu_last_reg == { fifo_gie, 4'hf });
		end else if (f_first_in_fifo && f_first_addr == f_last_written)
		begin
			assert(f_first_return_reg == cpu_last_reg);
		end

		if (!cpu_axi_write_cycle && f_next_in_fifo
					&& f_next_addr == f_last_written)
		begin
			assert(f_next_return_reg == cpu_last_reg);
		end

		if (rdaddr == f_last_written
				&& (rdaddr != f_first_addr)
				&& (rdaddr != f_next_addr))
			`BMC_ASSERT({ fifo_gie, fifo_return_reg } == cpu_last_reg);
	end
	// }}}

	// Verifying the cpu_addr_reg
	// {{{
	always @(posedge S_AXI_ACLK)
	if (i_stb)
		f_ar_areg <= f_areg;

	always @(*)
	if (o_rdbusy)
		`ASSERT(f_ar_areg == cpu_addr_reg);

	always @(*)
	if (!f_clrfifo && o_rdbusy && f_fifo_fill > 0)
	begin
		if (f_first_in_fifo && f_first_addr != f_last_written)
			assert(f_first_return_reg != cpu_addr_reg
				|| f_first_misaligned);
		if (f_next_in_fifo && f_next_addr != f_last_written)
			assert(f_next_return_reg != cpu_addr_reg
				|| f_next_misaligned);

		// If the base address register exists in the FIFO, then it
		// can't be part of any current requests.
		if ((f_first_in_fifo && (f_first_return_reg == cpu_addr_reg) && !f_first_misaligned)
			||(f_next_in_fifo && (f_next_return_reg == cpu_addr_reg) && !f_next_misaligned))
			assert(!M_AXI_WVALID && !M_AXI_ARVALID);
			
		if ((rdaddr != f_last_written || M_AXI_WVALID || M_AXI_ARVALID)
				&& !misaligned_response_pending
				&& (cpu_outstanding > (o_valid ? 1:0))
				&& (rdaddr != f_first_addr)
				&& (rdaddr != f_next_addr))
			`BMC_ASSERT({ fifo_gie, fifo_return_reg } != cpu_addr_reg);
	end

	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Exclusive access properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (M_AXI_ARVALID && M_AXI_ARREADY && M_AXI_ARLOCK)
	begin
		f_exlock_addr <= M_AXI_ARADDR;
		f_exlock_size <= M_AXI_ARSIZE;
	end

	assign	f_exlock_len = 0;
	assign	f_exlock_burst = M_AXI_AWBURST;

	always @(*)
	if (faxi_ex_state != 2'b00)
	begin
		assert(f_exlock_addr  == faxi_exreq_addr);
		assert(f_exlock_len   == faxi_exreq_len);
		assert(f_exlock_size  == faxi_exreq_size);
		assert(f_exlock_burst == faxi_exreq_burst);
	end

	always @(*)
	if (r_lock)
	begin
		if (M_AXI_ARVALID)
		begin
			assert(M_AXI_ARLOCK);
			assert(!M_AXI_AWVALID);
			assert(faxi_rdid_bursts_to_lock == 0);
		end else if (M_AXI_AWVALID)
		begin
			assert(!M_AXI_ARVALID);
			assert(M_AXI_AWLOCK);
			assert(faxi_rdid_bursts_to_lock == 0);
		end else if (faxi_ex_checklock&&(M_AXI_ARID == faxi_rd_checkid))
		begin
			assert(faxi_rdid_bursts_to_lock == faxi_rd_nbursts);
		end else
			assert(faxi_rdid_bursts_to_lock == 0);

		if (faxi_rd_nbursts > 1)
			assume(!M_AXI_RVALID || M_AXI_RRESP != EXOKAY);

		assert(faxi_rdid_bursts_to_lock    <= 1);
		assert(faxi_wrid_bursts_to_exwrite <= 1);
	end else begin
		assume(r_flushing || !M_AXI_RVALID || M_AXI_RRESP != EXOKAY);
		assert(r_flushing || faxi_rdid_bursts_to_lock    == 0);
		assert(r_flushing || faxi_wrid_bursts_to_exwrite == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire	cpu_axi_write_cycle;

	initial	f_done = 1'b0;
	always @(posedge i_clk)
	if (i_cpu_reset || r_flushing)
		f_done <= 1'b0;
	else
		f_done <= (M_AXI_RVALID && !M_AXI_RRESP[1]
			|| M_AXI_BVALID && !M_AXI_BRESP[1]) && !pending_err
				&& !misaligned_response_pending;


	localparam	FMEM_OPT_MAXDEPTH = (1<<LGPIPE);
	fmem #(
		// {{{
		.F_LGDEPTH(LGPIPE+1),
		.OPT_LOCK(OPT_LOCK),
		.OPT_AXI_LOCK(OPT_LOCK),
		.OPT_MAXDEPTH(FMEM_OPT_MAXDEPTH[LGPIPE:0])
		// }}}
	) fcheck(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_sys_reset(!S_AXI_ARESETN),
		.i_cpu_reset(i_cpu_reset),
		.i_stb(i_stb),
		.i_pipe_stalled(o_pipe_stalled),
		.i_clear_cache(1'b0),
		.i_lock(i_lock), .i_op(i_op), .i_addr({ {(32-AW){1'b0}}, i_addr }),
		.i_data(i_data), .i_oreg(i_oreg), .i_busy(o_busy),
			.i_areg(f_areg),
		.i_rdbusy(o_rdbusy), .i_valid(o_valid), .i_done(f_done),
		.i_err(o_err), .i_wreg(o_wreg), .i_result(o_result),
		.f_outstanding(cpu_outstanding),
		.f_pc(cpu_pc), .f_gie(cpu_gie), .f_read_cycle(cpu_read_cycle),
		.f_axi_write_cycle(cpu_axi_write_cycle),
		.f_last_reg(cpu_last_reg), .f_addr_reg(cpu_addr_reg)
		// }}}
	);

	always @(*)
	if (flush_request)
	begin
		`ASSERT(cpu_outstanding == 0 || o_err);
	end else if (r_flushing)
	begin
		`ASSERT(o_err || cpu_outstanding == 0);
	end else if (OPT_ALIGNMENT_ERR)
	begin
		if (!o_err)
		`ASSERT(cpu_outstanding == (beats_outstanding - flushcount)
			+ ((M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) ? 1:0)
			+ ((o_valid || f_done) ? 1:0));
		// else `ASSERT(cpu_outstanding == flushcount);
	end

	always @(*)
	if (o_err && beats_outstanding > 0)
		`ASSERT(r_flushing);

	always @(*)
	if (!o_err && cpu_outstanding > 0)
	begin
		if (cpu_axi_write_cycle)
		begin
			assert(faxi_rd_outstanding == 0);
			assert(!M_AXI_ARVALID);
			if (f_done)
			begin
				assert(!M_AXI_AWVALID && !M_AXI_WVALID
					&& faxi_awr_nbursts == 0);
				assert(!o_rdbusy);
			end else begin
				assert(faxi_awr_nbursts == (M_AXI_AWVALID ? 0:1));
				assert(o_rdbusy);
			end
		end else if (faxi_rd_outstanding > 0 || M_AXI_ARVALID
						|| o_rdbusy)
		begin
			assert(cpu_read_cycle);
		end else if (faxi_awr_nbursts > 0 || M_AXI_AWVALID || M_AXI_WVALID)
			assert(!cpu_read_cycle);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[LGPIPE:0]	cvr_writes, cvr_reads, cvr_valids;
	reg			cvr_idle;

	always @(*)
	begin
		cvr_idle = 1;
		if (i_cpu_reset || o_err || f_done)
			cvr_idle = 1'b0;
		if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
			cvr_idle = 1'b0;
		if (faxi_awr_nbursts > 0)
			cvr_idle = 1'b0;
		if (faxi_rd_outstanding > 0)
			cvr_idle = 1'b0;
	end

	initial	cvr_writes = 0;
	always @(posedge i_clk)
	if (i_cpu_reset || o_err)
		cvr_writes <= 0;
	else if (M_AXI_BVALID&& !misaligned_response_pending  && !(&cvr_writes))
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge i_clk)
	if (i_cpu_reset || o_err)
		cvr_reads <= 0;
	else if (M_AXI_RVALID && !misaligned_response_pending && !(&cvr_reads))
		cvr_reads <= cvr_reads + 1;

	initial	cvr_valids = 0;
	always @(posedge i_clk)
	if (i_cpu_reset || o_err)
		cvr_valids <= 0;
	else if (o_valid)
		cvr_valids <= cvr_valids + 1;

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
	if (cvr_idle)
	begin
		cover(cvr_writes >  3);
		cover(cvr_reads  >  3);
		cover(cvr_valids >  3);

		cover(cvr_writes > (1<<LGPIPE));
		cover(cvr_reads  > (1<<LGPIPE));
		cover(cvr_valids > (1<<LGPIPE));

		cover(cvr_writes > (1<<LGPIPE)+2);
		cover(cvr_reads  > (1<<LGPIPE)+2);
		cover(cvr_valids > (1<<LGPIPE)+2);
	end

	generate if (!OPT_ALIGNMENT_ERR)
	begin
		reg	[LGPIPE:0]	cvr_unaligned_writes,
					cvr_unaligned_reads;

		initial	cvr_writes = 0;
		always @(posedge i_clk)
		if (i_cpu_reset || o_err)
			cvr_unaligned_writes <= 0;
		else if (i_stb && i_op[0] && w_misaligned)
			cvr_unaligned_writes <= cvr_unaligned_writes + 1;

		initial	cvr_reads = 0;
		always @(posedge i_clk)
		if (i_cpu_reset || o_err)
			cvr_unaligned_reads <= 0;
		else if (i_stb && !i_op[0] && w_misaligned)
			cvr_unaligned_reads <= cvr_unaligned_reads + 1;

		always @(posedge i_clk)
		if (cvr_idle)
		begin
			cover(cvr_unaligned_writes >  3);
			cover(cvr_unaligned_reads  >  3);

			cover(cvr_unaligned_writes > (1<<LGPIPE));
			cover(cvr_unaligned_reads  > (1<<LGPIPE));
		end

		
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (!OPT_ALIGNMENT_ERR)
	begin
		if (!r_flushing && !o_err)
		`BMC_ASSERT(cpu_outstanding <= beats_outstanding
			+ ((M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) ? 1:0)
			+ ((o_valid || f_done) ? 1:0));

		if (!r_flushing && cpu_read_cycle)
		begin
		`BMC_ASSERT({ 4'h0, cpu_outstanding } >= (f_done ? 1:0)
					+ faxi_rd_outstanding[F_LGDEPTH-1:1]);
		end else if (!r_flushing)
		`BMC_ASSERT({ 4'h0, cpu_outstanding } >= (f_done ? 1:0)
					+ faxi_awr_nbursts[F_LGDEPTH-1:1]);

		if (!r_flushing && !o_err)
		assert(f_fifo_fill == beats_outstanding
			+ ((misaligned_aw_request && !misaligned_request) ? 1:0)
				+ ((M_AXI_AWVALID && !M_AXI_WVALID) ? 1:0));

		if (!r_flushing && !o_err)
		begin
			`BMC_ASSERT((cpu_outstanding == 0) == (!M_AXI_AWVALID
				&& !M_AXI_WVALID && !M_AXI_ARVALID
				&& (beats_outstanding + (f_done ? 1:0) == 0)));
		end else if (o_err)
			`BMC_ASSERT(cpu_outstanding > 0);


		if (!r_flushing && !o_err && cpu_outstanding == (f_done ? 1:0))
			`BMC_ASSERT(beats_outstanding == 0
				&& !M_AXI_AWVALID && !M_AXI_WVALID
				&& !M_AXI_ARVALID);
	end

	// Lock assumptions
	always @(*)
	if (SWAP_WSTRB)
	begin
		if (M_AXI_AWVALID) //  && M_AXI_AWLOCK)
		begin
			assert(M_AXI_AWADDR[AXILSB-1:0] == 0);
			assert(M_AXI_AWSIZE == AXILSB[2:0]);
		end

		if (M_AXI_ARVALID) //  && M_AXI_AWLOCK)
		begin
			assert(M_AXI_ARADDR[AXILSB-1:0] == 0);
			assert(M_AXI_ARSIZE == AXILSB[2:0]);
		end
	end

	always @(*)
	if (i_stb && i_op[0] && i_lock)
	begin
		assume(i_addr == f_exlock_addr);
		assume(faxi_ex_state == 2'b10);

		if (SWAP_WSTRB)
		begin
			assume(f_exlock_size == AXILSB[2:0]);
			assume(f_exlock_addr[AXILSB-1:0] == 0);
		end else
		casez(i_op[2:1])
		2'b0?: assume(f_exlock_size == 3'b010);
		2'b10: assume(f_exlock_size == 3'b001);
		2'b11: assume(f_exlock_size == 3'b000);
		endcase
	end

	always @(*)
		assume(faxi_wr_checkid == AXI_ID);
	always @(*)
		assume(faxi_rd_checkid == AXI_ID);

	always @(*)
	if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID
			|| (beats_outstanding > 0))
		assume(!i_stb || !i_lock);
	// }}}

	// Make Verilator happy w/ formal
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, faxi_exlock_return, f_return_reg,
			faxi_rdid_ckign_outstanding, faxi_rdid_ckign_nbursts,
			faxi_wr_incr, faxi_wr_size, faxi_rd_cklen,
			faxi_rd_ckaddr, faxi_rd_cksize, faxi_rd_ckincr,
			faxi_wr_addr
			};
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
// yosys -p 'read -sv axipipe.v; synth_xilinx -flatten -top axipipe'
//
//			(!LOWPOWER)	(LOWPOWER)
//	Cells:		 932		1099
//	  FDRE,FDSE	 234		 234
//	  LUT1		   0		  32
//	  LUT2		  62		  73
//	  LUT3		  46		  58
//	  LUT4		  25		  36
//	  LUT5		  75		  62
//	  LUT6		 116		 130
//	  MUXF7		  14		  55
//	  MUXF8		   6		  12
//	  RAM32X1D	   9		   9
//	Estimated LCs:	 262		 286
//
