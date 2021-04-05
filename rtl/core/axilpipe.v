////////////////////////////////////////////////////////////////////////////////
//
// Filename:	axilpipe.v
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
//
`default_nettype	none
// }}}
module	axilpipe #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		parameter	C_AXI_ADDR_WIDTH = ADDRESS_WIDTH,
		parameter	C_AXI_DATA_WIDTH = 32,
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
		// Verilator lint_off UNUSED
		// This *should* be used -- need to rewrite so that it is
		parameter [0:0]	OPT_ZERO_ON_IDLE = 1'b0,
		// Verilator lint_on  UNUSED
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
		input	wire	[31:0]			i_addr,
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
		// AXI-Lite bus interface
		// {{{
		// Writes
		// {{{
		output	reg			M_AXI_AWVALID,
		input	wire			M_AXI_AWREADY,
		output	reg	[AW-1:0]	M_AXI_AWADDR,
		output	wire	[2:0]		M_AXI_AWPROT,
		//
		output	reg			M_AXI_WVALID,
		input	wire			M_AXI_WREADY,
		output	reg	[DW-1:0]	M_AXI_WDATA,
		output	reg	[DW/8-1:0]	M_AXI_WSTRB,
		//
		input	wire			M_AXI_BVALID,
		output	wire			M_AXI_BREADY,
		input	wire [1:0]		M_AXI_BRESP,
		// }}}
		// Reads
		// {{{
		output	reg			M_AXI_ARVALID,
		input	wire			M_AXI_ARREADY,
		output	reg	[AW-1:0]	M_AXI_ARADDR,
		output	wire	[2:0]		M_AXI_ARPROT,
		//
		input	wire			M_AXI_RVALID,
		output	wire			M_AXI_RREADY,
		input	wire	[DW-1:0]	M_AXI_RDATA,
		input	wire	[1:0]		M_AXI_RRESP
		// }}}
		// }}}
		// }}}
	);

	// Declarations
	// {{{
	localparam	LGPIPE = 4;
	localparam	FIFO_WIDTH = AXILLSB+1+2+5 + 1;

	wire	i_clk = S_AXI_ACLK;

	reg	misaligned_request, w_misaligned, misaligned_aw_request,
		misaligned_response_pending, pending_err;
	reg	[C_AXI_DATA_WIDTH-1:0]	next_wdata;
	reg [C_AXI_DATA_WIDTH/8-1:0]	next_wstrb;


	reg				none_outstanding, bus_abort,
					read_abort, write_abort;
	reg	[LGPIPE:0]		beats_outstanding;
	reg				r_flushing, flush_request,
					r_pipe_stalled;
	reg	[LGPIPE:0]		flushcount, new_flushcount;
	reg	[LGPIPE:0]		wraddr, rdaddr;
	reg	[4:0]			ar_oreg, return_reg;
	reg	[1:0]			ar_op;
	reg	[AXILLSB-1:0]		adr_lsb;
	reg	[FIFO_WIDTH-1:0]	fifo_data	[0:((1<<LGPIPE)-1)];
	reg	[FIFO_WIDTH-1:0]	fifo_read_data;

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
			M_AXI_AWVALID <= 1;
		else
			M_AXI_AWVALID <= M_AXI_AWVALID && misaligned_aw_request;

		if ((write_abort && !misaligned_aw_request)
				|| (OPT_ALIGNMENT_ERR && w_misaligned))
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
			M_AXI_WVALID <= 1;
		else
			M_AXI_WVALID <= M_AXI_WVALID && misaligned_request;

		if ((write_abort && !misaligned_request)
				|| (OPT_ALIGNMENT_ERR && w_misaligned))
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
			M_AXI_ARVALID <= 1;
		else
			M_AXI_ARVALID <= M_AXI_ARVALID && misaligned_request;

		if ((read_abort && !misaligned_request)
				|| (OPT_ALIGNMENT_ERR && w_misaligned))
			M_AXI_ARVALID <= 0;
	end
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
	else if (i_stb && (!w_misaligned || !OPT_ALIGNMENT_ERR)
				&&(!bus_abort))
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
	if (!S_AXI_ARESETN || i_cpu_reset || r_flushing)
		o_rdbusy <= 0;
	else if ((i_stb && (w_misaligned && OPT_ALIGNMENT_ERR)) || bus_abort)
		o_rdbusy <= 0;
	else if (i_stb && !i_op[0])
		o_rdbusy <= !bus_abort && (!w_misaligned || !OPT_ALIGNMENT_ERR);
	else if (o_rdbusy && !M_AXI_ARVALID)
		o_rdbusy <= (beats_outstanding > (M_AXI_RVALID ? 1:0));
`ifdef	FORMAL
	reg	writing;

	always @(posedge S_AXI_ACLK)
	if (!o_busy)
		writing <= i_op[0];

	always @(*)
	begin
		if (writing)
			assert(!o_rdbusy);
		if (r_flushing)
			assert(!o_rdbusy);
		if (!o_busy)
			assert(!o_rdbusy);
	end
`endif
	// }}}

	// r_pipe_stalled
	// {{{
	// True if the CPU should expect some kind of pending response from a
	// read, and so should stall for that purpose.  False otherwise.
	generate if (OPT_ALIGNMENT_ERR)
	begin : FULL_PIPE_STALL
		// {{{
		reg	[LGPIPE:0]		beats_committed;

		always @(*)
			beats_committed = beats_outstanding
				+ ((i_stb && !w_misaligned && !o_pipe_stalled) ? 1:0)
				+ ((M_AXI_AWVALID || M_AXI_WVALID
						|| M_AXI_ARVALID) ? 1:0);

		initial	r_pipe_stalled = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || i_cpu_reset)
			r_pipe_stalled <= 0;
		else if (M_AXI_RVALID || M_AXI_BVALID)
			r_pipe_stalled <= 0;
		else // if (!r_pipe_stalled)
			r_pipe_stalled <= (beats_committed >= (1<<LGPIPE));

`ifdef	FORMAL
		always @(*)
		if (beats_outstanding + ((M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) ? 1:0) >= (1<<LGPIPE))
			assert(r_pipe_stalled || r_flushing);
		else if (beats_outstanding + (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID) < (1<<LGPIPE)-1)
			assert(!r_pipe_stalled);
`endif
		// }}}
	end else begin : PENULTIMATE_FULL_STALL
		// {{{
		reg	[LGPIPE:0]		beats_committed;

		always @(*)
		begin
			beats_committed = beats_outstanding
				+ ((i_stb && !r_pipe_stalled) ? 1:0)
				+ ((M_AXI_AWVALID || M_AXI_WVALID
						|| M_AXI_ARVALID) ? 1:0)
				- ((M_AXI_BVALID || M_AXI_RVALID) ? 1:0);
		end

		initial	r_pipe_stalled = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || i_cpu_reset || bus_abort)
			r_pipe_stalled <= 0;
		else begin
			r_pipe_stalled <= 0;
			if (i_stb && w_misaligned && !o_pipe_stalled)
				r_pipe_stalled <= 1'b1;
			if (misaligned_request && (M_AXI_WVALID && !M_AXI_WREADY))
				r_pipe_stalled <= 1'b1;
			if (misaligned_request && (M_AXI_ARVALID && !M_AXI_ARREADY))
				r_pipe_stalled <= 1'b1;
			if (misaligned_aw_request && (M_AXI_AWVALID && !M_AXI_AWREADY))
				r_pipe_stalled <= 1'b1;
			if (beats_committed >= (1<<LGPIPE)-2)
				r_pipe_stalled <= 1'b1;
		end

`ifdef	FORMAL
		always @(*)
		if (!r_flushing && (beats_outstanding
				+ (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
				+ (misaligned_aw_request || misaligned_request)
				>= (1<<LGPIPE)))
			assert(r_pipe_stalled);
		else if (!r_flushing && !o_err
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
`endif
	// }}}

	// Count the number of outstanding beats
	// {{{
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
	end else if (i_cpu_reset || bus_abort || (OPT_ALIGNMENT_ERR && i_stb && w_misaligned))
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
			assert(!flush_request);
		else
			assert(flush_request == (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID));
		if (r_flushing && !flush_request)
		begin
			assert(!misaligned_request);
			assert(!misaligned_aw_request);
		end

		if (flush_request)
			assert(flushcount == beats_outstanding + 1
				+ ((misaligned_request
				|| misaligned_aw_request) ? 1:0));
		// else if (faxil_rd_outstanding > 0 || M_AXI_ARVALID)
		else if (r_flushing)
			assert(beats_outstanding == flushcount);
		else
			assert(beats_outstanding >= flushcount);
	end
`endif
	// }}}

	// Bus addressing
	// {{{
	initial	M_AXI_AWADDR = 0;
	always @(posedge i_clk)
	if (i_stb)
		M_AXI_AWADDR <= i_addr[C_AXI_ADDR_WIDTH-1:0];
	else if (!OPT_ALIGNMENT_ERR
		&& ((M_AXI_AWVALID && M_AXI_AWREADY) // && misaligned_aw_request
		|| (M_AXI_ARVALID && M_AXI_ARREADY))) // && misaligned_request))
	begin
		M_AXI_AWADDR <= M_AXI_AWADDR + 4;
		M_AXI_AWADDR[AXILLSB-1:0] <= 0;
	end

	always @(*)
		M_AXI_ARADDR = M_AXI_AWADDR;
	// }}}

	// Is this request misaligned?
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

	// WDATA and WSTRB
	// {{{
	initial	M_AXI_WDATA = 0;
	initial	M_AXI_WSTRB = 0;
	initial	next_wdata  = 0;
	initial	next_wstrb  = 0;
	always @(posedge i_clk)
	if (i_stb)
	begin
		casez(i_op[2:1])
		2'b10: { next_wdata, M_AXI_WDATA }
			<= { (2*C_AXI_DATA_WIDTH/16){ i_data[15:0] } };
		2'b11: { next_wdata, M_AXI_WDATA }
			<= { (2*C_AXI_DATA_WIDTH/8){  i_data[7:0] } };
		default: { next_wdata, M_AXI_WDATA }
			<= { (2*C_AXI_DATA_WIDTH/32){ i_data } };
		endcase

		casez(i_op[2:1])
		2'b0?: { next_wstrb, M_AXI_WSTRB }
			<= { {(C_AXI_DATA_WIDTH/4-4){1'b0}}, 4'b1111} << i_addr[AXILLSB-1:0];
		2'b10: { next_wstrb, M_AXI_WSTRB }
			<= { {(C_AXI_DATA_WIDTH/4-4){1'b0}}, 4'b0011} << i_addr[AXILLSB-1:0];
		2'b11: { next_wstrb, M_AXI_WSTRB }
			<= { {(C_AXI_DATA_WIDTH/4-4){1'b0}}, 4'b0001} << i_addr[AXILLSB-1:0];
		endcase

		if (OPT_ALIGNMENT_ERR)
			{ next_wstrb, next_wdata } <= 0;

	end else if ((M_AXI_WVALID && M_AXI_WREADY)
			|| (M_AXI_ARVALID && M_AXI_ARREADY))
	begin
		M_AXI_WDATA <= OPT_ALIGNMENT_ERR ? 0 : next_wdata;
		M_AXI_WSTRB <= OPT_ALIGNMENT_ERR ? 0 : next_wstrb;
		{ next_wdata, next_wstrb } <= 0;
	end
	// }}}

	generate if (OPT_ALIGNMENT_ERR)
	begin
		// {{{
		// Generate an error on any misaligned request
		always @(*)
		begin
			misaligned_request = 1'b0;

			misaligned_aw_request = 1'b0;
			pending_err = 1'b0;
		end
		// }}}
	end else begin
		// {{{
		initial	misaligned_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset && !bus_abort)
			misaligned_request <= w_misaligned;
		else if ((M_AXI_WVALID && M_AXI_WREADY)
					|| (M_AXI_ARVALID && M_AXI_ARREADY))
			misaligned_request <= 1'b0;
	
		initial	misaligned_aw_request = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN)
			misaligned_aw_request <= 0;
		else if (i_stb && !o_err && !i_cpu_reset && !write_abort)
			misaligned_aw_request <= w_misaligned && i_op[0];
		else if (M_AXI_AWREADY)
			misaligned_aw_request <= 1'b0;

		initial	pending_err = 1'b0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN || i_stb || (!M_AXI_BREADY && !M_AXI_RREADY)
				|| o_err || r_flushing || i_cpu_reset)
			pending_err <= 1'b0;
		else if ((M_AXI_BVALID && M_AXI_BRESP[1])
				|| (M_AXI_RVALID && M_AXI_RRESP[1]))
			pending_err <= 1'b1;

`ifdef	FORMAL
		always @(*)
		if (pending_err)
			assert(r_flushing || o_err);
`endif
		// }}}
	end endgenerate
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
	if (!S_AXI_ARESETN || bus_abort || flush_request)
		wraddr <= 0;
	else if ((M_AXI_ARVALID && M_AXI_ARREADY) || (M_AXI_WVALID && M_AXI_WREADY))
		wraddr <= wraddr + 1;
	// }}}

	// rdaddr
	// {{{
	initial	rdaddr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || bus_abort || r_flushing)
		rdaddr <= 0;
	else if((M_AXI_RVALID && M_AXI_RREADY)||(M_AXI_BVALID && M_AXI_BREADY))
		rdaddr <= rdaddr + 1;
	// }}}

	// ar_oreg, ar_op, adr_lsb
	// {{{
	always @(posedge S_AXI_ACLK)
	if (i_stb)
		{ ar_oreg, ar_op, adr_lsb } <= { i_oreg, i_op[2:1], i_addr[AXILLSB-1:0] };
	else if ((M_AXI_ARVALID && M_AXI_ARREADY)||(M_AXI_WVALID && M_AXI_WREADY))
		adr_lsb <= 0;
	// }}}

	// fifo_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if ((M_AXI_ARVALID && M_AXI_ARREADY) || (M_AXI_WVALID && M_AXI_WREADY))
		fifo_data[wraddr[LGPIPE-1:0]] <= { M_AXI_ARVALID, ar_oreg, ar_op,
				misaligned_request, M_AXI_ARADDR[AXILLSB-1:0] };

	always @(*)
		fifo_read_data = fifo_data[rdaddr[LGPIPE-1:0]];
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read return generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
		return_reg = fifo_read_data[AXILLSB+3 +: 5];

	always @(*)
	if (OPT_ALIGNMENT_ERR)
		misaligned_response_pending = 0;
	else begin
		misaligned_response_pending = fifo_read_data[AXILLSB];
		if (wraddr == rdaddr)
			misaligned_response_pending = 0;
	end

	// o_valid
	// {{{
	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || r_flushing || i_cpu_reset)
		o_valid <= 1'b0;
	else if (OPT_ALIGNMENT_ERR && i_stb && w_misaligned)
		o_valid <= 1'b0;
	else
		o_valid <= M_AXI_RVALID && !M_AXI_RRESP[1] // && !pending_err
				&& !misaligned_response_pending;
	// }}}

	// o_wreg
	// {{{
	always @(posedge i_clk)
		o_wreg <= return_reg;
	// }}}

	generate if (OPT_ALIGNMENT_ERR)
	begin : RETURN_DATA
		// {{{
		// No realignment of results required
		reg	[C_AXI_DATA_WIDTH-1:0]	wide_return;

		always @(*)
			wide_return = M_AXI_RDATA >> (fifo_read_data[AXILLSB-1:0] * 8);

		always @(posedge i_clk)
		begin
			o_result <= wide_return[31:0];

			case(fifo_read_data[AXILLSB+1 +: 2])
			2'b10: o_result[31:16] <= 0;
			2'b11: o_result[31: 8] <= 0;
			default: begin end
			endcase
		end

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	wide_unused;

		if (C_AXI_DATA_WIDTH > 32)
		begin : WIDE_WIDTH_UNUSED
			assign	wide_unused = &{ 1'b0,
				wide_return[C_AXI_DATA_WIDTH-1:32] };
		end else begin : WIDE_WIDTH_NOT_UNUSED
			assign	wide_unused = 1'b0;
		end
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end else begin : REALIGN_RETURN_DATA
		// {{{
		// Need to realign any returning data
		reg	[C_AXI_DATA_WIDTH-1:0]	wide_return, misdata, redata,
						return_data;
		reg	[AXILLSB-1:0]		lastshift;

		always @(*)
			redata = M_AXI_RDATA >> (8*fifo_read_data[AXILLSB-1:0]);

		always @(posedge i_clk)
		if (M_AXI_RVALID)
		begin
			misdata <= 0;
			lastshift <= (1<<AXILLSB)
					- fifo_read_data[AXILLSB-1:0];

			if (misaligned_response_pending)
				misdata <= redata;
		end

		always @(*)
		if (!misaligned_response_pending)
			return_data = (o_result << (8*lastshift)) | misdata;
		else
			return_data = redata;

		always @(posedge i_clk)
		begin
			o_result <= return_data[31:0];

			if (fifo_read_data[AXILLSB+2])
				o_result[31:16] <= 0;
			if (fifo_read_data[AXILLSB+2:AXILLSB+1])
				o_result[15:8] <= 0;
		end

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	wide_unused;

		if (C_AXI_DATA_WIDTH > 32)
		begin : WIDE_WIDTH_UNUSED
			assign	wide_unused = &{ 1'b0,
				wide_return[C_AXI_DATA_WIDTH-1:32] };
		end else begin : WIDE_WIDTH_NOT_UNUSED
			assign	wide_unused = 1'b0;
		end
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end endgenerate

	// o_err - report bus errors back to the CPU
	// {{{
	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (r_flushing || i_cpu_reset || o_err)
		o_err <= 1'b0;
	else if (OPT_ALIGNMENT_ERR && i_stb && w_misaligned)
		o_err <= 1'b1;
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

	// AxPROT -- CPU data
	// {{{
	assign	M_AXI_AWPROT = 3'b000;
	assign	M_AXI_ARPROT = 3'b000;

	// }}}
	// }}}
	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, M_AXI_RRESP[0], M_AXI_BRESP[0], i_lock,
			// i_addr[31:C_AXI_ADDR_WIDTH],
			(&i_addr),
			pending_err, adr_lsb,
			none_outstanding };
	// verilator lint_on  UNUSED
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
	localparam	F_LGDEPTH = LGPIPE+1;

	wire	[F_LGDEPTH-1:0]	faxil_rd_outstanding, faxil_wr_outstanding,
				faxil_awr_outstanding;
	reg	[LGPIPE:0]	f_fifo_fill;

	reg		f_clrfifo, f_wrfifo, f_rdfifo;
	reg	[1:0]	f_fsmfifo;
	(* anyconst *)	reg	[LGPIPE:0]		f_first_addr;
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

	(* anyseq *) reg [4:0]	f_areg;
	reg			f_done;


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
	// Bus property checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
		f_fifo_fill = wraddr - rdaddr;

	always @(*)
	begin
		if (misaligned_request)
			`ASSERT(M_AXI_WVALID || M_AXI_ARVALID);
		if (misaligned_aw_request)
			`ASSERT(M_AXI_AWVALID);

		if (M_AXI_ARVALID || faxil_rd_outstanding > 0)
		begin
			assert(faxil_wr_outstanding == 0
				&& faxil_awr_outstanding == 0);
			assert(!M_AXI_AWVALID);
			assert(!M_AXI_WVALID);
		end

		if (faxil_wr_outstanding > 0 || faxil_awr_outstanding > 0
			|| M_AXI_AWVALID || M_AXI_WVALID)
		begin
			assert(faxil_rd_outstanding == 0);
			assert(!M_AXI_ARVALID);
		end

		// Rule: Only one of the two VALID's may be valid, never both
		`ASSERT(!M_AXI_RVALID || (!M_AXI_AWVALID && !M_AXI_WVALID));

		assert(beats_outstanding
			+ ((misaligned_request && !misaligned_aw_request && M_AXI_WVALID) ? 1:0)
			+ ((M_AXI_WVALID && !M_AXI_AWVALID) ? 1:0)
			== faxil_rd_outstanding + faxil_awr_outstanding);

		assert(beats_outstanding
			+ ((misaligned_aw_request && !misaligned_request) ? 1:0)
			+ ((M_AXI_AWVALID && !M_AXI_WVALID) ? 1:0)
			== faxil_rd_outstanding + faxil_wr_outstanding);

		if (OPT_ALIGNMENT_ERR && !r_flushing
				&& (faxil_rd_outstanding > 0 || M_AXI_ARVALID))
			assert(f_fifo_fill == faxil_rd_outstanding);
		else if (OPT_ALIGNMENT_ERR && !r_flushing
				&& (faxil_wr_outstanding > 0 || M_AXI_WVALID))
			assert(f_fifo_fill == faxil_wr_outstanding);

		if (faxil_rd_outstanding == 0 && faxil_wr_outstanding == 0)
			assert(f_fifo_fill == 0);
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
	if (o_busy && !misaligned_request && OPT_ZERO_ON_IDLE)
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
			`ASSERT(!o_err);
		else if ($past(M_AXI_BVALID && M_AXI_BRESP[1]))
			`ASSERT(o_err);
		else if ($past(M_AXI_RVALID && M_AXI_RRESP[1]))
			`ASSERT(o_err);
		else if (OPT_ALIGNMENT_ERR && $past(i_stb && w_misaligned))
			`ASSERT(o_err);
		else if (!$past(pending_err))
			`ASSERT(!o_err);
	end
	// }}}

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_cpu_reset))&&($past(i_stb)))
	begin
		// On a write, assert o_wb_we should be true
		assert($past(i_op[0] && !o_err
			&& (!M_AXI_BVALID || !M_AXI_BRESP[1])
			&& (!OPT_ALIGNMENT_ERR || !w_misaligned))
				== (M_AXI_AWVALID && M_AXI_WVALID));
	end

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_cpu_reset)))
		`ASSUME(!i_stb);

	always @(*)
	if (!S_AXI_ARESETN)
		`ASSUME(i_cpu_reset);

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

		f_return_reg = return_reg;

		f_first_return_reg = f_first_data[AXILLSB+3 +: 5];
		f_next_return_reg  = f_next_data[AXILLSB+3 +: 5];
		f_penu_return_reg  = f_penu_data[AXILLSB+3 +: 5];

		f_first_misaligned = f_first_data[AXILLSB];
		f_next_misaligned = f_next_data[AXILLSB];
		f_this_misaligned = fifo_read_data[AXILLSB];
		f_penu_misaligned = f_penu_data[AXILLSB];

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
			`ASSERT(f_first_data == fifo_data[f_first_addr]);
		if (f_next_in_fifo)
			`ASSERT(f_next_data == fifo_data[f_next_addr]);
	end

	always @(posedge S_AXI_ACLK)
	if (f_wrfifo && wraddr == f_first_addr)
		f_first_data <= { M_AXI_ARVALID, ar_oreg, ar_op, misaligned_request, M_AXI_ARADDR[AXILLSB-1:0] };

	always @(posedge S_AXI_ACLK)
	if (f_wrfifo && wraddr == f_next_addr)
		f_next_data <= { M_AXI_ARVALID, ar_oreg, ar_op, misaligned_request, M_AXI_ARADDR[AXILLSB-1:0] };

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
		end
		// }}}
	endcase
	// }}}

	// { ar_oreg, ar_op, misaligned_request, M_AXI_ARADDR[AXILLSB-1:0] };

	// cpu_gie checks
	// {{{
	always @(*)
	if (M_AXI_ARVALID)
		`ASSERT(cpu_gie == ar_oreg[4]);

	always @(*)
	if (!f_clrfifo && f_fifo_fill != 0)
	begin
		if (M_AXI_ARVALID || M_AXI_WVALID || M_AXI_AWVALID)
			`ASSERT(cpu_gie == ar_oreg[4]);

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
			`ASSERT(f_this_misaligned || !cpu_read_cycle || !(&f_return_reg[3:1]));
		else if (f_fifo_fill > 0 && !M_AXI_ARVALID)
			`ASSERT(f_this_misaligned || !cpu_read_cycle || cpu_pc == (&f_return_reg[3:1]));

		if ((!f_first_in_fifo || rdaddr != f_first_addr)
			&& (!f_next_in_fifo || rdaddr != f_next_addr)
			&& cpu_read_cycle)
		begin
			if (M_AXI_ARVALID) // && (&ar_oreg[3:1]))
				`ASSUME(!(&f_return_reg[3:1]));
			else if (rdaddr != f_last_written)
				`ASSUME(!(&f_return_reg[3:1]));
			else if (!M_AXI_ARVALID && !o_err)
				`ASSUME(cpu_pc == (&f_return_reg[3:1])); // Not last written
		end

		if (f_first_in_fifo && cpu_read_cycle)
		begin
			if (!cpu_pc || M_AXI_ARVALID
					|| (f_last_written != f_first_addr))
				`ASSERT(f_first_misaligned || !cpu_read_cycle || !(&f_first_return_reg[3:1]));
			else if (!M_AXI_ARVALID && !o_err)
				`ASSERT(&f_first_return_reg[3:1]);
		end

		if (f_next_in_fifo && cpu_read_cycle)
		begin
			if (!cpu_pc || M_AXI_ARVALID
					|| (f_last_written != f_next_addr))
				`ASSERT(f_next_misaligned || !(&f_next_return_reg[3:1]));
			else if (!M_AXI_ARVALID && !o_err)
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
		assert(!M_AXI_AWVALID && !M_AXI_WVALID && faxil_awr_outstanding == 0);

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
					`ASSERT(!f_next_misaligned);
				else begin
					`ASSERT(!misaligned_request);
					`ASSERT(M_AXI_ARVALID || M_AXI_WVALID);
				end
			end

			if (misaligned_response_pending
				&& (!f_first_in_fifo || rdaddr != f_first_addr))
			begin
				if (f_fifo_fill > 1)
					`BMC_ASSERT(!f_penu_misaligned);
				else if (f_fifo_fill == 1)
					`BMC_ASSERT(!misaligned_request);
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
				`ASSERT(f_first_return_reg == ar_oreg);
			end
		end

		if (misaligned_response_pending
			&& (!f_first_in_fifo || rdaddr != f_first_addr))
		begin
			if (f_fifo_fill == 1)
			begin
				`BMC_ASSERT(M_AXI_ARVALID || M_AXI_WVALID);
				`BMC_ASSERT(!misaligned_request);
				`BMC_ASSERT(f_first_return_reg == ar_oreg);
			end else
				`BMC_ASSERT(return_reg == f_penu_return_reg);
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
			`ASSERT(faxil_awr_outstanding == 0);
			`ASSERT(faxil_wr_outstanding == 0);
		end
	end
	// }}}

	// Verifying the cpu_last_reg
	// {{{
	always @(*)
	if (M_AXI_WVALID || M_AXI_ARVALID)
		assert(cpu_last_reg == ar_oreg);
	else if (!f_clrfifo && f_fifo_fill > 0)
	begin
		if (f_first_in_fifo && f_first_addr == f_last_written)
			assert(f_first_return_reg == cpu_last_reg);
		if (f_next_in_fifo && f_next_addr == f_last_written)
			assert(f_next_return_reg == cpu_last_reg);
		if (rdaddr == f_last_written
				&& (rdaddr != f_first_addr)
				&& (rdaddr != f_next_addr))
			`BMC_ASSERT(return_reg == cpu_last_reg);
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
			`BMC_ASSERT(return_reg != cpu_addr_reg);
	end

	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	f_done = 1'b0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || r_flushing || i_cpu_reset)
		f_done <= 1'b0;
	else
		f_done <= (M_AXI_RVALID && !M_AXI_RRESP[1]
			|| M_AXI_BVALID && !M_AXI_BRESP[1]) && !pending_err
				&& !misaligned_response_pending;


	fmem #(
		// {{{
		.F_LGDEPTH(LGPIPE+1), .OPT_MAXDEPTH(1<<LGPIPE)
		// }}}
	) fcheck(
		// {{{
		.i_clk(S_AXI_ACLK),
		.i_bus_reset(!S_AXI_ARESETN),
		.i_cpu_reset(i_cpu_reset),
		.i_stb(i_stb),
		.i_pipe_stalled(o_pipe_stalled),
		.i_clear_cache(1'b0),
		.i_lock(i_lock), .i_op(i_op), .i_addr(i_addr),
		.i_data(i_data), .i_oreg(i_oreg), .i_busy(o_busy),
			.i_areg(f_areg),
		.i_rdbusy(o_rdbusy), .i_valid(o_valid), .i_done(f_done),
		.i_err(o_err), .i_wreg(o_wreg), .i_result(o_result),
		.f_outstanding(cpu_outstanding),
		.f_pc(cpu_pc), .f_gie(cpu_gie), .f_read_cycle(cpu_read_cycle),
		.f_last_reg(cpu_last_reg), .f_addr_reg(cpu_addr_reg)
		// }}}
	);

	always @(*)
	if (flush_request)
		`ASSERT(cpu_outstanding == 0 || o_err);
	else if (r_flushing)
		`ASSERT(o_err || cpu_outstanding == 0);
	else if (OPT_ALIGNMENT_ERR)
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
		if (faxil_rd_outstanding > 0 || M_AXI_ARVALID || o_rdbusy)
			assert(cpu_read_cycle);
		else if (faxil_awr_outstanding > 0 || faxil_wr_outstanding > 0
				|| M_AXI_AWVALID || M_AXI_WVALID)
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
		if (!S_AXI_ARESETN || i_cpu_reset || o_err || f_done)
			cvr_idle = 1'b0;
		if (M_AXI_AWVALID || M_AXI_WVALID || M_AXI_ARVALID)
			cvr_idle = 1'b0;
		if (faxil_awr_outstanding > 0)
			cvr_idle = 1'b0;
		if (faxil_wr_outstanding > 0)
			cvr_idle = 1'b0;
		if (faxil_rd_outstanding > 0)
			cvr_idle = 1'b0;
	end

	initial	cvr_writes = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || i_cpu_reset || o_err)
		cvr_writes <= 0;
	else if (M_AXI_BVALID&& !misaligned_response_pending  && !(&cvr_writes))
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || i_cpu_reset || o_err)
		cvr_reads <= 0;
	else if (M_AXI_RVALID && !misaligned_response_pending && !(&cvr_reads))
		cvr_reads <= cvr_reads + 1;

	initial	cvr_valids = 0;
	always @(posedge i_clk)
	if (!S_AXI_ARESETN || i_cpu_reset || o_err)
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
		if (!S_AXI_ARESETN || i_cpu_reset || o_err)
			cvr_unaligned_writes <= 0;
		else if (i_stb && i_op[0] && w_misaligned)
			cvr_unaligned_writes <= cvr_unaligned_writes + 1;

		initial	cvr_reads = 0;
		always @(posedge i_clk)
		if (!S_AXI_ARESETN || i_cpu_reset || o_err)
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
		`BMC_ASSERT(cpu_outstanding >= (f_done ? 1:0)
					+ faxil_rd_outstanding[F_LGDEPTH-1:1]);
		else if (!r_flushing)
		`BMC_ASSERT(cpu_outstanding >= (f_done ? 1:0)
					+ faxil_wr_outstanding[F_LGDEPTH-1:1]);

		if (!r_flushing && !o_err)
		assert(f_fifo_fill == beats_outstanding
			+ ((misaligned_aw_request && !misaligned_request) ? 1:0)
				+ (M_AXI_AWVALID && !M_AXI_WVALID));

		if (!r_flushing && !o_err)
			`BMC_ASSERT((cpu_outstanding == 0) == (!M_AXI_AWVALID
				&& !M_AXI_WVALID && !M_AXI_ARVALID
				&& (beats_outstanding + (f_done ? 1:0) == 0)));
		else if (o_err)
			`BMC_ASSERT(cpu_outstanding > 0);


		if (!r_flushing && !o_err && cpu_outstanding == (f_done ? 1:0))
			`BMC_ASSERT(beats_outstanding == 0
				&& !M_AXI_AWVALID && !M_AXI_WVALID
				&& !M_AXI_ARVALID);
	end

	// }}}
`endif
// }}}
endmodule
