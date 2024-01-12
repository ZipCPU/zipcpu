////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/axilscope.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is a generic/library routine for providing a bus accessed
//	'scope' or (perhaps more appropriately) a bus accessed logic analyzer.
//	The general operation is such that this 'scope' can record and report
//	on any 32 bit value transiting through the FPGA.  Once started and
//	reset, the scope records a copy of the input data every time the clock
//	ticks with the circuit enabled.  That is, it records these values up
//	until the trigger.  Once the trigger goes high, the scope will record
//	for br_holdoff more counts before stopping.  Values may then be read
//	from the buffer, oldest to most recent.  After reading, the scope may
//	then be reset for another run.
//
//	In general, therefore, operation happens in this fashion:
//		1. A reset is issued.
//		2. Recording starts, in a circular buffer, and continues until
//		3. The trigger line is asserted.
//			The scope registers the asserted trigger by setting
//			the 'o_triggered' output flag.
//		4. A counter then ticks until the last value is written
//			The scope registers that it has stopped recording by
//			setting the 'o_stopped' output flag.
//		5. The scope recording is then paused until the next reset.
//		6. While stopped, the CPU can read the data from the scope
//		7. -- oldest to most recent
//		8. -- one value per i_rd&i_data_clk
//		9. Writes to the data register reset the address to the
//			beginning of the buffer
//
//	Although the data width DW is parameterized, it is not very changable,
//	since the width is tied to the width of the data bus, as is the
//	control word.  Therefore changing the data width would require changing
//	the interface.  It's doable, but it would be a change to the interface.
//
//	The SYNCHRONOUS parameter turns on and off meta-stability
//	synchronization.  Ideally a wishbone scope able to handle one or two
//	clocks would have a changing number of ports as this SYNCHRONOUS
//	parameter changed.  Other than running another script to modify
//	this, I don't know how to do that so ... we'll just leave it running
//	off of two clocks or not.
//
//
//	Internal to this routine, registers and wires are named with one of the
//	following prefixes:
//
//	i_	An input port to the routine
//	o_	An output port of the routine
//	br_	A register, controlled by the bus clock
//	dr_	A register, controlled by the data clock
//	bw_	A wire/net, controlled by the bus clock
//	dw_	A wire/net, controlled by the data clock
//
//	And, of course, since AXI wants to be particular about their port
//	naming conventions, anything beginning with
//
//	S_AXI_
//
//	is a signal associated with this function as an AXI slave.
//	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module axilscope #(
		// {{{
		parameter [4:0]	LGMEM = 5'd10,
		parameter	SYNCHRONOUS=1,
		parameter	HOLDOFFBITS = 20,
		parameter [(HOLDOFFBITS-1):0]	DEFAULT_HOLDOFF
						= ((1<<(LGMEM-1))-4),
		localparam	BUSW = 32,
		//
		// Width of S_AXI data bus
		localparam integer C_S_AXI_DATA_WIDTH	= 32,
		// Width of S_AXI address bus
		parameter integer C_S_AXI_ADDR_WIDTH	= 3,
		localparam	ADDR_LSBS = $clog2(C_S_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input wire	i_data_clk, // The data clock, can be set to ACLK
		input wire	i_ce,	// = '1' when recordable data is present
		input wire	i_trigger,// = '1' when interesting event hapns
		input wire	[31:0]	i_data,
		output	wire	o_interrupt,	// ='1' when scope has stopped
		//
		// Global Clock Signal
		input wire  S_AXI_ACLK,
		// Global Reset Signal. This Signal is Active LOW
		input wire  S_AXI_ARESETN,
		// Write address (issued by master, acceped by Slave)
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_AWADDR,
		// Write channel Protection type. This signal indicates the
    		// privilege and security level of the transaction, and whether
    		// the transaction is a data access or an instruction access.
		input wire [2 : 0] S_AXI_AWPROT,
		// Write address valid. This signal indicates that the master
    		// signaling valid write address and control information.
		input wire  S_AXI_AWVALID,
		// Write address ready. This signal indicates that the slave
    		// is ready to accept an address and associated control signals.
		output wire  S_AXI_AWREADY,
		// Write data (issued by master, acceped by Slave) 
		input wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_WDATA,
		// Write strobes. This signal indicates which byte lanes hold
    		// valid data. There is one write strobe bit for each eight
    		// bits of the write data bus.    
		input wire [(C_S_AXI_DATA_WIDTH/8)-1 : 0] S_AXI_WSTRB,
		// Write valid. This signal indicates that valid write
    		// data and strobes are available.
		input wire  S_AXI_WVALID,
		// Write ready. This signal indicates that the slave
    		// can accept the write data.
		output wire  S_AXI_WREADY,
		// Write response. This signal indicates the status
    		// of the write transaction.
		output wire [1 : 0] S_AXI_BRESP,
		// Write response valid. This signal indicates that the channel
    		// is signaling a valid write response.
		output wire  S_AXI_BVALID,
		// Response ready. This signal indicates that the master
    		// can accept a write response.
		input wire  S_AXI_BREADY,
		// Read address (issued by master, acceped by Slave)
		input wire [C_S_AXI_ADDR_WIDTH-1 : 0] S_AXI_ARADDR,
		// Protection type. This signal indicates the privilege
    		// and security level of the transaction, and whether the
    		// transaction is a data access or an instruction access.
		input wire [2 : 0] S_AXI_ARPROT,
		// Read address valid. This signal indicates that the channel
    		// is signaling valid read address and control information.
		input wire  S_AXI_ARVALID,
		// Read address ready. This signal indicates that the slave is
    		// ready to accept an address and associated control signals.
		output wire  S_AXI_ARREADY,
		// Read data (issued by slave)
		output wire [C_S_AXI_DATA_WIDTH-1 : 0] S_AXI_RDATA,
		// Read response. This signal indicates the status of the
    		// read transfer.
		output wire [1 : 0] S_AXI_RRESP,
		// Read valid. This signal indicates that the channel is
    		// signaling the required read data.
		output wire  S_AXI_RVALID,
		// Read ready. This signal indicates that the master can
    		// accept the read data and response information.
		input wire  S_AXI_RREADY
		// }}}
	);

	// Signal declarations
	// {{{
	// AXI4LITE signals
	reg [C_S_AXI_ADDR_WIDTH-1 : 0] 	axi_awaddr;
	reg			 	axi_awready;
	reg				axi_wready;
	reg [C_S_AXI_DATA_WIDTH-1:0]	axi_wdata;
	// reg		[1 : 0] 	axi_bresp;
	reg 				axi_bvalid;
	// reg [C_S_AXI_ADDR_WIDTH-1 : 0] 	axi_araddr;
	reg 			 	axi_arready;
	// reg		 [1 : 0] 	axi_rresp;

	// Pseudo bus signals
	wire			bus_clock;
	reg			read_from_data;
	wire			write_stb;
	wire			write_to_control;
	reg	[1:0]	read_address;
	// reg			read_address;
	wire	[31:0]		i_bus_data;
	reg	[31:0]		o_bus_data;

	//
	reg	[(LGMEM-1):0]	raddr, waddr;
	reg	[(BUSW-1):0]	mem[0:((1<<LGMEM)-1)];

	wire			bw_reset_request, bw_manual_trigger,
				bw_disable_trigger, bw_reset_complete;
	reg	[2:0]		br_config;
	reg [(HOLDOFFBITS-1):0]	br_holdoff;
	wire			dw_reset, dw_manual_trigger, dw_disable_trigger;
	reg			dr_triggered, dr_primed;
	wire			dw_trigger;
	reg			dr_stopped;

	(* ASYNC_REG="TRUE" *) reg	[(HOLDOFFBITS-1):0]	counter;

	localparam	STOPDELAY = 1;	// Calibrated value--don't change this
	wire	[(BUSW-1):0]	wr_piped_data;
	wire			bw_stopped, bw_triggered, bw_primed;
	reg	[(LGMEM-1):0]	this_addr;
	reg	[31:0]		nxt_mem;
	wire	[19:0]		full_holdoff;
	wire	[4:0]		bw_lgmem;
	reg			br_level_interrupt;
`ifdef	FORMAL
	(* gclk *) reg	gbl_clk;
	reg	f_past_valid_bus, f_past_valid_gbl, f_past_valid_data;
`endif	// FORMAL
	wire		i_reset;
	reg		valid_write_data, valid_write_address,
			write_response_stall;
	reg	[1:0]	rvalid;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Decode and handle the bus signaling in a (somewhat) portable manner
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	//
	assign	i_reset = !S_AXI_ARESETN;

	always @(*)
	begin
		valid_write_address = (S_AXI_AWVALID || !S_AXI_AWREADY);
		valid_write_data    = (S_AXI_WVALID  || !S_AXI_WREADY);
		write_response_stall= (S_AXI_BVALID  && !S_AXI_BREADY);
	end

	initial	axi_awready = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_awready <= 1'b1;
	else if (write_response_stall)
		axi_awready <= !valid_write_address;
	else if (valid_write_data)
		axi_awready <= 1'b1;
	else
		axi_awready <= !valid_write_address;

	initial	axi_wready = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		axi_wready <= 1'b1;
	else if (write_response_stall)
		axi_wready <= !valid_write_data;
	else if (valid_write_address)
		axi_wready <= 1'b1;
	else
		axi_wready <= !valid_write_data;

	always @(posedge S_AXI_ACLK)
	if (S_AXI_WREADY)
		axi_wdata <= S_AXI_WDATA;

	assign	S_AXI_AWREADY = axi_awready;
	assign	S_AXI_WREADY  = axi_wready;

	always @(posedge S_AXI_ACLK)
	if ((S_AXI_AWVALID)&&(S_AXI_AWREADY))
		axi_awaddr <= S_AXI_AWADDR;

	initial	axi_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axi_bvalid <= 0;
	else if (write_stb)
		axi_bvalid <= 1'b1;
	else if (S_AXI_BREADY)
		axi_bvalid <= 1'b0;

	assign	S_AXI_BRESP = 2'b00;	// An 'OKAY' response
	assign	S_AXI_BVALID= axi_bvalid;

	assign	write_stb = valid_write_data && valid_write_address
				&& !write_response_stall;

	initial	axi_arready = 1'b1;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axi_arready <= 1'b1;
	else if ((&rvalid) && (S_AXI_RVALID && !S_AXI_RREADY))
		axi_arready <= axi_arready && !S_AXI_ARVALID;
	else
		axi_arready <= 1'b1;

	// always @(posedge S_AXI_ACLK)
	// if (axi_arready && S_AXI_ARVALID)
	//	axi_araddr <= S_AXI_ARADDR;

	assign	S_AXI_ARREADY = axi_arready;

	initial	rvalid = 2'b00;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		rvalid <= 2'b00;
	else begin
		if (!rvalid[0] || !rvalid[1] || S_AXI_RREADY)
			rvalid[0] <= S_AXI_ARVALID || !axi_arready;

		if (rvalid[0])
			rvalid[1] <= 1'b1;
		else if (S_AXI_RREADY)
			rvalid[1] <= 1'b0;
	end

	assign	S_AXI_RVALID = rvalid[1];
	assign	S_AXI_RRESP  = 2'b00;


	///////////////////////////////////////////////////
	//
	// Final simplification of the AXI code
	//
	///////////////////////////////////////////////////
	//
	// Now that we've provided all of the bus signaling
	// above, can we make any sense of it?
	//
	// The following wires are here to provide some
	// simplification of the complex bus protocol.  In
	// particular, are we reading or writing during this
	// clock?  The two *should* be mutually exclusive
	// (i.e., you *shouldn't* be able to both read and
	// write on the same clock) ... but Xilinx's default
	// implementation does nothing to ensure that this
	// would be the case.
	//
	// From here on down, Gisselquist Technology, LLC,
	// claims a copyright on the code.
	//
	assign	bus_clock = S_AXI_ACLK;

	assign	write_to_control = (write_stb)
			&&(axi_awready ? !S_AXI_AWADDR[ADDR_LSBS]
					: !axi_awaddr[ADDR_LSBS]);

	always @(posedge bus_clock)
	begin
		if (S_AXI_ARVALID && S_AXI_ARREADY)
			read_address[0] <= S_AXI_ARADDR[ADDR_LSBS];
		if (!rvalid[0] || !rvalid[1] || S_AXI_RREADY)
		begin
			if (S_AXI_ARREADY)
				read_address[1] <= S_AXI_ARADDR[ADDR_LSBS];
			else
				read_address[1] <= read_address[0];
		end
	end

	always @(*)
	begin
		if (S_AXI_ARREADY)
			read_from_data = S_AXI_ARVALID
						&& S_AXI_ARADDR[ADDR_LSBS];
		else
			read_from_data = read_address[0];

		if (rvalid[0] && rvalid[1] && !S_AXI_RREADY)
			read_from_data = 0;
	end

	assign	i_bus_data = (S_AXI_WREADY ? S_AXI_WDATA : axi_wdata);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Our status/config register
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Now that we've finished reading/writing from the
	// bus, ... or at least acknowledging reads and
	// writes from and to the bus--even if they haven't
	// happened yet, now we implement our actual scope.
	// This includes implementing the actual reads/writes
	// from/to the bus.
	//
	// From here on down, is the heart of the scope itself.
	//
	initial	br_config = 3'b0;
	initial	br_holdoff = DEFAULT_HOLDOFF;
	always @(posedge bus_clock)
	begin
		if (write_to_control)
		begin
			br_config[1:0] <= {
				i_bus_data[27],
				i_bus_data[26] };
			if (!i_bus_data[31] && br_config[2])
				br_holdoff <= i_bus_data[(HOLDOFFBITS-1):0];
		end

		//
		// Reset logic
		if (bw_reset_complete)
			// Clear the reset request, regardless of the write
			br_config[2] <= 1'b1;
		else if (!br_config[2])
			// Reset request is already pending--don't change it
			br_config[2] <= 1'b0;
		else if (write_to_control && !i_bus_data[31])
			// Initiate a new reset request
			//   Note that we won't initiate a new reset request
			//   while one is already pending.  Once the pending
			//   one completes we'll be in the reset state anyway
			br_config[2] <= 1'b0;

		if (i_reset)
			br_config[2] <= 1'b0;
	end
	assign	bw_reset_request   = (!br_config[2]);
	assign	bw_manual_trigger  = (br_config[1]);
	assign	bw_disable_trigger = (br_config[0]);

	generate
	if (SYNCHRONOUS > 0)
	begin : GEN_SYNCHRONOUS
		assign	dw_reset = bw_reset_request;
		assign	dw_manual_trigger = bw_manual_trigger;
		assign	dw_disable_trigger = bw_disable_trigger;
		assign	bw_reset_complete = bw_reset_request;
	end else begin : GEN_ASYNC
		reg		r_reset_complete;
		(* ASYNC_REG = "TRUE" *) reg	[2:0]	q_iflags, r_iflags;

		// Resets are synchronous to the bus clock, not the data clock
		// so do a clock transfer here
		initial	{ q_iflags, r_iflags } = 6'h0;
		initial	r_reset_complete = 1'b0;
		always @(posedge i_data_clk or posedge i_reset)
		if (i_reset)
		begin
			{ q_iflags, r_iflags } <= 6'h0;
			r_reset_complete <= 1'b0;
		end else begin
			q_iflags <= { bw_reset_request, bw_manual_trigger, bw_disable_trigger };
			r_iflags <= q_iflags;
			r_reset_complete <= (dw_reset);
		end

		assign	dw_reset = r_iflags[2];
		assign	dw_manual_trigger = r_iflags[1];
		assign	dw_disable_trigger = r_iflags[0];

		(* ASYNC_REG = "TRUE" *) reg	q_reset_complete,
						qq_reset_complete;
		// Pass an acknowledgement back from the data clock to the bus
		// clock that the reset has been accomplished
		initial	q_reset_complete = 1'b0;
		initial	qq_reset_complete = 1'b0;
		always @(posedge bus_clock or posedge i_reset)
		if (i_reset)
		begin
			q_reset_complete  <= 1'b0;
			qq_reset_complete <= 1'b0;
		end else begin
			q_reset_complete  <= r_reset_complete;
			qq_reset_complete <= q_reset_complete;
		end

		assign bw_reset_complete = qq_reset_complete;

`ifdef	FORMAL
		always @(posedge gbl_clk)
		if (f_past_valid_data)
		begin
			if ($rose(r_reset_complete))
				assert(bw_reset_request);
		end

		always @(*)
		case({ bw_reset_request, q_iflags[2], dw_reset, q_reset_complete, qq_reset_complete })
		5'h00: begin end
		5'h10: begin end
		5'h18: begin end
		5'h1c: begin end
		5'h1e: begin end
		5'h1f: begin end
		5'h0f: begin end
		5'h07: begin end
		5'h03: begin end
		5'h01: begin end
		default: assert(0);
		endcase
`endif
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Set up the trigger
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// dw_trigger -- trigger wire, defined on the data clock
	// {{{
	// Write with the i_clk, or input clock.  All outputs read with the
	// bus clock, or bus_clock  as we've called it here.
	assign	dw_trigger = (dr_primed)&&(
				((i_trigger)&&(!dw_disable_trigger))
				||(dw_manual_trigger));
	// }}}

	// dr_triggered
	// {{{
	initial	dr_triggered = 1'b0;
	always @(posedge i_data_clk)
	if (dw_reset)
		dr_triggered <= 1'b0;
	else if ((i_ce)&&(dw_trigger))
		dr_triggered <= 1'b1;
	// }}}

	//
	// Determine when memory is full and capture is complete
	//
	// Writes take place on the data clock

	// counter
	// {{{
	// The counter is unsigned
	initial	counter = 0;
	always @(posedge i_data_clk)
	if (dw_reset)
		counter <= 0;
	else if ((i_ce)&&(dr_triggered)&&(!dr_stopped))
		counter <= counter + 1'b1;
`ifdef	FORMAL
	always @(*)
	if (!dw_reset && !bw_reset_request)
		assert(counter <= br_holdoff+1'b1);
	always @(posedge i_data_clk)
		assume(!(&br_holdoff));
	always @(posedge i_data_clk)
	if (!dr_triggered)
		assert(counter == 0);
`endif
	// }}}

	// dr_stopped
	// {{{
	initial	dr_stopped = 1'b0;
	always @(posedge i_data_clk)
	if ((!dr_triggered)||(dw_reset))
		dr_stopped <= 1'b0;
	else if (!dr_stopped)
	begin
		if (HOLDOFFBITS > 1) // if (i_ce)
			dr_stopped <= (counter >= br_holdoff);
		else if (HOLDOFFBITS <= 1)
			dr_stopped <= ((i_ce)&&(dw_trigger));
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	//
	//	Actually do our writes to memory.  Record, via 'primed' when
	//	the memory is full.
	//
	//	The 'waddr' address that we are using really crosses two clock
	//	domains.  While writing and changing, it's in the data clock
	//	domain.  Once stopped, it becomes part of the bus clock domain.
	//	The clock transfer on the stopped line handles the clock
	//	transfer for these signals.
	//

	// waddr, dr_primed
	// {{{
	initial	waddr = {(LGMEM){1'b0}};
	initial	dr_primed = 1'b0;
	always @(posedge i_data_clk)
	if (dw_reset) // For simulation purposes, supply a valid value
	begin
		waddr <= 0; // upon reset.
		dr_primed <= 1'b0;
	end else if (i_ce && !dr_stopped)
	begin
		// mem[waddr] <= i_data;
		waddr <= waddr + {{(LGMEM-1){1'b0}},1'b1};
		if (!dr_primed)
			dr_primed <= (&waddr);
	end
	// }}}

	// wr_piped_data -- delay data to match the trigger
	// {{{
	// Delay the incoming data so that we can get our trigger
	// logic to line up with the data.  The goal is to have a
	// hold off of zero place the trigger in the last memory
	// address.
	generate
	if (STOPDELAY == 0)
	begin : NO_STOPDLY
		// No delay ... just assign the wires to our input lines
		assign	wr_piped_data = i_data;
	end else if (STOPDELAY == 1)
	begin : GEN_ONE_STOPDLY
		//
		// Delay by one means just register this once
		reg	[(BUSW-1):0]	data_pipe;
		always @(posedge i_data_clk)
		if (i_ce)
			data_pipe <= i_data;

		assign	wr_piped_data = data_pipe;
	end else begin : GEN_STOPDELAY
		// Arbitrary delay ... use a longer pipe
		reg	[(STOPDELAY*BUSW-1):0]	data_pipe;

		always @(posedge i_data_clk)
		if (i_ce)
			data_pipe <= { data_pipe[((STOPDELAY-1)*BUSW-1):0], i_data };
		assign	wr_piped_data = { data_pipe[(STOPDELAY*BUSW-1):((STOPDELAY-1)*BUSW)] };
	end endgenerate
	// }}}

	// mem[] <= wr_piped_data
	// {{{
	always @(posedge i_data_clk)
	if ((i_ce)&&(!dr_stopped))
		mem[waddr] <= wr_piped_data;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Move the status signals back to the bus clock
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	generate if (SYNCHRONOUS > 0)
	begin : SYNCHRONOUS_RETURN
		assign	bw_stopped   = dr_stopped;
		assign	bw_triggered = dr_triggered;
		assign	bw_primed    = dr_primed;
	end else begin : ASYNC_STATUS
		// {{{
		// These aren't a problem, since none of these are strobe
		// signals.  They goes from low to high, and then stays high
		// for many clocks.  Swapping is thus easy--two flip flops to
		// protect against meta-stability and we're done.
		//
		(* ASYNC_REG = "TRUE" *) reg	[2:0]	q_oflags;
		reg	[2:0]	r_oflags;
		initial	q_oflags = 3'h0;
		initial	r_oflags = 3'h0;
		always @(posedge bus_clock)
		if (bw_reset_request)
		begin
			q_oflags <= 3'h0;
			r_oflags <= 3'h0;
		end else begin
			q_oflags <= { dr_stopped, dr_triggered, dr_primed };
			r_oflags <= q_oflags;
		end

		assign	bw_stopped   = r_oflags[2];
		assign	bw_triggered = r_oflags[1];
		assign	bw_primed    = r_oflags[0];
		// }}}
`ifdef	FORMAL
		always @(*)
		if (!bw_reset_request)
		begin
			if (bw_primed)
				assert(q_oflags[0] && dr_primed);
			else if (q_oflags[0])
				assert(dr_primed);

			if (bw_triggered)
				assert(q_oflags[1] && dr_triggered);
			else if (q_oflags[1])
				assert(dr_triggered);

			if (bw_stopped)
				assert(q_oflags[2] && dr_stopped);
			else if (q_oflags[2])
				assert(dr_stopped);
		end
		
`endif
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read from the memory, using the bus clock.  Otherwise respond to bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Reads use the bus clock
	initial	raddr = 0;
	always @(posedge bus_clock)
	begin
		if ((bw_reset_request)||(write_to_control))
			raddr <= 0;
		else if ((read_from_data)&&(bw_stopped))
			raddr <= raddr + 1'b1; // Data read, when stopped
	end

	always @(posedge bus_clock)
	if (read_from_data)
		this_addr <= raddr + waddr + 1'b1;
	else
		this_addr <= raddr + waddr;

	always @(posedge bus_clock)
	if (read_from_data)
		nxt_mem <= mem[this_addr];

	// holdoff sub-register
	// {{{
	assign full_holdoff[(HOLDOFFBITS-1):0] = br_holdoff;
	generate if (HOLDOFFBITS < 20)
	begin : GEN_FULL_HOLDOFF
		assign full_holdoff[19:(HOLDOFFBITS)] = 0;
	end endgenerate
	// }}}

	assign		bw_lgmem = LGMEM;

	// Bus read
	// {{{
	always @(posedge bus_clock)
	if (rvalid[0] && (!S_AXI_RVALID || S_AXI_RREADY))
	begin
		if (!read_address[1]) // Control register read
			o_bus_data <= { bw_reset_request,
					bw_stopped,
					bw_triggered,
					bw_primed,
					bw_manual_trigger,
					bw_disable_trigger,
					(raddr == {(LGMEM){1'b0}}),
					bw_lgmem,
					full_holdoff  };
		else if (!bw_stopped) // read, prior to stopping
			//
			// *WARNING*: THIS READ IS NOT PROTECTED FROM
			// ASYNCHRONOUS COHERENCE ISSUES!
			//
			o_bus_data <= i_data;
		else // if (i_wb_addr) // Read from FIFO memory
			o_bus_data <= nxt_mem; // mem[raddr+waddr];
	end
	// }}}

	assign	S_AXI_RDATA = o_bus_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Interrupt generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	br_level_interrupt = 1'b0;
	always @(posedge bus_clock)
	if ((bw_reset_complete)||(bw_reset_request))
		br_level_interrupt<= 1'b0;
	else
		br_level_interrupt<= (bw_stopped)&&(!bw_disable_trigger);

	assign	o_interrupt = (bw_stopped)&&(!bw_disable_trigger)
					&&(!br_level_interrupt);
	// }}}

	// Make verilator happy
	// {{{
	// verilator lint_off UNUSED
	// Make verilator happy
	wire		unused;
	assign unused = &{ 1'b0, S_AXI_WSTRB, S_AXI_ARPROT, S_AXI_AWPROT,
		axi_awaddr[ADDR_LSBS-1:0],
		i_bus_data[30:28], i_bus_data[25:0] };
	// verilator lint_on UNUSED
	// }}}
`ifdef	FORMAL
	generate if (SYNCHRONOUS)
	begin : ASSUME_CLK

		always @(*)
			assume(i_data_clk == S_AXI_ACLK);

	end else begin : ASSUME_ASYN
		localparam	CKSTEP_BITS = 3;
		localparam [CKSTEP_BITS-1:0]
				MAX_STEP = { 1'b0, {(CKSTEP_BITS-1){1'b1}} };

		// "artificially" generate two clocks
		(* anyconst *) wire [CKSTEP_BITS-1:0] f_data_step, f_bus_step;
		reg	[CKSTEP_BITS-1:0]	f_data_count, f_bus_count;

		always @(*)
		begin
			assume(f_data_step > 0);
			assume(f_bus_step  > 0);
			assume(f_data_step <= MAX_STEP);
			assume(f_bus_step  <= MAX_STEP);

			assume((f_data_step == MAX_STEP)
				||(f_bus_step == MAX_STEP));
		end

		always @(posedge gbl_clk)
		begin
			f_data_count <= f_data_count + f_data_step;
			f_bus_count  <= f_bus_count  + f_bus_step;

			assume(i_data_clk  == f_data_count[CKSTEP_BITS-1]);
			assume(bus_clock   == f_bus_count[CKSTEP_BITS-1]);
		end

		always @(posedge gbl_clk)
		if (!$rose(i_data_clk))
		begin
			assume($stable(i_trigger));
			assume($stable(i_data));
		end

		always @(posedge gbl_clk)
		if (!$rose(S_AXI_ACLK))
		begin
			assume($stable(S_AXI_ARESETN));
			//
			assume($stable(S_AXI_AWADDR));
			assume($stable(S_AXI_AWPROT));
			assume($stable(S_AXI_AWVALID));
			//
			assume($stable(S_AXI_WDATA));
			assume($stable(S_AXI_WSTRB));
			assume($stable(S_AXI_WVALID));
			//
			assume($stable(S_AXI_BREADY));
			//
			assume($stable(S_AXI_ARADDR));
			assume($stable(S_AXI_ARPROT));
			assume($stable(S_AXI_ARVALID));
			//
			assume($stable(S_AXI_RREADY));
			//
		end

		always @(posedge gbl_clk)
		if (!$rose(i_data_clk))
		begin
			assume($stable(i_ce));
			assume($stable(i_trigger));
			assume($stable(i_data));
		end

		always @(*)
		if (!dw_reset && !bw_reset_request)
		begin
			if (bw_triggered)
				assert(dr_triggered);
			if (bw_primed)
				assert(dr_primed);
			if (bw_stopped)
				assert(dr_stopped);
		end
	end endgenerate

	initial	f_past_valid_bus = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid_bus <= 1'b1;

	generate if (!SYNCHRONOUS)
	begin
		initial { f_past_valid_gbl, f_past_valid_data }= 2'b0;
		always @(posedge gbl_clk)
			f_past_valid_gbl <= 1'b1;

		always @(posedge i_data_clk)
			f_past_valid_data = 1'b1;

		always @(posedge gbl_clk)
		if (f_past_valid_gbl && !$rose(bus_clock))
			assert($stable(o_interrupt));

		always @(posedge gbl_clk)
		if ((f_past_valid_gbl)&&(!$rose(S_AXI_ACLK)))
		begin
			assert($stable(S_AXI_AWREADY));
			assert($stable(S_AXI_ARREADY));
			assert($stable(S_AXI_RDATA));
			assert($stable(S_AXI_RRESP));
			assert($stable(S_AXI_RVALID));
			assert($stable(S_AXI_WREADY));
			assert($stable(S_AXI_BRESP));
			assert($stable(S_AXI_BVALID));
		end

	end else begin

		always @(*)
			f_past_valid_data = f_past_valid_bus;
		always @(*)
			f_past_valid_gbl  = f_past_valid_bus;

	end endgenerate

	localparam	F_LGDEPTH = 5;
	wire	[F_LGDEPTH-1:0]	f_axi_rd_outstanding,
				f_axi_wr_outstanding,
				f_axi_awr_outstanding;

	faxil_slave #(
		// .C_S_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
		// Width of S_AXI address bus
		.C_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_LGDEPTH),
		.F_OPT_HAS_CACHE(1'b0),
		// .F_OPT_CLK2FFLOGIC(!SYNCHRONOUS),
		.F_AXI_MAXWAIT(5'h6),
		.F_AXI_MAXDELAY(5'h6)
		) faxil_slave(
			.i_clk(S_AXI_ACLK),
			.i_axi_reset_n(S_AXI_ARESETN),
			//
			.i_axi_awvalid(S_AXI_AWVALID),
			.i_axi_awready(S_AXI_AWREADY),
			.i_axi_awaddr(S_AXI_AWADDR),
			.i_axi_awprot(S_AXI_AWPROT),
			//
			.i_axi_wdata(S_AXI_WDATA),
			.i_axi_wstrb(S_AXI_WSTRB),
			.i_axi_wvalid(S_AXI_WVALID),
			.i_axi_wready(S_AXI_WREADY),
			//
			.i_axi_bvalid(S_AXI_BVALID),
			.i_axi_bready(S_AXI_BREADY),
			.i_axi_bresp(S_AXI_BRESP),
			//
			.i_axi_arvalid(S_AXI_ARVALID),
			.i_axi_arready(S_AXI_ARREADY),
			.i_axi_araddr(S_AXI_ARADDR),
			.i_axi_arprot(S_AXI_ARPROT),
			//
			.i_axi_rvalid(S_AXI_RVALID),
			.i_axi_rready(S_AXI_RREADY),
			.i_axi_rdata(S_AXI_RDATA),
			.i_axi_rresp(S_AXI_RRESP),
			//
			.f_axi_rd_outstanding(f_axi_rd_outstanding),
			.f_axi_wr_outstanding(f_axi_wr_outstanding),
			.f_axi_awr_outstanding(f_axi_awr_outstanding));

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(f_axi_awr_outstanding == (S_AXI_AWREADY ? 0:1)
				+ (S_AXI_BVALID ? 1:0));
		assert(f_axi_wr_outstanding == (S_AXI_WREADY ? 0:1)
				+ (S_AXI_BVALID ? 1:0));

		assert(f_axi_rd_outstanding == (axi_arready ? 0:1)
				+ (rvalid[0] ? 1:0) + (rvalid[1] ? 1:0));
	end

	always @(*)
	if (dr_triggered)
		assert(dr_primed);

	always @(*)
	if (dr_stopped)
		assert((dr_primed)&&(dr_triggered));

	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[(LGMEM-1):0]	f_addr;
	reg	[BUSW-1:0]	f_data;
	reg			f_filled,     f_nxtstopped, f_busstopped;
	reg	[(LGMEM-1):0]	f_busmemaddr, f_nxtaddr;
	reg	[2:0]		f_axi_addr;

	initial	f_filled = 1'b0;
	always @(posedge i_data_clk)
	if (dw_reset)
		f_filled <= 1'b0;
	else if ((i_ce)&&(!dr_stopped)&&(waddr == f_addr))
		f_filled <= 1'b1;

	always @(posedge i_data_clk)
	if (waddr > f_addr)
		assert(f_filled);

	always @(posedge i_data_clk)
	if (!f_filled)
		assert(!dr_primed);

	always @(posedge i_data_clk)
	if ((i_ce)&&(!dr_stopped)&&(waddr == f_addr))
		f_data <= wr_piped_data;

	always @(posedge i_data_clk)
	if (f_filled)
		assert(mem[f_addr] == f_data);

	always @(posedge bus_clock)
	if (f_past_valid_bus && $past(!bw_stopped))
		assert(raddr == 0);

	always @(posedge bus_clock)
	begin
		if (!rvalid[0] || !rvalid[1] || S_AXI_RREADY)
			f_axi_addr[0] <= (S_AXI_ARREADY
					? S_AXI_ARADDR[ADDR_LSBS]
					: read_address[0]);

		if (!rvalid[1] || S_AXI_RREADY)
			f_axi_addr[1] <= f_axi_addr[0];

		if (f_past_valid_bus && !$past(read_from_data))
			assert(!$rose(rvalid[0] && f_axi_addr[0]));
		if (f_past_valid_bus && $past(!i_reset && read_from_data))
			assert(f_axi_addr[0] && rvalid[0]);
	end

	always @(*)
	if (rvalid[0])
		assert(f_axi_addr[0] == read_address[1]);

	always @(*)
	if (S_AXI_ARREADY && !S_AXI_ARVALID)
		assert(!read_from_data);
	else if (rvalid[0] && rvalid[1] && !S_AXI_RREADY)
		assert(!read_from_data);
	else if (!S_AXI_ARREADY)
		assert(read_from_data == read_address[0]);
	else if (S_AXI_ARVALID)
		assert(read_from_data == S_AXI_ARADDR[ADDR_LSBS]);
	else
		assert(!read_from_data);

	initial	f_nxtaddr = 0;
	initial	f_nxtstopped = 0;
	always @(posedge bus_clock)
	if (i_reset || bw_reset_request)
		f_nxtstopped <= 1'b0;
	else if (read_from_data)
		f_nxtstopped <= bw_stopped;

	initial	f_busstopped = 0;
	always @(posedge bus_clock)
	if (i_reset || bw_reset_request)
		f_busstopped <= 1'b0;
	else if (rvalid[0] && (!S_AXI_RVALID || S_AXI_RREADY))
		f_busstopped <= f_nxtstopped;

	always @(*)
	if (f_nxtstopped)
		assert(bw_stopped);

	always @(*)
	if (f_busstopped)
		assert(bw_stopped && f_nxtstopped);

	always @(posedge bus_clock)
	if (read_from_data)
		f_nxtaddr = this_addr;

	always @(posedge bus_clock)
	if (f_past_valid_bus && $past(f_past_valid_bus)
		&& $past(bw_stopped) && dr_stopped
		&& $past(bw_stopped && !write_to_control,2))
	begin
		if ($past(read_from_data))
			assert(this_addr == $past(this_addr + 1'b1));
		else
			assert($stable(this_addr));
	end

	always @(*)
	if (!bw_reset_request && !dw_reset && rvalid[0]
		&& f_nxtstopped && f_nxtaddr == f_addr && f_axi_addr[0])
		assert(nxt_mem == mem[f_nxtaddr]);

	always @(posedge bus_clock)
	if (rvalid[0] && (!S_AXI_RVALID || S_AXI_RREADY))
		f_busmemaddr <= f_nxtaddr;

	always @(posedge bus_clock)
	if (f_past_valid_bus && $past(!i_reset && rvalid[0]
			&& !bw_reset_request
			&& (!S_AXI_RVALID || S_AXI_RREADY)
			&& f_axi_addr[0] && f_busstopped))
	begin
		if (f_filled && f_busmemaddr == f_addr)
			assert(S_AXI_RDATA == f_data);
	end

	always @(*)
	if (S_AXI_RVALID && !f_axi_addr[1])
		assert(S_AXI_RDATA[24:20] == bw_lgmem);

	always @(*)
	if (dr_triggered)
		assert(dr_primed);

	always @(*)
	if (dr_stopped)
		assert(dr_triggered);

`endif
endmodule
// `default_nettype 	wire
