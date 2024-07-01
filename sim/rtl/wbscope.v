////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/wbscope.v
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
module wbscope #(
		// {{{
		parameter [4:0]			LGMEM = 5'd10,
		parameter			BUSW = 32,
		parameter [0:0]			SYNCHRONOUS=1,
		parameter		 	HOLDOFFBITS = 20,
		parameter [(HOLDOFFBITS-1):0]	DEFAULT_HOLDOFF = ((1<<(LGMEM-1))-4)
		// }}}
	) (
		// {{{
		// The input signals that we wish to record
		input	wire			i_data_clk, i_ce, i_trigger,
		input	wire	[(BUSW-1):0]	i_data,
		// The WISHBONE bus for reading and configuring this scope
		// {{{
		input	wire			i_wb_clk, i_wb_cyc,
						i_wb_stb, i_wb_we,
		input	wire			i_wb_addr, // One address line only
		input	wire	[(BUSW-1):0]	i_wb_data,
		input	wire	[(BUSW/8-1):0]	i_wb_sel,
		output	wire			o_wb_stall, o_wb_ack,
		output	wire	[(BUSW-1):0]	o_wb_data,
		// }}}
		// And, finally, for a final flair --- offer to interrupt the
		// CPU after our trigger has gone off.  This line is equivalent
		// to the scope  being stopped.  It is not maskable here.
		output	wire			o_interrupt
		// }}}
	);

	// Signal declarations
	// {{{
	wire			bus_clock;
	wire			read_from_data;
	wire			write_stb;
	wire			write_to_control;
	reg			read_address;
	wire	[31:0]		i_bus_data;
	reg	[(LGMEM-1):0]	raddr;
	reg	[(BUSW-1):0]	mem[0:((1<<LGMEM)-1)];
	wire		bw_reset_request, bw_manual_trigger,
			bw_disable_trigger, bw_reset_complete;
	reg	[2:0]	br_config;
	reg	[(HOLDOFFBITS-1):0]	br_holdoff;
	wire			dw_reset, dw_manual_trigger, dw_disable_trigger;
	reg			dr_triggered, dr_primed;
	wire			dw_trigger;
	(* ASYNC_REG="TRUE" *) reg	[(HOLDOFFBITS-1):0]	counter;

	reg			dr_stopped;
	reg	[(LGMEM-1):0]	waddr;
	localparam	STOPDELAY = 1;	// Calibrated value--don't change this
	wire	[(BUSW-1):0]		wr_piped_data;
	wire			bw_stopped, bw_triggered, bw_primed;
	reg			br_wb_ack, br_pre_wb_ack;
	wire			bw_cyc_stb;
	reg	[(LGMEM-1):0]	this_addr;
	reg	[31:0]		nxt_mem;
	wire	[19:0]		full_holdoff;
	reg	[31:0]		o_bus_data;
	wire	[4:0]		bw_lgmem;
	reg			br_level_interrupt;
	// }}}

	assign	bus_clock = i_wb_clk;

	////////////////////////////////////////////////////////////////////////
	//
	// Decode and handle the bus signaling in a (somewhat) portable manner
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	///////////////////////////////////////////////////
	//
	//

	assign	i_bus_data = i_wb_data;
	assign	o_wb_stall = 1'b0;
	assign	read_from_data = i_wb_stb && !i_wb_we && i_wb_addr && (&i_wb_sel);
	assign	write_stb = (i_wb_stb)&&(i_wb_we);
	assign	write_to_control = write_stb && !i_wb_addr && (&i_wb_sel);

	always @(posedge bus_clock)
		read_address <= i_wb_addr;
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

	// Our status/config register
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

		// if (i_reset)
		//	br_config[2] <= 1'b0;
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
		(* ASYNC_REG = "TRUE" *) reg	[2:0]	q_iflags;
		reg	[2:0]	r_iflags;

		// Resets are synchronous to the bus clock, not the data clock
		// so do a clock transfer here
		initial	{ q_iflags, r_iflags } = 6'h0;
		initial	r_reset_complete = 1'b0;
		always @(posedge i_data_clk)
		begin
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
		always @(posedge bus_clock)
		begin
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
	// bus clock, or i_wb_clk as we've called it here.
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
	assign	bw_cyc_stb = (i_wb_stb);

	initial	br_pre_wb_ack = 1'b0;
	initial	br_wb_ack = 1'b0;
	always @(posedge bus_clock)
	begin
		if ((bw_reset_request)||(write_to_control))
			raddr <= 0;
		else if ((read_from_data)&&(bw_stopped))
			raddr <= raddr + 1'b1; // Data read, when stopped

		br_pre_wb_ack <= bw_cyc_stb;
		br_wb_ack <= (br_pre_wb_ack)&&(i_wb_cyc);
	end

	assign	o_wb_ack = (i_wb_cyc)&&(br_wb_ack);

	always @(posedge bus_clock)
	if (read_from_data)
		this_addr <= raddr + waddr + 1'b1;
	else
		this_addr <= raddr + waddr;

	always @(posedge bus_clock)
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
	begin
		if (!read_address) // Control register read
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

	assign	o_wb_data = o_bus_data;
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
	wire	unused;
	assign unused = &{ 1'b0, i_bus_data[30:28], i_bus_data[25:0],
			i_wb_sel };
	// verilator lint_on UNUSED
	// }}}
endmodule
