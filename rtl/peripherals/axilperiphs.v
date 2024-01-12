////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilperiphs
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	
// Registers:	
//	0x00	PIC	Interrupt controller
//	0x04	Watchdog
//	0x08	(Reserved)
//	0x0c	CTRIC	Secondary interrupt controller
//	0x10	TMRA
//	0x14	TMRB
//	0x18	TMRC
//	0x1c	JIFF
//	(No User counters)
//	(No DMA)
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2024, Gisselquist Technology, LLC
// {{{
//
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	axilperiphs #(
		// {{{
		//
		// Size of the AXI-lite bus.  These are fixed, since 1) AXI-lite
		// is fixed at a width of 32-bits by Xilinx def'n, and 2) since
		// we only ever have 4 configuration words.
		parameter	C_AXI_ADDR_WIDTH =  6,
		localparam	C_AXI_DATA_WIDTH = 32,
		parameter [0:0]	OPT_SKIDBUFFER = 1'b1,
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter 	EXTERNAL_INTERRUPTS = 1,
		parameter [0:0]	OPT_COUNTERS = 1,
		localparam	ADDRLSB = $clog2(C_AXI_DATA_WIDTH)-3
		// }}}
	) (
		// {{{
		input	wire					S_AXI_ACLK,
		input	wire					S_AXI_ARESETN,
		// AXI-lite interface
		// {{{
		input	wire					S_AXI_AWVALID,
		output	wire					S_AXI_AWREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_AWADDR,
		input	wire	[2:0]				S_AXI_AWPROT,
		//
		input	wire					S_AXI_WVALID,
		output	wire					S_AXI_WREADY,
		input	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_WDATA,
		input	wire	[C_AXI_DATA_WIDTH/8-1:0]	S_AXI_WSTRB,
		//
		output	wire					S_AXI_BVALID,
		input	wire					S_AXI_BREADY,
		output	wire	[1:0]				S_AXI_BRESP,
		//
		input	wire					S_AXI_ARVALID,
		output	wire					S_AXI_ARREADY,
		input	wire	[C_AXI_ADDR_WIDTH-1:0]		S_AXI_ARADDR,
		input	wire	[2:0]				S_AXI_ARPROT,
		//
		output	wire					S_AXI_RVALID,
		input	wire					S_AXI_RREADY,
		output	wire	[C_AXI_DATA_WIDTH-1:0]		S_AXI_RDATA,
		output	wire	[1:0]				S_AXI_RRESP,
		// }}}
		input	wire				i_cpu_reset,
		input	wire				i_cpu_halted,
		input	wire				i_cpu_gie,
		input	wire				i_cpu_pfstall,
		input	wire				i_cpu_opstall,
		input	wire				i_cpu_icount,
		input wire [EXTERNAL_INTERRUPTS-1:0]	i_ivec,
		output	wire				o_interrupt,
		output	wire				o_watchdog_reset
		// }}}
	);

	////////////////////////////////////////////////////////////////////////
	//
	// Register/wire signal declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam	[3:0]	ADR_PIC		= 4'h0,
				ADR_WATCHDOG	= 4'h1,
				ADR_APIC	= 4'h2;
				// No bus watchdog
				
	localparam	[3:0]	ADR_TIMERA = 4'h4,
				ADR_TIMERB = 4'h5,
				ADR_TIMERC = 4'h6,
				ADR_JIFFIES= 4'h7;

	localparam	[3:0]	ADR_MCLOCKS = 4'h8,
				ADR_MOPSTALL = 4'h9,
				ADR_MPFSTALL = 4'ha,
				ADR_MICOUNT  = 4'hb;

	localparam	[3:0]	ADR_UCLOCKS = 4'hc,
				ADR_UOPSTALL = 4'hd,
				ADR_UPFSTALL = 4'he,
				ADR_UICOUNT  = 4'hf;

	wire	i_reset = !S_AXI_ARESETN;

	wire				axil_write_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	awskd_addr;
	//
	wire	[C_AXI_DATA_WIDTH-1:0]	wskd_data;
	wire [C_AXI_DATA_WIDTH/8-1:0]	wskd_strb;
	reg				axil_bvalid;
	//
	wire				axil_read_ready;
	wire	[C_AXI_ADDR_WIDTH-ADDRLSB-1:0]	arskd_addr;
	reg	[C_AXI_DATA_WIDTH-1:0]	axil_read_data;
	reg				axil_read_valid;

	wire		pic_stall, pic_ack;
	wire	[31:0]	pic_data;

	wire		wdog_stall, wdog_ack;
	wire	[31:0]	wdog_data;

	wire		apic_stall, apic_ack, apic_int;
	wire	[31:0]	apic_data;

	wire		tmra_stall, tmra_ack, tmra_int;
	wire	[31:0]	tmra_data;

	wire		tmrb_stall, tmrb_ack, tmrb_int;
	wire	[31:0]	tmrb_data;

	wire		tmrc_stall, tmrc_ack, tmrc_int;
	wire	[31:0]	tmrc_data;

	wire		jif_stall, jif_ack, jif_int;
	wire	[31:0]	jif_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Write signaling
	//
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_WRITE

		wire	awskd_valid, wskd_valid;

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
		axilawskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_AWVALID), .o_ready(S_AXI_AWREADY),
			.i_data(S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
			.o_valid(awskd_valid), .i_ready(axil_write_ready),
			.o_data(awskd_addr));

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_DATA_WIDTH+C_AXI_DATA_WIDTH/8))
		axilwskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_WVALID), .o_ready(S_AXI_WREADY),
			.i_data({ S_AXI_WDATA, S_AXI_WSTRB }),
			.o_valid(wskd_valid), .i_ready(axil_write_ready),
			.o_data({ wskd_data, wskd_strb }));

		assign	axil_write_ready = awskd_valid && wskd_valid
				&& (!S_AXI_BVALID || S_AXI_BREADY);

	end else begin : SIMPLE_WRITES

		reg	axil_awready;

		initial	axil_awready = 1'b0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			axil_awready <= 1'b0;
		else
			axil_awready <= !axil_awready
				&& (S_AXI_AWVALID && S_AXI_WVALID)
				&& (!S_AXI_BVALID || S_AXI_BREADY);

		assign	S_AXI_AWREADY = axil_awready;
		assign	S_AXI_WREADY  = axil_awready;

		assign 	awskd_addr = S_AXI_AWADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB];
		assign	wskd_data  = S_AXI_WDATA;
		assign	wskd_strb  = S_AXI_WSTRB;

		assign	axil_write_ready = axil_awready;

	end endgenerate

	initial	axil_bvalid = 0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_bvalid <= 0;
	else if (axil_write_ready)
		axil_bvalid <= 1;
	else if (S_AXI_BREADY)
		axil_bvalid <= 0;

	assign	S_AXI_BVALID = axil_bvalid;
	assign	S_AXI_BRESP = 2'b00;
	// }}}

	//
	// Read signaling
	//
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : SKIDBUFFER_READ

		wire	arskd_valid;

		skidbuffer #(.OPT_OUTREG(0),
				.OPT_LOWPOWER(OPT_LOWPOWER),
				.DW(C_AXI_ADDR_WIDTH-ADDRLSB))
		axilarskid(//
			.i_clk(S_AXI_ACLK), .i_reset(i_reset),
			.i_valid(S_AXI_ARVALID), .o_ready(S_AXI_ARREADY),
			.i_data(S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB]),
			.o_valid(arskd_valid), .i_ready(axil_read_ready),
			.o_data(arskd_addr));

		assign	axil_read_ready = arskd_valid
				&& (!axil_read_valid || S_AXI_RREADY);

	end else begin : SIMPLE_READS

		reg	axil_arready;

		always @(*)
			axil_arready = !S_AXI_RVALID;

		assign	arskd_addr = S_AXI_ARADDR[C_AXI_ADDR_WIDTH-1:ADDRLSB];
		assign	S_AXI_ARREADY = axil_arready;
		assign	axil_read_ready = (S_AXI_ARVALID && S_AXI_ARREADY);

	end endgenerate

	initial	axil_read_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (i_reset)
		axil_read_valid <= 1'b0;
	else if (axil_read_ready)
		axil_read_valid <= 1'b1;
	else if (S_AXI_RREADY)
		axil_read_valid <= 1'b0;

	assign	S_AXI_RVALID = axil_read_valid;
	assign	S_AXI_RDATA  = axil_read_data;
	assign	S_AXI_RRESP = 2'b00;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI-lite register logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Interrupt handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[30:0]	int_vector;

	// Generate the interrupt vector
	// {{{
	generate if (EXTERNAL_INTERRUPTS == 0)
	begin : NO_EXTERNAL_INTERRUPTS
		// {{{
		always @(*)
		begin
			int_vector = 0;
			int_vector[5:0] = { apic_int, tmra_int, tmrb_int,
					tmrc_int, jif_int, 1'b0 };
		end
		// }}}
	end else if (EXTERNAL_INTERRUPTS == 1)
	begin : SINGLE_EXTERNAL_INTERRUPT
		// {{{

		always @(*)
		begin
			int_vector = 0;
			int_vector[5:0] = { apic_int, tmra_int, tmrb_int,
					tmrc_int, jif_int, i_ivec[0] };
		end
		// }}}
	end else begin : MANY_EXTERNAL_INTERRUPTS
		// {{{
		always @(*)
		begin
			int_vector = 0;
			int_vector[5:0] = { apic_int, tmra_int, tmrb_int,
					tmrc_int, jif_int, i_ivec[0] };
			int_vector[EXTERNAL_INTERRUPTS+5-1:6]
					= i_ivec[EXTERNAL_INTERRUPTS-1:1];
		end
		// }}}
	end endgenerate
	// }}}

	icontrol #(.IUSED(15))
	pic(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
		.i_wb_cyc(axil_write_ready),
		.i_wb_stb(axil_write_ready && awskd_addr == ADR_PIC),
		.i_wb_we(1'b1), .i_wb_data(wskd_data), .i_wb_sel(wskd_strb),
		.o_wb_stall(pic_stall), .o_wb_ack(pic_ack),.o_wb_data(pic_data),
		.i_brd_ints(int_vector[14:0]), .o_interrupt(o_interrupt)
		// }}}
	);

	ziptimer #(32,31,0)
	watchdog(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
		.i_ce(!i_cpu_halted), .i_wb_cyc(1'b1),
		.i_wb_stb(axil_write_ready && awskd_addr == ADR_WATCHDOG),
		.i_wb_we(1'b1), .i_wb_data(wskd_data), .i_wb_sel(wskd_strb),
		.o_wb_stall(wdog_stall),
		.o_wb_ack(wdog_ack), .o_wb_data(wdog_data),
		.o_int(o_watchdog_reset)
		// }}}
	);

	// APIC
	// {{{
	generate if (EXTERNAL_INTERRUPTS > 15)
	begin : APIC

		icontrol #(.IUSED(15))
		apic(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
			.i_wb_cyc(axil_write_ready),
			.i_wb_stb(axil_write_ready && awskd_addr == ADR_APIC),
			.i_wb_we(1'b1), .i_wb_data(wskd_data),
				.i_wb_sel(wskd_strb),
			.o_wb_stall(apic_stall), .o_wb_ack(apic_ack),
				.o_wb_data(apic_data),
			.i_brd_ints(int_vector[30:15]),
			.o_interrupt(o_interrupt)
			// }}}
		);

	end else begin : NO_APIC

		assign	apic_data  = 0;
		assign	apic_stall = 0;
		assign	apic_ack   = 0;
		assign	apic_int   = 0;

	end endgenerate
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Timers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	ziptimer
	timer_a(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
		.i_ce(!i_cpu_halted), .i_wb_cyc(1'b1),
		.i_wb_stb(axil_write_ready && awskd_addr == ADR_TIMERA),
		.i_wb_we(1'b1), .i_wb_data(wskd_data), .i_wb_sel(wskd_strb),
				.o_wb_stall(tmra_stall),
		.o_wb_ack(tmra_ack), .o_wb_data(tmra_data), .o_int(tmra_int)
		// }}}
	);

	ziptimer
	timer_b(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
		.i_ce(!i_cpu_halted), .i_wb_cyc(1'b1),
		.i_wb_stb(axil_write_ready && awskd_addr == ADR_TIMERB),
		.i_wb_we(1'b1), .i_wb_data(wskd_data),  .i_wb_sel(wskd_strb),
				.o_wb_stall(tmrb_stall),
		.o_wb_ack(tmrb_ack), .o_wb_data(tmrb_data), .o_int(tmrb_int)
		// }}}
	);

	ziptimer
	timer_c(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
		.i_ce(!i_cpu_halted), .i_wb_cyc(1'b1),
		.i_wb_stb(axil_write_ready && awskd_addr == ADR_TIMERC),
		.i_wb_we(1'b1), .i_wb_data(wskd_data),  .i_wb_sel(wskd_strb),
				.o_wb_stall(tmrc_stall),
		.o_wb_ack(tmrc_ack), .o_wb_data(tmrc_data), .o_int(tmrc_int)
		// }}}
	);

	zipjiffies
	jiffies(
		// {{{
		.i_clk(S_AXI_ACLK), .i_reset(i_cpu_reset),
		.i_ce(!i_cpu_halted), .i_wb_cyc(1'b1),
		.i_wb_stb(axil_write_ready && awskd_addr == ADR_JIFFIES),
		.i_wb_we(1'b1), .i_wb_data(wskd_data), .i_wb_sel(wskd_strb),
				.o_wb_stall(jif_stall),
		.o_wb_ack(jif_ack), .o_wb_data(jif_data), .o_int(jif_int)
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Optional performance counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire	[31:0]	mtask, mopstall, mpfstall, micount;
	wire	[31:0]	utask, uopstall, upfstall, uicount;

	generate if (OPT_COUNTERS)
	begin : ACCOUNTING_COUNTERS
		// {{{
		reg	[31:0]	r_mtask, r_mopstall, r_mpfstall, r_micount;
		reg	[31:0]	r_utask, r_uopstall, r_upfstall, r_uicount;

		initial	{ r_mtask, r_mopstall, r_mpfstall, r_micount } = 0;
		always @(posedge S_AXI_ACLK)
		if (i_cpu_reset)
			{ r_mtask, r_mopstall, r_mpfstall, r_micount } <= 0;
		else begin
			if (!i_cpu_halted)
				r_mtask <= r_mtask + 1;
			if (i_cpu_opstall)
				r_mopstall <= mopstall + 1;
			if (i_cpu_pfstall)
				r_mpfstall <= r_mpfstall + 1;
			if (i_cpu_icount)
				r_micount <= r_micount + 1;

			if (axil_write_ready)
			case(awskd_addr)
			ADR_MCLOCKS: begin
				// {{{
				if(wskd_strb[0]) r_mtask[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_mtask[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_mtask[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_mtask[31:24]<=wskd_data[31:24];
				end
				// }}}
			ADR_MOPSTALL: begin
				// {{{
				if(wskd_strb[0]) r_mopstall[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_mopstall[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_mopstall[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_mopstall[31:24]<=wskd_data[31:24];
				end
				// }}}
			ADR_MPFSTALL: begin
				// {{{
				if(wskd_strb[0]) r_mpfstall[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_mpfstall[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_mpfstall[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_mpfstall[31:24]<=wskd_data[31:24];
				end
				// }}}
			ADR_MICOUNT: begin
				// {{{
				if(wskd_strb[0]) r_micount[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_micount[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_micount[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_micount[31:24]<=wskd_data[31:24];
				end
				// }}}
			default: begin end
			endcase
		end

		initial	{ r_utask, r_uopstall, r_upfstall, r_uicount } = 0;
		always @(posedge S_AXI_ACLK)
		if (i_cpu_reset)
			{ r_utask, r_uopstall, r_upfstall, r_uicount } <= 0;
		else begin
			if (!i_cpu_halted && i_cpu_gie)
				r_utask <= r_utask + 1;
			if (i_cpu_opstall && i_cpu_gie)
				r_uopstall <= r_uopstall + 1;
			if (i_cpu_pfstall && i_cpu_gie)
				r_upfstall <= r_upfstall + 1;
			if (i_cpu_icount && i_cpu_gie)
				r_uicount <= r_uicount + 1;

			if (axil_write_ready)
			case(awskd_addr)
			ADR_UCLOCKS: begin
				// {{{
				if(wskd_strb[0]) r_utask[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_utask[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_utask[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_utask[31:24]<=wskd_data[31:24];
				end
				// }}}
			ADR_UOPSTALL: begin
				// {{{
				if(wskd_strb[0]) r_uopstall[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_uopstall[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_uopstall[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_uopstall[31:24]<=wskd_data[31:24];
				end
				// }}}
			ADR_UPFSTALL: begin
				// {{{
				if(wskd_strb[0]) r_upfstall[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_upfstall[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_upfstall[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_upfstall[31:24]<=wskd_data[31:24];
				end
				// }}}
			ADR_UICOUNT: begin
				// {{{
				if(wskd_strb[0]) r_uicount[ 7: 0]<=wskd_data[ 7: 0];
				if(wskd_strb[1]) r_uicount[15: 8]<=wskd_data[15: 8];
				if(wskd_strb[2]) r_uicount[23:16]<=wskd_data[23:16];
				if(wskd_strb[3]) r_uicount[31:24]<=wskd_data[31:24];
				end
				// }}}
			default: begin end
			endcase
		end

		assign	{ mtask, mopstall, mpfstall, micount } = 
				{ r_mtask, r_mopstall, r_mpfstall, r_micount };
		assign	{ utask, uopstall, upfstall, uicount } = 
				{ r_utask, r_uopstall, r_upfstall, r_uicount };

		// }}}
	end else begin : NO_ACCOUNTING
	
		assign	{ mtask, mopstall, mpfstall, micount } = 0;
		assign	{ utask, uopstall, upfstall, uicount } = 0;

	end endgenerate
	// }}}

	// axil_read_data
	// {{{
	initial	axil_read_data = 0;
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !S_AXI_ARESETN)
		axil_read_data <= 0;
	else if (!S_AXI_RVALID || S_AXI_RREADY)
	begin
		axil_read_data	<= 0;
		case({ (OPT_COUNTERS & arskd_addr[3]), arskd_addr[2:0] })
		ADR_PIC:	axil_read_data	<= pic_data;
		ADR_WATCHDOG:	axil_read_data	<= wdog_data;
		// 3'b10:	axil_read_data	<= watchdog_data;
		ADR_APIC:	axil_read_data	<= apic_data;
		ADR_TIMERA:	axil_read_data	<= tmra_data;
		ADR_TIMERB:	axil_read_data	<= tmrb_data;
		ADR_TIMERC:	axil_read_data	<= tmrc_data;
		ADR_JIFFIES:	axil_read_data	<= jif_data;
		// Supervisor counters
		ADR_MCLOCKS:	axil_read_data	<= mtask;
		ADR_MOPSTALL:	axil_read_data	<= mopstall;
		ADR_MPFSTALL:	axil_read_data	<= mpfstall;
		ADR_MICOUNT:	axil_read_data	<= micount;
		// User counters
		ADR_UCLOCKS:	axil_read_data	<= utask;
		ADR_UOPSTALL:	axil_read_data	<= uopstall;
		ADR_UPFSTALL:	axil_read_data	<= upfstall;
		ADR_UICOUNT:	axil_read_data	<= uicount;
		default: axil_read_data <= 0;
		endcase

		if (OPT_LOWPOWER && !axil_read_ready)
			axil_read_data <= 0;
	end
	// }}}

	// apply_wstrb
	// {{{
	// Verilator coverage_off
	function automatic [C_AXI_DATA_WIDTH-1:0]	apply_wstrb;
		input	[C_AXI_DATA_WIDTH-1:0]		prior_data;
		input	[C_AXI_DATA_WIDTH-1:0]		new_data;
		input	[C_AXI_DATA_WIDTH/8-1:0]	wstrb;

		integer	k;
		for(k=0; k<C_AXI_DATA_WIDTH/8; k=k+1)
		begin
			apply_wstrb[k*8 +: 8]
				= wstrb[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// Verilator coverage_on
	// }}}

	// }}}

	// Make Verilator happy
	// {{{
	// Verilator coverage_off
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXI_AWPROT, S_AXI_ARPROT,
			S_AXI_ARADDR[ADDRLSB-1:0],
			S_AXI_AWADDR[ADDRLSB-1:0], wskd_strb,
			int_vector[30:6], int_vector[0],
			pic_stall, wdog_stall, apic_stall,
			pic_ack, wdog_ack, apic_ack,
			tmra_stall, tmrb_stall, tmrc_stall, jif_stall,
			tmra_ack, tmrb_ack, tmrc_ack, jif_ack };
	// Verilator lint_on  UNUSED
	// Verilator coverage_on
	// }}}
`ifdef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// Formal properties used in verfiying this core
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// The AXI-lite control interface
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{
	localparam	F_AXIL_LGDEPTH = 4;
	wire	[F_AXIL_LGDEPTH-1:0]	faxil_rd_outstanding,
					faxil_wr_outstanding,
					faxil_awr_outstanding;

	faxil_slave #(
		// {{{
		.C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
		.C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
		.F_LGDEPTH(F_AXIL_LGDEPTH),
		.F_AXI_MAXWAIT(2),
		.F_AXI_MAXDELAY(2),
		.F_AXI_MAXRSTALL(3),
		.F_OPT_COVER_BURST(4)
		// }}}
	) faxil(
		// {{{
		.i_clk(S_AXI_ACLK), .i_axi_reset_n(S_AXI_ARESETN),
		//
		.i_axi_awvalid(S_AXI_AWVALID),
		.i_axi_awready(S_AXI_AWREADY),
		.i_axi_awaddr( S_AXI_AWADDR),
		.i_axi_awprot( S_AXI_AWPROT),
		//
		.i_axi_wvalid(S_AXI_WVALID),
		.i_axi_wready(S_AXI_WREADY),
		.i_axi_wdata( S_AXI_WDATA),
		.i_axi_wstrb( S_AXI_WSTRB),
		//
		.i_axi_bvalid(S_AXI_BVALID),
		.i_axi_bready(S_AXI_BREADY),
		.i_axi_bresp( S_AXI_BRESP),
		//
		.i_axi_arvalid(S_AXI_ARVALID),
		.i_axi_arready(S_AXI_ARREADY),
		.i_axi_araddr( S_AXI_ARADDR),
		.i_axi_arprot( S_AXI_ARPROT),
		//
		.i_axi_rvalid(S_AXI_RVALID),
		.i_axi_rready(S_AXI_RREADY),
		.i_axi_rdata( S_AXI_RDATA),
		.i_axi_rresp( S_AXI_RRESP),
		//
		.f_axi_rd_outstanding(faxil_rd_outstanding),
		.f_axi_wr_outstanding(faxil_wr_outstanding),
		.f_axi_awr_outstanding(faxil_awr_outstanding)
		// }}}
		);

	always @(*)
	if (OPT_SKIDBUFFER)
	begin
		assert(faxil_awr_outstanding== (S_AXI_BVALID ? 1:0)
			+(S_AXI_AWREADY ? 0:1));
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0)
			+(S_AXI_WREADY ? 0:1));

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0)
			+(S_AXI_ARREADY ? 0:1));
	end else begin
		assert(faxil_wr_outstanding == (S_AXI_BVALID ? 1:0));
		assert(faxil_awr_outstanding == faxil_wr_outstanding);

		assert(faxil_rd_outstanding == (S_AXI_RVALID ? 1:0));
	end

	//
	// Check that our low-power only logic works by verifying that anytime
	// S_AXI_RVALID is inactive, then the outgoing data is also zero.
	//
	always @(*)
	if (OPT_LOWPOWER && !S_AXI_RVALID)
		assert(S_AXI_RDATA == 0);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// {{{

	// While there are already cover properties in the formal property
	// set above, you'll probably still want to cover something
	// application specific here

	// }}}
	// }}}
`endif
endmodule
