////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipsystem.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This portion of the ZIP CPU implements a number of soft
//		peripherals to the CPU nearby its CORE.  The functionality
//		sits on the data bus, and does not include any true
//		external hardware peripherals.  The peripherals included here
//		include:
//
//
//	Local interrupt controller--for any/all of the interrupts generated
//		here.  This would include a pin for interrupts generated
//		elsewhere, so this interrupt controller could be a master
//		handling all interrupts.  My interrupt controller would work
//		for this purpose.
//
//		The ZIP-CPU supports only one interrupt because, as I understand
//		modern systems (Linux), they tend to send all interrupts to the
//		same interrupt vector anyway.  Hence, that's what we do here.
//
//	Bus Error interrupts -- generates an interrupt any time the wishbone
//		bus produces an error on a given access, for whatever purpose
//		also records the address on the bus at the time of the error.
//
//	Trap instructions
//		Writing to this "register" will always create an interrupt.
//		After the interrupt, this register may be read to see what
//		value had been written to it.
//
//	Bit reverse register ... ?
//
//	(Potentially an eventual floating point co-processor ...)
//
//	Real-time clock
//
//	Interval timer(s) (Count down from fixed value, and either stop on
//		zero, or issue an interrupt and restart automatically on zero)
//		These can be implemented as watchdog timers if desired--the
//		only difference is that a watchdog timer's interrupt feeds the
//		reset line instead of the processor interrupt line.
//
//	Watch-dog timer: this is the same as an interval timer, only it's
//		interrupt/time-out line is wired to the reset line instead of
//		the interrupt line of the CPU.
//
//	ROM Memory map
//		Set a register to control this map, and a DMA will begin to
//		fill this memory from a slower FLASH.  Once filled, accesses
//		will be from this memory instead of 
//
//
//	Doing some market comparison, let's look at what peripherals a TI
//	MSP430 might offer: MSP's may have I2C ports, SPI, UART, DMA, ADC,
//	Comparators, 16,32-bit timers, 16x16 or 32x32 timers, AES, BSL,
//	brown-out-reset(s), real-time-clocks, temperature sensors, USB ports,
//	Spi-Bi-Wire, UART Boot-strap Loader (BSL), programmable digital I/O,
//	watchdog-timers,
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
//
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
`include "cpudefs.v"
//
// While I hate adding delays to any bus access, this next delay is required
// to make timing close in my Basys-3 design.
`define	DELAY_DBG_BUS
// On my previous version, I needed to add a delay to access the external
// bus.  Activate the define below and that delay will be put back into place.
// This particular version no longer needs the delay in order to run at 
// 100 MHz.  Timing indicates I may even run this at 250 MHz without the
// delay too, so we're doing better.  To get rid of this, I placed the logic
// determining whether or not I was accessing the local system bus one clock
// earlier, or into the memops.v file.  This also required my wishbone bus
// arbiter to maintain the bus selection as well, so that got updated ...
// you get the picture.  But, the bottom line is that I no longer need this
// delay.
//
// `define	DELAY_EXT_BUS	// Required no longer!
//
//
// If space is tight, you might not wish to have your performance and
// accounting counters, so let's make those optional here
//	Without this flag, Slice LUT count is 3315 (ZipSystem),2432 (ZipCPU)
//	When including counters, 
//		Slice LUTs	ZipSystem	ZipCPU
//	With Counters		3315		2432
//	Without Counters	2796		2046

//
// Now, where am I placing all of my peripherals?
`define	PERIPHBASE	32'hc0000000
`define	INTCTRL		5'h0	// 
`define	WATCHDOG	5'h1	// Interrupt generates reset signal
`define	BUSWATCHDOG	5'h2	// Sets IVEC[0]
`define	CTRINT		5'h3	// Sets IVEC[5]
`define	TIMER_A		5'h4	// Sets IVEC[4]
`define	TIMER_B		5'h5	// Sets IVEC[3]
`define	TIMER_C		5'h6	// Sets IVEC[2]
`define	JIFFIES		5'h7	// Sets IVEC[1]


`ifdef	INCLUDE_ACCOUNTING_COUNTERS
`define	MSTR_TASK_CTR	5'h08
`define	MSTR_MSTL_CTR	5'h09
`define	MSTR_PSTL_CTR	5'h0a
`define	MSTR_INST_CTR	5'h0b
`define	USER_TASK_CTR	5'h0c
`define	USER_MSTL_CTR	5'h0d
`define	USER_PSTL_CTR	5'h0e
`define	USER_INST_CTR	5'h0f
`endif

// Although I have a hole at 5'h2, the DMA controller requires four wishbone
// addresses, therefore we place it by itself and expand our address bus
// width here by another bit.
`define	DMAC		5'h10

// `define	RTC_CLOCK	32'hc0000008	// A global something
// `define	BITREV		32'hc0000003
//
//	DBGCTRL
//		10 HALT
//		 9 HALT(ED)
//		 8 STEP	(W=1 steps, and returns to halted)
//		 7 INTERRUPT-FLAG
//		 6 RESET_FLAG
//		ADDRESS:
//		 5	PERIPHERAL-BIT
//		[4:0]	REGISTER-ADDR
//	DBGDATA
//		read/writes internal registers
//
//
//
module	zipsystem(i_clk, i_rst,
		// Wishbone master interface from the CPU
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
		// Incoming interrupts
		i_ext_int,
		// Our one outgoing interrupt
		o_ext_int,
		// Wishbone slave interface for debugging purposes
		i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr, i_dbg_data,
			o_dbg_ack, o_dbg_stall, o_dbg_data
`ifdef	DEBUG_SCOPE
		, o_cpu_debug
`endif
		);
	parameter	RESET_ADDRESS=32'h0100000, ADDRESS_WIDTH=30,
			LGICACHE=10, START_HALTED=1, EXTERNAL_INTERRUPTS=1,
`ifdef	OPT_MULTIPLY
			IMPLEMENT_MPY = `OPT_MULTIPLY,
`else
			IMPLEMENT_MPY = 0,
`endif
`ifdef	OPT_DIVIDE
			IMPLEMENT_DIVIDE=1,
`else
			IMPLEMENT_DIVIDE=0,
`endif
`ifdef	OPT_IMPLEMENT_FPU
			IMPLEMENT_FPU=1,
`else
			IMPLEMENT_FPU=0,
`endif
			IMPLEMENT_LOCK=1;
	localparam	// Derived parameters
			AW=ADDRESS_WIDTH;
	input	i_clk, i_rst;
	// Wishbone master
	output	wire		o_wb_cyc, o_wb_stb, o_wb_we;
	output	wire	[(AW-1):0]	o_wb_addr;
	output	wire	[31:0]	o_wb_data;
	output	wire	[3:0]	o_wb_sel;
	input			i_wb_ack, i_wb_stall;
	input		[31:0]	i_wb_data;
	input			i_wb_err;
	// Incoming interrupts
	input		[(EXTERNAL_INTERRUPTS-1):0]	i_ext_int;
	// Outgoing interrupt
	output	wire		o_ext_int;
	// Wishbone slave
	input			i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr;
	input		[31:0]	i_dbg_data;
	output	wire		o_dbg_ack;
	output	wire		o_dbg_stall;
	output	wire	[31:0]	o_dbg_data;
	//
`ifdef	DEBUG_SCOPE
	output	wire	[31:0]	o_cpu_debug;
`endif

	wire	[31:0]	ext_idata;

	// Handle our interrupt vector generation/coordination
	wire	[14:0]	main_int_vector, alt_int_vector;
	wire		ctri_int, tma_int, tmb_int, tmc_int, jif_int, dmac_int;
	wire		mtc_int, moc_int, mpc_int, mic_int,
			utc_int, uoc_int, upc_int, uic_int;

	assign	main_int_vector[5:0] = { ctri_int, tma_int, tmb_int, tmc_int,
					jif_int, dmac_int };

	generate
	if (EXTERNAL_INTERRUPTS < 9)
		assign	main_int_vector[14:6] = { {(9-EXTERNAL_INTERRUPTS){1'b0}},
					i_ext_int };
	else
		assign	main_int_vector[14:6] = i_ext_int[8:0];
	endgenerate
	generate
	if (EXTERNAL_INTERRUPTS <= 9)
`ifdef	INCLUDE_ACCOUNTING_COUNTERS
		assign	alt_int_vector = { 7'h00,
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
`else
		assign	alt_int_vector = { 15'h00 };
`endif
	else
`ifdef	INCLUDE_ACCOUNTING_COUNTERS
		assign	alt_int_vector = { {(7-(EXTERNAL_INTERRUPTS-9)){1'b0}},
					i_ext_int[(EXTERNAL_INTERRUPTS-1):9],
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
`else
		assign	alt_int_vector = { {(15-(EXTERNAL_INTERRUPTS-9)){1'b0}},
					i_ext_int[(EXTERNAL_INTERRUPTS-1):9] };
`endif
	endgenerate


	// Delay the debug port by one clock, to meet timing requirements
	wire		dbg_cyc, dbg_stb, dbg_we, dbg_addr, dbg_stall;
	wire	[31:0]	dbg_idata, dbg_odata;
	reg		dbg_ack;
`ifdef	DELAY_DBG_BUS
	wire		dbg_err, no_dbg_err;
	wire	[3:0]	dbg_sel;
	assign		dbg_err = 1'b0;
	busdelay #(1,32) wbdelay(i_clk,
		i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr, i_dbg_data, 4'hf,
			o_dbg_ack, o_dbg_stall, o_dbg_data, no_dbg_err,
		dbg_cyc, dbg_stb, dbg_we, dbg_addr, dbg_idata, dbg_sel,
			dbg_ack, dbg_stall, dbg_odata, dbg_err);
`else
	assign	dbg_cyc     = i_dbg_cyc;
	assign	dbg_stb     = i_dbg_stb;
	assign	dbg_we      = i_dbg_we;
	assign	dbg_addr    = i_dbg_addr;
	assign	dbg_idata   = i_dbg_data;
	assign	o_dbg_ack   = dbg_ack;
	assign	o_dbg_stall = dbg_stall;
	assign	o_dbg_data  = dbg_odata;
`endif

	// 
	//
	//
	wire	sys_cyc, sys_stb, sys_we;
	wire	[4:0]	sys_addr;
	wire	[(AW-1):0]	cpu_addr;
	wire	[31:0]	sys_data;
	wire		sys_ack, sys_stall;

	//
	// The external debug interface
	//
	// We offer only a limited interface here, requiring a pre-register
	// write to set the local address.  This interface allows access to
	// the Zip System on a debug basis only, and not to the rest of the
	// wishbone bus.  Further, to access these registers, the control
	// register must first be accessed to both stop the CPU and to 
	// set the following address in question.  Hence all accesses require
	// two accesses: write the address to the control register (and halt
	// the CPU if not halted), then read/write the data from the data
	// register.
	//
	wire		cpu_break, dbg_cmd_write;
	reg		cmd_reset, cmd_halt, cmd_step, cmd_clear_pf_cache;
	reg	[5:0]	cmd_addr;
	wire	[3:0]	cpu_dbg_cc;
	assign	dbg_cmd_write = (dbg_cyc)&&(dbg_stb)&&(dbg_we)&&(~dbg_addr);
	//
	initial	cmd_reset = 1'b1;
	always @(posedge i_clk)
		cmd_reset <= ((dbg_cmd_write)&&(dbg_idata[6]));
	//
	initial	cmd_halt  = START_HALTED;
	always @(posedge i_clk)
		if (i_rst)
			cmd_halt <= (START_HALTED == 1)? 1'b1 : 1'b0;
		else if (dbg_cmd_write)
			cmd_halt <= ((dbg_idata[10])||(dbg_idata[8]));
		else if ((cmd_step)||(cpu_break))
			cmd_halt  <= 1'b1;

	initial	cmd_clear_pf_cache = 1'b1;
	always @(posedge i_clk)
		cmd_clear_pf_cache = (~i_rst)&&(dbg_cmd_write)
					&&((dbg_idata[11])||(dbg_idata[6]));
	//
	initial	cmd_step  = 1'b0;
	always @(posedge i_clk)
		cmd_step <= (dbg_cmd_write)&&(dbg_idata[8]);
	//
	always @(posedge i_clk)
		if (dbg_cmd_write)
			cmd_addr <= dbg_idata[5:0];

	wire	cpu_reset;
	assign	cpu_reset = (cmd_reset)||(wdt_reset)||(i_rst);

	wire	cpu_halt, cpu_dbg_stall;
	assign	cpu_halt = (i_rst)||((cmd_halt)&&(~cmd_step));
	wire	[31:0]	pic_data;
	wire	[31:0]	cmd_data;
	// Values:
	//	0x0003f -> cmd_addr mask
	//	0x00040 -> reset
	//	0x00080 -> PIC interrrupt pending
	//	0x00100 -> cmd_step
	//	0x00200 -> cmd_stall
	//	0x00400 -> cmd_halt
	//	0x00800 -> cmd_clear_pf_cache
	//	0x01000 -> cc.sleep
	//	0x02000 -> cc.gie
	//	0x04000 -> External (PIC) interrupt line is high
	//	Other external interrupts follow
	generate
	if (EXTERNAL_INTERRUPTS < 16)
		assign	cmd_data = { {(16-EXTERNAL_INTERRUPTS){1'b0}},
					i_ext_int,
				cpu_dbg_cc,	// 4 bits
				1'b0, cmd_halt, (~cpu_dbg_stall), 1'b0,
				pic_data[15], cpu_reset, cmd_addr };
	else
		assign	cmd_data = { i_ext_int[15:0], cpu_dbg_cc,
				1'b0, cmd_halt, (~cpu_dbg_stall), 1'b0,
				pic_data[15], cpu_reset, cmd_addr };
	endgenerate

	wire	cpu_gie;
	assign	cpu_gie = cpu_dbg_cc[1];

	//
	// The WATCHDOG Timer
	//
	wire		wdt_ack, wdt_stall, wdt_reset;
	wire	[31:0]	wdt_data;
	ziptimer #(32,31,0)
		watchdog(i_clk, cpu_reset, ~cmd_halt,
			sys_cyc, ((sys_stb)&&(sys_addr == `WATCHDOG)), sys_we,
				sys_data,
			wdt_ack, wdt_stall, wdt_data, wdt_reset);

	//
	// Position two, a second watchdog timer--this time for the wishbone
	// bus, in order to tell/find wishbone bus lockups.  In its current
	// configuration, it cannot be configured and all bus accesses must
	// take less than the number written to this register.
	//
	reg	wdbus_ack;
	reg	[(AW-1):0] 	r_wdbus_data;
	wire	[31:0]	 	wdbus_data;
	wire	[14:0]	wdbus_ignored_data;
	wire	reset_wdbus_timer, wdbus_int;
	assign	reset_wdbus_timer = ((o_wb_cyc)&&((o_wb_stb)||(i_wb_ack)));
	wbwatchdog #(14) watchbus(i_clk,(cpu_reset)||(reset_wdbus_timer),
			o_wb_cyc, 14'h2000, wdbus_int);
	initial	r_wdbus_data = 0;
	always @(posedge i_clk)
		if ((wdbus_int)||(cpu_ext_err))
			r_wdbus_data = o_wb_addr;
	assign	wdbus_data = { {(32-AW){1'b0}}, r_wdbus_data };
	initial	wdbus_ack = 1'b0;
	always @(posedge i_clk)
		wdbus_ack <= ((sys_cyc)&&(sys_stb)&&(sys_addr == 5'h02));

	// Counters -- for performance measurement and accounting
	//
	// Here's the stuff we'll be counting ....
	//
	wire		cpu_op_stall, cpu_pf_stall, cpu_i_count;

`ifdef	INCLUDE_ACCOUNTING_COUNTERS
	//
	// The master counters will, in general, not be reset.  They'll be used
	// for an overall counter.
	//
	// Master task counter
	wire		mtc_ack, mtc_stall;
	wire	[31:0]	mtc_data;
	zipcounter	mtask_ctr(i_clk, (~cpu_halt), sys_cyc,
				(sys_stb)&&(sys_addr == `MSTR_TASK_CTR),
					sys_we, sys_data,
				mtc_ack, mtc_stall, mtc_data, mtc_int);

	// Master Operand Stall counter
	wire		moc_ack, moc_stall;
	wire	[31:0]	moc_data;
	zipcounter	mmstall_ctr(i_clk,(cpu_op_stall), sys_cyc,
				(sys_stb)&&(sys_addr == `MSTR_MSTL_CTR),
					sys_we, sys_data,
				moc_ack, moc_stall, moc_data, moc_int);

	// Master PreFetch-Stall counter
	wire		mpc_ack, mpc_stall;
	wire	[31:0]	mpc_data;
	zipcounter	mpstall_ctr(i_clk,(cpu_pf_stall), sys_cyc,
				(sys_stb)&&(sys_addr == `MSTR_PSTL_CTR),
					sys_we, sys_data,
				mpc_ack, mpc_stall, mpc_data, mpc_int);

	// Master Instruction counter
	wire		mic_ack, mic_stall;
	wire	[31:0]	mic_data;
	zipcounter	mins_ctr(i_clk,(cpu_i_count), sys_cyc,
				(sys_stb)&&(sys_addr == `MSTR_INST_CTR),
					sys_we, sys_data,
				mic_ack, mic_stall, mic_data, mic_int);

	//
	// The user counters are different from those of the master.  They will
	// be reset any time a task is given control of the CPU.
	//
	// User task counter
	wire		utc_ack, utc_stall;
	wire	[31:0]	utc_data;
	zipcounter	utask_ctr(i_clk,(~cpu_halt)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sys_addr == `USER_TASK_CTR),
					sys_we, sys_data,
				utc_ack, utc_stall, utc_data, utc_int);

	// User Op-Stall counter
	wire		uoc_ack, uoc_stall;
	wire	[31:0]	uoc_data;
	zipcounter	umstall_ctr(i_clk,(cpu_op_stall)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sys_addr == `USER_MSTL_CTR),
					sys_we, sys_data,
				uoc_ack, uoc_stall, uoc_data, uoc_int);

	// User PreFetch-Stall counter
	wire		upc_ack, upc_stall;
	wire	[31:0]	upc_data;
	zipcounter	upstall_ctr(i_clk,(cpu_pf_stall)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sys_addr == `USER_PSTL_CTR),
					sys_we, sys_data,
				upc_ack, upc_stall, upc_data, upc_int);

	// User instruction counter
	wire		uic_ack, uic_stall;
	wire	[31:0]	uic_data;
	zipcounter	uins_ctr(i_clk,(cpu_i_count)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sys_addr == `USER_INST_CTR),
					sys_we, sys_data,
				uic_ack, uic_stall, uic_data, uic_int);

	// A little bit of pre-cleanup (actr = accounting counters)
	wire		actr_ack, actr_stall;
	wire	[31:0]	actr_data;
	assign	actr_ack = ((mtc_ack | moc_ack | mpc_ack | mic_ack)
				|(utc_ack | uoc_ack | upc_ack | uic_ack));
	assign	actr_stall = ((mtc_stall | moc_stall | mpc_stall | mic_stall)
				|(utc_stall | uoc_stall | upc_stall|uic_stall));
	assign	actr_data = ((mtc_ack) ? mtc_data
				: ((moc_ack) ? moc_data
				: ((mpc_ack) ? mpc_data
				: ((mic_ack) ? mic_data
				: ((utc_ack) ? utc_data
				: ((uoc_ack) ? uoc_data
				: ((upc_ack) ? upc_data
				: uic_data)))))));
`else //	INCLUDE_ACCOUNTING_COUNTERS
	reg		actr_ack;
	wire		actr_stall;
	wire	[31:0]	actr_data;
	assign	actr_stall = 1'b0;
	assign	actr_data = 32'h0000;

	assign	mtc_int = 1'b0;
	assign	moc_int = 1'b0;
	assign	mpc_int = 1'b0;
	assign	mic_int = 1'b0;
	assign	utc_int = 1'b0;
	assign	uoc_int = 1'b0;
	assign	upc_int = 1'b0;
	assign	uic_int = 1'b0;

	always @(posedge i_clk)
		actr_ack <= (sys_stb)&&(sys_addr[4:3] == 2'b01);
`endif	//	INCLUDE_ACCOUNTING_COUNTERS

	//
	// The DMA Controller
	//
	wire		dmac_stb, dc_err;
	wire	[31:0]	dmac_data;
	wire		dmac_ack, dmac_stall;
	wire		dc_cyc, dc_stb, dc_we, dc_ack, dc_stall;
	wire	[31:0]	dc_data;
	wire	[(AW-1):0]	dc_addr;
	wire		cpu_gbl_cyc;
	wire	[31:0]	dmac_int_vec;
	assign	dmac_int_vec = { 1'b0, alt_int_vector, 1'b0,
					main_int_vector[14:1], 1'b0 };
	assign	dmac_stb = (sys_stb)&&(sys_addr[4]);
`ifdef	INCLUDE_DMA_CONTROLLER
	wbdmac	#(AW) dma_controller(i_clk, cpu_reset,
				sys_cyc, dmac_stb, sys_we,
					sys_addr[1:0], sys_data,
					dmac_ack, dmac_stall, dmac_data,
				// Need the outgoing DMAC wishbone bus
				dc_cyc, dc_stb, dc_we, dc_addr, dc_data,
					dc_ack, dc_stall, ext_idata, dc_err,
				// External device interrupts
				dmac_int_vec,
				// DMAC interrupt, for upon completion
				dmac_int);
`else
	reg	r_dmac_ack;
	always @(posedge i_clk)
		r_dmac_ack <= (sys_cyc)&&(dmac_stb);
	assign	dmac_ack = r_dmac_ack;
	assign	dmac_data = 32'h000;
	assign	dmac_stall = 1'b0;

	assign	dc_cyc  = 1'b0;
	assign	dc_stb  = 1'b0;
	assign	dc_we   = 1'b0;
	assign	dc_addr = { (AW) {1'b0} };
	assign	dc_data = 32'h00;

	assign	dmac_int = 1'b0;
`endif

	wire		ctri_sel, ctri_stall;
	reg		ctri_ack;
	wire	[31:0]	ctri_data;
	assign	ctri_sel = (sys_stb)&&(sys_addr == `CTRINT);
	always @(posedge i_clk)
		ctri_ack <= ctri_sel;
	assign	ctri_stall = 1'b0;
`ifdef	INCLUDE_ACCOUNTING_COUNTERS
	//
	// Counter Interrupt controller
	//
	generate
	if (EXTERNAL_INTERRUPTS <= 9)
	begin
		icontrol #(8)	ctri(i_clk, cpu_reset, (ctri_sel),
					sys_data, ctri_data, alt_int_vector[7:0],
					ctri_int);
	end else begin
		icontrol #(8+(EXTERNAL_INTERRUPTS-9))
				ctri(i_clk, cpu_reset, (ctri_sel),
					sys_data, ctri_data,
					alt_int_vector[(EXTERNAL_INTERRUPTS-2):0],
					ctri_int);
	end endgenerate

`else	//	INCLUDE_ACCOUNTING_COUNTERS

	generate
	if (EXTERNAL_INTERRUPTS <= 9)
	begin
		assign	ctri_stall = 1'b0;
		assign	ctri_data  = 32'h0000;
		assign	ctri_int   = 1'b0;
	end else begin
		icontrol #(EXTERNAL_INTERRUPTS-9)
				ctri(i_clk, cpu_reset, (ctri_sel),
					sys_data, ctri_data,
				alt_int_vector[(EXTERNAL_INTERRUPTS-10):0],
					ctri_int);
	end endgenerate
`endif	//	INCLUDE_ACCOUNTING_COUNTERS


	//
	// Timer A
	//
	wire		tma_ack, tma_stall;
	wire	[31:0]	tma_data;
	ziptimer timer_a(i_clk, cpu_reset, ~cmd_halt,
			sys_cyc, (sys_stb)&&(sys_addr == `TIMER_A), sys_we,
				sys_data,
			tma_ack, tma_stall, tma_data, tma_int);

	//
	// Timer B
	//
	wire		tmb_ack, tmb_stall;
	wire	[31:0]	tmb_data;
	ziptimer timer_b(i_clk, cpu_reset, ~cmd_halt,
			sys_cyc, (sys_stb)&&(sys_addr == `TIMER_B), sys_we,
				sys_data,
			tmb_ack, tmb_stall, tmb_data, tmb_int);

	//
	// Timer C
	//
	wire		tmc_ack, tmc_stall;
	wire	[31:0]	tmc_data;
	ziptimer timer_c(i_clk, cpu_reset, ~cmd_halt,
			sys_cyc, (sys_stb)&&(sys_addr == `TIMER_C), sys_we,
				sys_data,
			tmc_ack, tmc_stall, tmc_data, tmc_int);

	//
	// JIFFIES
	//
	wire		jif_ack, jif_stall;
	wire	[31:0]	jif_data;
	zipjiffies jiffies(i_clk, ~cmd_halt,
			sys_cyc, (sys_stb)&&(sys_addr == `JIFFIES), sys_we,
				sys_data,
			jif_ack, jif_stall, jif_data, jif_int);

	//
	// The programmable interrupt controller peripheral
	//
	wire		pic_interrupt;
	generate
	if (EXTERNAL_INTERRUPTS < 9)
	begin
		icontrol #(6+EXTERNAL_INTERRUPTS)	pic(i_clk, cpu_reset,
					(sys_cyc)&&(sys_stb)&&(sys_we)
						&&(sys_addr==`INTCTRL),
					sys_data, pic_data,
					main_int_vector[(6+EXTERNAL_INTERRUPTS-1):0], pic_interrupt);
	end else begin
		icontrol #(15)	pic(i_clk, cpu_reset,
					(sys_cyc)&&(sys_stb)&&(sys_we)
						&&(sys_addr==`INTCTRL),
					sys_data, pic_data,
					main_int_vector[14:0], pic_interrupt);
	end endgenerate

	wire	pic_stall;
	assign	pic_stall = 1'b0;
	reg	pic_ack;
	always @(posedge i_clk)
		pic_ack <= (sys_stb)&&(sys_addr == `INTCTRL);

	//
	// The CPU itself
	//
	wire		cpu_gbl_stb, cpu_lcl_cyc, cpu_lcl_stb, 
			cpu_we, cpu_dbg_we;
	wire	[31:0]	cpu_data, wb_data;
	wire	[3:0]	cpu_sel;
	wire		cpu_ack, cpu_stall, cpu_err;
	wire	[31:0]	cpu_dbg_data;
	assign cpu_dbg_we = ((dbg_cyc)&&(dbg_stb)&&(~cmd_addr[5])
					&&(dbg_we)&&(dbg_addr));
	zipcpu	#(
			.RESET_ADDRESS(RESET_ADDRESS),
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.LGICACHE(LGICACHE),
			.IMPLEMENT_MPY(IMPLEMENT_MPY),
			.IMPLEMENT_DIVIDE(IMPLEMENT_DIVIDE),
			.IMPLEMENT_FPU(IMPLEMENT_FPU),
			.IMPLEMENT_LOCK(IMPLEMENT_LOCK)
		)
		thecpu(i_clk, cpu_reset, pic_interrupt,
			cpu_halt, cmd_clear_pf_cache, cmd_addr[4:0], cpu_dbg_we,
				dbg_idata, cpu_dbg_stall, cpu_dbg_data,
				cpu_dbg_cc, cpu_break,
			cpu_gbl_cyc, cpu_gbl_stb,
				cpu_lcl_cyc, cpu_lcl_stb,
				cpu_we, cpu_addr, cpu_data, cpu_sel,
				cpu_ack, cpu_stall, wb_data,
				cpu_err,
			cpu_op_stall, cpu_pf_stall, cpu_i_count
`ifdef	DEBUG_SCOPE
			, o_cpu_debug
`endif
			);

	// Now, arbitrate the bus ... first for the local peripherals
	// For the debugger to have access to the local system bus, the
	// following must be true:
	//	(dbg_cyc)	The debugger must request the bus
	//	(~cpu_lcl_cyc)	The CPU cannot be using it (CPU gets priority)
	//	(dbg_addr)	The debugger must be requesting its data
	//				register, not just the control register
	// and one of two other things.  Either
	//	((cpu_halt)&&(~cpu_dbg_stall))	the CPU is completely halted,
	// or
	//	(~cmd_addr[5])		we are trying to read a CPU register
	//			while in motion.  Let the user beware that,
	//			by not waiting for the CPU to fully halt,
	//			his results may not be what he expects.
	//
	wire	sys_dbg_cyc = ((dbg_cyc)&&(~cpu_lcl_cyc)&&(dbg_addr))
				&&(((cpu_halt)&&(~cpu_dbg_stall))
					||(~cmd_addr[5]));
	assign	sys_cyc = (cpu_lcl_cyc)||(sys_dbg_cyc);
	assign	sys_stb = (cpu_lcl_cyc)
				? (cpu_lcl_stb)
				: ((dbg_stb)&&(dbg_addr)&&(cmd_addr[5]));

	assign	sys_we  = (cpu_lcl_cyc) ? cpu_we : dbg_we;
	assign	sys_addr= (cpu_lcl_cyc) ? cpu_addr[4:0] : cmd_addr[4:0];
	assign	sys_data= (cpu_lcl_cyc) ? cpu_data : dbg_idata;

	// Return debug response values
	assign	dbg_odata = (~dbg_addr)?cmd_data
				:((~cmd_addr[5])?cpu_dbg_data : wb_data);
	initial dbg_ack = 1'b0;
	always @(posedge i_clk)
		dbg_ack <= (dbg_cyc)&&(dbg_stb)&&(~dbg_stall);
	assign	dbg_stall=(dbg_cyc)&&((~sys_dbg_cyc)||(sys_stall))&&(dbg_addr);

	// Now for the external wishbone bus
	//	Need to arbitrate between the flash cache and the CPU
	// The way this works, though, the CPU will stall once the flash 
	// cache gets access to the bus--the CPU will be stuck until the 
	// flash cache is finished with the bus.
	wire		ext_cyc, ext_stb, ext_we, ext_err;
	wire		cpu_ext_ack, cpu_ext_stall, ext_ack, ext_stall,
				cpu_ext_err;
	wire	[(AW-1):0]	ext_addr;
	wire	[31:0]		ext_odata;
	wire	[3:0]		ext_sel;
	wbpriarbiter #(32,AW) dmacvcpu(i_clk,
			cpu_gbl_cyc, cpu_gbl_stb, cpu_we, cpu_addr, cpu_data, cpu_sel,
				cpu_ext_ack, cpu_ext_stall, cpu_ext_err,
			dc_cyc, dc_stb, dc_we, dc_addr, dc_data, 4'hf,
					dc_ack, dc_stall, dc_err,
			ext_cyc, ext_stb, ext_we, ext_addr, ext_odata, ext_sel,
				ext_ack, ext_stall, ext_err);

`ifdef	DELAY_EXT_BUS
	busdelay #(AW,32) extbus(i_clk,
			ext_cyc, ext_stb, ext_we, ext_addr, ext_odata,
				ext_ack, ext_stall, ext_idata, ext_err,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_data, (i_wb_err)||(wdbus_int));
`else
	assign	o_wb_cyc  = ext_cyc;
	assign	o_wb_stb  = ext_stb;
	assign	o_wb_we   = ext_we;
	assign	o_wb_addr = ext_addr;
	assign	o_wb_data = ext_odata;
	assign	o_wb_sel  = ext_sel;
	assign	ext_ack   = i_wb_ack;
	assign	ext_stall = i_wb_stall;
	assign	ext_idata = i_wb_data;
	assign	ext_err   = (i_wb_err)||(wdbus_int);
`endif

	wire		tmr_ack;
	assign	tmr_ack = (tma_ack|tmb_ack|tmc_ack|jif_ack);
	wire	[31:0]	tmr_data;
	assign	tmr_data = (tma_ack)?tma_data
				:(tmb_ack ? tmb_data
				:(tmc_ack ? tmc_data
				:jif_data));
	assign	wb_data = (tmr_ack|wdt_ack)?((tmr_ack)?tmr_data:wdt_data)
			:((actr_ack|dmac_ack)?((actr_ack)?actr_data:dmac_data)
			:((pic_ack|ctri_ack)?((pic_ack)?pic_data:ctri_data)
			:((wdbus_ack)?wdbus_data:(ext_idata))));

	assign	sys_stall = (tma_stall | tmb_stall | tmc_stall | jif_stall
				| wdt_stall | ctri_stall | actr_stall 
				| pic_stall | dmac_stall); // Always 1'b0!
	assign	cpu_stall = (sys_stall)|(cpu_ext_stall);
	assign	sys_ack = (tmr_ack|wdt_ack|ctri_ack|actr_ack|pic_ack|dmac_ack|wdbus_ack);
	assign	cpu_ack = (sys_ack)||(cpu_ext_ack);
	assign	cpu_err = (cpu_ext_err)&&(cpu_gbl_cyc);

	assign	o_ext_int = (cmd_halt) && (~cpu_stall);

endmodule
