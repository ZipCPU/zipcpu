////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipsystem.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This portion of the ZIP CPU implements a number of soft
//		peripherals to the CPU nearby its CORE.  The functionality
//	sits on the data bus, and does not include any true external hardware
//	peripherals.  The peripherals included here include:
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
//	Direct Memory Access Controller: This controller allows you to command
//		automatic memory moves.  Such memory moves will take place
//		without the CPU's involvement until they are done.  See the
//		DMA specification for more information. (Currently contained
//		w/in the ZipCPU spec.)
//
//	(Potentially an eventual floating point co-processor ...?)
//
// Busses:	The ZipSystem implements a series of busses to make this take
//		place.  These busses are identified by their prefix:
//
//	cpu	This is the bus as the CPU sees it.  Since the CPU controls
//		two busses (a local and a global one), it uses _gbl_ to indicate
//		the external bus (going through the MMU if necessary) and
//		_lcl_ to indicate a peripheral bus seen here.
//
//	mmu	Sits between the CPU's wishbone interface and the external
//		bus.  Has no access to peripherals.
//
//	sys	A local bus implemented here within this space.  This is how the
//		CPU talks to the ZipSystem peripherals.  However, this bus
//		can also be accessed from the external debug bus.
//
//	io_dbg
//	io_wb
//
//	dbg	This is identical to the io_dbg bus, but separated by a clock
//	dc	The output of the DMA controller
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2020, Gisselquist Technology, LLC
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
`default_nettype	none
//
`include "cpudefs.v"
//
`define	RESET_BIT	6
`define	STEP_BIT	8
`define	HALT_BIT	10
`define	CLEAR_CACHE_BIT	11
//
// While I hate adding delays to any bus access, this next delay is required
// to make timing close in my Basys-3 design.
`define	DELAY_DBG_BUS
//
// `define	DELAY_EXT_BUS
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
`define	INTCTRL		8'h0	//
`define	WATCHDOG	8'h1	// Interrupt generates reset signal
`define	BUSWATCHDOG	8'h2	// Sets IVEC[0]
`define	CTRINT		8'h3	// Sets IVEC[5]
`define	TIMER_A		8'h4	// Sets IVEC[4]
`define	TIMER_B		8'h5	// Sets IVEC[3]
`define	TIMER_C		8'h6	// Sets IVEC[2]
`define	JIFFIES		8'h7	// Sets IVEC[1]


`ifdef	INCLUDE_ACCOUNTING_COUNTERS
`define	MSTR_TASK_CTR	8'h08
`define	MSTR_MSTL_CTR	8'h09
`define	MSTR_PSTL_CTR	8'h0a
`define	MSTR_INST_CTR	8'h0b
`define	USER_TASK_CTR	8'h0c
`define	USER_MSTL_CTR	8'h0d
`define	USER_PSTL_CTR	8'h0e
`define	USER_INST_CTR	8'h0f
`endif

`ifdef	OPT_MMU
`define	MMU_ADDR	8'h80
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
`ifdef	OPT_TRADITIONAL_PFCACHE
`define	LGICACHE_DEFAULT	10
`else
`define	LGICACHE_DEFAULT	0
`endif
//
`ifdef	OPT_DCACHE
`define	LGDCACHE_DEFAULT	10
`else
`define	LGDCACHE_DEFAULT	0
`endif
module	zipsystem(i_clk, i_reset,
		// Wishbone master interface from the CPU
		o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_stall, i_wb_ack, i_wb_data, i_wb_err,
		// Incoming interrupts
		i_ext_int,
		// Our one outgoing interrupt
		o_ext_int,
		// Wishbone slave interface for debugging purposes
		i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr, i_dbg_data,
				i_dbg_sel,
			o_dbg_stall, o_dbg_ack, o_dbg_data
`ifdef	DEBUG_SCOPE
		, o_cpu_debug
`endif
		);
	parameter	RESET_ADDRESS=32'h1000_0000, ADDRESS_WIDTH=30,
			LGICACHE=`LGICACHE_DEFAULT,
			LGDCACHE=`LGDCACHE_DEFAULT;	// Set to zero for no data cache
	parameter [0:0]	START_HALTED=1;
	parameter	EXTERNAL_INTERRUPTS=1,
`ifdef	OPT_MULTIPLY
			IMPLEMENT_MPY = `OPT_MULTIPLY;
`else
			IMPLEMENT_MPY = 0;
`endif
	parameter [0:0]
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
	parameter	RESET_DURATION = 0;
	localparam	// Derived parameters
			PHYSICAL_ADDRESS_WIDTH=ADDRESS_WIDTH,
			PAW=ADDRESS_WIDTH,
`ifdef	OPT_MMU
			VIRTUAL_ADDRESS_WIDTH=30,
`else
			VIRTUAL_ADDRESS_WIDTH=PAW,
`endif
			LGTLBSZ = 6,
			VAW=VIRTUAL_ADDRESS_WIDTH;

	localparam	AW=ADDRESS_WIDTH;
	input	wire	i_clk, i_reset;
	// Wishbone master
	output	wire		o_wb_cyc, o_wb_stb, o_wb_we;
	output	wire	[(PAW-1):0]	o_wb_addr;
	output	wire	[31:0]	o_wb_data;
	output	wire	[3:0]	o_wb_sel;
	input	wire		i_wb_stall, i_wb_ack;
	input	wire	[31:0]	i_wb_data;
	input	wire		i_wb_err;
	// Incoming interrupts
	input	wire	[(EXTERNAL_INTERRUPTS-1):0]	i_ext_int;
	// Outgoing interrupt
	output	wire		o_ext_int;
	// Wishbone slave
	input	wire		i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr;
	input	wire	[31:0]	i_dbg_data;
	input	wire	[3:0]	i_dbg_sel;
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
	if (EXTERNAL_INTERRUPTS >= 15)
		assign	alt_int_vector = { i_ext_int[14:8],
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
	else
		assign	alt_int_vector = { {(7-(EXTERNAL_INTERRUPTS-9)){1'b0}},
					i_ext_int[(EXTERNAL_INTERRUPTS-1):9],
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
`else
	if (EXTERNAL_INTERRUPTS >= 24)
		assign	alt_int_vector = { i_ext_int[(EXTERNAL_INTERRUPTS-1):9] };
	else
		assign	alt_int_vector = { {(15-(EXTERNAL_INTERRUPTS-9)){1'b0}},
					i_ext_int[(EXTERNAL_INTERRUPTS-1):9] };
`endif
	endgenerate


	// Delay the debug port by one clock, to meet timing requirements
	wire		dbg_cyc, dbg_stb, dbg_we, dbg_addr, dbg_stall;
	wire	[31:0]	dbg_idata, dbg_odata;
	reg		dbg_ack;
	wire	[3:0]	dbg_sel;
	wire		no_dbg_err;
`ifdef	DELAY_DBG_BUS
	// Make verilator happy
	// verilator lint_off UNUSED
	// verilator lint_on  UNUSED
	wire		dbg_err;
	assign		dbg_err = 1'b0;
	busdelay #(1,32) wbdelay(i_clk, i_reset,
		i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr, i_dbg_data, 4'hf,
			o_dbg_stall, o_dbg_ack, o_dbg_data, no_dbg_err,
		dbg_cyc, dbg_stb, dbg_we, dbg_addr, dbg_idata, dbg_sel,
			dbg_stall, dbg_ack, dbg_odata, dbg_err);
`else
	assign	dbg_cyc     = i_dbg_cyc;
	assign	dbg_stb     = i_dbg_stb;
	assign	dbg_we      = i_dbg_we;
	assign	dbg_addr    = i_dbg_addr;
	assign	dbg_idata   = i_dbg_data;
	assign	o_dbg_ack   = dbg_ack;
	assign	o_dbg_stall = dbg_stall;
	assign	o_dbg_data  = dbg_odata;
	assign	dbg_sel     = 4'b1111;
	assign	no_dbg_err  = 1'b0;
`endif

	//
	//
	//
	wire	sys_cyc, sys_stb, sys_we;
	wire	[7:0]	sys_addr;
	wire	[(PAW-1):0]	cpu_addr;
	wire	[31:0]	sys_data;
	reg	[31:0]	sys_idata;
	reg		sys_ack;
	wire		sys_stall;

	wire	sel_counter, sel_timer, sel_pic, sel_apic,
		sel_watchdog, sel_bus_watchdog, sel_dmac, sel_mmus;
	//
	assign	sel_pic         = (sys_stb)&&(sys_addr == `INTCTRL);
	assign	sel_watchdog    = (sys_stb)&&(sys_addr == `WATCHDOG);
	assign	sel_bus_watchdog= (sys_stb)&&(sys_addr == `BUSWATCHDOG);
	assign	sel_apic        = (sys_stb)&&(sys_addr == `CTRINT);
	assign	sel_timer       = (sys_stb)&&(sys_addr[7:2] == 6'h1);
	assign	sel_counter     = (sys_stb)&&(sys_addr[7:3] == 5'h1);
	assign	sel_dmac        = (sys_stb)&&(sys_addr[7:4] == 4'h1);
	assign	sel_mmus        = (sys_stb)&&(sys_addr[7]);

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
	reg		cmd_reset, cmd_halt, cmd_step, cmd_clear_pf_cache,
			reset_hold, cpu_halt;
	reg	[5:0]	cmd_addr;
	wire	[3:0]	cpu_dbg_cc;
	assign	dbg_cmd_write = (dbg_stb)&&(dbg_we)&&(!dbg_addr);
	//
	// Always start us off with an initial reset
	//
	generate if (RESET_DURATION > 0)
	begin : INITIAL_RESET_HOLD

		reg	[$clog2(RESET_DURATION)-1:0]	reset_counter;

		initial	reset_counter = RESET_DURATION;
		always @(posedge i_clk)
		if (i_reset)
			reset_counter <= RESET_DURATION;
		else if (reset_counter > 0)
			reset_counter <= reset_counter - 1;

		initial	reset_hold = 1;
		always @(posedge i_clk)
		if (i_reset)
			reset_hold <= 1;
		else
			reset_hold <= (reset_counter != 0);

		initial	cmd_halt  = START_HALTED;
		always @(posedge i_clk)
		if (i_reset)
			cmd_halt <= START_HALTED;
		else if (dbg_cmd_write)
			cmd_halt <= ((dbg_idata[`HALT_BIT])&&(!dbg_idata[`STEP_BIT]));

	end else begin

		always @(*)
			reset_hold = 0;

		always @(*)
			cmd_halt = START_HALTED;

	end endgenerate

	initial	cmd_reset = 1'b1;
	always @(posedge i_clk)
		cmd_reset <= ((dbg_cmd_write)&&(dbg_idata[`RESET_BIT]))
			||(wdt_reset) || reset_hold;
	//
	initial	cpu_halt  = START_HALTED;
	always @(posedge i_clk)
	if (i_reset)
		cpu_halt <= cmd_halt;
	else if (cmd_reset)
		cpu_halt <= cmd_halt;
	else if (dbg_cmd_write)
		cpu_halt <= ((dbg_idata[`HALT_BIT])&&(!dbg_idata[`STEP_BIT]));
	else if ((cmd_step)||(cpu_break))
		cpu_halt  <= 1'b1;

	initial	cmd_clear_pf_cache = 1'b1;
	always @(posedge i_clk)
		cmd_clear_pf_cache <= (dbg_cmd_write)&&(dbg_idata[`CLEAR_CACHE_BIT]);
	//
	initial	cmd_step  = 1'b0;
	always @(posedge i_clk)
		cmd_step <= (dbg_cmd_write)&&(dbg_idata[`STEP_BIT]);
	//
	initial	cmd_addr = 6'h0;
	always @(posedge i_clk)
	if (dbg_cmd_write)
		cmd_addr <= dbg_idata[5:0];

	wire	cpu_reset;
	assign	cpu_reset = (cmd_reset);

	wire	cpu_dbg_stall;
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
				1'b0, cmd_halt, (!cpu_dbg_stall), 1'b0,
				pic_data[15], cpu_reset, cmd_addr };
	else
		assign	cmd_data = { i_ext_int[15:0], cpu_dbg_cc,
				1'b0, cmd_halt, (!cpu_dbg_stall), 1'b0,
				pic_data[15], cpu_reset, cmd_addr };
	endgenerate

	wire	cpu_gie;
	assign	cpu_gie = cpu_dbg_cc[1];

	//
	// The WATCHDOG Timer
	//
	wire		wdt_stall, wdt_ack, wdt_reset;
	wire	[31:0]	wdt_data;
	ziptimer #(32,31,0)
		watchdog(i_clk, cpu_reset, !cmd_halt,
			sys_cyc, (sys_stb)&&(sel_watchdog), sys_we,
				sys_data,
			wdt_stall, wdt_ack, wdt_data, wdt_reset);

	//
	// Position two, a second watchdog timer--this time for the wishbone
	// bus, in order to tell/find wishbone bus lockups.  In its current
	// configuration, it cannot be configured and all bus accesses must
	// take less than the number written to this register.
	//
	reg	wdbus_ack;
	reg	[(PAW-1):0] 	r_wdbus_data;
	wire	[31:0]	 	wdbus_data;
	wire	reset_wdbus_timer, wdbus_int;
	assign	reset_wdbus_timer = (!o_wb_cyc)||(o_wb_stb)||(i_wb_ack);
	wbwatchdog #(14) watchbus(i_clk,(cpu_reset)||(reset_wdbus_timer),
			14'h2000, wdbus_int);
	initial	r_wdbus_data = 0;
	always @(posedge i_clk)
		if ((wdbus_int)||(cpu_err))
			r_wdbus_data <= o_wb_addr;
	assign	wdbus_data = { {(32-PAW){1'b0}}, r_wdbus_data };
	initial	wdbus_ack = 1'b0;
	always @(posedge i_clk)
		wdbus_ack <= ((sys_cyc)&&(sys_stb)&&(sel_bus_watchdog));

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
	wire		mtc_stall, mtc_ack;
	wire	[31:0]	mtc_data;
	zipcounter	mtask_ctr(i_clk, 1'b0, (!cpu_halt), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b000),
					sys_we, sys_data,
				mtc_stall, mtc_ack, mtc_data, mtc_int);

	// Master Operand Stall counter
	wire		moc_stall, moc_ack;
	wire	[31:0]	moc_data;
	zipcounter	mmstall_ctr(i_clk,1'b0, (cpu_op_stall), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b001),
					sys_we, sys_data,
				moc_stall, moc_ack, moc_data, moc_int);

	// Master PreFetch-Stall counter
	wire		mpc_stall, mpc_ack;
	wire	[31:0]	mpc_data;
	zipcounter	mpstall_ctr(i_clk,1'b0, (cpu_pf_stall), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b010),
					sys_we, sys_data,
				mpc_stall, mpc_ack, mpc_data, mpc_int);

	// Master Instruction counter
	wire		mic_stall, mic_ack;
	wire	[31:0]	mic_data;
	zipcounter	mins_ctr(i_clk,1'b0, (cpu_i_count), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b011),
					sys_we, sys_data,
				mic_stall, mic_ack, mic_data, mic_int);

	//
	// The user counters are different from those of the master.  They will
	// be reset any time a task is given control of the CPU.
	//
	// User task counter
	wire		utc_stall, utc_ack;
	wire	[31:0]	utc_data;
	zipcounter	utask_ctr(i_clk,1'b0, (!cpu_halt)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b100),
					sys_we, sys_data,
				utc_stall, utc_ack, utc_data, utc_int);

	// User Op-Stall counter
	wire		uoc_stall, uoc_ack;
	wire	[31:0]	uoc_data;
	zipcounter	umstall_ctr(i_clk,1'b0, (cpu_op_stall)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b101),
					sys_we, sys_data,
				uoc_stall, uoc_ack, uoc_data, uoc_int);

	// User PreFetch-Stall counter
	wire		upc_stall, upc_ack;
	wire	[31:0]	upc_data;
	zipcounter	upstall_ctr(i_clk,1'b0, (cpu_pf_stall)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b110),
					sys_we, sys_data,
				upc_stall, upc_ack, upc_data, upc_int);

	// User instruction counter
	wire		uic_stall, uic_ack;
	wire	[31:0]	uic_data;
	zipcounter	uins_ctr(i_clk,1'b0, (cpu_i_count)&&(cpu_gie), sys_cyc,
				(sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b111),
					sys_we, sys_data,
				uic_stall, uic_ack, uic_data, uic_int);

	// A little bit of pre-cleanup (actr = accounting counters)
	wire		actr_stall, actr_ack;
	reg	[31:0]	actr_data;
	assign	actr_ack = sel_counter;
	assign	actr_stall = 1'b0;
	always @(*)
	begin
		case(sys_addr[2:0])
		3'h0: actr_data = mtc_data;
		3'h1: actr_data = moc_data;
		3'h2: actr_data = mpc_data;
		3'h3: actr_data = mic_data;
		3'h4: actr_data = utc_data;
		3'h5: actr_data = uoc_data;
		3'h6: actr_data = upc_data;
		3'h7: actr_data = uic_data;
		endcase
	end
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
		actr_ack <= sel_counter;
`endif	//	INCLUDE_ACCOUNTING_COUNTERS

	//
	// The DMA Controller
	//
	wire		dmac_stb, dc_err;
	wire	[31:0]	dmac_data;
	wire		dmac_stall, dmac_ack;
	wire		dc_cyc, dc_stb, dc_we, dc_stall, dc_ack;
	wire	[31:0]	dc_data;
	wire	[(PAW-1):0]	dc_addr;
	wire		cpu_gbl_cyc;
	wire	[31:0]	dmac_int_vec;
	assign	dmac_int_vec = { 1'b0, alt_int_vector, 1'b0,
					main_int_vector[14:1], 1'b0 };
	assign	dmac_stb = (sys_stb)&&(sel_dmac);
`ifdef	INCLUDE_DMA_CONTROLLER
	wbdmac	#(PAW) dma_controller(i_clk, cpu_reset,
				sys_cyc, dmac_stb, sys_we,
					sys_addr[1:0], sys_data,
					dmac_stall, dmac_ack, dmac_data,
				// Need the outgoing DMAC wishbone bus
				dc_cyc, dc_stb, dc_we, dc_addr, dc_data,
					dc_stall, dc_ack, ext_idata, dc_err,
				// External device interrupts
				dmac_int_vec,
				// DMAC interrupt, for upon completion
				dmac_int);
`else
	reg	r_dmac_ack;
	initial	r_dmac_ack = 1'b0;
	always @(posedge i_clk)
		r_dmac_ack <= (sys_cyc)&&(dmac_stb);
	assign	dmac_ack = r_dmac_ack;
	assign	dmac_data = 32'h000;
	assign	dmac_stall = 1'b0;

	assign	dc_cyc  = 1'b0;
	assign	dc_stb  = 1'b0;
	assign	dc_we   = 1'b0;
	assign	dc_addr = { (PAW) {1'b0} };
	assign	dc_data = 32'h00;

	assign	dmac_int = 1'b0;
`endif

	wire		ctri_sel, ctri_stall, ctri_ack;
	wire	[31:0]	ctri_data;
	assign	ctri_sel = (sys_stb)&&(sel_apic);
`ifdef	INCLUDE_ACCOUNTING_COUNTERS
	//
	// Counter Interrupt controller
	//
	generate if (EXTERNAL_INTERRUPTS <= 9)
	begin : ALT_PIC
		icontrol #(8)	ctri(i_clk, cpu_reset, sys_cyc, (ctri_sel), sys_we,
				sys_data, 4'hf, ctri_stall, ctri_ack, ctri_data,
				alt_int_vector[7:0], ctri_int);
	end else begin : ALT_PIC
		icontrol #(8+(EXTERNAL_INTERRUPTS-9))
				ctri(i_clk, cpu_reset, sys_cyc, (ctri_sel), sys_we,
				sys_data, 4'hf, ctri_stall, ctri_ack, ctri_data,
				alt_int_vector[(EXTERNAL_INTERRUPTS-2):0],
					ctri_int);
	end endgenerate

`else	//	INCLUDE_ACCOUNTING_COUNTERS

	generate if (EXTERNAL_INTERRUPTS <= 9)
	begin : ALT_PIC
		assign	ctri_stall = 1'b0;
		assign	ctri_data  = 32'h0000;
		assign	ctri_int   = 1'b0;
	end else begin : ALT_PIC
		icontrol #(EXTERNAL_INTERRUPTS-9)
				ctri(i_clk, cpu_reset, (ctri_sel), sys_we,
				sys_data, ctri_stall, ctri_ack, ctri_data,
				alt_int_vector[(EXTERNAL_INTERRUPTS-10):0],
					ctri_int);
	end endgenerate
`endif	//	INCLUDE_ACCOUNTING_COUNTERS


	//
	// Timer A
	//
	wire		tma_stall, tma_ack;
	wire	[31:0]	tma_data;
	ziptimer timer_a(i_clk, cpu_reset, !cmd_halt,
		sys_cyc, (sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b00),
			sys_we, sys_data,
		tma_stall, tma_ack, tma_data, tma_int);

	//
	// Timer B
	//
	wire		tmb_stall, tmb_ack;
	wire	[31:0]	tmb_data;
	ziptimer timer_b(i_clk, cpu_reset, !cmd_halt,
		sys_cyc, (sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b01),
			sys_we, sys_data,
		tmb_stall, tmb_ack, tmb_data, tmb_int);

	//
	// Timer C
	//
	wire		tmc_stall, tmc_ack;
	wire	[31:0]	tmc_data;
	ziptimer timer_c(i_clk, cpu_reset, !cmd_halt,
		sys_cyc, (sys_stb)&&(sel_timer)&&(sys_addr[1:0]==2'b10),
			sys_we, sys_data,
		tmc_stall, tmc_ack, tmc_data, tmc_int);

	//
	// JIFFIES
	//
	wire		jif_stall, jif_ack;
	wire	[31:0]	jif_data;
	zipjiffies jiffies(i_clk, cpu_reset, !cmd_halt,
			sys_cyc, (sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b11), sys_we,
				sys_data,
			jif_stall, jif_ack, jif_data, jif_int);

	//
	// The programmable interrupt controller peripheral
	//
	wire		pic_interrupt, pic_stall, pic_ack;

	generate if (EXTERNAL_INTERRUPTS < 9)
	begin : MAIN_PIC
		icontrol #(6+EXTERNAL_INTERRUPTS)	pic(i_clk, cpu_reset,
				sys_cyc, (sys_cyc)&&(sys_stb)&&(sel_pic),sys_we,
				sys_data, 4'hf, pic_stall, pic_ack, pic_data,
				main_int_vector[(6+EXTERNAL_INTERRUPTS-1):0], pic_interrupt);
	end else begin : MAIN_PIC
		icontrol #(15)	pic(i_clk, cpu_reset,
				sys_cyc, (sys_cyc)&&(sys_stb)&&(sel_pic),sys_we,
				sys_data, 4'hf, pic_stall, pic_ack, pic_data,
				main_int_vector[14:0], pic_interrupt);
	end endgenerate

	//
	// The CPU itself
	//
	wire		cpu_gbl_stb, cpu_lcl_cyc, cpu_lcl_stb,
			cpu_we, cpu_dbg_we;
	wire	[31:0]	cpu_data, cpu_idata;
	wire	[3:0]	cpu_sel, mmu_sel;
	wire		cpu_stall, cpu_ack, cpu_err;
	wire	[31:0]	cpu_dbg_data;
	assign cpu_dbg_we = ((dbg_cyc)&&(dbg_stb)&&(!cmd_addr[5])
					&&(dbg_we)&&(dbg_addr));
	zipcpu	#(	.RESET_ADDRESS(RESET_ADDRESS),
			.ADDRESS_WIDTH(VIRTUAL_ADDRESS_WIDTH),
			.LGICACHE(LGICACHE),
			.OPT_LGDCACHE(LGDCACHE),
			.IMPLEMENT_MPY(IMPLEMENT_MPY),
			.IMPLEMENT_DIVIDE(IMPLEMENT_DIVIDE),
			.IMPLEMENT_FPU(IMPLEMENT_FPU),
			.IMPLEMENT_LOCK(IMPLEMENT_LOCK),
			.WITH_LOCAL_BUS(1'b1)
		)
		thecpu(i_clk, cpu_reset, pic_interrupt,
			cpu_halt, cmd_clear_pf_cache, cmd_addr[4:0], cpu_dbg_we,
				dbg_idata, cpu_dbg_stall, cpu_dbg_data,
				cpu_dbg_cc, cpu_break,
			cpu_gbl_cyc, cpu_gbl_stb,
				cpu_lcl_cyc, cpu_lcl_stb,
				cpu_we, cpu_addr, cpu_data, cpu_sel,
				// Return values from the Wishbone bus
				cpu_stall, cpu_ack, cpu_idata, cpu_err,
			cpu_op_stall, cpu_pf_stall, cpu_i_count
`ifdef	DEBUG_SCOPE
			, o_cpu_debug
`endif
			);

	wire	ext_stall, ext_ack;
	wire	mmu_cyc, mmu_stb, mmu_we, mmu_stall, mmu_ack, mmu_err;
	wire	mmus_stall, mmus_ack;
	wire [PAW-1:0]	mmu_addr;
	wire [31:0]	mmu_data, mmu_idata, mmus_data;

	// Specific responses from the MMU
	wire		cpu_miss;

	// The mmu_cpu_ lines are the return bus lines from the MMU.  They
	// are separate from the cpu_'s lines simply because either the sys_
	// (local) bus or the mmu_cpu_ (global) bus might return a response to
	// the CPU, and the responses haven't been merged back together again
	// yet.
	wire		mmu_cpu_stall, mmu_cpu_ack;
	wire	[31:0]	mmu_cpu_idata;

	// The wires associated with cache snooping
	wire		pf_return_stb, pf_return_we, pf_return_cachable;
	wire	[19:0]	pf_return_v, pf_return_p;

`ifdef	OPT_MMU
	// Ok ... here's the MMU
	zipmmu	#(	.LGTBL(LGTLBSZ),
			.ADDRESS_WIDTH(PHYSICAL_ADDRESS_WIDTH)
			)
		themmu(i_clk, cpu_reset,
			// Slave interface
			(sys_stb)&&(sel_mmus),
				sys_we, sys_addr[7:0], sys_data,
				mmus_stall, mmus_ack, mmus_data,
			// CPU global bus master lines
			cpu_gbl_cyc, cpu_gbl_stb, cpu_we, cpu_addr,
				cpu_data, cpu_sel,
			// MMU bus master outgoing lines
			mmu_cyc, mmu_stb, mmu_we, mmu_addr, mmu_data, mmu_sel,
				// .... and the return from the slave(s)
				mmu_stall, mmu_ack, mmu_err, mmu_idata,
			// CPU gobal bus master return lines
				mmu_cpu_stall, mmu_cpu_ack, cpu_err, cpu_miss, mmu_cpu_idata,
				pf_return_stb, pf_return_we, pf_return_p, pf_return_v,
					pf_return_cachable);

`else
	assign	mmu_cyc   = cpu_gbl_cyc;
	assign	mmu_stb   = cpu_gbl_stb;
	assign	mmu_we    = cpu_we;
	assign	mmu_addr  = cpu_addr;
	assign	mmu_data  = cpu_data;
	assign	mmu_sel   = cpu_sel;
	assign	cpu_miss  = 1'b0;
	assign	cpu_err   = (mmu_err)&&(cpu_gbl_cyc);
	assign	mmu_cpu_idata = mmu_idata;
	assign	mmu_cpu_stall = mmu_stall;
	assign	mmu_cpu_ack   = mmu_ack;
	reg	r_mmus_ack;
	initial	r_mmus_ack = 1'b0;
	always @(posedge i_clk)
		r_mmus_ack <= (sys_stb)&&(sys_addr[7]);
	assign	mmus_ack   = r_mmus_ack;
	assign	mmus_stall = 1'b0;
	assign	mmus_data  = 32'h0;

	assign	pf_return_stb = 0;
	assign	pf_return_v   = 0;
	assign	pf_return_p   = 0;
	assign	pf_return_we  = 0;
	assign	pf_return_cachable = 0;
`endif
	// Responses from the MMU still need to be merged/muxed back together
	// with the responses from the local bus
	assign	cpu_ack   = ((cpu_lcl_cyc)&&(sys_ack))
				||((cpu_gbl_cyc)&&(mmu_cpu_ack));
	assign	cpu_stall = ((cpu_lcl_cyc)&&(sys_stall))
				||((cpu_gbl_cyc)&&(mmu_cpu_stall));
	assign	cpu_idata     = (cpu_gbl_cyc)?mmu_cpu_idata : sys_idata;

	// The following lines (will be/) are used to allow the prefetch to
	// snoop on any external interaction.  Until this capability is
	// integrated into the CPU, they are unused.  Here we tell Verilator
	// not to be surprised that these lines are unused:

	// verilator lint_off UNUSED
	wire	[(3+1+20+20-1):0]	mmu_unused;
	assign	mmu_unused = { pf_return_stb, pf_return_we,
				pf_return_p, pf_return_v, pf_return_cachable,
				cpu_miss };
	// verilator lint_on UNUSED

	// Now, arbitrate the bus ... first for the local peripherals
	// For the debugger to have access to the local system bus, the
	// following must be true:
	//	(dbg_cyc)	The debugger must request the bus
	//	(!cpu_lcl_cyc)	The CPU cannot be using it (CPU gets priority)
	//	(dbg_addr)	The debugger must be requesting its data
	//				register, not just the control register
	// and one of two other things.  Either
	//	((cpu_halt)&&(!cpu_dbg_stall))	the CPU is completely halted,
	// or
	//	(!cmd_addr[5])		we are trying to read a CPU register
	//			while in motion.  Let the user beware that,
	//			by not waiting for the CPU to fully halt,
	//			his results may not be what he expects.
	//
	wire	sys_dbg_cyc = ((dbg_cyc)&&(!cpu_lcl_cyc)&&(dbg_addr))
				&&(cmd_addr[5]);
	assign	sys_cyc = (cpu_lcl_cyc)||(sys_dbg_cyc);
	assign	sys_stb = (cpu_lcl_cyc)
				? (cpu_lcl_stb)
				: ((dbg_stb)&&(dbg_addr)&&(cmd_addr[5]));

	assign	sys_we  = (cpu_lcl_cyc) ? cpu_we : dbg_we;
	assign	sys_addr= (cpu_lcl_cyc) ? cpu_addr[7:0] : { 3'h0, cmd_addr[4:0]};
	assign	sys_data= (cpu_lcl_cyc) ? cpu_data : dbg_idata;

	// Return debug response values
	// A return from one of three busses:
	//	CMD	giving command instructions to the CPU (step, halt, etc)
	//	CPU-DBG-DATA	internal register responses from within the CPU
	//	sys	Responses from the front-side bus here in the ZipSystem
	assign	dbg_odata = (!dbg_addr) ? cmd_data
				:((!cmd_addr[5])?cpu_dbg_data : sys_idata);
	initial dbg_ack = 1'b0;
	always @(posedge i_clk)
		dbg_ack <= (dbg_stb)&&(!dbg_stall);
	assign	dbg_stall=(dbg_cyc)&&(
		((!sys_dbg_cyc)&&(cpu_dbg_stall))
			||(sys_stall)
		)&&(dbg_addr);

	// Now for the external wishbone bus
	//	Need to arbitrate between the flash cache and the CPU
	// The way this works, though, the CPU will stall once the flash
	// cache gets access to the bus--the CPU will be stuck until the
	// flash cache is finished with the bus.
	wire		ext_cyc, ext_stb, ext_we, ext_err;
	wire	[(PAW-1):0]	ext_addr;
	wire	[31:0]		ext_odata;
	wire	[3:0]		ext_sel;
	wbpriarbiter #(32,PAW) dmacvcpu(i_clk,
			mmu_cyc, mmu_stb, mmu_we, mmu_addr, mmu_data, mmu_sel,
				mmu_stall, mmu_ack, mmu_err,
			dc_cyc, dc_stb, dc_we, dc_addr, dc_data, 4'hf,
					dc_stall, dc_ack, dc_err,
			ext_cyc, ext_stb, ext_we, ext_addr, ext_odata, ext_sel,
				ext_stall, ext_ack, ext_err);
	assign	mmu_idata = ext_idata;
/*
	assign	ext_cyc  = mmu_cyc;
	assign	ext_stb  = mmu_stb;
	assign	ext_we   = mmu_we;
	assign	ext_odata= mmu_data;
	assign	ext_addr = mmu_addr;
	assign	ext_sel  = mmu_sel;
	assign	mmu_ack  = ext_ack;
	assign	mmu_stall= ext_stall;
	assign	mmu_err  = ext_err;
*/

`ifdef	DELAY_EXT_BUS
	busdelay #(.AW(PAW),.DW(32),.DELAY_STALL(0)) extbus(i_clk, i_reset,
			ext_cyc, ext_stb, ext_we, ext_addr, ext_odata, ext_sel,
				ext_stall, ext_ack, ext_idata, ext_err,
			o_wb_cyc, o_wb_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_stall, i_wb_ack, i_wb_data, (i_wb_err)||(wdbus_int));
`else
	assign	o_wb_cyc  = ext_cyc;
	assign	o_wb_stb  = ext_stb;
	assign	o_wb_we   = ext_we;
	assign	o_wb_addr = ext_addr;
	assign	o_wb_data = ext_odata;
	assign	o_wb_sel  = ext_sel;
	assign	ext_stall = i_wb_stall;
	assign	ext_ack   = i_wb_ack;
	assign	ext_idata = i_wb_data;
	assign	ext_err   = (i_wb_err)||(wdbus_int);
`endif

	reg	[31:0]	tmr_data;
	always @(*)
	begin
		case(sys_addr[1:0])
		2'b00: tmr_data = tma_data;
		2'b01: tmr_data = tmb_data;
		2'b10: tmr_data = tmc_data;
		2'b11: tmr_data = jif_data;
		endcase

		// tmr_ack == sys_stb && sel_timer
	end

	reg	[2:0]	w_ack_idx, ack_idx;
	always @(*)
	begin
		w_ack_idx = 0;
		if (sel_mmus)         w_ack_idx = w_ack_idx | 3'h0;
		if (sel_watchdog)     w_ack_idx = w_ack_idx | 3'h1;
		if (sel_bus_watchdog) w_ack_idx = w_ack_idx | 3'h2;
		if (sel_apic)         w_ack_idx = w_ack_idx | 3'h3;
		if (sel_timer)        w_ack_idx = w_ack_idx | 3'h4;
		if (sel_counter)      w_ack_idx = w_ack_idx | 3'h5;
		if (sel_dmac)         w_ack_idx = w_ack_idx | 3'h6;
		if (sel_pic)          w_ack_idx = w_ack_idx | 3'h7;
	end

	always @(posedge i_clk)
	if (sys_stb)
		ack_idx <= w_ack_idx;

	reg	last_sys_stb;
	initial	last_sys_stb = 0;
	always @(posedge i_clk)
	if (i_reset)
		last_sys_stb <= 0;
	else
		last_sys_stb <= sys_stb;

	always @(posedge i_clk)
	begin
		case(ack_idx)
		3'h0: { sys_ack, sys_idata } <= { mmus_ack, mmus_data };
		3'h1: { sys_ack, sys_idata } <= { last_sys_stb,  wdt_data  };
		3'h2: { sys_ack, sys_idata } <= { last_sys_stb,  wdbus_data };
		3'h3: { sys_ack, sys_idata } <= { last_sys_stb,  ctri_data };// A-PIC
		3'h4: { sys_ack, sys_idata } <= { last_sys_stb,  tmr_data };
		3'h5: { sys_ack, sys_idata } <= { last_sys_stb,  actr_data };//countr
		3'h6: { sys_ack, sys_idata } <= { dmac_ack, dmac_data };
		3'h7: { sys_ack, sys_idata } <= { last_sys_stb,  pic_data };
		endcase

		if (i_reset || !sys_cyc)
			sys_ack <= 1'b0;
	end

	assign	sys_stall = 1'b0;
	assign	o_ext_int = (cmd_halt) && (!cpu_stall);

	// Make verilator happy
	// verilator lint_off UNUSED
	wire		unused;
	assign unused = &{ 1'b0, pic_ack, pic_stall,
		tma_ack, tma_stall, tmb_ack, tmb_stall, tmc_ack, tmc_stall,
		jif_ack, jif_stall, no_dbg_err, dbg_sel,
		sel_mmus, ctri_ack, ctri_stall, mmus_stall, dmac_stall,
		wdt_ack, wdt_stall, actr_ack, actr_stall,
		wdbus_ack, i_dbg_sel,
		moc_ack, mtc_ack, mic_ack, mpc_ack,
		uoc_ack, utc_ack, uic_ack, upc_ack,
		moc_stall, mtc_stall, mic_stall, mpc_stall,
		uoc_stall, utc_stall, uic_stall, upc_stall };
`ifndef	INCLUDE_ACCOUNTING_COUNTERS
	wire	[11:0]	unused_ctrs;
	assign	unused_ctrs = {
		moc_int, mpc_int, mic_int, mtc_int,
		uoc_int, upc_int, uic_int, utc_int,
		cpu_gie, cpu_op_stall, cpu_pf_stall, cpu_i_count };
`endif
`ifndef	INCLUDE_DMA_CONTROLLER
	wire	[34:0]	unused_dmac;
	assign	unused_dmac = { dc_err, dc_ack, dc_stall, dmac_int_vec };
`endif
	// verilator lint_on UNUSED
endmodule
