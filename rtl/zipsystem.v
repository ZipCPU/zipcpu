////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/zipsystem.v
// {{{
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
// }}}
// Copyright (C) 2015-2026, Gisselquist Technology, LLC
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
//
// Debug address space:
// {{{
//	 0-15	0x0?	Supervisors registers
//	16-31	0x1?	User registers
//	32-63	0x2?	CPU command register (singular, one register only)
//	64	0x40	Interrupt controller
//	65	0x41	Watchdog
//	66	0x42	Bus watchdog
//	67	0x43	CTRINT
//	68	0x44	Timer A
//	69	0x45	Timer B
//	70	0x46	Timer C
//	71	0x47	Jiffies
//	72	0x48	Master task counter
//	73	0x49	Master task counter
//	74	0x4a	Master task counter
//	75	0x4b	Master instruction counter
//	76	0x4c	User task counter
//	77	0x4d	User task counter
//	78	0x4e	User task counter
//	79	0x4f	User instruction counter
//	80	0x50	DMAC	Control/Status register
//	81	0x51	DMAC	Length
//	82	0x52	DMAC	Read (source) address
//	83	0x53	DMAC	Write (destination) address
//
/////// /////// /////// ///////
//
//	(MMU ... is not available via debug bus)
// }}}
module	zipsystem #(
		// {{{
		parameter	RESET_ADDRESS=32'h1000_0000,
				ADDRESS_WIDTH=32,
		parameter	BUS_WIDTH=32,	// Bus data width
		localparam	DBG_WIDTH=32,
		// CPU options
		// {{{
		parameter [0:0]	OPT_PIPELINED=1,
		parameter [0:0]	OPT_EARLY_BRANCHING=OPT_PIPELINED,
		parameter [0:0]	OPT_WRAP=1,
		// OPT_LGICACHE
		// {{{
		parameter	OPT_LGICACHE=10,
		// }}}
		// OPT_LGDCACHE
		// {{{
		// Set to zero for no data cache
		parameter	OPT_LGDCACHE=10,
		// }}}
		parameter [0:0]	START_HALTED=1,
		parameter [0:0]	OPT_DISTRIBUTED_REGS=1,
		parameter	EXTERNAL_INTERRUPTS=1,
		// OPT_MPY
		// {{{
		parameter	OPT_MPY = 3,
		// }}}
		// OPT_DIV
		// {{{
		parameter [0:0]	OPT_DIV=1,
		// }}}
		// OPT_SHIFTS
		// {{{
		parameter [0:0]	OPT_SHIFTS = 1,
		// }}}
		// OPT_FPU
		// {{{
		parameter [0:0]	OPT_FPU = 0,
		// }}}
		parameter [0:0]	OPT_CIS=1,
		parameter [0:0]	OPT_LOCK=1,
		parameter [0:0]	OPT_USERMODE=1,
		parameter [0:0]	OPT_DBGPORT=START_HALTED,
		parameter [0:0]	OPT_TRACE_PORT=1,
		parameter [0:0]	OPT_PROFILER=0,
`ifndef	FORMAL
		parameter [0:0]	OPT_LOWPOWER=0,
`endif
		// }}}
		// Local bus options
		// {{{
		// OPT_DMA
		// {{{
		parameter [0:0]	OPT_DMA=1,
		parameter	DMA_LGMEM = 10,
		// }}}
		// OPT_ACCOUNTING
		// {{{
		parameter [0:0]	OPT_ACCOUNTING = 1'b1,
		// }}}
		// Bus delay options
		// {{{
		// While I hate adding delays to any bus access, this next
		// delay is required to make timing close in my Basys-3 design.
		parameter [0:0]		DELAY_DBG_BUS = 1'b1,
		//
		parameter [0:0]		DELAY_EXT_BUS = 1'b0,
		// }}}
`ifdef	VERILATOR
		parameter [0:0]	OPT_SIM=1'b1,
		parameter [0:0]	OPT_CLKGATE = OPT_LOWPOWER,
`else
		parameter [0:0]	OPT_SIM=1'b0,
		parameter [0:0]	OPT_CLKGATE = 1'b0,
`endif
		// }}}
		parameter	RESET_DURATION = 0,
		// Short-cut names
		// {{{
		localparam	// Derived parameters
				// PHYSICAL_ADDRESS_WIDTH=ADDRESS_WIDTH,
				PAW=ADDRESS_WIDTH-$clog2(BUS_WIDTH/8)
		// }}}
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Wishbone master interface from the CPU
		// {{{
		output	wire			o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire [PAW-1:0]		o_wb_addr,
		output	wire [BUS_WIDTH-1:0]	o_wb_data,
		output	wire [BUS_WIDTH/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall, i_wb_ack,
		input	wire [BUS_WIDTH-1:0]	i_wb_data,
		input	wire			i_wb_err,
		// }}}
		// Incoming interrupts
		input	wire	[(EXTERNAL_INTERRUPTS-1):0]	i_ext_int,
		// Our one outgoing interrupt
		output	wire			o_ext_int,
		// Wishbone slave interface for debugging purposes
		// {{{
		input	wire			i_dbg_cyc, i_dbg_stb, i_dbg_we,
		input	wire	[6:0]		i_dbg_addr,
		input	wire [DBG_WIDTH-1:0]	i_dbg_data,
		input	wire [DBG_WIDTH/8-1:0]	i_dbg_sel,
		output	wire			o_dbg_stall,
		output	wire			o_dbg_ack,
		output	wire [DBG_WIDTH-1:0]	o_dbg_data,
		// }}}
		output	wire	[31:0]		o_cpu_debug,
		//
`ifdef	VBENCH_TB
		// {{{
		// output	wire			cpu_halt,
		//				cmd_reset,
		//				cmd_step,
		output	wire			early_branch,
		output	wire	[31:0]		early_branch_pc,
		output	wire	[6:0]		dcdA, dcdB,
		output	wire			new_pc,
		output	wire	[31:0]		cpu_ipc, cpu_upc, pf_pc,
		output	wire			pf_cyc, pf_stb, pf_we,
		output	wire	[31:0]		pf_addr,
		output	wire			pf_ack,
		output	wire			pf_valid, pf_illegal,
		// pf_vmask, pf_r_v, pf_tagsrc, pf_tagipc, pf_tagvallst,
		// output	wire	[31:0]		pf_lastpc,
		output	wire	[31:0]		pf_instruction,
		output	wire	[31:0]		pf_instruction_pc,
		//
		output	wire			dcd_ce, dcd_stalled, dcd_gie,
						dcd_valid, dcd_illegal,
						dcd_phase, dcd_break, dcd_pipe,
		output	wire	[3:0]		dcd_opn,
		output	wire			dcd_rA, dcd_rB, dcd_wR, dcd_wF,
		output	wire	[4:0]		dcdR,
		output	wire			dcdRpc, dcdRcc,
		output	wire	[31:0]		dcd_pc,
		output	wire			dcd_M,
		//
		output	wire			op_ce, op_illegal, op_valid,
						op_valid_mem, op_valid_alu,
						op_stall, op_wR, op_wF,
						op_phase, op_gie,
		output	wire	[4:0]		op_R, op_Aid, op_Bid,
		output	wire	[31:0]		op_Av, op_Bv, op_pc,
		output	wire			master_stall,
		//
		output	wire			alu_ce, adf_ce_unconditional,
						alu_valid, alu_wR, alu_wF,
						alu_pc_valid, alu_illegal,
						alu_gie,
						set_cond, alu_phase,
		output	wire	[3:0]		alu_flags,
		output	wire	[31:0]		alu_pc,
		//
		output	wire			mem_valid, mem_pc_valid, mem_ce,
						mem_busy, mem_rdbusy,
		output	wire	[4:0]		mem_wreg,
		//
		output	wire			div_valid, div_ce, div_busy,
		//
		output	wire	[4:0]		wr_reg_id,
		output	wire			wr_reg_ce, wr_flags_ce,
		output	wire	[31:0]		wr_gpreg_vl, wr_spreg_vl,
		output	wire	[15:0]		w_iflags, w_uflags,
		//
		output	wire			cpu_sim,
						r_sleep, master_ce, op_break,
						r_gie,
		output	wire	[22:0]		cpu_sim_immv,
		output	wire	[7:0]		op_F,
		//
		output	wire			dbg_cyc, dbg_stb, dbg_we,
		output	wire	[6:0]		dbg_addr,
		output	reg			dbg_ack,
		output	wire [DBG_WIDTH-1:0]	dbg_idata,
		output	wire			sys_cyc, sys_stb, sys_we,
		output	wire	[7:0]		sys_addr,
		output	wire	[DBG_WIDTH-1:0]	sys_data,
		//
		output	wire [BUS_WIDTH-1:0]	cpu_idata,
		output	wire			cpu_stall,
		output	wire			cpu_interrupt,
		//
		// ZipSystem peripherals
		output	wire	[31:0]		watchbus, watchdog, pic_data,
						wdbus_data,
		output	wire	[15:0]		int_state, alt_int_state,
		output	wire	[31:0]		timer_a,
						timer_b, timer_c, jiffies,
						utc_data, uoc_data, uic_data,
						upc_data, mtc_data, moc_data,
						mpc_data, mic_data,
		output	wire			wb_cyc_gbl, wb_cyc_lcl,
						wb_stb_gbl, wb_stb_lcl,
						mem_stb_gbl, mem_stb_lcl,
						mem_we, mem_ack, mem_stall,
		output	wire	[31:0]		mem_data, mem_addr, mem_result,
		output	wire			op_pipe,
						// op_A_alu, op_B_alu,
						// op_A_mem, op_B_mem,
		output	wire	[3:0]		op_opn,
		output	wire	[31:0]		alu_result,
		output	wire			alu_busy,
		output	wire	[4:0]		alu_reg,
		output	wire			switch_to_interrupt,
						release_from_interrupt,
						break_en,
		output	wire			pformem_owner,
		// }}}
`endif
		output	wire			o_prof_stb,
		output wire [ADDRESS_WIDTH-1:0]	o_prof_addr,
		output	wire	[31:0]		o_prof_ticks
		// }}}
	);

	// Local declarations
	// {{{
`ifdef	FORMAL
	wire	[0:0]	OPT_LOWPOWER;
`endif
	// Local parameter declarations
	// {{{
	localparam	DW=BUS_WIDTH;
	// Peripheral addresses
	// {{{
	// Verilator lint_off UNUSED
	// These values may (or may not) be used, depending on whether or not
	// the respective peripheral is included in the CPU.
	localparam [31:0] PERIPHBASE = 32'hc0000000;
	localparam [7:0] INTCTRL     = 8'h0,
			WATCHDOG    = 8'h1, // Interrupt generates reset signal
			BUSWATCHDOG = 8'h2,	// Sets IVEC[0]
			CTRINT      = 8'h3,	// Sets IVEC[5]
			TIMER_A     = 8'h4,	// Sets IVEC[4]
			TIMER_B     = 8'h5,	// Sets IVEC[3]
			TIMER_C     = 8'h6,	// Sets IVEC[2]
			JIFFIES     = 8'h7,	// Sets IVEC[1]
			// Accounting counter addresses
			MSTR_TASK_CTR = 8'h08,
			MSTR_MSTL_CTR = 8'h09,
			MSTR_PSTL_CTR = 8'h0a,
			MSTR_INST_CTR = 8'h0b,
			USER_TASK_CTR = 8'h0c,
			USER_MSTL_CTR = 8'h0d,
			USER_PSTL_CTR = 8'h0e,
			USER_INST_CTR = 8'h0f,
			// The MMU
			MMU_ADDR = 8'h80,
			// DMA controller (DMAC)
			// Although I have a hole at 5'h2, the DMA controller
			// requires four wishbone addresses, therefore we place
			// it by itself and expand our address bus width here
			// by another bit.
			DMAC_ADDR = 8'h10;
	// Verilator lint_on  UNUSED
	// }}}

	// Debug bit allocations
	// {{{
	//	DBGCTRL
	//		 5 DBG Catch -- Catch exceptions/fautls w/ debugger
	//		 4 Clear cache
	//		 3 RESET_FLAG
	//		 2 STEP	(W=1 steps, and returns to halted)
	//		 1 HALT(ED)
	//		 0 HALT
	//	DBGDATA
	//		read/writes internal registers
	//
	localparam	HALT_BIT = 0,
			STEP_BIT = 2,
			RESET_BIT = 3,
			CLEAR_CACHE_BIT = 4,
			CATCH_BIT = 5;
	// }}}

	// Virtual address width (unused)
	// {{{
	localparam
`ifdef	OPT_MMU
				VIRTUAL_ADDRESS_WIDTH=30;
`else
				VIRTUAL_ADDRESS_WIDTH=PAW;
`endif
				// LGTLBSZ = 6,	// Log TLB size
				// VAW=VIRTUAL_ADDRESS_WIDTH,
	// }}}

	localparam	[1:0]	DBG_ADDR_CTRL= 2'b00,
				DBG_ADDR_CPU = 2'b01,
				DBG_ADDR_SYS = 2'b10;
	// }}}

	wire	[14:0]	main_int_vector, alt_int_vector;
	wire		ctri_int, tma_int, tmb_int, tmc_int, jif_int, dmac_int;
	wire		mtc_int, moc_int, mpc_int, mic_int,
			utc_int, uoc_int, upc_int, uic_int;
	wire	[DBG_WIDTH-1:0]	actr_data;
	wire		actr_ack, actr_stall;

	wire			cpu_clken;
	//
	//
`ifndef	VBENCH_TB
	wire			sys_cyc, sys_stb, sys_we;
	wire	[7:0]		sys_addr;
	wire	[DBG_WIDTH-1:0]	sys_data;
`endif
	wire	[PAW-1:0]	cpu_addr;
	reg	[DBG_WIDTH-1:0]	sys_idata;
	reg			sys_ack;
	wire			sys_stall;

	wire	sel_counter, sel_timer, sel_pic, sel_apic,
		sel_watchdog, sel_bus_watchdog, sel_dmac;

`ifndef	VBENCH_TB
	wire				dbg_cyc, dbg_stb, dbg_we;
	wire	[6:0]			dbg_addr;
	wire	[DBG_WIDTH-1:0]		dbg_idata;
	reg				dbg_ack;
`endif
	wire				dbg_stall;
	reg	[DBG_WIDTH-1:0]		dbg_odata;
	wire	[DBG_WIDTH/8-1:0]	dbg_sel;
	wire				no_dbg_err;

	wire			cpu_break, dbg_cmd_write,
				dbg_cpu_write, dbg_cpu_read, dbg_cpu_read_req;
	wire	[DBG_WIDTH-1:0]	dbg_cmd_data;
	wire [DBG_WIDTH/8-1:0]	dbg_cmd_strb;
	wire			reset_hold, halt_on_fault, dbg_catch;
	wire			reset_request, release_request, halt_request,
				step_request, clear_cache_request;
	reg			cmd_reset, cmd_halt, cmd_step, cmd_clear_cache,
				cmd_write, cpu_read_ack;
	reg	[4:0]		cmd_waddr;
	reg	[DBG_WIDTH-1:0]	cmd_wdata;
	wire	[2:0]		cpu_dbg_cc;

	wire			cpu_reset, cpu_halt,
				cpu_has_halted;
	wire			cpu_dbg_stall;
	wire	[DBG_WIDTH-1:0]	cpu_status;
	wire			cpu_gie;

	wire			wdt_stall, wdt_ack, wdt_reset;
	wire	[DBG_WIDTH-1:0]	wdt_data;
	reg			wdbus_ack;
	reg	[PAW-1:0] 	r_wdbus_data;
`ifndef	VBENCH_TB
	wire	[DBG_WIDTH-1:0]	pic_data;
	wire	[DBG_WIDTH-1:0]	wdbus_data;
`endif
	wire	reset_wdbus_timer, wdbus_int;

	wire			cpu_op_stall, cpu_pf_stall, cpu_i_count;

	wire			dmac_stb, dc_err;
	wire	[DBG_WIDTH-1:0]	dmac_data;
	wire			dmac_stall, dmac_ack;
	wire			dc_cyc, dc_stb, dc_we, dc_stall, dc_ack;
	wire	[PAW-1:0]	dc_addr;
	wire	[BUS_WIDTH-1:0]	dc_data;
	wire [BUS_WIDTH/8-1:0]	dc_sel;
	wire			cpu_gbl_cyc;
	wire	[31:0]		dmac_int_vec;

	wire			ctri_sel, ctri_stall, ctri_ack;
	wire	[DBG_WIDTH-1:0]	ctri_data;

	wire			tma_stall, tma_ack;
	wire			tmb_stall, tmb_ack;
	wire			tmc_stall, tmc_ack;
	wire			jif_stall, jif_ack;
	wire	[DBG_WIDTH-1:0]	tma_data;
	wire	[DBG_WIDTH-1:0]	tmb_data;
	wire	[DBG_WIDTH-1:0]	tmc_data;
	wire	[DBG_WIDTH-1:0]	jif_data;

	wire			pic_stall, pic_ack;

	wire		cpu_gbl_stb, cpu_lcl_cyc, cpu_lcl_stb,
			cpu_we;
	wire	[BUS_WIDTH-1:0]		cpu_data;
	wire	[BUS_WIDTH/8-1:0]	cpu_sel, mmu_sel;
`ifndef	VBENCH_TB
	wire	[BUS_WIDTH-1:0]		cpu_idata;
	wire				cpu_stall;
`endif
	wire				pic_interrupt;
	wire				cpu_ack, cpu_err;
	wire	[DBG_WIDTH-1:0]	cpu_dbg_data;

	wire			ext_stall, ext_ack;
	wire			mmu_cyc, mmu_stb, mmu_we, mmu_stall, mmu_ack,
				mmu_err, mmus_stall, mmus_ack;
	wire	[PAW-1:0]	mmu_addr;
	wire	[BUS_WIDTH-1:0]	mmu_data, mmu_idata;
	wire	[DBG_WIDTH-1:0]	mmus_data;
	wire			cpu_miss;

	wire			mmu_cpu_stall, mmu_cpu_ack;
	wire	[BUS_WIDTH-1:0]	mmu_cpu_idata;

	// The wires associated with cache snooping
	wire			pf_return_stb, pf_return_we, pf_return_cachable;
	wire	[19:0]		pf_return_v, pf_return_p;

	wire				ext_cyc, ext_stb, ext_we, ext_err;
	wire	[PAW-1:0]		ext_addr;
	wire	[BUS_WIDTH-1:0]		ext_odata;
	wire	[BUS_WIDTH/8-1:0]	ext_sel;
	wire	[BUS_WIDTH-1:0]		ext_idata;

	reg	[DBG_WIDTH-1:0]		tmr_data;
	reg	[2:0]			w_ack_idx, ack_idx;
	reg	[2:0]			ack_subaddr;
	reg				pre_cpu_ack, sys_ack_cpu;

	reg			pre_dbg_ack;
	reg	[1:0]		pre_dbg_addr, dbg_ack_addr;
	reg	[DBG_WIDTH-1:0]	dbg_cpu_status;
	reg	[DBG_WIDTH-1:0]	dbg_r_odata;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Handle our interrupt vector generation/coordination
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Main interrupt vector
	// {{{
	assign	main_int_vector[5:0] = { ctri_int, tma_int, tmb_int, tmc_int,
					jif_int, dmac_int };
	generate if (EXTERNAL_INTERRUPTS < 9)
	begin : TRIM_MAIN_INTS
		assign	main_int_vector[14:6] = { {(9-EXTERNAL_INTERRUPTS){1'b0}},
					i_ext_int };
	end else begin : NO_TRIM_MAIN_INTS
		assign	main_int_vector[14:6] = i_ext_int[8:0];
	end endgenerate
	// }}}

	// The alternate interrupt vector
	// {{{
	generate if (EXTERNAL_INTERRUPTS <= 9 && OPT_ACCOUNTING)
	begin : ALT_ACCOUNTING_INTS
		assign	alt_int_vector = { 7'h00,
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
	end else if (EXTERNAL_INTERRUPTS <= 9) // && !OPT_ACCOUNTING
	begin : ALT_NO_INTS
		assign	alt_int_vector = { 15'h00 };
	end else if (OPT_ACCOUNTING && EXTERNAL_INTERRUPTS >= 15)
	begin : ALT_ACCT_PLUS_INTS
		assign	alt_int_vector = { i_ext_int[14:8],
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
	end else if (OPT_ACCOUNTING)
	begin : ALT_ACCT_SOME_INTS

		assign	alt_int_vector = { {(7-(EXTERNAL_INTERRUPTS-9)){1'b0}},
					i_ext_int[(EXTERNAL_INTERRUPTS-1):9],
					mtc_int, moc_int, mpc_int, mic_int,
					utc_int, uoc_int, upc_int, uic_int };
	end else if (!OPT_ACCOUNTING && EXTERNAL_INTERRUPTS >= 24)
	begin : ALT_NO_ACCOUNTING_INTS

		assign	alt_int_vector = { i_ext_int[(EXTERNAL_INTERRUPTS-1):9] };
	end else begin : ALT_TRIM_INTS
		assign	alt_int_vector = { {(15-(EXTERNAL_INTERRUPTS-9)){1'b0}},
					i_ext_int[(EXTERNAL_INTERRUPTS-1):9] };

	end endgenerate
	// }}}

	// Make Verilator happy
	// {{{
	generate if (!OPT_ACCOUNTING)
	begin : UNUSED_ACCOUNTING
		// Verilator lint_off UNUSED
		wire	unused_ctrs;
		assign	unused_ctrs = &{ 1'b0,
			moc_int, mpc_int, mic_int, mtc_int,
			uoc_int, upc_int, uic_int, utc_int,
			cpu_gie, cpu_op_stall, cpu_pf_stall, cpu_i_count };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Delay the debug port by one clock, to meet timing requirements
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	generate if (DELAY_DBG_BUS)
	begin : DELAY_THE_DEBUG_BUS
		// {{{
		wire		dbg_err;
		assign		dbg_err = 1'b0;

		busdelay #(
			// {{{
			.AW(7),.DW(32)
			// }}}
		) wbdelay(
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(i_dbg_cyc), .i_wb_stb(i_dbg_stb),
			.i_wb_we(i_dbg_we), .i_wb_addr(i_dbg_addr),
			.i_wb_data(i_dbg_data), .i_wb_sel(i_dbg_sel),
			.o_wb_stall(o_dbg_stall), .o_wb_ack(o_dbg_ack),
				.o_wb_data(o_dbg_data), .o_wb_err(no_dbg_err),
			//
			.o_dly_cyc(dbg_cyc), .o_dly_stb(dbg_stb),
				.o_dly_we(dbg_we),
			.o_dly_addr(dbg_addr), .o_dly_data(dbg_idata),
				.o_dly_sel(dbg_sel),
			.i_dly_stall(dbg_stall),
			.i_dly_ack(dbg_ack), .i_dly_data(dbg_odata),
			.i_dly_err(dbg_err)
			// }}}
		);
		// }}}
	end else begin : NO_DEBUG_BUS_DELAY
		// {{{
		assign	dbg_cyc     = i_dbg_cyc;
		assign	dbg_stb     = i_dbg_stb;
		assign	dbg_we      = i_dbg_we;
		assign	dbg_addr    = i_dbg_addr;
		assign	dbg_idata   = i_dbg_data;
		assign	o_dbg_ack   = dbg_ack;
		assign	o_dbg_stall = dbg_stall;
		assign	o_dbg_data  = dbg_odata;
		assign	dbg_sel     = i_dbg_sel;
		assign	no_dbg_err  = 1'b0;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus decoding, sel_*
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	sel_pic         = (sys_stb)&&(sys_addr == INTCTRL);
	assign	sel_watchdog    = (sys_stb)&&(sys_addr == WATCHDOG);
	assign	sel_bus_watchdog= (sys_stb)&&(sys_addr == BUSWATCHDOG);
	assign	sel_apic        = (sys_stb)&&(sys_addr == CTRINT);
	assign	sel_timer       = (sys_stb)&&(sys_addr[7:2]==TIMER_A[7:2]);
	assign	sel_counter     = (sys_stb)&&(sys_addr[7:3]==MSTR_TASK_CTR[7:3]);
	assign	sel_dmac        = (sys_stb)&&(sys_addr[7:4] ==DMAC_ADDR[7:4]);

`ifdef	FORMAL
	always @(*)
		assert($onehot0({ sel_pic, sel_watchdog, sel_bus_watchdog,
				sel_apic, sel_timer, sel_counter,
				sel_dmac }));
`endif

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The external debug interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	dbg_cpu_write = OPT_DBGPORT && (dbg_stb && !dbg_stall && dbg_we)
				&& (dbg_addr[6:5] == DBG_ADDR_CPU)
				&& dbg_sel == 4'hf;
	assign	dbg_cpu_read_req = (dbg_stb && !dbg_we
				&& dbg_addr[6:5] == DBG_ADDR_CPU);
	assign	dbg_cpu_read = (dbg_cpu_read_req && !dbg_stall);
	assign	dbg_cmd_write = (dbg_stb)&&(dbg_we)
					&&(dbg_addr[6:5] == DBG_ADDR_CTRL);
	assign	dbg_cmd_data = dbg_idata;
	assign	dbg_cmd_strb = dbg_sel;


	assign	reset_request = dbg_cmd_write && dbg_cmd_strb[RESET_BIT/8]
						&& dbg_cmd_data[RESET_BIT];
	assign	release_request = dbg_cmd_write && dbg_cmd_strb[HALT_BIT/8]
						&& !dbg_cmd_data[HALT_BIT];
	assign	halt_request = dbg_cmd_write && dbg_cmd_strb[HALT_BIT/8]
						&& dbg_cmd_data[HALT_BIT];
	assign	step_request = dbg_cmd_write && dbg_cmd_strb[STEP_BIT/8]
						&& dbg_cmd_data[STEP_BIT];
	assign	clear_cache_request = dbg_cmd_write
					&& dbg_cmd_strb[CLEAR_CACHE_BIT/8]
					&& dbg_cmd_data[CLEAR_CACHE_BIT];

	//
	// reset_hold: Always start us off with an initial reset
	// {{{
	generate if (RESET_DURATION > 0)
	begin : INITIAL_RESET_HOLD
		// {{{
		reg	[$clog2(RESET_DURATION)-1:0]	reset_counter;
		reg					r_reset_hold;

		initial	reset_counter = RESET_DURATION;
		always @(posedge i_clk)
		if (i_reset)
			reset_counter <= RESET_DURATION;
		else if (reset_counter > 0)
			reset_counter <= reset_counter - 1;

		initial	r_reset_hold = 1;
		always @(posedge i_clk)
		if (i_reset)
			r_reset_hold <= 1;
		else
			r_reset_hold <= (reset_counter > 1);

		assign	reset_hold = r_reset_hold;
`ifdef	FORMAL
		always @(*)
			assert(reset_hold == (reset_counter != 0));
`endif
		// }}}
	end else begin : NO_RESET_HOLD

		assign reset_hold = 0;

	end endgenerate
	// }}}

	assign	halt_on_fault = dbg_catch;

	// cmd_reset
	// {{{
	// Always start us off with an initial reset
	initial	cmd_reset = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		cmd_reset <= 1'b1;
	else if (reset_hold || wdt_reset)
		cmd_reset <= 1'b1;
	else if (cpu_break && !halt_on_fault)
		cmd_reset <= 1'b1;
	else
		cmd_reset <= reset_request;
	// }}}

	// cmd_halt
	// {{{
	initial	cmd_halt  = START_HALTED;
	always @(posedge i_clk)
	if (i_reset)
		cmd_halt <= START_HALTED;
	else if (cmd_reset && START_HALTED)
		cmd_halt <= START_HALTED;
	else begin
		// {{{
		// When shall we release from a halt?  Only if we have
		// come to a full and complete stop.  Even then, we only
		// release if we aren't being given a command to step the CPU.
		//
		if (!cmd_write && cpu_has_halted && dbg_cmd_write
				&& (release_request || step_request))
			cmd_halt <= 1'b0;

		// Reasons to halt

		// 1. Halt on any unhandled CPU exception.  The cause of the
		//	exception must be cured before we can (re)start.
		//	If the CPU is configured to start immediately on power
		//	up, we leave it to reset on any exception instead.
		if (cpu_break && halt_on_fault)
			cmd_halt <= 1'b1;

		// 2. Halt on any user request to halt.  (Only valid if the
		//	STEP bit isn't also set)
		if (dbg_cmd_write && halt_request && !step_request)
			cmd_halt <= 1'b1;

		// 3. Halt on any user request to write to a CPU register
		if (dbg_cpu_write)
			cmd_halt <= 1'b1;

		// 4. Halt following any step command
		if (cmd_step && !step_request)
			cmd_halt <= 1'b1;

		// 5. Halt following any clear cache
		if (cmd_clear_cache)
			cmd_halt <= 1'b1;

		// 6. Halt on any clear cache bit--independent of any step bit
		if (clear_cache_request)
			cmd_halt <= 1'b1;
		// }}}
	end
	// }}}

	// cmd_clear_cache
	// {{{
	initial	cmd_clear_cache = 1'b0;
	always @(posedge i_clk)
	if (i_reset || cpu_reset)
		cmd_clear_cache <= 1'b0;
	else if (dbg_cmd_write && clear_cache_request && halt_request)
		cmd_clear_cache <= 1'b1;
	else if (cmd_halt && !cpu_dbg_stall)
		cmd_clear_cache <= 1'b0;
	// }}}

	// cmd_step
	// {{{
	initial	cmd_step = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cmd_step <= 1'b0;
	else if (cmd_reset || cpu_break
			|| reset_request
			|| clear_cache_request || cmd_clear_cache
			|| halt_request || dbg_cpu_write)
		cmd_step <= 1'b0;
	else if (!cmd_write && cpu_has_halted && step_request)
		cmd_step <= 1'b1;
	else // if (cpu_dbg_stall)
		cmd_step <= 1'b0;
`ifdef	FORMAL
	// While STEP is true, we can't halt
	always @(*)
	if (!i_reset && cmd_step)
		assert(!cmd_halt);
`endif
	// }}}

	// dbg_catch
	// {{{
	generate if (!OPT_DBGPORT)
	begin : NO_DBG_CATCH
		assign	dbg_catch = START_HALTED;
	end else begin : GEN_DBG_CATCH
		reg	r_dbg_catch;

		initial	r_dbg_catch = START_HALTED;
		always @(posedge i_clk)
		if (i_reset)
			r_dbg_catch <= START_HALTED;
		else if (dbg_cmd_write && dbg_cmd_strb[CATCH_BIT/8])
			r_dbg_catch <= dbg_cmd_data[CATCH_BIT];

		assign	dbg_catch = r_dbg_catch;
	end endgenerate
	// }}}

	assign	cpu_reset = (cmd_reset);
	assign	cpu_halt = (cmd_halt);

	// cpu_status
	// {{{
	// Values:
	//	0xxxxx_0000 -> External interrupt lines
	//
	//	0xffff_f000 -> (Unused / reserved)
	//
	//	0x0000_0800 -> cpu_break
	//	0x0000_0400 -> Interrupt pending
	//	0x0000_0200 -> User mode
	//	0x0000_0100 -> Sleep (CPU is sleeping)
	//
	//	0x0000_00c0 -> (Unused/reserved)
	//	0x0000_0020 -> dbg_catch
	//	0x0000_0010 -> cmd_clear_cache
	//
	//	0x0000_0008 -> Reset
	//	0x0000_0004 -> Step (auto clearing, write only)
	//	0x0000_0002 -> Halt (status)
	//	0x0000_0001 -> Halt (request)
	generate
	if (EXTERNAL_INTERRUPTS < 20)
	begin : CPU_STATUS_NO_EXTRA_INTERRUPTS
		assign	cpu_status = { {(20-EXTERNAL_INTERRUPTS){1'b0}},
			i_ext_int,
			cpu_break, pic_interrupt, cpu_dbg_cc[1:0],
			2'h0, dbg_catch, 1'b0,
			cmd_reset, 1'b0, !cpu_dbg_stall, cmd_halt
		};
	end else begin : CPU_STATUS_MAX_INTERRUPTS
		assign	cpu_status = { i_ext_int[19:0],
			cpu_break, pic_interrupt, cpu_dbg_cc[1:0],
			2'h0, dbg_catch, 1'b0,
			cmd_reset, 1'b0, !cpu_dbg_stall, cmd_halt
		};
	end endgenerate

	// }}}

	assign	cpu_gie = cpu_dbg_cc[1];

	// cmd_write
	// {{{
	initial	cmd_write = 0;
	always @(posedge i_clk)
	if (i_reset || cpu_reset)
		cmd_write <= 1'b0;
	else if (!cmd_write || cpu_has_halted)
		cmd_write <= dbg_cpu_write;
	// }}}

	// cpu_read_ack
	// {{{
	generate if (OPT_DISTRIBUTED_REGS)
	begin : GEN_CMD_READ_ACK

		initial	cpu_read_ack = 0;
		always @(posedge i_clk)
		if (i_reset || !dbg_cyc || !OPT_DBGPORT)
			cpu_read_ack <= 0;
		else if (dbg_cpu_read)
			cpu_read_ack <= 1;
		else // if (cpu_read_ack != 0)
			cpu_read_ack <= 0;

	end else begin : GEN_FWD_CMDREAD_ACK

		always @(*)
			cpu_read_ack = dbg_cpu_read;

	end endgenerate
	// }}}

	// cmd_waddr, cmd_wdata
	// {{{
	always @(posedge i_clk)
	if ((!cmd_write || cpu_has_halted) && dbg_cpu_write)
	begin
		cmd_waddr <= dbg_addr[4:0];
		cmd_wdata <= dbg_idata;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The WATCHDOG Timer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	FORMAL
	fwb_single
`else
	ziptimer #( .BW(32),.VW(31),.RELOADABLE(0) )
`endif
	u_watchdog (
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset),
`ifndef	FORMAL
		.i_ce(!cmd_halt),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_watchdog)),
			.i_wb_we(sys_we), .i_wb_data(sys_data), .i_wb_sel(4'hf),
			.o_wb_stall(wdt_stall),
			.o_wb_ack(wdt_ack),
			.o_wb_data(wdt_data),
			.o_int(wdt_reset)
		// }}}
	);

	//
	// Position two, a second watchdog timer--this time for the wishbone
	// bus, in order to tell/find wishbone bus lockups.  In its current
	// configuration, it cannot be configured and all bus accesses must
	// take less than the number written to this register.
	//
	assign	reset_wdbus_timer = (!o_wb_cyc)||(o_wb_stb)||(i_wb_ack);

	wbwatchdog #(14)
	u_watchbus(
		// {{{
		.i_clk(i_clk),.i_reset((cpu_reset)||(reset_wdbus_timer)),
			.i_timeout(14'h2000),
		.o_int(wdbus_int)
		// }}}
	);

	initial	r_wdbus_data = 0;
	always @(posedge i_clk)
	if ((wdbus_int)||(cpu_err))
		r_wdbus_data <= o_wb_addr;

	assign	wdbus_data = { {(32-PAW){1'b0}}, r_wdbus_data };
	initial	wdbus_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !sys_cyc)
		wdbus_ack <= 1'b0;
	else
		wdbus_ack <= (sys_stb)&&(sel_bus_watchdog);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Performance counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Here's the stuff we'll be counting ....
	//
`ifndef	VBENCH_TB
	wire	[DBG_WIDTH-1:0]	mtc_data;
	wire	[DBG_WIDTH-1:0]	moc_data;
	wire	[DBG_WIDTH-1:0]	mpc_data;
	wire	[DBG_WIDTH-1:0]	mic_data;
	wire	[DBG_WIDTH-1:0]	utc_data;
	wire	[DBG_WIDTH-1:0]	uoc_data;
	wire	[DBG_WIDTH-1:0]	upc_data;
	wire	[DBG_WIDTH-1:0]	uic_data;
`endif
	generate if (OPT_ACCOUNTING)
	begin : ACCOUNTING_COUNTERS
		// {{{
		// Local definitions
		// {{{
		// Verilator lint_off UNUSED
		wire		mtc_stall, mtc_ack;
		wire		moc_stall, moc_ack;
		wire		mpc_stall, mpc_ack;
		wire		mic_stall, mic_ack;
		wire		utc_stall, utc_ack;
		wire		uoc_stall, uoc_ack;
		wire		upc_stall, upc_ack;
		wire		uic_stall, uic_ack;
		// Verilator lint_on  UNUSED
		reg	[DBG_WIDTH-1:0]	r_actr_data;
		// }}}

		// Master counters
		// {{{
		// The master counters will, in general, not be reset.  They'll
		// be used for an overall counter.
		//
		// Master task counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		mtask_ctr(
			// {{{
			.i_clk(i_clk), .i_reset(1'b0),
`ifndef	FORMAL
			.i_event(!cmd_halt),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)
					&&(sys_addr[2:0] == 3'b000)),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(mtc_stall),
			.o_wb_ack(mtc_ack), .o_wb_data(mtc_data),
			.o_int(mtc_int)
			// }}}
		);

		// Master Operand Stall counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		mmstall_ctr(
			// {{{
			.i_clk(i_clk),.i_reset(1'b0),
`ifndef	FORMAL
			.i_event(cpu_op_stall),
`endif
			.i_wb_cyc(sys_cyc), .i_wb_stb((sys_stb)&&(sel_counter)
						&&(sys_addr[2:0] == 3'b001)),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(moc_stall), .o_wb_ack(moc_ack),
				.o_wb_data(moc_data),
			.o_int(moc_int)
			// }}}
		);

		// Master PreFetch-Stall counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		mpstall_ctr(
			// {{{
			.i_clk(i_clk),.i_reset(1'b0),
`ifndef	FORMAL
			.i_event(cpu_pf_stall),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)
					&&(sys_addr[2:0] == 3'b010)),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(mpc_stall),
			.o_wb_ack(mpc_ack), .o_wb_data(mpc_data),
			.o_int(mpc_int)
			// }}}
		);

		// Master Instruction counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		mins_ctr(
			// {{{
			.i_clk(i_clk),.i_reset(1'b0),
`ifndef	FORMAL
			.i_event(cpu_i_count),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)
					&&(sys_addr[2:0] == 3'b011)),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(mic_stall),
			.o_wb_ack(mic_ack), .o_wb_data(mic_data),
			.o_int(mic_int)
			// }}}
		);
		// }}}
		// User counters
		// {{{
		// The user counters are different from those of the master.
		// They will be reset any time a task is given control of the
		// CPU.
		//
		// User task counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		utask_ctr(
			// {{{
			.i_clk(i_clk), .i_reset(1'b0),
`ifndef	FORMAL
			.i_event((!cmd_halt)&&(cpu_gie)),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)
						&&(sys_addr[2:0] == 3'b100)),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(utc_stall),
			.o_wb_ack(utc_ack), .o_wb_data(utc_data),
			.o_int(utc_int)
			// }}}
		);

		// User Op-Stall counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		umstall_ctr(
			// {{{
			.i_clk(i_clk),.i_reset(1'b0),
`ifndef	FORMAL
			.i_event((cpu_op_stall)&&(cpu_gie)),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)&&(sys_addr[2:0] == 3'b101)),
					.i_wb_we(sys_we), .i_wb_data(sys_data),
				.o_wb_stall(uoc_stall),
			.o_wb_ack(uoc_ack), .o_wb_data(uoc_data),
			.o_int(uoc_int)
			// }}}
		);

		// User PreFetch-Stall counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		upstall_ctr(
			// {{{
			.i_clk(i_clk),.i_reset(1'b0),
`ifndef	FORMAL
			.i_event((cpu_pf_stall)&&(cpu_gie)),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)
					&&(sys_addr[2:0] == 3'b110)),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(upc_stall),
			.o_wb_ack(upc_ack), .o_wb_data(upc_data),
			.o_int(upc_int)
			// }}}
		);

		// User instruction counter
`ifdef	FORMAL
		fwb_single
`else
		zipcounter
`endif
		uins_ctr(
			// {{{
			.i_clk(i_clk),.i_reset(1'b0),
`ifndef	FORMAL
			.i_event((cpu_i_count)&&(cpu_gie)),
`endif
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_stb)&&(sel_counter)
						&&(sys_addr[2:0] == 3'b111)),
					.i_wb_we(sys_we), .i_wb_data(sys_data),
			.o_wb_stall(uic_stall),
			.o_wb_ack(uic_ack), .o_wb_data(uic_data),
			.o_int(uic_int)
			// }}}
		);
		// }}}

		// A little bit of pre-cleanup (actr = accounting counters)
		assign	actr_ack = sel_counter;
		assign	actr_stall = 1'b0;

		// actr_data
		// {{{
		always @(*)
		begin
			case(ack_subaddr[2:0])
			3'h0: r_actr_data = mtc_data;
			3'h1: r_actr_data = moc_data;
			3'h2: r_actr_data = mpc_data;
			3'h3: r_actr_data = mic_data;
			3'h4: r_actr_data = utc_data;
			3'h5: r_actr_data = uoc_data;
			3'h6: r_actr_data = upc_data;
			3'h7: r_actr_data = uic_data;
			endcase
		end

		assign	actr_data = r_actr_data;
		// }}}
		// }}}
	end else begin : NO_ACCOUNTING_COUNTERS
		// {{{
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

		assign	actr_ack = sel_counter;

		assign	mtc_data = 32'h0;
		assign	moc_data = 32'h0;
		assign	mpc_data = 32'h0;
		assign	mic_data = 32'h0;
		assign	utc_data = 32'h0;
		assign	uoc_data = 32'h0;
		assign	upc_data = 32'h0;
		assign	uic_data = 32'h0;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_counter_data;
		assign	unused_counter_data = &{ 1'b0,
				mtc_data, moc_data, mpc_data, mic_data,
				utc_data, uoc_data, upc_data, uic_data };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The DMA Controller
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	dmac_int_vec = { 1'b0, alt_int_vector, 1'b0,
					main_int_vector[14:1], 1'b0 };
	assign	dmac_stb = (sys_stb)&&(sel_dmac);

	generate if (OPT_DMA)
	begin : DMA
		// {{{
`ifndef	FORMAL
		zipdma	#(
			// {{{
			.ADDRESS_WIDTH(ADDRESS_WIDTH), .LGMEMLEN(DMA_LGMEM),
			.OPT_REGISTER_RAM(!OPT_DISTRIBUTED_REGS),
			.BUS_WIDTH(DW), .OPT_LITTLE_ENDIAN(1'b0)
			// }}}
		) dma_controller(
			// {{{
			.i_clk(i_clk), .i_reset(cpu_reset),
			.i_swb_cyc(sys_cyc), .i_swb_stb(dmac_stb),
				.i_swb_we(sys_we), .i_swb_addr(sys_addr[1:0]),
				.i_swb_data(sys_data), .i_swb_sel(4'hf),
			.o_swb_stall(dmac_stall), .o_swb_ack(dmac_ack),
				.o_swb_data(dmac_data),
			// Need the outgoing DMAC wishbone bus
			.o_mwb_cyc(dc_cyc), .o_mwb_stb(dc_stb),
				.o_mwb_we(dc_we), .o_mwb_addr(dc_addr),
				.o_mwb_data(dc_data), .o_mwb_sel(dc_sel),
			.i_mwb_stall(dc_stall),
				.i_mwb_ack(dc_ack), .i_mwb_data(ext_idata),
				.i_mwb_err(dc_err),
			// External device interrupts
			.i_dev_ints(dmac_int_vec),
			// DMAC interrupt, for upon completion
			.o_interrupt(dmac_int)
			// }}}
		);
`else
		(* anyseq *) reg [31:0]	dmac_data;
		reg	f_dmac_ack;

		assign	dmac_stall = 1'b0;
		always @(posedge i_clk)
		if (cpu_reset || !sys_cyc)
			f_dmac_ack <= 1'b0;
		else
			f_dmac_ack <= (dmac_stb && !dmac_stall);
		assign	dmac_ack = f_dmac_ack;

		assign	dc_cyc = 1'b0;
		assign	dc_stb = 1'b0;

		assign	dmac_ack = f_dmac_ack;
		assign	dmac_data = 32'h000;
		assign	dmac_stall = 1'b0;
`endif
		// }}}
	end else begin : NO_DMA
		// {{{
		reg	r_dmac_ack;

		initial	r_dmac_ack = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			r_dmac_ack <= 1'b0;
		else
			r_dmac_ack <= (sys_cyc)&&(dmac_stb);
		assign	dmac_ack = r_dmac_ack;
		assign	dmac_data = 32'h000;
		assign	dmac_stall = 1'b0;

		assign	dc_cyc  = 1'b0;
		assign	dc_stb  = 1'b0;
		assign	dc_we   = 1'b0;
		assign	dc_addr = { (PAW) {1'b0} };
		assign	dc_data = 32'h00;
		assign	dc_sel  = 4'h0;

		assign	dmac_int = 1'b0;

		// Make Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_dmac;
		assign	unused_dmac = &{ 1'b0, dc_err, dc_ack,
					dc_stall, dmac_int_vec };
		// Verilator lint_on UNUSED
		// }}}
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The alternate interrupt controller
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	ctri_sel = (sys_stb)&&(sel_apic);
	generate if (OPT_ACCOUNTING)
	begin : PIC_WITH_ACCOUNTING
		//
		// Interrupt controller
		//
		if (EXTERNAL_INTERRUPTS <= 9)
		begin : ALT_PIC
`ifdef	FORMAL
			fwb_single
`else
			icontrol #(8)
`endif
			ctri(
			// {{{
			.i_clk(i_clk), .i_reset(cpu_reset),
			.i_wb_cyc(sys_cyc), .i_wb_stb(ctri_sel),
			.i_wb_we(sys_we), .i_wb_data(sys_data), .i_wb_sel(4'hf),
			.o_wb_stall(ctri_stall), .o_wb_ack(ctri_ack),
			.o_wb_data(ctri_data),
`ifndef	FORMAL
			.i_brd_ints(alt_int_vector[7:0]),
`endif
			.o_int(ctri_int)
			// }}}
			);
`ifdef	VBENCH_TB
			assign	alt_int_state = { 8'h0, ctri.r_int_state };
`endif
		end else begin : ALT_PIC
`ifdef	FORMAL
			fwb_single
`else
			icontrol #(8+(EXTERNAL_INTERRUPTS-9))
`endif
			ctri(
			// {{{
			.i_clk(i_clk), .i_reset(cpu_reset),
			.i_wb_cyc(sys_cyc), .i_wb_stb(ctri_sel),
				.i_wb_we(sys_we), .i_wb_data(sys_data),
				.i_wb_sel(4'hf),
				.o_wb_stall(ctri_stall),
				.o_wb_ack(ctri_ack),
				.o_wb_data(ctri_data),
`ifndef	FORMAL
				.i_brd_ints(alt_int_vector[(EXTERNAL_INTERRUPTS-2):0]),
`endif
				.o_int(ctri_int)
			// }}}
			);
`ifdef	VBENCH_TB
			assign	alt_int_state = {
					{(17-EXTERNAL_INTERRUPTS){1'b0}},
						ctri.r_int_state };
`endif
		end
	end else begin : PIC_WITHOUT_ACCOUNTING

		if (EXTERNAL_INTERRUPTS <= 9)
		begin : ALT_PIC
			assign	ctri_stall = 1'b0;
			assign	ctri_data  = 32'h0000;
			assign	ctri_int   = 1'b0;
`ifdef	VBENCH_TB
			assign	alt_int_state = 16'h0;
`endif
		end else begin : ALT_PIC
`ifdef	FORMAL
			fwb_single
`else
			icontrol #(EXTERNAL_INTERRUPTS-9)
`endif
			ctri(
				// {{{
				.i_clk(i_clk), .i_reset(cpu_reset),
				.i_wb_cyc(sys_cyc), .i_wb_stb(ctri_sel),
					.i_wb_we(sys_we), .i_wb_data(sys_data),
				.i_wb_sel(4'hf),
				.o_wb_stall(ctri_stall),
				.o_wb_ack(ctri_ack),
				.o_wb_data(ctri_data),
`ifndef	FORMAL
				.i_brd_ints(alt_int_vector[(EXTERNAL_INTERRUPTS-10):0]),
`endif
				.o_int(ctri_int)
				// }}}
			);
`ifdef	VBENCH_TB
			assign	alt_int_state = {
					{(25-EXTERNAL_INTERRUPTS){1'b0}},
					ctri.r_int_state };
`endif
		end

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Timers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Timer A
	//
`ifdef	FORMAL
	fwb_single
`else
	ziptimer
`endif
	u_timer_a(
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset),
`ifndef	FORMAL
		.i_ce(!cmd_halt),
`endif
		.i_wb_cyc(sys_cyc),
		.i_wb_stb((sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b00)),
		.i_wb_we(sys_we), .i_wb_data(sys_data), .i_wb_sel(4'hf),
		.o_wb_stall(tma_stall), .o_wb_ack(tma_ack),
		.o_wb_data(tma_data),
		.o_int(tma_int)
		// }}}
	);

	//
	// Timer B
	//
`ifdef	FORMAL
	fwb_single
`else
	ziptimer
`endif
	u_timer_b(
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset),
`ifndef	FORMAL
		.i_ce(!cmd_halt),
`endif
		.i_wb_cyc(sys_cyc),
		.i_wb_stb((sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b01)),
		.i_wb_we(sys_we), .i_wb_data(sys_data), .i_wb_sel(4'hf),
		.o_wb_stall(tmb_stall), .o_wb_ack(tmb_ack),
		.o_wb_data(tmb_data),
		.o_int(tmb_int)
		// }}}
	);

	//
	// Timer C
	//
`ifdef	FORMAL
	fwb_single
`else
	ziptimer
`endif
	u_timer_c(
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset),
`ifndef	FORMAL
		.i_ce(!cmd_halt),
`endif
		.i_wb_cyc(sys_cyc),
		.i_wb_stb((sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b10)),
		.i_wb_we(sys_we), .i_wb_data(sys_data), .i_wb_sel(4'hf),
		.o_wb_stall(tmc_stall), .o_wb_ack(tmc_ack),
		.o_wb_data(tmc_data),
		.o_int(tmc_int)
		// }}}
	);

	//
	// JIFFIES
	//
`ifdef	FORMAL
	fwb_single
`else
	zipjiffies
`endif
	u_jiffies(
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset),
`ifndef	FORMAL
		.i_ce(!cmd_halt),
`endif
		.i_wb_cyc(sys_cyc),
		.i_wb_stb((sys_stb)&&(sel_timer)&&(sys_addr[1:0] == 2'b11)),
		.i_wb_we(sys_we), .i_wb_data(sys_data), .i_wb_sel(4'hf),
		.o_wb_stall(jif_stall), .o_wb_ack(jif_ack),
		.o_wb_data(jif_data),
		.o_int(jif_int)
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The main (programmable) interrupt controller peripheral
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (EXTERNAL_INTERRUPTS < 9)
	begin : MAIN_PIC
`ifdef	FORMAL
		fwb_single
`else
		icontrol #(6+EXTERNAL_INTERRUPTS)
`endif
		pic(
			// {{{
			.i_clk(i_clk), .i_reset(cpu_reset),
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_cyc)&&(sys_stb)&&(sel_pic)),
			.i_wb_we(sys_we),
			.i_wb_data(sys_data),
			.i_wb_sel(4'hf), .o_wb_stall(pic_stall),
			.o_wb_ack(pic_ack), .o_wb_data(pic_data),
`ifndef	FORMAL
			.i_brd_ints(main_int_vector[(6+EXTERNAL_INTERRUPTS-1):0]),
`endif
			.o_int(pic_interrupt)
			// }}}
		);

`ifdef	VBENCH_TB
		assign	int_state = { {(10-EXTERNAL_INTERRUPTS){1'b0}},
						pic.r_int_state };
`endif
	end else begin : MAIN_PIC
`ifdef	FORMAL
		fwb_single
`else
		icontrol #(15)
`endif
		pic(
			// {{{
			.i_clk(i_clk), .i_reset(cpu_reset),
			.i_wb_cyc(sys_cyc),
			.i_wb_stb((sys_cyc)&&(sys_stb)&&(sel_pic)),
			.i_wb_we(sys_we),
			.i_wb_data(sys_data),.i_wb_sel(4'hf),
			.o_wb_stall(pic_stall), .o_wb_ack(pic_ack), .o_wb_data(pic_data),
`ifndef	FORMAL
			.i_brd_ints(main_int_vector[14:0]),
`endif
			.o_int(pic_interrupt)
			// }}}
		);

`ifdef	VBENCH_TB
		assign	int_state = { 1'b0, pic.r_int_state };
`endif
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The CPU itself
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	assign	cpu_clken = cmd_write || cpu_read_ack || (dbg_stb && dbg_addr[6] == DBG_ADDR_CPU[1]);
`ifdef	FORMAL
	// {{{
	// Anyseq model of the (separately verified) ZipCPU: only its bus-facing
	// behavior matters here, constrained by fdebug and the fwb_* below.
	(* anyseq *)	reg	f_cpu_halted, f_cpu_stall, f_cpu_break;
	(* anyseq *) reg [2:0]	f_cpu_dbg_cc;
	(* anyseq *) reg [31:0]	f_cpu_dbg_data;
	//
	(* anyseq *)	reg	f_cpu_gbl_cyc, f_cpu_gbl_stb,
				f_cpu_lcl_cyc, f_cpu_lcl_stb,
				f_cpu_we;
	(* anyseq *)	reg	[PAW-1:0]		f_cpu_addr;
	(* anyseq *)	reg	[BUS_WIDTH-1:0]		f_cpu_odata;
	(* anyseq *)	reg	[BUS_WIDTH/8-1:0]	f_cpu_sel;
	(* anyseq *)	reg	f_cpu_op_stall, f_cpu_pf_stall, f_cpu_i_count;
	wire			cpu_dbg_we;

	assign cpu_dbg_we = ((dbg_stb)&&(dbg_we)
					&&(dbg_addr[6:5] == DBG_ADDR_CPU));

	assign	cpu_dbg_stall = f_cpu_stall && !f_cpu_halted;
	assign	cpu_break     = f_cpu_break;
	assign	cpu_dbg_cc    = f_cpu_dbg_cc;
	assign	cpu_dbg_data  = f_cpu_dbg_data;
	assign	cpu_has_halted= f_cpu_halted;
	//
	// The CPU's two Wishbone master interfaces
	assign	cpu_gbl_cyc = f_cpu_gbl_cyc;
	assign	cpu_gbl_stb = f_cpu_gbl_stb;
	assign	cpu_lcl_cyc = f_cpu_lcl_cyc;
	assign	cpu_lcl_stb = f_cpu_lcl_stb;
	assign	cpu_we      = f_cpu_we;
	assign	cpu_addr    = f_cpu_addr;
	assign	cpu_data    = f_cpu_odata;
	assign	cpu_sel     = f_cpu_sel;
	//
	// Accounting/profiling/trace outputs -- irrelevant to this proof
	assign	cpu_op_stall = f_cpu_op_stall;
	assign	cpu_pf_stall = f_cpu_pf_stall;
	assign	cpu_i_count  = f_cpu_i_count;
	assign	o_cpu_debug  = 32'h0;
	assign	o_prof_stb   = 1'b0;
	assign	o_prof_addr  = {(ADDRESS_WIDTH){1'b0}};
	assign	o_prof_ticks = 32'h0;

	fdebug #(
		// {{{
		.OPT_START_HALTED(START_HALTED),
		.OPT_DISTRIBUTED_RAM(OPT_DISTRIBUTED_REGS)
		// }}}
	) fdbg (
		// {{{
		.i_clk(i_clk),
		.i_reset(i_reset),
		.i_cpu_reset(cpu_reset),
		.i_halt(cpu_halt),
		.i_halted(f_cpu_halted),
		.i_clear_cache(cmd_clear_cache),
		.i_dbg_we(cmd_write),
		.i_dbg_reg(cmd_waddr),
		.i_dbg_data(cmd_wdata),
		.i_dbg_stall(cpu_dbg_stall),
		.i_dbg_break(cpu_break),
		.i_dbg_cc(cpu_dbg_cc)
		// }}}
	);

	// A halted CPU makes no bus requests at all
	always @(*)
	if (f_cpu_halted)
		assume(!f_cpu_gbl_cyc && !f_cpu_lcl_cyc);

	// The CPU drives at most one of its busses (asserted in wbdblpriarb)
	always @(*)
		assume(!f_cpu_gbl_cyc || !f_cpu_lcl_cyc);

	// STB is never high withut an ongoing bus CYCle
	always @(*)
	if (!f_cpu_gbl_cyc)
		assume(!f_cpu_gbl_stb);
	always @(*)
	if (!f_cpu_lcl_cyc)
		assume(!f_cpu_lcl_stb);

	// Reset always clears any ongoing bus cycles
	always @(posedge i_clk)
	if (f_past_valid || $past(i_reset) || $past(cpu_reset))
	begin
		assume(!f_cpu_gbl_cyc);
		assume(!f_cpu_lcl_cyc);
	end else begin
		// The CPU will always place at least one clock between
		// local and global clock cycles
		if ($past(f_cpu_gbl_cyc))
			assume(!f_cpu_lcl_cyc);

		if ($past(f_cpu_lcl_cyc))
			assume(!f_cpu_gbl_cyc);
	end

	// }}}
`else
	zipwb	#(
		// {{{
		.RESET_ADDRESS(RESET_ADDRESS),
		.ADDRESS_WIDTH(VIRTUAL_ADDRESS_WIDTH),
		.BUS_WIDTH(BUS_WIDTH),
		.OPT_PIPELINED(OPT_PIPELINED),
		.OPT_EARLY_BRANCHING(OPT_EARLY_BRANCHING),
		.OPT_WRAP(OPT_WRAP),
		.OPT_LGICACHE(OPT_LGICACHE),
		.OPT_LGDCACHE(OPT_LGDCACHE),
		.OPT_MPY(OPT_MPY),
		.OPT_DIV(OPT_DIV),
		.OPT_SHIFTS(OPT_SHIFTS),
		.IMPLEMENT_FPU(OPT_FPU),
		.OPT_CIS(OPT_CIS),
		.OPT_LOCK(OPT_LOCK),
		.OPT_LOWPOWER(OPT_LOWPOWER),
		.OPT_START_HALTED(START_HALTED),
		.OPT_SIM(OPT_SIM),
		.OPT_DBGPORT(OPT_DBGPORT),
		.OPT_TRACE_PORT(OPT_TRACE_PORT),
		.OPT_PROFILER(OPT_PROFILER),
		.OPT_CLKGATE(OPT_CLKGATE),
		.OPT_DISTRIBUTED_REGS(OPT_DISTRIBUTED_REGS),
		.OPT_USERMODE(OPT_USERMODE),
		.WITH_LOCAL_BUS(1'b1)
		// }}}
	) thecpu(
		// {{{
		.i_clk(i_clk), .i_reset(cpu_reset),
			.i_interrupt(pic_interrupt),
			.i_cpu_clken(cpu_clken),
		// Debug interface
		// {{{
		.i_halt(cpu_halt), .i_clear_cache(cmd_clear_cache),
				.i_dbg_wreg(cmd_waddr), .i_dbg_we(cmd_write),
				.i_dbg_data(cmd_wdata),
				.i_dbg_rreg(dbg_addr[4:0]),
			.o_dbg_stall(cpu_dbg_stall),
			.o_halted(cpu_has_halted),
			.o_dbg_reg(cpu_dbg_data),
			.o_dbg_cc(cpu_dbg_cc),
			.o_break(cpu_break),
		// }}}
		// Wishbone bus interface
		// {{{
		.o_wb_gbl_cyc(cpu_gbl_cyc), .o_wb_gbl_stb(cpu_gbl_stb),
				.o_wb_lcl_cyc(cpu_lcl_cyc),
				.o_wb_lcl_stb(cpu_lcl_stb),
				.o_wb_we(cpu_we), .o_wb_addr(cpu_addr),
				.o_wb_data(cpu_data), .o_wb_sel(cpu_sel),
				// Return values from the Wishbone bus
				.i_wb_stall(cpu_stall), .i_wb_ack(cpu_ack),
				.i_wb_data(cpu_idata), .i_wb_err(cpu_err),
		// }}}
			.o_op_stall(cpu_op_stall), .o_pf_stall(cpu_pf_stall),
				.o_i_count(cpu_i_count),
		.o_debug(o_cpu_debug),
		//
		.o_prof_stb(o_prof_stb),
		.o_prof_addr(o_prof_addr),
		.o_prof_ticks(o_prof_ticks)
		// }}}
	);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The (unused) MMU
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The mmu_cpu_ lines are the return bus lines from the MMU.  They
	// are separate from the cpu_'s lines simply because either the sys_
	// (local) bus or the mmu_cpu_ (global) bus might return a response to
	// the CPU, and the responses haven't been merged back together again
	// yet.

	reg	r_mmus_ack;

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

	initial	r_mmus_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_mmus_ack <= 1'b0;
	else
		r_mmus_ack <= (sys_stb)&&(sys_addr[7]);

	assign	mmus_ack   = r_mmus_ack;
	assign	mmus_stall = 1'b0;
	assign	mmus_data  = 32'h0;

	assign	pf_return_stb = 0;
	assign	pf_return_v   = 0;
	assign	pf_return_p   = 0;
	assign	pf_return_we  = 0;
	assign	pf_return_cachable = 0;
	//
	// Responses from the MMU still need to be merged/muxed back together
	// with the responses from the local bus
	// Forward a sys ack to the CPU only if the CPU issued the
	// request; a debug ack in flight used to be delivered to the CPU too
	assign	cpu_ack   = ((cpu_lcl_cyc)&&(sys_ack_cpu))
				||((cpu_gbl_cyc)&&(mmu_cpu_ack));
	assign	cpu_stall = ((cpu_lcl_cyc)&&(sys_stall))
				||((cpu_gbl_cyc)&&(mmu_cpu_stall));
	assign	cpu_idata     = (cpu_gbl_cyc)?mmu_cpu_idata
				: { {(BUS_WIDTH-DBG_WIDTH){1'b0}}, sys_idata };

	// The following lines (will be/) are used to allow the prefetch to
	// snoop on any external interaction.  Until this capability is
	// integrated into the CPU, they are unused.  Here we tell Verilator
	// not to be surprised that these lines are unused:

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The internal sys bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

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
	//	(dbg_addr[6:5]==2'b01)	we are trying to read a CPU register
	//			while in motion.  Let the user beware that,
	//			by not waiting for the CPU to fully halt,
	//			his results may not be what he expects.
	//
	assign	sys_cyc = (cpu_lcl_cyc)||(dbg_cyc);
	assign	sys_stb = (cpu_lcl_cyc)
				? (cpu_lcl_stb)
				: ((dbg_stb)&&(dbg_addr[6:5]==DBG_ADDR_SYS));

	assign	sys_we  = (cpu_lcl_cyc) ? cpu_we : dbg_we;
	assign	sys_addr= (cpu_lcl_cyc) ? cpu_addr[7:0] : { 3'h0, dbg_addr[4:0]};
	assign	sys_data= (cpu_lcl_cyc) ? cpu_data[DBG_WIDTH-1:0] : dbg_idata;

	// tmr_data
	// {{{
	always @(*)
	begin
		case(ack_subaddr[1:0])
		2'b00: tmr_data = tma_data;
		2'b01: tmr_data = tmb_data;
		2'b10: tmr_data = tmc_data;
		2'b11: tmr_data = jif_data;
		endcase

		// tmr_ack == sys_stb && sel_timer
	end
	// }}}

	// sys_ack_cpu, pre_cpu_ack
	// {{{
	initial	{ sys_ack_cpu, pre_cpu_ack } = 2'b00;
	always @(posedge i_clk)
	if (i_reset || cpu_reset || !cpu_lcl_cyc)
		{ sys_ack_cpu, pre_cpu_ack } <= 2'b00;
	else
		{ sys_ack_cpu, pre_cpu_ack } <= { pre_cpu_ack, sys_stb };
	// }}}

	// sys_ack, sys_idata
	// {{{
	always @(posedge i_clk)
	case(ack_idx)
	3'h0: sys_idata <= mmus_data;
	3'h1: sys_idata <= wdt_data;
	3'h2: sys_idata <= wdbus_data;
	3'h3: sys_idata <= ctri_data;// A-PIC
	3'h4: sys_idata <= tmr_data;
	3'h5: sys_idata <= actr_data;//countr
	3'h6: sys_idata <= dmac_data;
	3'h7: sys_idata <= pic_data;
	endcase
	// }}}

	// w_ack_idx
	// {{{
	always @(*)
	begin
		w_ack_idx = 0;
		if (sel_watchdog)     w_ack_idx = w_ack_idx | 3'h1;
		if (sel_bus_watchdog) w_ack_idx = w_ack_idx | 3'h2;
		if (sel_apic)         w_ack_idx = w_ack_idx | 3'h3;
		if (sel_timer)        w_ack_idx = w_ack_idx | 3'h4;
		if (sel_counter)      w_ack_idx = w_ack_idx | 3'h5;
		if (sel_dmac)         w_ack_idx = w_ack_idx | 3'h6;
		if (sel_pic)          w_ack_idx = w_ack_idx | 3'h7;
	end
	// }}}

	// ack_idx
	// {{{
	always @(posedge i_clk)
	if (sys_stb)
		ack_idx <= w_ack_idx;
	// }}}

	// ack_subaddr
	// {{{
	always @(posedge i_clk)
	if (sys_stb)
		ack_subaddr <= sys_addr[2:0];
	// }}}
	assign	sys_stall = 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Return debug response values
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (dbg_stb && !dbg_stall)
		pre_dbg_addr <= dbg_addr[6:5];

	// ... then carry it one more clock, to the cycle the ack goes out
	always @(posedge i_clk)
	if (!OPT_LOWPOWER || dbg_cyc)	// Already accepted, no stalls allowed
		dbg_ack_addr <= pre_dbg_addr;

	always @(posedge i_clk)
		dbg_cpu_status <= cpu_status;

	initial	pre_dbg_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_dbg_cyc)
		pre_dbg_ack <= 1'b0;
	else
		pre_dbg_ack <= dbg_stb && !dbg_stall && !dbg_cpu_read;

	// A return from one of three busses:
	//	CMD	giving command instructions to the CPU (step, halt, etc)
	//	CPU-DBG-DATA	internal register responses from within the CPU
	//	sys	Responses from the front-side bus here in the ZipSystem
	// assign	dbg_odata = (!dbg_addr) ? cpu_status
	//			:((!cmd_addr[5])?cpu_dbg_data : sys_idata);
	initial dbg_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !dbg_cyc)
		dbg_ack <= 1'b0;
	else
		dbg_ack <= pre_dbg_ack || cpu_read_ack;

	always @(posedge i_clk)
	if (!OPT_LOWPOWER || (dbg_cyc && (pre_dbg_ack || cpu_read_ack)))
	casez(pre_dbg_addr)
	DBG_ADDR_CPU:	dbg_r_odata <= cpu_dbg_data;
	// DBG_ADDR_CTRL, and the (reserved) 2'b11 space
	default:	dbg_r_odata <= dbg_cpu_status;
	endcase

	always @(*)
	if (dbg_ack_addr == DBG_ADDR_SYS)
		dbg_odata = sys_idata;
	else
		dbg_odata = dbg_r_odata;

	assign	dbg_stall = (OPT_DISTRIBUTED_REGS ? cpu_read_ack : 1'b0) ||
			(dbg_cpu_read_req && pre_dbg_ack)
			|| (cmd_write && cpu_dbg_stall
				&& dbg_addr[6:5] == DBG_ADDR_CPU)
			||(dbg_addr[6]==DBG_ADDR_SYS[1] && cpu_lcl_cyc);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Arbitrate between CPU and DMA
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Now for the external wishbone bus
	//	Need to arbitrate between the flash cache and the CPU
	// The way this works, though, the CPU will stall once the flash
	// cache gets access to the bus--the CPU will be stuck until the
	// flash cache is finished with the bus.
	generate if (OPT_DMA)
	begin : GEN_ARB
		wbpriarbiter #(
		// {{{
		.DW(BUS_WIDTH),
		.AW(PAW)
		// }}}
		) dmacvcpu(
			// {{{
			.i_clk(i_clk),
			//
			.i_a_cyc(mmu_cyc), .i_a_stb(mmu_stb), .i_a_we(mmu_we),
			.i_a_adr(mmu_addr),.i_a_dat(mmu_data), .i_a_sel(mmu_sel),
				.o_a_stall(mmu_stall),
				.o_a_ack(mmu_ack), .o_a_err(mmu_err),
			//
			.i_b_cyc(dc_cyc), .i_b_stb(dc_stb), .i_b_we(dc_we),
			.i_b_adr(dc_addr), .i_b_dat(dc_data), .i_b_sel(dc_sel),
				.o_b_stall(dc_stall),
				.o_b_ack(dc_ack), .o_b_err(dc_err),
			//
			.o_cyc(ext_cyc), .o_stb(ext_stb), .o_we(ext_we),
			.o_adr(ext_addr), .o_dat(ext_odata), .o_sel(ext_sel),
				.i_stall(ext_stall),
				.i_ack(ext_ack), .i_err(ext_err)
			// }}}
		);
	end else begin : NO_ARB
		assign	ext_cyc   = mmu_cyc;
		assign	ext_stb   = mmu_stb;
		assign	ext_we    = mmu_we;
		assign	ext_addr  = mmu_addr;
		assign	ext_odata = mmu_data;
		assign	ext_sel   = mmu_sel;
		assign	mmu_stall = ext_stall;
		assign	mmu_ack   = ext_ack;
		assign	mmu_err   = ext_err;

		assign	dc_stall = 1'b0;
		assign	dc_ack   = 1'b0;
		assign	dc_err   = 1'b0;
	end endgenerate

	assign	mmu_idata = ext_idata;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Delay access to the external bus by one clock (if necessary)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (DELAY_EXT_BUS)
	begin : DELAY_EXTERNAL_BUS
		// {{{
		busdelay #(
			// {{{
			.AW(PAW),
			.DW(BUS_WIDTH),
			.DELAY_STALL(0)
			// }}}
		) extbus(
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.i_wb_cyc(ext_cyc), .i_wb_stb(ext_stb),
				.i_wb_we(ext_we),
			.i_wb_addr(ext_addr), .i_wb_data(ext_odata),
				.i_wb_sel(ext_sel),
				.o_wb_stall(ext_stall), .o_wb_ack(ext_ack),
				.o_wb_data(ext_idata), .o_wb_err(ext_err),
			//
			.o_dly_cyc(o_wb_cyc), .o_dly_stb(o_wb_stb),
				.o_dly_we(o_wb_we), .o_dly_addr(o_wb_addr),
				.o_dly_data(o_wb_data),
				.o_dly_sel(o_wb_sel),
			.i_dly_stall(i_wb_stall),
			.i_dly_ack(i_wb_ack && !wdbus_int),
				.i_dly_data(i_wb_data),
			.i_dly_err((i_wb_err)||(wdbus_int))
			// }}}
		);
		// }}}
	end else begin : NO_EXTERNAL_BUS_DELAY
		// {{{
		assign	o_wb_cyc  = ext_cyc;
		assign	o_wb_stb  = ext_stb;
		assign	o_wb_we   = ext_we;
		assign	o_wb_addr = ext_addr;
		assign	o_wb_data = ext_odata;
		assign	o_wb_sel  = ext_sel;
		assign	ext_stall = i_wb_stall;
		assign	ext_ack   = i_wb_ack && !wdbus_int;
		assign	ext_idata = i_wb_data;
		assign	ext_err   = (i_wb_err)||(wdbus_int);
		// }}}
	end endgenerate
	// }}}

	assign	o_ext_int = (cmd_halt) && (!cpu_stall);

	////////////////////////////////////////////////////////////////////////
	//
	// Simulation only accesses, to make the simulation display work
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	VBENCH_TB
	// {{{
	assign	early_branch = thecpu.core.dcd_early_branch;
	assign	early_branch_pc = thecpu.core.dcd_branch_pc;

	assign	dcdA = thecpu.core.dcd_full_A;
	assign	dcdB = thecpu.core.dcd_full_B;

	assign	new_pc = thecpu.core.new_pc;
	assign	cpu_ipc= thecpu.core.ipc;
	assign	cpu_upc= thecpu.core.upc;
	assign	pf_pc  = thecpu.core.pf_pc;
	assign	cpu_interrupt = pic_interrupt;

	assign	pf_cyc = thecpu.pf_cyc;
	assign	pf_stb = thecpu.pf_stb;
	assign	pf_we  = thecpu.pf_we;
	assign	pf_addr= { thecpu.pf_addr, 2'b00 };
	assign	pf_ack = thecpu.pf_ack;
	assign	pf_valid = thecpu.pf_valid;
	assign	pf_illegal = thecpu.pf_illegal;
	// assign	cpu_idata  = thecpu.i_wb_data;
	assign	pf_instruction = thecpu.pf_instruction;
	assign	pf_instruction_pc = thecpu.pf_instruction_pc;
	generate if (OPT_PIPELINED)
	begin : GEN_PFORMEM_OWNER_PIPE
		assign	pformem_owner = thecpu.PRIORITY_DATA.pformem.r_a_owner;
	end else begin : GEN_PFORMEM_OWNER
		assign	pformem_owner = thecpu.PRIORITY_PREFETCH.pformem.r_a_owner;
	end endgenerate
	//
	//
	// Peeking into the decode stage
	// {{{
	assign	dcd_ce      = thecpu.core.dcd_ce;
	assign	dcd_stalled = thecpu.core.dcd_stalled;
	assign	dcd_gie     = thecpu.core.dcd_gie;
	assign	dcd_valid   = thecpu.core.dcd_valid;
	assign	dcd_illegal = thecpu.core.dcd_illegal;
	assign	dcd_phase   = thecpu.core.dcd_phase;
	assign	dcd_break   = thecpu.core.dcd_break;
	assign	dcd_pipe    = thecpu.core.dcd_pipe;
		//
	assign	dcd_opn     = thecpu.core.dcd_opn;
	assign	dcd_rA      = thecpu.core.dcd_rA;
	assign	dcd_rB      = thecpu.core.dcd_rB;
	assign	dcd_wR      = thecpu.core.dcd_wR;
	assign	dcd_wF      = thecpu.core.dcd_wF;
	assign	dcdR        = thecpu.core.instruction_decoder.w_dcdR;
	assign	dcdRpc      = thecpu.core.instruction_decoder.w_dcdR_pc;
	assign	dcdRcc      = thecpu.core.instruction_decoder.w_dcdR_cc;
	assign	dcd_pc      = thecpu.core.dcd_pc;
	assign	dcd_M       = thecpu.core.dcd_M;
	// }}}
	// Peeking into the op stage
	// {{{
	assign	op_ce        = thecpu.core.op_ce;
	assign	op_illegal   = thecpu.core.op_illegal;
	assign	op_valid     = thecpu.core.op_valid;
	assign	op_valid_mem = thecpu.core.op_valid_mem;
	assign	op_valid_alu = thecpu.core.op_valid_alu;
	assign	op_stall     = thecpu.core.op_stall;
	assign	op_wR        = thecpu.core.op_wR;
	assign	op_wF        = thecpu.core.op_wF;
	assign	op_phase     = thecpu.core.op_phase;
	assign	op_gie       = thecpu.core.op_gie;
	assign	op_pipe      = thecpu.core.op_pipe;
	assign	op_R         = thecpu.core.op_R;
	assign	op_Aid       = thecpu.core.op_Aid;
	assign	op_Bid       = thecpu.core.op_Bid;
	assign	op_Av        = thecpu.core.op_Av;
	assign	op_Bv        = thecpu.core.op_Bv;
	assign	op_pc        = thecpu.core.op_pc;
	assign	master_stall = thecpu.core.master_stall;

	assign	op_F         = thecpu.core.op_F;
	assign	op_pipe      = thecpu.core.op_pipe;
	assign	op_opn       = thecpu.core.op_opn;
	// }}}
	// Peeking into the ALU stage
	// {{{
	assign	alu_ce   = thecpu.core.alu_ce;
	assign	adf_ce_unconditional   = thecpu.core.adf_ce_unconditional;
	assign	alu_valid   = thecpu.core.alu_valid;
	assign	alu_wR   = thecpu.core.alu_wR;
	assign	alu_wF   = thecpu.core.alu_wF;
	assign	alu_pc_valid   = thecpu.core.alu_pc_valid;
	assign	alu_illegal    = thecpu.core.alu_illegal;
	assign	alu_gie        = thecpu.core.alu_gie;
	assign	set_cond       = thecpu.core.set_cond;
	assign	alu_phase      = thecpu.core.alu_phase;
	assign	alu_flags      = thecpu.core.alu_flags;
	assign	alu_pc         = thecpu.core.alu_pc;

	assign	alu_result     = thecpu.core.alu_result;
	assign	alu_busy       = thecpu.core.alu_busy;
	assign	alu_reg        = thecpu.core.alu_reg;
	// }}}
	// Peeking into the MEM stage
	// {{{
	//
	assign	mem_valid    = thecpu.mem_valid;
	assign	mem_pc_valid = thecpu.core.mem_pc_valid;
	assign	mem_ce       = thecpu.core.o_mem_ce;
	assign	mem_busy     = thecpu.core.i_mem_busy;
	assign	mem_rdbusy   = thecpu.core.i_mem_rdbusy;
	assign	mem_wreg     = thecpu.core.i_mem_wreg;
	// }}}
	// Peeking into the divide stage
	// {{{
	assign	div_valid = thecpu.core.div_valid;
	assign	div_ce    = thecpu.core.div_ce;
	assign	div_busy  = thecpu.core.div_busy;
	// }}}
	// Writeback stage
	// {{{
	assign	wr_reg_id = thecpu.core.wr_reg_id;
	assign	wr_reg_ce = thecpu.core.wr_reg_ce;
	assign	wr_flags_ce = thecpu.core.wr_flags_ce;
	assign	wr_gpreg_vl = thecpu.core.wr_gpreg_vl;
	assign	wr_spreg_vl = thecpu.core.wr_spreg_vl;
	assign	w_iflags    = thecpu.core.w_iflags;
	assign	w_uflags    = thecpu.core.w_uflags;
	// }}}
	// Miscellaneous
	// {{{
	assign	cpu_sim      = thecpu.core.cpu_sim;
	assign	cpu_sim_immv = thecpu.core.op_sim_immv;
	assign	r_sleep      = thecpu.core.sleep;
	assign	master_ce    = thecpu.core.master_ce;
	assign	op_break     = thecpu.core.op_break;
	assign	r_gie        = thecpu.core.gie;
	// }}}
	//
	// ZipSystem peripherals
	// {{{
	assign	watchbus = { 18'h0, u_watchbus.r_value };
	assign	watchdog = {  1'b0, u_watchdog.r_value };
	assign	timer_a = tma_data;
	assign	timer_b = tmb_data;
	assign	timer_c = tmc_data;
	assign	jiffies = jif_data;
	//
	assign	wb_cyc_gbl = thecpu.mem_cyc_gbl;
	assign	wb_stb_gbl = thecpu.mem_stb_gbl;
	assign	wb_cyc_lcl = thecpu.mem_cyc_lcl;
	assign	wb_stb_lcl = thecpu.mem_stb_lcl;
	assign	mem_stb_gbl = thecpu.mem_stb_gbl;
	assign	mem_stb_lcl = thecpu.mem_stb_lcl;
	assign	mem_we     = thecpu.mem_we;
	assign	mem_ack    = thecpu.mem_ack;
	assign	mem_stall  = thecpu.mem_stall;
	assign	mem_data   = thecpu.mem_data;
	assign	mem_addr   = { thecpu.core.o_mem_addr };
	assign	mem_result = thecpu.mem_result;
	assign	switch_to_interrupt = thecpu.core.w_switch_to_interrupt;
	assign	release_from_interrupt = thecpu.core.w_release_from_interrupt;
	assign	break_en = thecpu.core.break_en;
	// }}}
	// }}}
`endif
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire		unused;
	assign unused = &{ 1'b0,
		cpu_dbg_cc[2],
		pic_ack, pic_stall, cpu_clken,
		tma_ack, tma_stall, tmb_ack, tmb_stall, tmc_ack, tmc_stall,
		jif_ack, jif_stall, no_dbg_err, dbg_sel,
		ctri_ack, ctri_stall, mmus_stall, dmac_stall,
		wdt_ack, wdt_stall, actr_ack, actr_stall,
		wdbus_ack,
		// moc_ack, mtc_ack, mic_ack, mpc_ack,
		// uoc_ack, utc_ack, uic_ack, upc_ack,
		// moc_stall, mtc_stall, mic_stall, mpc_stall,
		// uoc_stall, utc_stall, uic_stall, upc_stall,
		// Unused MMU pins
		pf_return_stb, pf_return_we, pf_return_p, pf_return_v,
		pf_return_cachable, cpu_miss };
	// verilator lint_on UNUSED
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
	////////////////////////////////////////////////////////////////////////
	//
	// Formal setup
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	localparam	F_LGDEPTH  = 4,	// Debug/local bus outstanding counts
			F_LGXDEPTH = 6;	// External bus outstanding counts
	(* anyconst *)	reg	f_lowpower;

	assign	OPT_LOWPOWER = f_lowpower;

	reg	f_past_valid;

	// Per-interface outstanding-request counters (see the fwb_* below)
	wire	[F_LGDEPTH-1:0]	 fdbg_nreqs, fdbg_nacks, fdbg_outstanding;
	wire	[F_LGDEPTH-1:0]	 flcl_nreqs, flcl_nacks, flcl_outstanding;
	wire	[F_LGXDEPTH-1:0] fgbl_nreqs, fgbl_nacks, fgbl_outstanding;
	wire	[F_LGXDEPTH-1:0] fdma_nreqs, fdma_nacks, fdma_outstanding;
	wire	[F_LGXDEPTH-1:0] fext_nreqs, fext_nacks, fext_outstanding;

	// sys-bus shadow pipeline: every accepted request must be acked two
	// clocks later, with that request's device data
	reg		f_sys1_valid;
	reg		f_sys1_we, f_sys2_we;
	reg	[7:0]	f_sys1_addr;
	wire		f_sys_now_dmac;

	// debug-bus shadow pipeline (same idea, for the external debug port)
	reg			f_dbg1_valid, f_dbg2_valid;
	reg			f_dbg1_we, f_dbg2_we;
	reg	[1:0]		f_dbg1_space, f_dbg2_space;
	reg	[4:0]		f_dbg1_addr;
	reg	[DBG_WIDTH-1:0]	f_dbg1_status, f_dbg2_data;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties: count(STB && !STALL) == count(ACK), etc.
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// 1. The external debug bus: we are the slave of an assumed-legal
	// master, which contends with the CPU for the peripherals within
	fwb_slave #(
		// {{{
		.AW(7), .DW(DBG_WIDTH), .F_LGDEPTH(F_LGDEPTH)
		// }}}
	) fwb_dbg (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(i_dbg_cyc), .i_wb_stb(i_dbg_stb),
			.i_wb_we(i_dbg_we),	.i_wb_addr(i_dbg_addr),
			.i_wb_data(i_dbg_data),	.i_wb_sel(i_dbg_sel),
		.i_wb_ack(o_dbg_ack), .i_wb_stall(o_dbg_stall),
		.i_wb_idata(o_dbg_data), .i_wb_err(1'b0),
		.f_nreqs(fdbg_nreqs), .f_nacks(fdbg_nacks),
			.f_outstanding(fdbg_outstanding)
		// }}}
	);

	// 2. The CPU's local bus: the anyseq CPU model, assumed legal here,
	// is the other master contending for the peripherals
	fwb_slave #(
		// {{{
		.AW(8), .DW(DBG_WIDTH), .F_LGDEPTH(F_LGDEPTH)
		// }}}
	) fwb_cpu_lcl (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cpu_reset),
		.i_wb_cyc(cpu_lcl_cyc), .i_wb_stb(cpu_lcl_stb),
		.i_wb_we(cpu_we), .i_wb_addr(cpu_addr[7:0]),
		.i_wb_data(cpu_data[DBG_WIDTH-1:0]),
		.i_wb_sel(cpu_sel[DBG_WIDTH/8-1:0]),
		.i_wb_ack(cpu_lcl_cyc && sys_ack_cpu),
		.i_wb_stall(sys_stall),
		.i_wb_idata(sys_idata), .i_wb_err(1'b0),
		.f_nreqs(flcl_nreqs), .f_nacks(flcl_nacks),
		.f_outstanding(flcl_outstanding)
		// }}}
	);

	// 3. The CPU's global bus, through the null MMU to the arbiter
	fwb_slave #(
		// {{{
		.AW(PAW), .DW(BUS_WIDTH), .F_LGDEPTH(F_LGXDEPTH)
		// }}}
	) fwb_cpu_gbl (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cpu_reset),
		.i_wb_cyc(cpu_gbl_cyc), .i_wb_stb(cpu_gbl_stb),
		.i_wb_we(cpu_we), .i_wb_addr(cpu_addr),
		.i_wb_data(cpu_data), .i_wb_sel(cpu_sel),
		.i_wb_ack(cpu_gbl_cyc && mmu_cpu_ack),
		.i_wb_stall(mmu_cpu_stall),
		.i_wb_idata(mmu_cpu_idata), .i_wb_err(cpu_err),
		.f_nreqs(fgbl_nreqs), .f_nacks(fgbl_nacks),
		.f_outstanding(fgbl_outstanding)
		// }}}
	);


	// 4. The DMA's (anyseq) master port, assumed legal here, contending
	// with the CPU's global bus for the external bus
	fwb_slave #(
		// {{{
		.AW(PAW), .DW(BUS_WIDTH), .F_LGDEPTH(F_LGXDEPTH)
		// }}}
	) fwb_dma (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cpu_reset),
		.i_wb_cyc(dc_cyc), .i_wb_stb(dc_stb),
		.i_wb_we(dc_we), .i_wb_addr(dc_addr),
		.i_wb_data(dc_data), .i_wb_sel(dc_sel),
		// A master ignores acks/errs once it has dropped CYC
		.i_wb_ack(dc_cyc && dc_ack), .i_wb_stall(dc_stall),
		.i_wb_idata(ext_idata), .i_wb_err(dc_cyc && dc_err),
		.f_nreqs(fdma_nreqs), .f_nacks(fdma_nacks),
		.f_outstanding(fdma_outstanding)
		// }}}
	);

	always @(*)
	if (!i_reset)
		assert(fdma_outstanding == 0);

	// 5. The external bus: prove the outgoing bus obeys Wishbone,
	// whatever the CPU and DMA do
	fwb_master #(
		// {{{
		.AW(PAW), .DW(BUS_WIDTH), .F_LGDEPTH(F_LGXDEPTH)
		// }}}
	) fwb_ext (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(o_wb_cyc), .i_wb_stb(o_wb_stb),
		.i_wb_we(o_wb_we), .i_wb_addr(o_wb_addr),
		.i_wb_data(o_wb_data), .i_wb_sel(o_wb_sel),
		.i_wb_ack(i_wb_ack), .i_wb_stall(i_wb_stall),
		.i_wb_idata(i_wb_data), .i_wb_err(i_wb_err),
		.f_nreqs(fext_nreqs), .f_nacks(fext_nacks),
		.f_outstanding(fext_outstanding)
		// }}}
	);

	// The (anyseq) bus watchdog model may only fire at a hung request --
	// its real hang-recovery purpose -- not while the bus sits idle
	always @(*)
	if (fext_outstanding == 0)
		assume(!wdbus_int);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Sys bus properties ...
	// {{{
	// Only the DMAC's ack dies on cpu_reset (its i_reset is cpu_reset):
	// a DMAC request accepted during cpu_reset is never answered. The
	// 0x10-0x1f decode matches sel_dmac above.
	// assign	f_sys_now_dmac = (sys_addr[7:4] == 4'h1);

	// Every accepted cpu request is acked two clocks later
	initial	{ f_sys1_valid } = 2'b00;
	always @(posedge i_clk)
	if (i_reset || !sys_cyc)
		{ f_sys1_valid } <= 2'b00;
	else begin
		// Stage 1
		f_sys1_valid <= sys_stb;
		if (dbg_stb && !dbg_stall && (dbg_addr[6:5] != DBG_ADDR_CPU))
			f_sys1_valid <= 1;
		f_sys1_we    <= sys_we;
		f_sys1_addr  <= sys_addr;

		// Stage 2
		f_sys2_we    <= f_sys1_we;
	end

	// External bus tracks its owner
/*
	always @(*)
	if (f_past_valid)
	begin
		if (f_arb_cpu_owner)
		begin
			assert(fdma_outstanding == 0);
			if (o_wb_cyc)
				assert(fext_outstanding == fgbl_outstanding);
		end else begin
			assert(fgbl_outstanding == 0);
			if (o_wb_cyc)
				assert(fext_outstanding == fdma_outstanding);
		end
	end
*/

	always @(*)
	if (f_past_valid)
	begin
		assert(!pre_cpu_ack || !pre_dbg_ack);
		assert(!sys_ack_cpu || !dbg_ack);
	end

	// Tie the CPU's outstanding count
	always @(*)
	if (f_past_valid && cpu_lcl_cyc)
		assert(flcl_outstanding == (pre_cpu_ack ? 1:0)
			+ (sys_ack_cpu ? 1:0));
	// }}}

	// Tie the (external) debug bus outstanding count to the shadow
	always @(*)
	if (f_past_valid && i_dbg_cyc)
		assert(fdbg_outstanding == (o_dbg_ack ? 1:0)+(pre_dbg_ack ? 1:0)
			+ ((DELAY_DBG_BUS && dbg_ack) ? 1:0)
			+ ((OPT_DISTRIBUTED_REGS && cpu_read_ack) ? 1:0));

	always @(posedge i_clk)
	if (f_past_valid && $past(cpu_lcl_stb, 2) && $past(cpu_lcl_cyc))
	begin
		assert(sys_ack_cpu);
		assert(cpu_ack);

		if ($past(sys_we,2))
		begin end else if ($past(sys_addr[7:4] == DMAC_ADDR[7:4]))
		begin
			assert(cpu_idata == $past(dmac_data));
		end else if (!$past(sys_addr[7],2))
		casez($past(sys_addr[4:0],2))
		5'h00: assert(cpu_idata == $past(pic_data));
		5'h01: assert(cpu_idata == $past(wdt_data));
		5'h02: assert(cpu_idata == $past(wdbus_data));
		5'h03: assert(cpu_idata == $past(ctri_data));
		5'h04: assert(cpu_idata == $past(tma_data));
		5'h05: assert(cpu_idata == $past(tmb_data));
		5'h06: assert(cpu_idata == $past(tmc_data));
		5'h07: assert(cpu_idata == $past(jif_data));
		5'h08: assert(cpu_idata == $past(mtc_data));
		5'h09: assert(cpu_idata == $past(moc_data));
		5'h0a: assert(cpu_idata == $past(mpc_data));
		5'h0b: assert(cpu_idata == $past(mic_data));
		5'h0c: assert(cpu_idata == $past(utc_data));
		5'h0d: assert(cpu_idata == $past(uoc_data));
		5'h0e: assert(cpu_idata == $past(upc_data));
		5'h0f: assert(cpu_idata == $past(uic_data));
		endcase
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(dbg_stb && !dbg_stall && dbg_we
			&& dbg_addr[6:5] == DBG_ADDR_CPU))
	begin
		assert(!cpu_reset);
		assert(cmd_write);
		assert(cmd_waddr == $past(dbg_addr[4:0]));
		assert(cmd_wdata == $past(dbg_idata));
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset || cpu_reset))
	begin
		assert(!cmd_write);
	end else if ($past(cmd_write && !cpu_has_halted))
	begin
		assert(cmd_write);
		assert($stable(cmd_waddr));
		assert($stable(cmd_wdata));
	end

	always @(posedge i_clk)
	if (f_past_valid && $past(dbg_stb && !dbg_stall && !dbg_we, 2)
					&& $past(dbg_cyc) && dbg_cyc && dbg_ack)
	begin
		if ($past(dbg_we,2))
		begin
			// Return data following a write operation is a don't
			// care.
		end else if ($past(dbg_addr[6:5],2) == DBG_ADDR_CTRL)
		begin
			assert(dbg_odata == $past(dbg_cpu_status));
		end else if ($past(dbg_addr[6:5],2) == DBG_ADDR_CPU)
		begin
			assert(dbg_odata == $past(cpu_dbg_data));
		end else if ($past(dbg_addr[6:5],2) != DBG_ADDR_SYS)
		begin
		end else casez($past(dbg_addr[4:0],2))
		5'h00: assert(dbg_odata == $past(pic_data));
		5'h01: assert(dbg_odata == $past(wdt_data));
		5'h02: assert(dbg_odata == $past(wdbus_data));
		5'h03: assert(dbg_odata == $past(ctri_data));
		5'h04: assert(dbg_odata == $past(tma_data));
		5'h05: assert(dbg_odata == $past(tmb_data));
		5'h06: assert(dbg_odata == $past(tmc_data));
		5'h07: assert(dbg_odata == $past(jif_data));
		5'h08: assert(dbg_odata == $past(mtc_data));
		5'h09: assert(dbg_odata == $past(moc_data));
		5'h0a: assert(dbg_odata == $past(mpc_data));
		5'h0b: assert(dbg_odata == $past(mic_data));
		5'h0c: assert(dbg_odata == $past(utc_data));
		5'h0d: assert(dbg_odata == $past(uoc_data));
		5'h0e: assert(dbg_odata == $past(upc_data));
		5'h0f: assert(dbg_odata == $past(uic_data));
		5'b1????: assert(dbg_odata == $past(dmac_data));
		endcase
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks: make sure the assumptions above still allow traffic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (f_past_valid)
	begin
		// Completed debug reads, one per address space
		cover(dbg_ack && f_dbg2_valid && !f_dbg2_we
					&& f_dbg2_space == DBG_ADDR_CTRL);
		cover(dbg_ack && f_dbg2_valid && !f_dbg2_we
					&& f_dbg2_space == DBG_ADDR_CPU);
		cover(dbg_ack && f_dbg2_valid && !f_dbg2_we
					&& f_dbg2_space == DBG_ADDR_SYS);

		// A completed CPU (local bus) read
		// cover(sys_ack && f_sys2_valid && !f_sys2_we);

		// Back-to-back sys-bus requests from different masters
		// cover(f_sys1_valid && f_sys2_valid);

		// External bus activity, from either master
		// cover(o_wb_cyc && i_wb_ack && f_arb_cpu_owner);
		// cover(o_wb_cyc && i_wb_ack && !f_arb_cpu_owner);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless Assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (f_past_valid)
		assert(!pre_dbg_ack || !cpu_read_ack);

	(* anyconst *) reg	fnvr_cpu, fnvr_dbg;

	always @(*)
	if (fnvr_cpu && !i_reset && dbg_stb && !dbg_we)
		assume(dbg_addr[6:5] != DBG_ADDR_CPU);

	always @(*)
	if (fnvr_dbg && !i_reset && dbg_stb)
		assume(dbg_addr[6:5] == DBG_ADDR_SYS);

	always @(*)
	if (fnvr_cpu && !i_reset)
		assert(!cpu_read_ack);

always @(*)
assume(!cpu_lcl_cyc);

always @(*)
if (i_dbg_stb)
assume(!i_dbg_we);
	// }}}
`endif
// }}}
endmodule
