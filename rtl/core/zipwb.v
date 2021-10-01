////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipwb.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	This is the top level module holding the core of the Zip CPU
//		together.  The Zip CPU is designed to be as simple as possible.
//	(actual implementation aside ...)  The instruction set is about as
//	RISC as you can get, with only 26 instruction types currently supported.
//	(There are still 8-instruction Op-Codes reserved for floating point,
//	and 5 which can be used for transactions not requiring registers.)
//	Please see the accompanying spec.pdf file for a description of these
//	instructions.
//
//	All instructions are 32-bits wide.  All bus accesses, both address and
//	data, are 32-bits over a wishbone bus.
//
//	The Zip CPU is fully pipelined with the following pipeline stages:
//
//		1. Prefetch, returns the instruction from memory.
//
//		2. Instruction Decode
//
//		3. Read Operands
//
//		4. Apply Instruction
//
//		4. Write-back Results
//
//	Further information about the inner workings of this CPU, such as
//	what causes pipeline stalls, may be found in the spec.pdf file.  (The
//	documentation within this file had become out of date and out of sync
//	with the spec.pdf, so look to the spec.pdf for accurate and up to date
//	information.)
//
//
//	In general, the pipelining is controlled by three pieces of logic
//	per stage: _ce, _stall, and _valid.  _valid means that the stage
//	holds a valid instruction.  _ce means that the instruction from the
//	previous stage is to move into this one, and _stall means that the
//	instruction from the previous stage may not move into this one.
//	The difference between these control signals allows individual stages
//	to propagate instructions independently.  In general, the logic works
//	as:
//
//
//	assign	(n)_ce = (n-1)_valid && (!(n)_stall)
//
//
//	always @(posedge i_clk)
//		if ((i_reset)||(clear_pipeline))
//			(n)_valid = 0
//		else if (n)_ce
//			(n)_valid = 1
//		else if (n+1)_ce
//			(n)_valid = 0
//
//	assign (n)_stall = (  (n-1)_valid && ( pipeline hazard detection )  )
//			|| (  (n)_valid && (n+1)_stall );
//
//	and ...
//
//	always @(posedge i_clk)
//		if (n)_ce
//			(n)_variable = ... whatever logic for this stage
//
//	Note that a stage can stall even if no instruction is loaded into
//	it.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2021, Gisselquist Technology, LLC
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
`default_nettype	none
//
`include "cpudefs.v"
//
// }}}
module	zipwb #(
		// {{{
		parameter [31:0] RESET_ADDRESS=32'h010_0000,
		parameter	ADDRESS_WIDTH=30,
				LGICACHE=12,
`ifdef	OPT_MULTIPLY
		parameter	IMPLEMENT_MPY = `OPT_MULTIPLY,
`else
		parameter	IMPLEMENT_MPY = 0,
`endif
`ifdef	OPT_DIVIDE
		parameter [0:0]	IMPLEMENT_DIVIDE = 1,
`else
		parameter [0:0]	IMPLEMENT_DIVIDE = 0,
`endif
`ifdef	OPT_IMPLEMENT_FPU
		parameter [0:0]	IMPLEMENT_FPU = 1,
`else
		parameter [0:0]	IMPLEMENT_FPU = 0,
`endif
`ifdef	OPT_EARLY_BRANCHING
		parameter [0:0]	EARLY_BRANCHING = 1,
`else
		parameter [0:0]	EARLY_BRANCHING = 0,
`endif
`ifdef	OPT_CIS
		parameter [0:0]	OPT_CIS = 1'b1,
`else
		parameter [0:0]	OPT_CIS = 1'b0,
`endif
`ifdef	OPT_PIPELINED
		parameter	[0:0]	OPT_PIPELINED = 1'b1,
`else
		parameter	[0:0]	OPT_PIPELINED = 1'b0,
`endif
		parameter	[0:0]	IMPLEMENT_LOCK=1,
`ifdef	OPT_DCACHE
		parameter		OPT_LGDCACHE = 10,
`else
		parameter		OPT_LGDCACHE = 0,
`endif
`ifdef	VERILATOR
		parameter [0:0]		OPT_SIM = 1'b1,
`else
		parameter [0:0]		OPT_SIM = 1'b0,
`endif
		parameter [0:0]	WITH_LOCAL_BUS = 1'b1,
		localparam	AW=ADDRESS_WIDTH
`ifdef	FORMAL
		, parameter	F_LGDEPTH=8
`endif
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset, i_interrupt,
		output	wire		o_cpu_clken,
		// Debug interface -- inputs
		input	wire		i_halt, i_clear_cache,
		input	wire	[4:0]	i_dbg_wreg,
		input	wire		i_dbg_we,
		input	wire	[31:0]	i_dbg_data,
		input	wire	[4:0]	i_dbg_rreg,
		// Debug interface -- outputs
		output	wire		o_dbg_stall,
		output	reg	[31:0]	o_dbg_reg,
		output	reg	[2:0]	o_dbg_cc,
		output	wire		o_break,
		// CPU interface to the wishbone bus
		// Wishbone interface -- outputs
		output	wire		o_wb_gbl_cyc, o_wb_gbl_stb,
		output	wire		o_wb_lcl_cyc, o_wb_lcl_stb, o_wb_we,
		output	wire	[(AW-1):0]	o_wb_addr,
		output	wire	[31:0]	o_wb_data,
		output	wire	[3:0]	o_wb_sel,
		// Wishbone interface -- inputs
		input	wire		i_wb_stall, i_wb_ack,
		input	wire	[31:0]	i_wb_data,
		input	wire		i_wb_err,
		// Accounting outputs ... to help us count stalls and usage
		output	wire		o_op_stall,
		output	wire		o_pf_stall,
		output	wire		o_i_count
		//
`ifdef	DEBUG_SCOPE
		, output reg	[31:0]	o_debug
`endif
	// }}}
	);

	// Declarations
	// {{{
	localparam	[0:0]	OPT_DCACHE = (OPT_LGDCACHE > 0);
`ifdef	OPT_PIPELINED_BUS_ACCESS
	localparam	[0:0]	OPT_PIPELINED_BUS_ACCESS = (OPT_PIPELINED);
`else
	localparam	[0:0]	OPT_PIPELINED_BUS_ACCESS = 1'b0;
`endif
	localparam	[0:0]	OPT_MEMPIPE = OPT_PIPELINED_BUS_ACCESS;
	localparam	[0:0]	OPT_LOCK=(IMPLEMENT_LOCK)&&(OPT_PIPELINED);
`ifdef	OPT_NO_USERMODE
	localparam	[0:0]	OPT_NO_USERMODE = 1'b1;
`else
	localparam	[0:0]	OPT_NO_USERMODE = 1'b0;
`endif
`ifdef	OPT_SINGLE_FETCH
	localparam FETCH_LIMIT = (LGICACHE > 0) ? 4 : 1;
`else
`ifdef	OPT_DOUBLE_FETCH
	localparam FETCH_LIMIT = (LGICACHE > 0) ? 4 : 2;
`else
	localparam FETCH_LIMIT = 4;
`endif	// OPT_DOUBLE_FETCH
`endif	// OPT_SINGLE_FETCH

	wire	[31:0]	cpu_debug;

	// Fetch
	// {{{
	wire		pf_new_pc, clear_icache, pf_ready;
	wire [AW+1:0]	pf_request_address;
	wire	[31:0]	pf_instruction;
	wire [AW+1:0]	pf_instruction_pc;
	wire		pf_valid, pf_illegal;
	//
	wire [AW-1:0]	pf_addr;
	wire	[31:0]	pf_data;
	wire		pf_cyc, pf_stb, pf_we, pf_stall, pf_ack, pf_err;
	// }}}
	// Memory
	// {{{
	wire		clear_dcache, mem_ce, bus_lock;
	wire	[2:0]	mem_op;
	wire	[31:0]	mem_cpu_addr;
	wire [AW+1:0]	mem_lock_pc;
	wire	[31:0]	mem_wdata, mem_data;
	wire	[4:0]	mem_reg;
	wire		mem_busy, mem_rdbusy, mem_pipe_stalled, mem_valid,
			mem_bus_err;
	wire	[4:0]	mem_wreg;
	wire	[31:0]	mem_result;
	//
	wire		mem_stb_lcl, mem_stb_gbl, mem_cyc_lcl, mem_cyc_gbl;
	wire [AW-1:0]	mem_bus_addr;
	wire		mem_we, mem_stall, mem_ack, mem_err;
	wire	[3:0]	mem_sel;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The ZipCPU Core
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	zipcore #(
		// {{{
		.RESET_ADDRESS(RESET_ADDRESS),
		.ADDRESS_WIDTH(ADDRESS_WIDTH),
		.IMPLEMENT_MPY(IMPLEMENT_MPY),
		.IMPLEMENT_DIVIDE(IMPLEMENT_DIVIDE),
		.IMPLEMENT_FPU(IMPLEMENT_FPU),
		.OPT_EARLY_BRANCHING(EARLY_BRANCHING),
		.OPT_CIS(OPT_CIS),
		.OPT_SIM(OPT_SIM),
		.OPT_PIPELINED(OPT_PIPELINED),
		.OPT_PIPELINED_BUS_ACCESS(OPT_MEMPIPE),
		.OPT_NO_USERMODE(OPT_NO_USERMODE),
		.IMPLEMENT_LOCK(IMPLEMENT_LOCK)
		// localparam	[0:0]	OPT_LOCK=(IMPLEMENT_LOCK)&&(OPT_PIPELINED);
		// parameter [0:0]	WITH_LOCAL_BUS = 1'b1;
		// localparam	AW=ADDRESS_WIDTH;
		// localparam	[(AW-1):0]	RESET_BUS_ADDRESS = RESET_ADDRESS[(AW+1):2];
`ifdef	FORMAL
		, .F_LGDEPTH(F_LGDEPTH)
`endif
		// }}}
	) core (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_interrupt(i_interrupt),
		.o_clken(o_cpu_clken),
		// Debug interface
		// {{{
		.i_halt(i_halt), .i_clear_cache(i_clear_cache),
			.i_dbg_wreg(i_dbg_wreg), .i_dbg_we(i_dbg_we),
			.i_dbg_data(i_dbg_data),
			.i_dbg_rreg(i_dbg_rreg), .o_dbg_stall(o_dbg_stall),
			.o_dbg_reg(o_dbg_reg), .o_dbg_cc(o_dbg_cc),
			.o_break(o_break),
		// }}}
		// Instruction fetch interface
		// {{{
		.o_pf_new_pc(pf_new_pc), .o_clear_icache(clear_icache),
			.o_pf_ready(pf_ready),
			.o_pf_request_address(pf_request_address),
			.i_pf_valid(pf_valid), .i_pf_illegal(pf_illegal),
				.i_pf_instruction(pf_instruction),
				.i_pf_instruction_pc(pf_instruction_pc),
		// }}}
		// Memory unit interface
		// {{{
		.o_clear_dcache(clear_dcache), .o_mem_ce(mem_ce),
			.o_bus_lock(bus_lock),
			.o_mem_op(mem_op), .o_mem_addr(mem_cpu_addr),
				.o_mem_data(mem_wdata),
				.o_mem_lock_pc(mem_lock_pc),
				.o_mem_reg(mem_reg),
			.i_mem_busy(mem_busy), .i_mem_rdbusy(mem_rdbusy),
				.i_mem_pipe_stalled(mem_pipe_stalled),
				.i_mem_valid(mem_valid),
				.i_bus_err(mem_bus_err),
				.i_mem_wreg(mem_wreg),
				.i_mem_result(mem_result),
		// }}}
		// Accounting/CPU usage interface
		// {{{
		.o_op_stall(o_op_stall), .o_pf_stall(o_pf_stall),
			.o_i_count(o_i_count),
		// }}}
		.o_debug(cpu_debug)
		// }}}
	);
	// }}}
	// o_debug -- the debugging bus input
	// {{{
`ifdef	DEBUG_SCOPE
	assign	o_debug = cpu_debug;
`else
	// Verilator lint_off UNUSED
	wire	dbg_unused;
	assign	dbg_unused = &{ 1'b0, cpu_debug };
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Instruction Fetch
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	generate if (FETCH_LIMIT <= 1)
	begin : SINGLE_FETCH

		prefetch	#(ADDRESS_WIDTH)
		// {{{
			pf(i_clk, i_reset,
				// CPU signals
				pf_new_pc, clear_icache, pf_ready,
					pf_request_address,
				pf_valid, pf_illegal, pf_instruction,
					pf_instruction_pc,
				// Wishbone signals
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
				pf_stall, pf_ack, pf_err, i_wb_data);
		// }}}
	end else if (FETCH_LIMIT == 2 || LGICACHE == 0)
	begin : DBLFETCH

		dblfetch #(ADDRESS_WIDTH)
		// {{{
			pf(i_clk, i_reset,
				// CPU signals
				pf_new_pc, clear_icache, pf_ready,
					pf_request_address,
				pf_valid, pf_illegal, pf_instruction,
					pf_instruction_pc,
				// Wishbone signals
				pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
					pf_stall, pf_ack, pf_err, i_wb_data);
		// }}}
	end else begin : PFCACHE

		pfcache #(LGICACHE, ADDRESS_WIDTH)
		// {{{
		pf(i_clk, i_reset,
			// CPU signals
			pf_new_pc, clear_icache, pf_ready,
				pf_request_address,
			pf_valid, pf_illegal, pf_instruction,
				pf_instruction_pc,
			// Wishbone signals
			pf_cyc, pf_stb, pf_we, pf_addr, pf_data,
				pf_stall, pf_ack, pf_err, i_wb_data);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Memory Unit
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	generate if (OPT_DCACHE)
	begin : DATA_CACHE

		dcache #(
			// {{{
			.LGCACHELEN(OPT_LGDCACHE),
			.ADDRESS_WIDTH(AW),
			.LGNLINES(OPT_LGDCACHE-3),
			.OPT_LOCAL_BUS(WITH_LOCAL_BUS),
			.OPT_PIPE(OPT_MEMPIPE),
			.OPT_LOCK(OPT_LOCK)
`ifdef	FORMAL
			, .OPT_FIFO_DEPTH(2)
			, .F_LGDEPTH(F_LGDEPTH)
`endif
			// }}}
		) mem(i_clk, i_reset, clear_dcache,
			/// {{{
			// CPU interface
			mem_ce, bus_lock && OPT_PIPELINED,
			mem_op, mem_cpu_addr, mem_wdata, mem_reg,
			mem_busy, mem_rdbusy, mem_pipe_stalled,
			mem_valid, mem_bus_err, mem_wreg, mem_result,
			// Wishbone interface
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_bus_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err, i_wb_data
			/// }}}
		);
	end else if (OPT_PIPELINED_BUS_ACCESS)
	begin : PIPELINED_MEM

		pipemem	#(
			// {{{
			.ADDRESS_WIDTH(AW),
			.IMPLEMENT_LOCK(OPT_LOCK),
			.WITH_LOCAL_BUS(WITH_LOCAL_BUS)
`ifdef	FORMAL
			, .OPT_MAXDEPTH(4'h3),
			.F_LGDEPTH(F_LGDEPTH)
`endif
			// }}}
		) domem(i_clk, i_reset,
			/// {{{
			// CPU interface
			mem_ce, bus_lock && OPT_PIPELINED,
			mem_op, mem_cpu_addr, mem_wdata, mem_reg,
			mem_busy, mem_rdbusy, mem_pipe_stalled,
			mem_valid, mem_bus_err, mem_wreg, mem_result,
			// Wishbone interface
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_bus_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err, i_wb_data
			// }}}
			);
	end else begin : BARE_MEM

		memops	#(
			// {{{
			.ADDRESS_WIDTH(AW),
			.IMPLEMENT_LOCK(OPT_LOCK),
			.WITH_LOCAL_BUS(WITH_LOCAL_BUS)
`ifdef	FORMAL
			, .F_LGDEPTH(F_LGDEPTH)
`endif	// F_LGDEPTH
			// }}}
		) domem(i_clk, i_reset,
			/// {{{
			// CPU interface
			mem_ce, bus_lock && OPT_PIPELINED,
			mem_op, mem_cpu_addr, mem_wdata, mem_reg,
			mem_busy, mem_rdbusy,
			mem_valid, mem_bus_err, mem_wreg, mem_result,
			// Wishbone interface
			mem_cyc_gbl, mem_cyc_lcl,
				mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_bus_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err, i_wb_data
			// }}}
			);

		assign	mem_pipe_stalled = mem_busy;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus arbiter
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Either the prefetch or the instruction gets the memory bus, but
	// never both under this arbitration scheme.
	generate if (OPT_PIPELINED)
	begin : PRIORITY_DATA

		wbdblpriarb	#(
			.DW(32),
			.AW(AW)
		) pformem(i_clk, i_reset,
			// {{{
			// Memory access to the arbiter, priority position
			mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_bus_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err,
			// Prefetch access to the arbiter
			//
			// At a first glance, we might want something like:
			//
			// pf_cyc, 1'b0, pf_stb, 1'b0, pf_we, pf_addr, pf_data, 4'hf,
			//
			// However, we know that the prefetch will not generate
			// any writes.  Therefore, the write specific lines
			// (mem_data and mem_sel) can be shared with the memory
			// in order to ease timing and LUT usage.
			pf_cyc,1'b0,pf_stb, 1'b0, pf_we,
				pf_addr, mem_data, mem_sel,
				pf_stall, pf_ack, pf_err,
			// Common wires, in and out, of the arbiter
			o_wb_gbl_cyc, o_wb_lcl_cyc, o_wb_gbl_stb, o_wb_lcl_stb,
				o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_stall, i_wb_ack, i_wb_err
			// }}}
		);

	end else begin : PRIORITY_PREFETCH

		wbdblpriarb	#(
			.DW(32), .AW(AW)
		) pformem(i_clk, i_reset,
			//{{{
			// Prefetch access to the arbiter, priority position
			//
			pf_cyc,1'b0,pf_stb, 1'b0, pf_we,
				pf_addr, mem_data, mem_sel,
				pf_stall, pf_ack, pf_err,
			// Memory access to the arbiter
			mem_cyc_gbl, mem_cyc_lcl, mem_stb_gbl, mem_stb_lcl,
				mem_we, mem_bus_addr, mem_data, mem_sel,
				mem_stall, mem_ack, mem_err,
			// Common wires, in and out, of the arbiter
			o_wb_gbl_cyc, o_wb_lcl_cyc, o_wb_gbl_stb, o_wb_lcl_stb,
				o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_stall, i_wb_ack, i_wb_err
		);
		//}}}
	end endgenerate
	//}}}
	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, pf_data, mem_lock_pc, clear_dcache };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
