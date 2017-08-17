////////////////////////////////////////////////////////////////////////////////
//
// Filename:	zipbones.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	In the spirit of keeping the Zip CPU small, this implements a
//		Zip System with no peripherals: Any peripherals you wish will
//		need to be implemented off-module.
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
`default_nettype	none
//
`include "cpudefs.v"
//
`define	RESET_BIT	6
`define	STEP_BIT	8
`define	HALT_BIT	10
`define	CLEAR_CACHE_BIT	11
//
module	zipbones(i_clk, i_rst,
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
			LGICACHE=8;
	parameter [0:0]	START_HALTED=0;
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
	input	wire	i_clk, i_rst;
	// Wishbone master
	output	wire		o_wb_cyc, o_wb_stb, o_wb_we;
	output	wire	[(PAW-1):0]	o_wb_addr;
	output	wire	[31:0]	o_wb_data;
	output	wire	[3:0]	o_wb_sel;
	input	wire		i_wb_ack, i_wb_stall;
	input	wire	[31:0]	i_wb_data;
	input	wire		i_wb_err;
	// Incoming interrupts
	input	wire		i_ext_int;
	// Outgoing interrupt
	output	wire		o_ext_int;
	// Wishbone slave
	input	wire		i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr;
	input	wire	[31:0]	i_dbg_data;
	output	wire		o_dbg_ack;
	output	wire		o_dbg_stall;
	output	wire	[31:0]	o_dbg_data;
	//
`ifdef	DEBUG_SCOPE
	output	wire	[31:0]	o_cpu_debug;
`endif
	wire		dbg_cyc, dbg_stb, dbg_we, dbg_addr, dbg_stall;
	wire	[31:0]	dbg_idata, dbg_odata;
	reg		dbg_ack;

	assign	dbg_cyc     = i_dbg_cyc;
	assign	dbg_stb     = i_dbg_stb;
	assign	dbg_we      = i_dbg_we;
	assign	dbg_addr    = i_dbg_addr;
	assign	dbg_idata   = i_dbg_data;
	assign	o_dbg_ack   = dbg_ack;
	assign	o_dbg_stall = dbg_stall;
	assign	o_dbg_data  = dbg_odata;
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
	reg	[4:0]	cmd_addr;
	wire	[3:0]	cpu_dbg_cc;
	assign	dbg_cmd_write = (dbg_stb)&&(dbg_we)&&(!dbg_addr);
	//
	// Always start us off with an initial reset
	//
	initial	cmd_reset = 1'b1;
	always @(posedge i_clk)
		cmd_reset <= ((dbg_cmd_write)&&(dbg_idata[`RESET_BIT]));
	//
	initial	cmd_halt  = START_HALTED;
	always @(posedge i_clk)
		if ((i_rst)||(cmd_reset))
			cmd_halt <= START_HALTED;
		else if (dbg_cmd_write)
			cmd_halt <= ((dbg_idata[`HALT_BIT])&&(!dbg_idata[`STEP_BIT]));
		else if ((cmd_step)||(cpu_break))
			cmd_halt  <= 1'b1;

	initial	cmd_clear_pf_cache = 1'b1;
	always @(posedge i_clk)
		cmd_clear_pf_cache <= (dbg_cmd_write)&&(dbg_idata[`CLEAR_CACHE_BIT]);
	//
	initial	cmd_step  = 1'b0;
	always @(posedge i_clk)
		cmd_step <= (dbg_cmd_write)&&(dbg_idata[`STEP_BIT]);
	//
	initial	cmd_addr = 5'h0;
	always @(posedge i_clk)
		if (dbg_cmd_write)
			cmd_addr <= dbg_idata[4:0];

	wire	cpu_reset;
	assign	cpu_reset = (cmd_reset);

	wire	cpu_halt, cpu_dbg_stall;
	assign	cpu_halt = (cmd_halt);
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
	//	0x10000 -> External interrupt line is high
	assign	cmd_data = { 7'h00, 8'h00, i_ext_int,
			cpu_dbg_cc,
			1'b0, cmd_halt, (!cpu_dbg_stall), 1'b0,
			i_ext_int, cpu_reset, 1'b0, cmd_addr };

	//
	// The CPU itself
	//
	wire		cpu_lcl_cyc, cpu_lcl_stb, 
			cpu_dbg_we,
			cpu_op_stall, cpu_pf_stall, cpu_i_count;
	wire	[31:0]	cpu_dbg_data;
	assign cpu_dbg_we = ((dbg_stb)&&(dbg_we)&&(dbg_addr));
	zipcpu	#(.RESET_ADDRESS(RESET_ADDRESS),
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.LGICACHE(LGICACHE),
			.WITH_LOCAL_BUS(0))
		thecpu(i_clk, cpu_reset, i_ext_int,
			cpu_halt, cmd_clear_pf_cache, cmd_addr[4:0], cpu_dbg_we,
				dbg_idata, cpu_dbg_stall, cpu_dbg_data,
				cpu_dbg_cc, cpu_break,
			o_wb_cyc, o_wb_stb,
				cpu_lcl_cyc, cpu_lcl_stb,
				o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_data,
				(i_wb_err)||(cpu_lcl_cyc),
			cpu_op_stall, cpu_pf_stall, cpu_i_count
`ifdef	DEBUG_SCOPE
			, o_cpu_debug
`endif
			);

	// Return debug response values
	assign	dbg_odata = (!dbg_addr)?cmd_data :cpu_dbg_data;
	initial dbg_ack = 1'b0;
	always @(posedge i_clk)
		dbg_ack <= (dbg_stb)&&(!o_dbg_stall);
	assign	dbg_stall= (cpu_dbg_stall)&&(dbg_addr);

	assign	o_ext_int = (cmd_halt) && (!i_wb_stall);

	// Make Verilator happy
	// verilator lint_off UNUSED
	wire	[4:0] unused;
	assign	unused = { dbg_cyc, cpu_lcl_stb, cpu_op_stall, cpu_pf_stall, cpu_i_count };
	// verilator lint_on  UNUSED

endmodule
