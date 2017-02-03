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
// Copyright (C) 2015, 2017, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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
		, o_zip_debug
`endif
		);
	parameter	RESET_ADDRESS=30'h0100000, ADDRESS_WIDTH=30,
			LGICACHE=8, START_HALTED=0;
	localparam	AW=ADDRESS_WIDTH;
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
	input			i_ext_int;
	// Outgoing interrupt
	output	wire		o_ext_int;
	// Wishbone slave
	input			i_dbg_cyc, i_dbg_stb, i_dbg_we, i_dbg_addr;
	input		[31:0]	i_dbg_data;
	output	reg		o_dbg_ack;
	output	wire		o_dbg_stall;
	output	wire	[31:0]	o_dbg_data;
	//
`ifdef	DEBUG_SCOPE
	output	wire	[31:0]	o_zip_debug;
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
	reg	[4:0]	cmd_addr;
	wire	[3:0]	cpu_dbg_cc;
	assign	dbg_cmd_write = (i_dbg_cyc)&&(i_dbg_stb)&&(i_dbg_we)&&(~i_dbg_addr);
	//
	// Always start us off with an initial reset
	//
	initial	cmd_reset = 1'b1;
	always @(posedge i_clk)
		cmd_reset <= ((dbg_cmd_write)&&(i_dbg_data[6]));
	//
	initial	cmd_halt  = START_HALTED;
	always @(posedge i_clk)
		if (i_rst)
			cmd_halt <= (START_HALTED == 1)? 1'b1 : 1'b0;
		else if (dbg_cmd_write)
			cmd_halt <= ((i_dbg_data[10])||(i_dbg_data[8]));
		else if ((cmd_step)||(cpu_break))
			cmd_halt  <= 1'b1;

	initial	cmd_clear_pf_cache = 1'b0;
	always @(posedge i_clk)
		if (i_rst)
			cmd_clear_pf_cache <= 1'b0;
		else if (dbg_cmd_write)
			cmd_clear_pf_cache <= i_dbg_data[11];
		else
			cmd_clear_pf_cache <= 1'b0;
	//
	initial	cmd_step  = 1'b0;
	always @(posedge i_clk)
		cmd_step <= (dbg_cmd_write)&&(i_dbg_data[8]);
	//
	initial	cmd_addr = 5'h0;
	always @(posedge i_clk)
		if (dbg_cmd_write)
			cmd_addr <= i_dbg_data[4:0];

	wire	cpu_reset;
	assign	cpu_reset = (cmd_reset)||(i_rst);

	wire	cpu_halt, cpu_dbg_stall;
	assign	cpu_halt = (i_rst)||((cmd_halt)&&(~cmd_step));
	wire	[31:0]	cmd_data;
	// Values:
	//	0x0003f -> cmd_addr mask
	//	0x00040 -> reset
	//	0x00080 -> PIC interrrupts enabled
	//	0x00100 -> cmd_step
	//	0x00200 -> cmd_stall
	//	0x00400 -> cmd_halt
	//	0x00800 -> cmd_clear_pf_cache
	//	0x01000 -> cc.sleep
	//	0x02000 -> cc.gie
	//	0x10000 -> External interrupt line is high
	assign	cmd_data = { 7'h00, 8'h00, i_ext_int,
			cpu_dbg_cc,
			1'b0, cmd_halt, (~cpu_dbg_stall), 1'b0,
			1'b0, cpu_reset, 1'b0, cmd_addr };

	//
	// The CPU itself
	//
	wire		cpu_gbl_stb, cpu_lcl_cyc, cpu_lcl_stb, 
			cpu_we, cpu_dbg_we,
			cpu_op_stall, cpu_pf_stall, cpu_i_count;
	wire	[31:0]	cpu_data;
	wire	[31:0]	cpu_dbg_data;
	assign cpu_dbg_we = ((i_dbg_cyc)&&(i_dbg_stb)
					&&(i_dbg_we)&&(i_dbg_addr));
	zipcpu	#(RESET_ADDRESS,ADDRESS_WIDTH,LGICACHE)
		thecpu(i_clk, cpu_reset, i_ext_int,
			cpu_halt, cmd_clear_pf_cache, cmd_addr[4:0], cpu_dbg_we,
				i_dbg_data, cpu_dbg_stall, cpu_dbg_data,
				cpu_dbg_cc, cpu_break,
			o_wb_cyc, o_wb_stb,
				cpu_lcl_cyc, cpu_lcl_stb,
				o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_data,
				(i_wb_err)||(cpu_lcl_cyc),
			cpu_op_stall, cpu_pf_stall, cpu_i_count
`ifdef	DEBUG_SCOPE
			, o_zip_debug
`endif
			);

	// Return debug response values
	assign	o_dbg_data = (~i_dbg_addr)?cmd_data :cpu_dbg_data;
	initial o_dbg_ack = 1'b0;
	always @(posedge i_clk)
		o_dbg_ack <= (i_dbg_cyc)&&((~i_dbg_addr)||(~o_dbg_stall));
	assign	o_dbg_stall=(i_dbg_cyc)&&(cpu_dbg_stall)&&(i_dbg_addr);

	assign	o_ext_int = (cmd_halt) && (~i_wb_stall);

endmodule
