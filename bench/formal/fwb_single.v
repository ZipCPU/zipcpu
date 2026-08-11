////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/formal/fwb_single.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Anyseq (* anyseq *) stand-ins for the ZipSystem peripherals,
//		used when formally verifying zipsystem.v.
//
// Creator:	Sukru Uzun
//
////////////////////////////////////////////////////////////////////////////////
`default_nettype	none
// }}}
module	fwb_single (
		input	wire		i_clk, i_reset,
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire [31:0]	i_wb_data,
		input	wire [3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	wire [31:0]	o_wb_data,
		output	wire		o_int
	);

	(* anyseq *)	reg	[31:0]	f_data;
	(* anyseq *)	reg		f_int;

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb;

	// SINGLE peripherals are not allowed to stall
	assign	o_wb_stall = 1'b0;
	assign	o_wb_data  = f_data;
	assign	o_int = f_int;

	// Keep Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_we, i_wb_data, i_wb_sel };
	// verilator lint_on  UNUSED
	// }}}
endmodule
// }}}
