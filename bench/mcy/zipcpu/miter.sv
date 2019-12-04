module miter (i_clk, i_reset, i_interrupt,
		// Debug interface
		i_halt, i_clear_pf_cache, i_dbg_reg, i_dbg_we, i_dbg_data,
			o_dbg_stall, o_dbg_reg, o_dbg_cc,
			o_break,
		// CPU interface to the wishbone bus
		o_wb_gbl_cyc, o_wb_gbl_stb,
			o_wb_lcl_cyc, o_wb_lcl_stb,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
			i_wb_stall, i_wb_data,
			i_wb_err,
		// Accounting/CPU usage interface
		o_op_stall, o_pf_stall, o_i_count

);
	parameter	AW = 30, LGICACHE=12,
			OPT_LGDCACHE = 10;
	parameter [0:0]	EARLY_BRANCHING = 1,
			OPT_CIS = 1,
			OPT_PIPELINED = 1,
			OPT_PIPELINED_BUS_ACCESS = 1,
			IMPLEMENT_LOCK = 1,
			WITH_LOCAL_BUS = 0,
			F_LGDEPTH = 4;
	localparam [0:0]	IMPLEMENT_MPY = 0,
			IMPLEMENT_DIVIDE = 0,
			IMPLEMENT_FPU    = 0,
			OPT_NO_USERMODE  = 0;
	localparam	RESET_ADDRESS = 32'h010_0000;

	input	wire		i_clk, i_reset, i_interrupt;
	// Debug interface -- inputs
	input	wire		i_halt, i_clear_pf_cache;
	input	wire	[4:0]	i_dbg_reg;
	input	wire		i_dbg_we;
	input	wire	[31:0]	i_dbg_data;
	// Debug interface -- outputs
	output	wire		o_dbg_stall;
	output	wire	[31:0]	o_dbg_reg;
	output	wire	[3:0]	o_dbg_cc;
	output	wire		o_break;
	// Wishbone interface -- outputs
	output	wire		o_wb_gbl_cyc, o_wb_gbl_stb;
	output	wire		o_wb_lcl_cyc, o_wb_lcl_stb, o_wb_we;
	output	wire	[(AW-1):0]	o_wb_addr;
	output	wire	[31:0]	o_wb_data;
	output	wire	[3:0]	o_wb_sel;
	// Wishbone interface -- inputs
	wire			i_wb_ack;
	input	wire		i_wb_stall;
	input	wire	[31:0]	i_wb_data;
	input	wire		i_wb_err;
	// Accounting outputs ... to help us count stalls and usage
	output	wire		o_op_stall;
	output	wire		o_pf_stall;
	output	wire		o_i_count;

	wire [30:0] ref_result;
	wire [30:0] uut_result;

	wire		uut_dbg_stall;
	wire	[31:0]	uut_dbg_reg;
	wire	[3:0]	uut_dbg_cc;
	wire		uut_break;
	// Wishbone interface -- outputs
	wire		uut_gbl_cyc, uut_gbl_stb;
	wire		uut_lcl_cyc, uut_lcl_stb, uut_we;
	wire [(AW-1):0]	uut_addr;
	wire	[31:0]	uut_data;
	wire	[3:0]	uut_sel;
	wire		uut_op_stall;
	wire		uut_pf_stall;
	wire		uut_i_count;

	zipcpu #(
		// .RESET_ADDRESS(RESET_ADDRESS),
		// .ADDRESS_WIDTH(AW),
		// .LGICACHE(LGICACHE),
		// .OPT_LGDCACHE(OPT_LGDCACHE),
		// .EARLY_BRANCHING(EARLY_BRANCHING),
		// .OPT_CIS(OPT_CIS),
		// .OPT_PIPELINED(OPT_PIPELINED),
		// .OPT_PIPELINED_BUS_ACCESS(OPT_PIPELINED_BUS_ACCESS),
		// .IMPLEMENT_LOCK(IMPLEMENT_LOCK),
		// .WITH_LOCAL_BUS(WITH_LOCAL_BUS),
		// .F_LGDEPTH(F_LGDEPTH),
		//
		// Locally fixed parameters
		// .IMPLEMENT_MPY(IMPLEMENT_MPY),
		// .IMPLEMENT_DIVIDE(IMPLEMENT_DIVIDE),
		// .IMPLEMENT_FPU(IMPLEMENT_FPU)
		// .OPT_NO_USERMODE(OPT_NO_USERMODE)
	) refi(.i_clk(i_clk),
		.i_reset(i_reset),
		.i_interrupt(i_interrupt),
		// Debug interface
		.i_halt(i_halt), .i_clear_pf_cache(i_clear_pf_cache),
			.i_dbg_reg(i_dbg_reg), .i_dbg_we(i_dbg_we),
				.i_dbg_data(i_dbg_data),
			.o_dbg_stall(o_dbg_stall), .o_dbg_reg(o_dbg_reg),
				.o_dbg_cc(o_dbg_cc),
			.o_break(o_break),
		// CPU interface to the wishbone bus
		.o_wb_gbl_cyc(o_wb_gbl_cyc),
			.o_wb_gbl_stb(o_wb_gbl_stb),
			.o_wb_lcl_cyc(o_wb_lcl_cyc),
			.o_wb_lcl_stb(o_wb_lcl_stb),
			.o_wb_we(o_wb_we), .o_wb_addr(o_wb_addr),
				.o_wb_data(o_wb_data), .o_wb_sel(o_wb_sel),
			.i_wb_stall(i_wb_stall),
			.i_wb_ack(i_wb_ack), .i_wb_data(i_wb_data),
			.i_wb_err(i_wb_err),
		// Accounting/CPU usage interface
		.o_op_stall(o_op_stall), .o_pf_stall(o_pf_stall),
		.o_i_count(o_i_count), .mutsel(8'h0)
	);


	zipcpu #(
		// .RESET_ADDRESS(RESET_ADDRESS),
		// .ADDRESS_WIDTH(AW),
		// .LGICACHE(LGICACHE),
		// .OPT_LGDCACHE(OPT_LGDCACHE),
		// .EARLY_BRANCHING(EARLY_BRANCHING),
		// .OPT_CIS(OPT_CIS),
		// .OPT_PIPELINED(OPT_PIPELINED),
		// .OPT_PIPELINED_BUS_ACCESS(OPT_PIPELINED_BUS_ACCESS),
		// .IMPLEMENT_LOCK(IMPLEMENT_LOCK),
		// .WITH_LOCAL_BUS(WITH_LOCAL_BUS),
		// .F_LGDEPTH(F_LGDEPTH),
		//
		// Locally fixed parameters
		// .IMPLEMENT_MPY(IMPLEMENT_MPY),
		// .IMPLEMENT_DIVIDE(IMPLEMENT_DIVIDE),
		// .IMPLEMENT_FPU(IMPLEMENT_FPU),
		// .OPT_NO_USERMODE(OPT_NO_USERMODE)
	) uut(.i_clk(i_clk),
		.i_reset(i_reset),
		.i_interrupt(i_interrupt),
		// Debug interface
		.i_halt(i_halt), .i_clear_pf_cache(i_clear_pf_cache),
			.i_dbg_reg(i_dbg_reg), .i_dbg_we(i_dbg_we),
				.i_dbg_data(i_dbg_data),
			.o_dbg_stall(uut_dbg_stall), .o_dbg_reg(uut_dbg_reg),
				.o_dbg_cc(uut_dbg_cc),
			.o_break(uut_break),
		// CPU interface to the wishbone bus
		.o_wb_gbl_cyc(uut_gbl_cyc),
			.o_wb_gbl_stb(uut_gbl_stb),
			.o_wb_lcl_cyc(uut_lcl_cyc),
			.o_wb_lcl_stb(uut_lcl_stb),
			.o_wb_we(uut_we), .o_wb_addr(uut_addr),
				.o_wb_data(uut_data), .o_wb_sel(uut_sel),
			.i_wb_stall(i_wb_stall),
			.i_wb_ack(i_wb_ack), .i_wb_data(i_wb_data),
			.i_wb_err(i_wb_err),
		// Accounting/CPU usage interface
		.o_op_stall(uut_op_stall), .o_pf_stall(uut_pf_stall),
		.o_i_count(uut_i_count), .mutsel(8'd`mutidx)
	);

	always @(*)
	begin
		assert (uut_gbl_cyc == o_wb_gbl_cyc);
		assert (uut_gbl_stb == o_wb_gbl_stb);
		assert (uut_lcl_cyc == o_wb_lcl_cyc);
		assert (uut_lcl_stb == o_wb_lcl_stb);

		if (uut_gbl_stb || uut_lcl_stb)
		begin
			assert (uut_we      == o_wb_we);
			assert (uut_addr    == o_wb_addr);
			assert (uut_data    == o_wb_data);
			assert (uut_sel     == o_wb_sel);
		end
	end

/*
	wire	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;

	fwb_master #(.AW(AW), .F_LGDEPTH(F_LGDEPTH)) fwb(i_clk, i_reset,
		o_wb_gbl_cyc|o_wb_lcl_cyc, o_wb_gbl_stb|o_wb_lcl_stb,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
		i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
		f_nreqs, f_nacks, f_outstanding);
*/
	assign	i_wb_ack = (o_wb_gbl_stb|o_wb_lcl_stb) && !i_wb_stall;
endmodule
