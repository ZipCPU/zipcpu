
`default_nettype none
// }}}
module wbdown #(
		// {{{
		parameter	ADDRESS_WIDTH = 28, // Byte address width
		parameter	WIDE_DW = 64,
		parameter	SMALL_DW = 32,
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		// Incoming wide port
		// {{{
		input	wire			i_wcyc, i_wstb, i_wwe,
		input	wire	[ADDRESS_WIDTH-$clog2(WIDE_DW/8)-1:0]	i_waddr,
		input	wire	[WIDE_DW-1:0]	i_wdata,
		input	wire	[WIDE_DW/8-1:0]	i_wsel,
		output	wire			o_wstall,
		output	wire			o_wack,
		output	wire	[WIDE_DW-1:0]	o_wdata,
		output	wire			o_werr,
		// }}}
		// Outgoing, small bus size, port
		// {{{
		output	wire			o_cyc, o_stb, o_we,
		output	wire	[ADDRESS_WIDTH-$clog2(SMALL_DW/8)-1:0]	o_addr,
		output	wire	[SMALL_DW-1:0]	o_data,
		output	wire [SMALL_DW/8-1:0]	o_sel,
		input	wire			i_stall,
		input	wire			i_ack,
		input	wire	[SMALL_DW-1:0]	i_data,
		input	wire			i_err
		// }}}
		// }}}
	);

	generate if (WIDE_DW == SMALL_DW)
	begin : NO_ADJUSTMENT
		// {{{
		assign	o_cyc  = i_wcyc;
		assign	o_stb  = i_wstb;
		assign	o_we   = i_wwe;
		assign	o_addr = i_waddr;
		assign	o_data = i_wdata;
		assign	o_sel  = i_wsel;

		assign	o_wstall = i_stall;
		assign	o_wack   = i_ack;
		assign	o_wdata  = i_data;
		assign	o_werr   = i_err;
		// }}}
	end else begin : DOWNSIZE
		localparam	LGFIFO = 5;
		reg			r_cyc, r_stb, r_we, r_ack, r_err;
		reg	[ADDRESS_WIDTH-$clog2(SMALL_DW/8)-1:0]	r_addr;
		reg	[WIDE_DW-1:0]	s_data, r_data;
		reg	[WIDE_DW/8-1:0]	s_sel;
		reg	[$clog2(WIDE_DW/SMALL_DW):0]	s_count;
		wire			fifo_full, ign_fifo_empty, fifo_ack;
		wire	[LGFIFO:0]	ign_fifo_fill;

		initial	r_cyc = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !i_wcyc ||(o_cyc && i_err) || o_werr)
			r_cyc <= 1'b0;
		else if (i_wcyc && i_wstb)
			r_cyc <= 1'b1;

		initial	r_stb   = 1'b0;
		initial	r_we    = 1'b0;
		initial	r_addr  = 0;
		initial	s_data  = 0;
		initial	s_sel   = 0;
		initial	s_count = 0;
		always @(posedge i_clk)
		if (i_reset || o_werr || (o_cyc && i_err))
		begin
			// {{{
			r_stb   <= 1'b0;
			r_we    <= 1'b0;
			r_addr  <= 0;
			s_data  <= 0;
			s_sel   <= 0;
			s_count <= 0;
			// }}}
		end else if (i_wstb && !o_wstall) // New request
		begin
			// {{{
			r_stb  <= 1'b1;
			r_we   <= i_wwe;
			r_addr <= { i_waddr,
					{($clog2(WIDE_DW/SMALL_DW)){1'b0}} };
			s_data <= i_wdata;
			s_sel  <= i_wsel;
			// Verilator lint_off WIDTH
			s_count <= (WIDE_DW/SMALL_DW);
			// Verilator lint_on  WIDTH
			// }}}
		end else if (o_stb && !i_stall)
		begin
			// {{{
			s_count <=  s_count - 1;
			r_stb   <= (s_count > 1);
			r_addr[$clog2(WIDE_DW/SMALL_DW)-1:0]
				<= r_addr[$clog2(WIDE_DW/SMALL_DW)-1:0] + 1;
			if (OPT_LITTLE_ENDIAN)
			begin
				s_data <= s_data >> SMALL_DW;
				s_sel  <= s_sel >> 1;
			end else begin
				s_data <= s_data << SMALL_DW;
				s_sel  <= s_sel << 1;
			end
			// }}}
		end

		assign	o_cyc = r_cyc;
		assign	o_stb = r_stb && !fifo_full;
		assign	o_we  = r_we;
		assign	o_addr= r_addr;

		if (OPT_LITTLE_ENDIAN)
		begin
			assign	o_data = s_data[SMALL_DW-1:0];
			assign	o_sel  = s_sel[SMALL_DW/8-1:0];
		end else begin
			assign	o_data =s_data[WIDE_DW-1:WIDE_DW-SMALL_DW];
			assign	o_sel  =s_sel[WIDE_DW/8-1:(WIDE_DW-SMALL_DW)/8];
		end

		sfifo #(
			.BW(1), .LGFLEN(LGFIFO)
		) u_fifo (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset || !i_wcyc),
			.i_wr(o_stb && !i_stall),
				.i_data({ (s_count == 1) ? 1'b1 : 1'b0 }),
				.o_full(fifo_full), .o_fill(ign_fifo_fill),
			.i_rd(i_ack), .o_data(fifo_ack),
				.o_empty(ign_fifo_empty)
			// }}}
		);

		initial	r_data = 0;
		always @(posedge i_clk)
		if (OPT_LOWPOWER && (!i_wcyc || !o_cyc || i_err))
			r_data <= 0;
		else if (i_ack)
		begin
			if (OPT_LITTLE_ENDIAN)
				r_data<= { i_data, r_data[WIDE_DW-1:SMALL_DW] };
			else
				r_data<={r_data[WIDE_DW-SMALL_DW-1:0], i_data };
		end

		initial	r_ack = 0;
		always @(posedge i_clk)
			r_ack <= !i_reset && i_wcyc && o_cyc && i_ack
				&& fifo_ack;

		initial	r_err = 0;
		always @(posedge i_clk)
			r_err <= !i_reset && i_wcyc && o_cyc && i_err;

		assign	o_wdata = r_data;
		assign	o_wack  = r_ack;
		assign	o_werr  = r_err;
		assign	o_wstall = (r_stb && (fifo_full || i_stall))
					|| (s_count > 1);

		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, ign_fifo_fill, ign_fifo_empty };
		// Verilator lint_on  UNUSED
	end endgenerate

endmodule
