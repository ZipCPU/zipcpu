////////////////////////////////////////////////////////////////////////////////
//
// Filename:	dcache.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	To provide a simple data cache for the ZipCPU.  The cache is
//		designed to be a drop in replacement for the pipememm memory
//	unit currently existing within the ZipCPU.  The goal of this unit is
//	to achieve single cycle read access to any memory in the last cache line
//	used, or two cycle access to any memory currently in the cache.
//
//	The cache separates between four types of accesses, one write and three
//	read access types.  The read accesses are split between those that are
//	not cacheable, those that are in the cache, and those that are not.
//
//	1. Write accesses always create writes to the bus.  For these reasons,
//		these may always be considered cache misses.
//
//		Writes to memory locations within the cache must also update
//		cache memory immediately, to keep the cache in synch.
//
//		It is our goal to be able to maintain single cycle write
//		accesses for memory bursts.
//
//	2. Read access to non-cacheable memory locations will also immediately
//		go to the bus, just as all write accesses go to the bus.
//
//	3. Read accesses to cacheable memory locations will immediately read
//		from the appropriate cache line.  However, since thee valid
//		line will take a second clock to read, it may take up to two
//		clocks to know if the memory was in cache.  For this reason,
//		we bypass the test for the last validly accessed cache line.
//
//		We shall design these read accesses so that reads to the cache
//		may take place concurrently with other writes to the bus.
//
//	Errors in cache reads will void the entire cache line.  For this reason,
//	cache lines must always be of a smaller in size than any associated
//	virtual page size--lest in the middle of reading a page a TLB miss
//	take place referencing only a part of the cacheable page.
//
//
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016-2019, Gisselquist Technology, LLC
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
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
//
`ifdef	FORMAL
`define	ASSERT	assert

`ifdef DCACHE
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif
`endif

module	dcache(i_clk, i_reset, i_pipe_stb, i_lock,
		i_op, i_addr, i_data, i_oreg,
			o_busy, o_pipe_stalled, o_valid, o_err, o_wreg,o_data,
		o_wb_cyc_gbl, o_wb_cyc_lcl, o_wb_stb_gbl, o_wb_stb_lcl,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
		i_wb_ack, i_wb_stall, i_wb_err, i_wb_data
`ifdef	FORMAL
		, f_nreqs, f_nacks, f_outstanding, f_pc
`endif
	);
	parameter	LGCACHELEN = 8,
			ADDRESS_WIDTH=30,
			LGNLINES=(LGCACHELEN-3), // Log of the number of separate cache lines
			NAUX=5;	// # of aux d-wires to keep aligned w/memops
	parameter [0:0]	OPT_LOCAL_BUS=1'b1;
	parameter [0:0]	OPT_PIPE=1'b1;
	parameter [0:0]	OPT_LOCK=1'b1;
	parameter [0:0]	OPT_DUAL_READ_PORT=1'b1;
	parameter 	OPT_FIFO_DEPTH = 4;
	localparam	AW = ADDRESS_WIDTH; // Just for ease of notation below
	localparam	CS = LGCACHELEN; // Number of bits in a cache address
	localparam	LS = CS-LGNLINES; // Bits to spec position w/in cline
	parameter	F_LGDEPTH=1 + (((!OPT_PIPE)||(LS > OPT_FIFO_DEPTH))
					? LS : OPT_FIFO_DEPTH);
	localparam	LGAUX = 3; // log_2 of the maximum number of piped data
	localparam	DW = 32; // Bus data width
	localparam	DP = OPT_FIFO_DEPTH;
	//
	localparam [1:0]	DC_IDLE  = 2'b00; // Bus is idle
	localparam [1:0]	DC_WRITE = 2'b01; // Write
	localparam [1:0]	DC_READS = 2'b10; // Read a single value(!cachd)
	localparam [1:0]	DC_READC = 2'b11; // Read a whole cache line
	//
	input	wire		i_clk, i_reset;
	// Interface from the CPU
	input	wire		i_pipe_stb, i_lock;
	input	wire [2:0]		i_op;
	input	wire [(DW-1):0]	i_addr;
	input	wire [(DW-1):0]	i_data;
	input	wire [(NAUX-1):0] i_oreg; // Aux data, such as reg to write to
	// Outputs, going back to the CPU
	output	reg		o_busy;
	output	reg		o_pipe_stalled;
	output	reg		o_valid, o_err;
	output reg [(NAUX-1):0]	o_wreg;
	output	reg [(DW-1):0]	o_data;
	// Wishbone bus master outputs
	output	wire		o_wb_cyc_gbl, o_wb_cyc_lcl;
	output	reg		o_wb_stb_gbl, o_wb_stb_lcl;
	output	reg		o_wb_we;
	output	reg [(AW-1):0]	o_wb_addr;
	output	reg [(DW-1):0]	o_wb_data;
	output	wire [(DW/8-1):0] o_wb_sel;
	// Wishbone bus slave response inputs
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;
	input	wire	[(DW-1):0]	i_wb_data;
`ifdef FORMAL
	output	wire [(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;
	output	wire			f_pc;

	reg	f_past_valid;
`endif
	//
	// output	reg	[31:0]		o_debug;


	reg	cyc, stb, last_ack, end_of_line, last_line_stb;
	reg	r_wb_cyc_gbl, r_wb_cyc_lcl;
	// npending is the number of pending non-cached operations, counted
	// from the i_pipe_stb to the o_wb_ack
	reg	[DP:0]	npending;


	reg	[((1<<LGNLINES)-1):0] c_v;	// One bit per cache line, is it valid?
	reg	[(AW-LS-1):0]	c_vtags	[0:((1<<LGNLINES)-1)];
	reg	[(DW-1):0]	c_mem	[0:((1<<CS)-1)];
	reg			set_vflag;
	reg	[1:0]		state;
	reg	[(CS-1):0]	wr_addr;
	reg	[(DW-1):0]	cached_idata, cached_rdata;
	reg	[DW-1:0]	pre_data;
	reg			lock_gbl, lock_lcl;


	// To simplify writing to the cache, and the job of the synthesizer to
	// recognize that a cache write needs to take place, we'll take an extra
	// clock to get there, and use these c_w... registers to capture the
	// data in the meantime.
	reg			c_wr;
	reg	[(DW-1):0]	c_wdata;
	reg	[(DW/8-1):0]	c_wsel;
	reg	[(CS-1):0]	c_waddr;

	reg	[(AW-LS-1):0]	last_tag;
	reg			last_tag_valid;


	wire	[(LGNLINES-1):0]	i_cline;
	wire	[(CS-1):0]	i_caddr;

`ifdef	FORMAL
	reg	[F_LGDEPTH-1:0]	f_fill;
	reg	[AW:0]		f_return_address;
	reg	[AW:0]		f_pending_addr;
`endif

	assign	i_cline = i_addr[(CS+1):LS+2];
	assign	i_caddr = i_addr[(CS+1):2];

	wire	cache_miss_inow, w_cachable;
	assign	cache_miss_inow = (!last_tag_valid)
					||(last_tag != i_addr[(AW+1):LS+2])
					||(!c_v[i_cline]);

	wire	raw_cachable_address;

	iscachable chkaddress(i_addr[AW+1:2], raw_cachable_address);

	assign	w_cachable = ((!OPT_LOCAL_BUS)||(i_addr[(DW-1):(DW-8)]!=8'hff))
		&&((!i_lock)||(!OPT_LOCK))&&(raw_cachable_address);

	reg	r_cachable, r_svalid, r_dvalid, r_rd, r_cache_miss,
		r_rd_pending;
	reg	[(AW-1):0]		r_addr;
	wire	[(LGNLINES-1):0]	r_cline;
	wire	[(CS-1):0]		r_caddr;
	wire	[(AW-LS-1):0]		r_ctag;

	assign	r_cline = r_addr[(CS-1):LS];
	assign	r_caddr = r_addr[(CS-1):0];
	assign	r_ctag  = r_addr[(AW-1):LS];


	reg	wr_cstb, r_iv, in_cache;
	reg	[(AW-LS-1):0]	r_itag;
	reg	[DW/8-1:0]	r_sel;
	reg	[(NAUX+4-1):0]	req_data;
	reg			gie;



	//
	// The one-clock delayed read values from the cache.
	//
	initial	r_rd = 1'b0;
	initial	r_cachable = 1'b0;
	initial	r_svalid = 1'b0;
	initial	r_dvalid = 1'b0;
	initial	r_cache_miss = 1'b0;
	initial	r_addr = 0;
	initial	last_tag_valid = 0;
	initial	r_rd_pending = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_rd <= 1'b0;
		r_cachable <= 1'b0;
		r_svalid <= 1'b0;
		r_dvalid <= 1'b0;
		r_cache_miss <= 1'b0;
		r_addr <= 0;
		r_rd_pending <= 0;
		last_tag_valid <= 0;
	end else begin
		// The single clock path
		// The valid for the single clock path
		//	Only ... we need to wait if we are currently writing
		//	to our cache.
		r_svalid<= (i_pipe_stb)&&(!i_op[0])&&(w_cachable)
				&&(!cache_miss_inow)&&(!c_wr)&&(!wr_cstb);

		//
		// The two clock in-cache path
		//
		// Some preliminaries that needed to be calculated on the first
		// clock
		if ((!o_pipe_stalled)&&(!r_rd_pending))
			r_addr <= i_addr[(AW+1):2];
		if ((!o_pipe_stalled)&&(!r_rd_pending))
		begin
			r_iv   <= c_v[i_cline];
			r_itag <= c_vtags[i_cline];
			r_cachable <= (!i_op[0])&&(w_cachable)&&(i_pipe_stb);
			r_rd_pending <= (i_pipe_stb)&&(!i_op[0])&&(w_cachable)
				&&((cache_miss_inow)||(c_wr)||(wr_cstb));
				// &&((!c_wr)||(!wr_cstb));
		end else begin
			r_iv   <= c_v[r_cline];
			r_itag <= c_vtags[r_cline];
			r_rd_pending <= (r_rd_pending)
				&&((!cyc)||(!i_wb_err))
				&&((r_itag != r_ctag)||(!r_iv));
		end
		r_rd <= (i_pipe_stb)&&(!i_op[0]);
		// r_itag contains the tag we didn't have available to us on the
		// last clock, r_ctag is a bit select from r_addr containing a
		// one clock delayed address.
		r_dvalid <= (!r_svalid)&&(!r_dvalid)&&(r_itag == r_ctag)&&(r_iv)
						&&(r_cachable)&&(r_rd_pending);
		if ((r_itag == r_ctag)&&(r_iv)&&(r_cachable)&&(r_rd_pending))
		begin
			last_tag_valid <= 1'b1;
			last_tag <= r_ctag;
		end else if ((state == DC_READC)
				&&(last_tag[CS-LS-1:0]==o_wb_addr[CS-1:LS])
				&&((i_wb_ack)||(i_wb_err)))
			last_tag_valid <= 1'b0;

		// r_cache miss takes a clock cycle.  It is only ever true for
		// something that should be cachable, but isn't in the cache.
		// A cache miss is only true _if_
		// 1. A read was requested
		// 2. It is for a cachable address, AND
		// 3. It isn't in the cache on the first read
		//	or the second read
		// 4. The read hasn't yet started to get this address
		r_cache_miss <= ((!cyc)||(o_wb_we))&&(r_cachable)
				// One clock path -- miss
				&&(!r_svalid)
				// Two clock path -- misses as well
				&&(r_rd)&&(!r_svalid)
				&&((r_itag != r_ctag)||(!r_iv));
	end

	initial	r_sel = 4'hf;
	always @(posedge i_clk)
	if (i_reset)
		r_sel <= 4'hf;
	else if (!o_pipe_stalled)
	begin
		casez({i_op[2:1], i_addr[1:0]})
		4'b0???: r_sel <= 4'b1111;
		4'b100?: r_sel <= 4'b1100;
		4'b101?: r_sel <= 4'b0011;
		4'b1100: r_sel <= 4'b1000;
		4'b1101: r_sel <= 4'b0100;
		4'b1110: r_sel <= 4'b0010;
		4'b1111: r_sel <= 4'b0001;
		endcase
	end

	assign	o_wb_sel = (state == DC_READC) ? 4'hf : r_sel;

	initial	o_wb_data = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_wb_data <= 0;
	else if ((!o_busy)||((stb)&&(!i_wb_stall)))
	begin
		casez(i_op[2:1])
		2'b0?: o_wb_data <= i_data;
		2'b10: o_wb_data <= { (2){i_data[15:0]} };
		2'b11: o_wb_data <= { (4){i_data[ 7:0]} };
		endcase
	end

	generate if (OPT_PIPE)
	begin : OPT_PIPE_FIFO
		reg	[NAUX+4-2:0]	fifo_data [0:((1<<OPT_FIFO_DEPTH)-1)];

		reg	[DP:0]		wraddr, rdaddr;

		always @(posedge i_clk)
		if (i_pipe_stb)
			fifo_data[wraddr[DP-1:0]]
				<= { i_oreg[NAUX-2:0], i_op[2:1], i_addr[1:0] };

		always @(posedge i_clk)
		if (i_pipe_stb)
			gie <= i_oreg[NAUX-1];

`ifdef	NO_BKRAM
		reg	[NAUX+4-2:0]	r_req_data, r_last_data;
		reg			single_write;

		always @(posedge i_clk)
			r_req_data <= fifo_data[rdaddr[DP-1:0]];

		always @(posedge i_clk)
			single_write <= (rdaddr == wraddr)&&(i_pipe_stb);

		always @(posedge i_clk)
		if (i_pipe_stb)
			r_last_data <= { i_oreg[NAUX-2:0],
						i_op[2:1], i_addr[1:0] };

		always @(*)
		begin
			req_data[NAUX+4-1] = gie;
			// if ((r_svalid)||(state == DC_READ))
			if (single_write)
				req_data[NAUX+4-2:0] = r_last_data;
			else
				req_data[NAUX+4-2:0] = r_req_data;
		end

		always @(*)
			`ASSERT(req_data == fifo_data[rdaddr[DP-1:0]]);
`else
		always @(*)
			req_data[NAUX+4-2:0] = fifo_data[rdaddr[DP-1:0]];
		always @(*)
			req_data[NAUX+4-1] = gie;
`endif

		initial	wraddr = 0;
		always @(posedge i_clk)
		if ((i_reset)||((cyc)&&(i_wb_err)))
			wraddr <= 0;
		else if (i_pipe_stb)
			wraddr <= wraddr + 1'b1;

		initial	rdaddr = 0;
		always @(posedge i_clk)
		if ((i_reset)||((cyc)&&(i_wb_err)))
			rdaddr <= 0;
		else if ((r_dvalid)||(r_svalid))
			rdaddr <= rdaddr + 1'b1;
		else if ((state == DC_WRITE)&&(i_wb_ack))
			rdaddr <= rdaddr + 1'b1;
		else if ((state == DC_READS)&&(i_wb_ack))
			rdaddr <= rdaddr + 1'b1;

`ifdef	FORMAL
		reg	[AW-1:0]	f_fifo_addr [0:((1<<OPT_FIFO_DEPTH)-1)];
		reg	[F_LGDEPTH-1:0]	f_last_wraddr;
		reg	f_pc_pending;

		always @(*)
		begin
			f_fill = 0;
			f_fill[DP:0] = wraddr - rdaddr;
		end

		always @(*)
			`ASSERT(f_fill <= { 1'b1, {(DP){1'b0}} });

		always @(*)
		if ((r_dvalid)||(r_svalid))
		begin
			if (r_svalid)
				`ASSERT(f_fill == 1);
			else if (r_dvalid)
				`ASSERT(f_fill == 1);
			else
				`ASSERT(f_fill == 0);
		end else if (r_rd_pending)
			`ASSERT(f_fill == 1);
		else
			`ASSERT(f_fill == npending);


		initial	f_pc_pending = 0;
		always @(posedge i_clk)
		if (i_reset)
			f_pc_pending <= 1'b0;
		else if (i_pipe_stb)
			f_pc_pending <= (!i_op[0])&&(i_oreg[3:1] == 3'h7);
		else if (f_fill == 0)
			f_pc_pending <= 1'b0;
		//else if ((o_valid)&&(o_wreg[3:1] == 3'h7)&&(f_fill == 0))
		//	f_pc_pending <= 1'b0;

		always @(posedge i_clk)
		if (f_pc_pending)
			`ASSUME(!i_pipe_stb);

		always @(posedge i_clk)
		if (state == DC_WRITE)
			`ASSERT(!f_pc_pending);

		always @(*)
		begin
			f_last_wraddr = 0;
			f_last_wraddr[DP:0] = wraddr - 1'b1;
		end

		always @(posedge i_clk)
		if (r_rd_pending)
			`ASSERT(f_pc_pending == (fifo_data[f_last_wraddr][7:5] == 3'h7));

`define	INSPECT_FIFO
		reg	[((1<<(DP+1))-1):0]	f_valid_fifo_entry;

		genvar	k;
		for(k=0; k<(1<<(DP+1)); k=k+1)
		begin

			always @(*)
			begin
			f_valid_fifo_entry[k] = 1'b0;
			/*
			if ((rdaddr[DP] != wraddr[DP])
					&&(rdaddr[DP-1:0] == wraddr[DP-1:0]))
				f_valid_fifo_entry[k] = 1'b1;
			else */
			if ((rdaddr < wraddr)&&(k < wraddr)
					&&(k >= rdaddr))
				f_valid_fifo_entry[k] = 1'b1;
			else if ((rdaddr > wraddr)&&(k >= rdaddr))
				f_valid_fifo_entry[k] = 1'b1;
			else if ((rdaddr > wraddr)&&(k <  wraddr))
				f_valid_fifo_entry[k] = 1'b1;
			end

`ifdef	INSPECT_FIFO
			wire	[NAUX+4-2:0]	fifo_data_k;

			assign	fifo_data_k = fifo_data[k[DP-1:0]];
			always @(*)
			if (f_valid_fifo_entry[k])
			begin
				if (!f_pc_pending)
					`ASSERT((o_wb_we)||(fifo_data_k[7:5] != 3'h7));
				else if (k != f_last_wraddr)
					`ASSERT(fifo_data_k[7:5] != 3'h7);
			end
`endif // INSPECT_FIFO

		end

`ifndef	INSPECT_FIFO
		always @(posedge i_clk)
		if ((r_rd_pending)&&(rdaddr[DP:0] != f_last_wraddr[DP-1]))
			assume(fifo_data[rdaddr][7:5] != 3'h7);
`endif // INSPECT_FIFO

		assign	f_pc = f_pc_pending;

		//
		//
		//
		always @(*)
			f_pending_addr = f_fifo_addr[rdaddr];

		//
		//
		//
		always @(posedge i_clk)
		if (i_pipe_stb)
			f_fifo_addr[wraddr[DP-1:0]] <= i_addr[AW+1:2];

		always @(*)
		begin
			f_return_address[AW] = (o_wb_cyc_lcl);
			f_return_address[AW-1:0] = f_fifo_addr[rdaddr];
			if (state == DC_READC)
				f_return_address[LS-1:0]
				= (o_wb_addr[LS-1:0] - f_outstanding[LS-1:0]);
		end

`define	TWIN_WRITE_TEST
`ifdef	TWIN_WRITE_TEST
		(* anyconst *)	reg	[DP:0]		f_twin_base;
				reg	[DP:0]		f_twin_next;
		(* anyconst *)	reg	[AW+NAUX+4-2-1:0]	f_twin_first,
							f_twin_second;
		// reg	[AW-1:0]	f_fifo_addr [0:((1<<OPT_FIFO_DEPTH)-1)];
		// reg	[NAUX+4-2:0]	fifo_data [0:((1<<OPT_FIFO_DEPTH)-1)];

		always @(*)	f_twin_next = f_twin_base+1;

		reg	f_twin_none, f_twin_single, f_twin_double, f_twin_last;
		reg	f_twin_valid_one, f_twin_valid_two;
		always @(*)
		begin
			f_twin_valid_one = ((f_valid_fifo_entry[f_twin_base])
				&&(f_twin_first == { f_fifo_addr[f_twin_base],
						fifo_data[f_twin_base] }));
			f_twin_valid_two = ((f_valid_fifo_entry[f_twin_next])
				&&(f_twin_second == { f_fifo_addr[f_twin_next],
						fifo_data[f_twin_next] }));
		end

		always @(*)
		begin
			f_twin_none   =(!f_twin_valid_one)&&(!f_twin_valid_two);
			f_twin_single =( f_twin_valid_one)&&(!f_twin_valid_two);
			f_twin_double =( f_twin_valid_one)&&( f_twin_valid_two);
			f_twin_last   =(!f_twin_valid_one)&&( f_twin_valid_two);
		end

		always @(posedge i_clk)
		if ((!f_past_valid)||($past(i_reset))||($past(cyc && i_wb_err)))
			`ASSERT(f_twin_none);
		else if ($past(f_twin_none))
			`ASSERT(f_twin_none || f_twin_single || f_twin_last);
		else if ($past(f_twin_single))
			`ASSERT(f_twin_none || f_twin_single || f_twin_double || f_twin_last);
		else if ($past(f_twin_double))
			`ASSERT(f_twin_double || f_twin_last);
		else if ($past(f_twin_last))
			`ASSERT(f_twin_none || f_twin_single || f_twin_last);

`endif // TWIN_WRITE_TEST

		always @(*)
			`ASSERT(req_data == { gie, fifo_data[rdaddr[DP-1:0]] });

		always @(posedge i_clk)
		if (r_svalid||r_dvalid || r_rd_pending)
			`ASSERT(f_fill == 1);
		else if (f_fill > 0)
			`ASSERT(cyc);

		always @(posedge i_clk)
		if (state != 0)
			`ASSERT(f_fill > 0);
		else if (!r_svalid && !r_dvalid && !r_rd_pending)
			`ASSERT(f_fill == 0);

`endif // FORMAL

		always @(posedge i_clk)
			o_wreg <= req_data[(NAUX+4-1):4];

		/*
		reg	fifo_err;
		always @(posedge i_clk)
		begin
			fifo_err <= 1'b0;
			if ((!o_busy)&&(rdaddr != wraddr))
				fifo_err <= 1'b1;
			if ((!r_dvalid)&&(!r_svalid)&&(!r_rd_pending))
				fifo_err <= (npending != (wraddr-rdaddr));
		end

		always @(*)
		o_debug = { i_pipe_stb, state, cyc, stb,	//  5b
				fifo_err, i_oreg[3:0], o_wreg, 		// 10b
				rdaddr, wraddr, 		// 10b
				i_wb_ack, i_wb_err, o_pipe_stalled, o_busy,//4b
				r_svalid, r_dvalid, r_rd_pending };
		*/
	end else begin : NO_FIFO

		always @(posedge i_clk)
		if (i_pipe_stb)
			req_data <= { i_oreg, i_op[2:1], i_addr[1:0] };

		always @(*)
			o_wreg = req_data[(NAUX+4-1):4];

		always @(*)
			gie = i_oreg[NAUX-1];

`ifdef	FORMAL
		assign	f_pc = ((r_rd_pending)||(o_valid))&&(o_wreg[3:1] == 3'h7);

		//
		//
		//
		initial	f_pending_addr = 0;
		always @(posedge i_clk)
		if (i_reset)
			f_pending_addr <= 0;
		else if (i_pipe_stb)
		begin
			f_pending_addr <= { (OPT_LOCAL_BUS)&&(&i_addr[DW-1:DW-8]),
						i_addr[(AW+1):2] };
		end

		//
		//
		always @(*)
		begin
			f_return_address[AW]      = o_wb_cyc_lcl;
			f_return_address[AW-1:LS] = o_wb_addr[AW-1:LS];
		end
		always @(*)
		if (state == DC_READS)
			f_return_address[LS-1:0] = o_wb_addr[LS-1:0];
		else
			f_return_address[LS-1:0]
				= (o_wb_addr[LS-1:0] - f_outstanding[LS-1:0]);

`endif
		/*
		always @(*)
		o_debug = { i_pipe_stb, state, cyc, stb,	//  5b
				i_oreg, o_wreg, 		// 10b
				10'hb,		 		// 10b
				i_wb_ack, i_wb_err, o_pipe_stalled, o_busy,//4b
				r_svalid, r_dvalid, r_rd_pending };
		*/

		// verilator lint_off UNUSED
		wire	unused_no_fifo;
		assign	unused_no_fifo = gie;
		// verilator lint_on  UNUSED
	end endgenerate


	initial	r_wb_cyc_gbl = 0;
	initial	r_wb_cyc_lcl = 0;
	initial	o_wb_stb_gbl = 0;
	initial	o_wb_stb_lcl = 0;
	initial	c_v = 0;
	initial	cyc = 0;
	initial	stb = 0;
	initial	c_wr = 0;
	initial	wr_cstb = 0;
	initial	state = DC_IDLE;
	initial	set_vflag = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		c_v <= 0;
		c_wr   <= 1'b0;
		c_wsel <= 4'hf;
		r_wb_cyc_gbl <= 1'b0;
		r_wb_cyc_lcl <= 1'b0;
		o_wb_stb_gbl <= 0;
		o_wb_stb_lcl <= 0;
		wr_cstb <= 1'b0;
		last_line_stb <= 1'b0;
		end_of_line <= 1'b0;
		state <= DC_IDLE;
		cyc <= 1'b0;
		stb <= 1'b0;
		state <= DC_IDLE;
		set_vflag <= 1'b0;
	end else begin
		// By default, update the cache from the write 1-clock ago
		// c_wr <= (wr_cstb)&&(wr_wtag == wr_vtag);
		// c_waddr <= wr_addr[(CS-1):0];
		c_wr <= 0;

		set_vflag <= 1'b0;
		if ((!cyc)&&(set_vflag))
			c_v[c_waddr[(CS-1):LS]] <= 1'b1;

		wr_cstb <= 1'b0;

		if (!cyc)
			wr_addr <= r_addr[(CS-1):0];
		else if (i_wb_ack)
			wr_addr <= wr_addr + 1'b1;
		else
			wr_addr <= wr_addr;

		if (LS <= 0)
			end_of_line <= 1'b1;
		else if (!cyc)
			end_of_line <= 1'b0;
		else if (!end_of_line)
		begin
			if (i_wb_ack)
				end_of_line
				<= (c_waddr[(LS-1):0] == {{(LS-2){1'b1}},2'b01});
			else
				end_of_line
				<= (c_waddr[(LS-1):0]=={{(LS-1){1'b1}}, 1'b0});
		end

		if (!cyc)
			last_line_stb <= (LS <= 0);
		else if ((stb)&&(!i_wb_stall)&&(LS <= 1))
			last_line_stb <= 1'b1;
		else if ((stb)&&(!i_wb_stall))
			last_line_stb <= (o_wb_addr[(LS-1):1]=={(LS-1){1'b1}});
		else if (stb)
			last_line_stb <= (o_wb_addr[(LS-1):0]=={(LS){1'b1}});

		//
		//
		if (state == DC_IDLE)
		begin
			o_wb_we <= 1'b0;

			cyc <= 1'b0;
			stb <= 1'b0;

			r_wb_cyc_gbl <= 1'b0;
			r_wb_cyc_lcl <= 1'b0;
			o_wb_stb_gbl <= 1'b0;
			o_wb_stb_lcl <= 1'b0;

			in_cache <= (i_op[0])&&(w_cachable);
			if ((i_pipe_stb)&&(i_op[0]))
			begin // Write  operation
				state <= DC_WRITE;
				o_wb_addr <= i_addr[(AW+1):2];
				o_wb_we <= 1'b1;

				cyc <= 1'b1;
				stb <= 1'b1;

				if (OPT_LOCAL_BUS)
				begin
				r_wb_cyc_gbl <= (i_addr[DW-1:DW-8]!=8'hff);
				r_wb_cyc_lcl <= (i_addr[DW-1:DW-8]==8'hff);
				o_wb_stb_gbl <= (i_addr[DW-1:DW-8]!=8'hff);
				o_wb_stb_lcl <= (i_addr[DW-1:DW-8]==8'hff);
				end else begin
					r_wb_cyc_gbl <= 1'b1;
					o_wb_stb_gbl <= 1'b1;
				end

			end else if (r_cache_miss)
			begin
				state <= DC_READC;
				o_wb_addr <= { r_ctag, {(LS){1'b0}} };

				c_waddr <= { r_ctag[CS-LS-1:0], {(LS){1'b0}} }-1'b1;
				cyc <= 1'b1;
				stb <= 1'b1;
				r_wb_cyc_gbl <= 1'b1;
				o_wb_stb_gbl <= 1'b1;
				wr_addr[LS-1:0] <= 0;
			end else if ((i_pipe_stb)&&(!w_cachable))
			begin // Read non-cachable memory area
				state <= DC_READS;
				o_wb_addr <= i_addr[(AW+1):2];

				cyc <= 1'b1;
				stb <= 1'b1;
				if (OPT_LOCAL_BUS)
				begin
				r_wb_cyc_gbl <= (i_addr[DW-1:DW-8]!=8'hff);
				r_wb_cyc_lcl <= (i_addr[DW-1:DW-8]==8'hff);
				o_wb_stb_gbl <= (i_addr[DW-1:DW-8]!=8'hff);
				o_wb_stb_lcl <= (i_addr[DW-1:DW-8]==8'hff);
				end else begin
				r_wb_cyc_gbl <= 1'b1;
				o_wb_stb_gbl <= 1'b1;
				end
			end // else we stay idle

		end else if (state == DC_READC)
		begin
			// We enter here once we have committed to reading
			// data into a cache line.
			if ((stb)&&(!i_wb_stall))
			begin
				stb <= (!last_line_stb);
				o_wb_stb_gbl <= (!last_line_stb);
				o_wb_addr[(LS-1):0] <= o_wb_addr[(LS-1):0]+1'b1;
			end

			if ((i_wb_ack)&&(!end_of_line))
				c_v[o_wb_addr[(CS-1):LS]] <= 1'b0;

			c_wr    <= (i_wb_ack);
			c_wdata <= i_wb_data;
			c_waddr <= ((i_wb_ack)?(c_waddr+1'b1):c_waddr);
			c_wsel  <= 4'hf;

			set_vflag <= !i_wb_err;
			if (i_wb_ack)
				c_vtags[r_addr[(CS-1):LS]]
						<= r_addr[(AW-1):LS];

			if (((i_wb_ack)&&(end_of_line))||(i_wb_err))
			begin
				state          <= DC_IDLE;
				cyc <= 1'b0;
				stb <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
				//
			end
		end else if (state == DC_READS)
		begin
			// We enter here once we have committed to reading
			// data that cannot go into a cache line
			if ((!i_wb_stall)&&(!i_pipe_stb))
			begin
				stb <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
			end

			if ((!i_wb_stall)&&(i_pipe_stb))
				o_wb_addr <= i_addr[(AW+1):2];

			c_wr <= 1'b0;

			if (((i_wb_ack)&&(last_ack))||(i_wb_err))
			begin
				state        <= DC_IDLE;
				cyc          <= 1'b0;
				stb          <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
			end
		end else if (state == DC_WRITE)
		begin
			c_wr    <= (stb)&&(c_v[o_wb_addr[CS-1:LS]])
				&&(c_vtags[o_wb_addr[CS-1:LS]]==o_wb_addr[AW-1:LS])
				&&(stb);
			c_wdata <= o_wb_data;
			c_waddr <= r_addr[CS-1:0];
			c_wsel  <= o_wb_sel;

			if ((!i_wb_stall)&&(!i_pipe_stb))
			begin
				stb          <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
			end

			wr_cstb  <= (stb)&&(!i_wb_stall)&&(in_cache);

			if ((stb)&&(!i_wb_stall))
				o_wb_addr <= i_addr[(AW+1):2];

			if (((i_wb_ack)&&(last_ack)
						&&((!OPT_PIPE)||(!i_pipe_stb)))
				||(i_wb_err))
			begin
				state        <= DC_IDLE;
				cyc          <= 1'b0;
				stb          <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
			end
		end
	end

	//
	// npending is the number of outstanding (non-cached) read or write
	// requests
	initial	npending = 0;
	always @(posedge i_clk)
	if ((i_reset)||(!OPT_PIPE)
			||((cyc)&&(i_wb_err))
			||((!cyc)&&(!i_pipe_stb))
			||(state == DC_READC))
		npending <= 0;
	else if (r_svalid)
		npending <= (i_pipe_stb) ? 1:0;
	else case({ (i_pipe_stb), (cyc)&&(i_wb_ack) })
	2'b01: npending <= npending - 1'b1;
	2'b10: npending <= npending + 1'b1;
	default: begin end
	endcase

	initial	last_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_ack <= 1'b0;
	else if (state == DC_IDLE)
	begin
		last_ack <= 1'b0;
		if ((i_pipe_stb)&&(i_op[0]))
			last_ack <= 1'b1;
		else if (r_cache_miss)
			last_ack <= (LS == 0);
		else if ((i_pipe_stb)&&(!w_cachable))
			last_ack <= 1'b1;
	end else if (state == DC_READC)
	begin
		if (i_wb_ack)
			last_ack <= last_ack || (&wr_addr[LS-1:1]);
		else
			last_ack <= last_ack || (&wr_addr[LS-1:0]);
	end else case({ (i_pipe_stb), (i_wb_ack) })
	2'b01: last_ack <= (npending <= 2);
	2'b10: last_ack <= (!cyc)||(npending == 0);
	default: begin end
	endcase

`ifdef	FORMAL
always @(*)
`ASSERT(npending <= { 1'b1, {(DP){1'b0}} });

`endif


	//
	// Writes to the cache
	//
	// These have been made as simple as possible.  Note that the c_wr
	// line has already been determined, as have the write value and address
	// on the last clock.  Further, this structure is defined to match the
	// block RAM design of as many architectures as possible.
	//
	always @(posedge i_clk)
	if (c_wr)
	begin
		if (c_wsel[0])
			c_mem[c_waddr][7:0] <= c_wdata[7:0];
		if (c_wsel[1])
			c_mem[c_waddr][15:8] <= c_wdata[15:8];
		if (c_wsel[2])
			c_mem[c_waddr][23:16] <= c_wdata[23:16];
		if (c_wsel[3])
			c_mem[c_waddr][31:24] <= c_wdata[31:24];
	end

	//
	// Reads from the cache
	//
	// Some architectures require that all reads be registered.  We
	// accomplish that here.  Whether or not the result of this read is
	// going to be our output will need to be determined with combinatorial
	// logic on the output.
	//
	generate if (OPT_DUAL_READ_PORT)
	begin

		always @(posedge i_clk)
			cached_idata <= c_mem[i_caddr];

		always @(posedge i_clk)
			cached_rdata <= c_mem[r_caddr];

	end else begin

		always @(posedge i_clk)
			cached_rdata <= c_mem[(o_busy) ? r_caddr : i_caddr];

		always @(*)
			cached_idata = cached_rdata;

	end endgenerate

// o_data can come from one of three places:
// 1. The cache, assuming the data was in the last cache line
// 2. The cache, second clock, assuming the data was in the cache at all
// 3. The cache, after filling the cache
// 4. The wishbone state machine, upon reading the value desired.
	always @(*)
		if (r_svalid)
			pre_data = cached_idata;
		else if (state == DC_READS)
			pre_data = i_wb_data;
		else
			pre_data = cached_rdata;

	always @(posedge i_clk)
	casez(req_data[3:0])
	4'b100?: o_data <= { 16'h0, pre_data[31:16] };
	4'b101?: o_data <= { 16'h0, pre_data[15: 0] };
	4'b1100: o_data <= { 24'h0, pre_data[31:24] };
	4'b1101: o_data <= { 24'h0, pre_data[23:16] };
	4'b1110: o_data <= { 24'h0, pre_data[15: 8] };
	4'b1111: o_data <= { 24'h0, pre_data[ 7: 0] };
	default	o_data <= pre_data;
	endcase

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_valid <= 1'b0;
	else if (state == DC_READS)
		o_valid <= i_wb_ack;
	else
		o_valid <= (r_svalid)||(r_dvalid);

	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_err <= 1'b0;
	else
		o_err <= (cyc)&&(i_wb_err);

	initial	o_busy = 0;
	always @(posedge i_clk)
	if ((i_reset)||((cyc)&&(i_wb_err)))
		o_busy <= 1'b0;
	else if (i_pipe_stb)
		o_busy <= 1'b1;
	else if ((state == DC_READS)&&(i_wb_ack))
		o_busy <= 1'b0;
	else if ((r_rd_pending)&&(!r_dvalid))
		o_busy <= 1'b1;
	else if ((state == DC_WRITE)
			&&(i_wb_ack)&&(last_ack)&&(!i_pipe_stb))
		o_busy <= 1'b0;
	else if (cyc)
		o_busy <= 1'b1;
	else // if ((r_dvalid)||(r_svalid))
		o_busy <= 1'b0;

	//
	// We can use our FIFO addresses to pre-calculate when an ACK is going
	// to be the last_noncachable_ack.


	always @(*)
	if (OPT_PIPE)
		o_pipe_stalled = (cyc)&&((!o_wb_we)||(i_wb_stall)||(!stb))
				||(r_rd_pending)||(npending[DP]);
	else
		o_pipe_stalled = o_busy;

	initial	lock_gbl = 0;
	initial	lock_lcl = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		lock_gbl <= 1'b0;
		lock_lcl<= 1'b0;
	end else begin
		lock_gbl <= (OPT_LOCK)&&(i_lock)&&((r_wb_cyc_gbl)||(lock_gbl));
		lock_lcl <= (OPT_LOCK)&&(i_lock)&&((r_wb_cyc_lcl)||(lock_lcl));
	end

	assign	o_wb_cyc_gbl = (r_wb_cyc_gbl)||(lock_gbl);
	assign	o_wb_cyc_lcl = (r_wb_cyc_lcl)||(lock_lcl);

	generate if (AW+2 < DW)
	begin : UNUSED_BITS

		// Verilator lint_off UNUSED
		wire	[DW-AW-2:0]	unused;
		assign	unused = i_addr[DW-1:AW+1];
		// Verilator lint_on  UNUSED
	end endgenerate

`ifdef	FORMAL

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////
	//
	// Reset properties
	//
	////////////////////////////////////////////////
	//
	//
	always @(*)
	if(!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		// Insist on initial statements matching reset values
		`ASSERT(r_rd == 1'b0);
		`ASSERT(r_cachable == 1'b0);
		`ASSERT(r_svalid == 1'b0);
		`ASSERT(r_dvalid == 1'b0);
		`ASSERT(r_cache_miss == 1'b0);
		`ASSERT(r_addr == 0);
		//
		`ASSERT(c_wr == 0);
		`ASSERT(c_v  == 0);
		//
		// assert(aux_head == 0);
		// assert(aux_tail == 0);
		//
		`ASSERT(lock_gbl == 0);
		`ASSERT(lock_lcl == 0);
	end

	////////////////////////////////////////////////
	//
	// Assumptions about our inputs
	//
	////////////////////////////////////////////////
	//
	//
	always @(*)
	if (o_pipe_stalled)
		`ASSUME(!i_pipe_stb);

	always @(*)
	if (!f_past_valid)
		`ASSUME(!i_pipe_stb);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
		&&($past(i_pipe_stb))&&($past(o_pipe_stalled)))
	begin
		`ASSUME($stable(i_pipe_stb));
		`ASSUME($stable(i_op[0]));
		`ASSUME($stable(i_addr));
		if (i_op[0])
			`ASSUME($stable(i_data));
	end

	always @(posedge i_clk)
	if (o_err)
		`ASSUME(!i_pipe_stb);

	////////////////////////////////////////////////
	//
	// Wishbone properties
	//
	////////////////////////////////////////////////
	//
	//
	wire	f_cyc, f_stb;

	assign	f_cyc = (o_wb_cyc_gbl)|(o_wb_cyc_lcl);
	assign	f_stb = (o_wb_stb_gbl)|(o_wb_stb_lcl);

	always @(*)
	begin
		// Only one interface can be active at once
		`ASSERT((!o_wb_cyc_gbl)||(!o_wb_cyc_lcl));
		// Strobe may only be active on the active interface
		`ASSERT((r_wb_cyc_gbl)||(!o_wb_stb_gbl));
		`ASSERT((r_wb_cyc_lcl)||(!o_wb_stb_lcl));
		if (o_wb_stb_lcl)
		begin
			if (o_wb_we)
				assert(state == DC_WRITE);
			else
				assert(state == DC_READS);
		end

		if (cyc)
			assert(o_wb_we == (state == DC_WRITE));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(cyc)&&($past(cyc)))
	begin
		`ASSERT($stable(r_wb_cyc_gbl));
		`ASSERT($stable(r_wb_cyc_lcl));
	end


`ifdef	DCACHE
`define	FWB_MASTER	fwb_master
`else
`define	FWB_MASTER	fwb_counter
`endif

	`FWB_MASTER #(
		.AW(AW), .DW(DW),
			.F_MAX_STALL(2),
			.F_MAX_ACK_DELAY(3),
			// If you need the proof to run faster, use these
			// lines instead of the two that follow
			// .F_MAX_STALL(1),
			// .F_MAX_ACK_DELAY(1),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS((OPT_PIPE) ? 0 : (1<<LS)),
`ifdef	DCACHE
			.F_OPT_SOURCE(1'b1),
`endif
			.F_OPT_DISCONTINUOUS(0)
		) fwb(i_clk, i_reset,
			cyc, f_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
		f_nreqs, f_nacks, f_outstanding);

`ifdef	DCACHE	// Arbitrary access is specific to local dcache implementation
	////////////////////////////////////////////////
	//
	// Arbitrary address properties
	//
	////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[AW:0]		f_const_addr;
	(* anyconst *)	reg			f_const_buserr;
	wire	[AW-LS-1:0]	f_const_tag, f_ctag_here, f_wb_tag;
	wire	[CS-LS-1:0]	f_const_tag_addr;
	reg	[DW-1:0]	f_const_data;
	wire	[DW-1:0]	f_cmem_here;
	reg			f_pending_rd;
	wire			f_cval_in_cache;

	assign	f_const_tag    = f_const_addr[AW-1:LS];
	assign	f_const_tag_addr = f_const_addr[CS-1:LS];
	assign	f_cmem_here    = c_mem[f_const_addr[CS-1:0]];
	assign	f_ctag_here    = c_vtags[f_const_addr[CS-1:LS]];
	assign	f_wb_tag       = o_wb_addr[AW-1:LS];

	assign	f_cval_in_cache= (c_v[f_const_addr[CS-1:LS]])
					&&(f_ctag_here == f_const_tag);

	generate if ((AW > DW - 8)&&(OPT_LOCAL_BUS))
	begin : UPPER_CONST_ADDR_BITS

		always @(*)
		if (f_const_addr[AW])
			assume(&f_const_addr[(AW-1):(DW-8)]);
		else
			assume(!(&f_const_addr[(AW-1):(DW-8)]));
	end endgenerate

	wire	[AW-1:0]	wb_start;
	assign	wb_start = (f_stb) ? (o_wb_addr - f_nreqs) : o_wb_addr;

	// Data changes upon request
	always @(posedge i_clk)
	begin
		if ((i_pipe_stb)&&(i_addr[(AW+1):2] == f_const_addr[AW-1:0])
			&&(f_const_addr[AW] == ((OPT_LOCAL_BUS)
						&&(&i_addr[(DW-1):(DW-8)])))
			&&(i_op[0]))
		begin
			casez({ i_op[2:1], i_addr[1:0] })
			4'b0???: f_const_data <= i_data;
			4'b100?: f_const_data[31:16] <= i_data[15:0];
			4'b101?: f_const_data[15: 0] <= i_data[15:0];
			4'b1100: f_const_data[31:24] <= i_data[ 7:0];
			4'b1101: f_const_data[23:16] <= i_data[ 7:0];
			4'b1110: f_const_data[15: 8] <= i_data[ 7:0];
			4'b1111: f_const_data[ 7: 0] <= i_data[ 7:0];
			endcase
		end

		if (f_cval_in_cache)
			assume((!i_wb_err)
				||(!i_pipe_stb)
				||(f_const_addr[AW-1:0] != i_addr[AW+1:2]));
	end


	always @(posedge i_clk)
	if ((f_past_valid)&&(!i_reset)&&(!f_const_buserr))
	begin
		if ((cyc)&&(o_wb_we)&&(f_stb)
				&&(o_wb_addr[AW-1:0] == f_const_addr[AW-1:0])
				&&( o_wb_stb_lcl == f_const_addr[AW]))
		begin

			//
			// Changing our data
			//
			if (o_wb_sel[0])
				`ASSERT(o_wb_data[ 7: 0]==f_const_data[ 7: 0]);
			if (o_wb_sel[1])
				`ASSERT(o_wb_data[15: 8]==f_const_data[15: 8]);
			if (o_wb_sel[2])
				`ASSERT(o_wb_data[23:16]==f_const_data[23:16]);
			if (o_wb_sel[3])
				`ASSERT(o_wb_data[31:24]==f_const_data[31:24]);

			// Check the data in the cache
			if ((!f_const_addr[AW])&&(c_v[f_const_tag_addr])
				&&(f_ctag_here == o_wb_addr[AW-1:LS]))
			begin
			if ((!c_wsel[0])&&(!o_wb_sel[0]))
				`ASSERT(f_cmem_here[ 7: 0]==f_const_data[ 7: 0]);
			if ((!c_wsel[1])&&(!o_wb_sel[1]))
				`ASSERT(f_cmem_here[15: 8]==f_const_data[15: 8]);
			if ((!c_wsel[2])&&(!o_wb_sel[2]))
				`ASSERT(f_cmem_here[23:16]==f_const_data[23:16]);
			if ((!c_wsel[3])&&(!o_wb_sel[3]))
				`ASSERT(f_cmem_here[31:24]==f_const_data[31:24]);

			end
		end else if ((!f_const_addr[AW])&&(c_v[f_const_tag_addr])
			&&(f_ctag_here ==f_const_addr[AW-1:LS]))
		begin
			// If ...
			//   1. Our magic address is cachable
			//   2. Our magic address is associated with a valid
			//		cache line
			//   3. The cache tag matches our magic address


			// if ($past(cyc && i_wb_err))
			// begin
				// Ignore what happens on an error, the result
				// becomes undefined anyway
			// end else
			if ((c_wr)
				&&(c_waddr[CS-1:0] == f_const_addr[CS-1:0]))
			begin
				//
				// If we are writing to this valid cache line
				//
				if (c_wsel[3])
					`ASSERT(c_wdata[31:24]
							== f_const_data[31:24]);
				else
					`ASSERT(f_cmem_here[31:24]
							== f_const_data[31:24]);
				if (c_wsel[2])
					`ASSERT(c_wdata[23:16]
							== f_const_data[23:16]);
				else
					`ASSERT(f_cmem_here[23:16] == f_const_data[23:16]);
				if (c_wsel[1])
					`ASSERT(c_wdata[15:8]
							== f_const_data[15:8]);
				else
					`ASSERT(f_cmem_here[15:8] == f_const_data[15:8]);
				if (c_wsel[0])
					`ASSERT(c_wdata[7:0]
							== f_const_data[7:0]);
				else
					`ASSERT(f_cmem_here[7:0] == f_const_data[7:0]);
			end else
				`ASSERT(f_cmem_here == f_const_data);
		end
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(state == DC_READC))
	begin
		`ASSERT(f_wb_tag == r_ctag);
		if ((wb_start[AW-1:LS] == f_const_tag)
			&&(!c_v[f_const_tag_addr])
			&&(f_const_addr[AW] == r_wb_cyc_lcl)
			&&(f_nacks > f_const_addr[LS-1:0]))
		begin
			// We are reading the cache line containing our
			// constant address f_const_addr.  Make sure the data
			// is correct.
			if ((c_wr)&&(c_waddr[CS-1:0] == f_const_addr[CS-1:0]))
				`ASSERT(c_wdata == f_const_data);
			else
				`ASSERT(f_cmem_here == f_const_data);
		end

		if (f_nacks > 0)
			`ASSERT(!c_v[wb_start[CS-1:LS]]);
	end

	always @(posedge i_clk)
	if ((state == DC_READC)&&(f_nacks > 0))
	begin
		`ASSERT(c_vtags[wb_start[(CS-1):LS]] <= wb_start[(AW-1):LS]);
		`ASSERT(c_vtags[wb_start[(CS-1):LS]] <= r_addr[AW-1:LS]);
	end

	reg	[AW-1:0]	f_cache_waddr;
	wire			f_this_cache_waddr;

	always @(*)
	begin
		// f_cache_waddr[AW-1:LS] = c_vtags[c_waddr[CS-1:CS-LS]];
		f_cache_waddr[AW-1:LS] = wb_start[AW-1:LS];
		f_cache_waddr[CS-1: 0] = c_waddr[CS-1:0];
	end

	assign	f_this_cache_waddr = (!f_const_addr[AW])
				&&(f_cache_waddr == f_const_addr[AW-1:0]);
	always @(posedge i_clk)
	if ((f_past_valid)&&(state == DC_READC))
	begin
		if ((c_wr)&&(c_waddr[LS-1:0] != 0)&&(f_this_cache_waddr))
			`ASSERT(c_wdata == f_const_data);
	end

	always @(posedge i_clk)
	if ((OPT_PIPE)&&(o_busy)&&(i_pipe_stb))
	begin
		`ASSUME(i_op[0] == o_wb_we);
		if (o_wb_cyc_lcl)
			assume(&i_addr[DW-1:DW-8]);
		else
			assume(!(&i_addr[DW-1:DW-8]));
	end

	initial	f_pending_rd = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_pending_rd <= 0;
	else if (i_pipe_stb)
		f_pending_rd <= (!i_op[0]);
	else if ((o_valid)&&((!OPT_PIPE)
		||((state != DC_READS)&&(!r_svalid)&&(!$past(i_pipe_stb)))))
		f_pending_rd <= 1'b0;

	always @(*)
	if ((state == DC_READC)&&(!f_stb))
		`ASSERT(f_nreqs == (1<<LS));

	always @(*)
	if ((state == DC_READC)&&(f_stb))
		`ASSERT(f_nreqs == { 1'b0, o_wb_addr[LS-1:0] });

	always @(posedge i_clk)
	if (state == DC_READC)
	begin
		if (($past(i_wb_ack))&&(!$past(f_stb)))
			`ASSERT(f_nacks-1 == { 1'b0, c_waddr[LS-1:0] });
		else if (f_nacks > 0)
		begin
			`ASSERT(f_nacks-1 == { 1'b0, c_waddr[LS-1:0] });
			`ASSERT(c_waddr[CS-1:LS] == o_wb_addr[CS-1:LS]);
		end else begin
			`ASSERT(c_waddr[CS-1:LS] == o_wb_addr[CS-1:LS]-1'b1);
			`ASSERT(&c_waddr[LS-1:0]);
		end
	end

	always @(*)
	if (r_rd_pending)
		`ASSERT(r_addr == f_pending_addr[AW-1:0]);

	always @(*)
	if (f_pending_addr[AW])
	begin
		`ASSERT(state != DC_READC);
		`ASSERT((!o_wb_we)||(!o_wb_cyc_gbl));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_valid)&&($past(f_pending_addr) == f_const_addr))
	begin
		if (f_const_buserr)
			`ASSERT(o_err);
		else if (f_pending_rd)
		begin
			casez($past(req_data[3:0]))
			4'b0???: `ASSERT(o_data ==f_const_data);
			4'b101?: `ASSERT(o_data =={16'h00,f_const_data[15: 0]});
			4'b100?: `ASSERT(o_data =={16'h00,f_const_data[31:16]});
			4'b1100: `ASSERT(o_data =={24'h00,f_const_data[31:24]});
			4'b1101: `ASSERT(o_data =={24'h00,f_const_data[23:16]});
			4'b1110: `ASSERT(o_data =={24'h00,f_const_data[15: 8]});
			4'b1111: `ASSERT(o_data =={24'h00,f_const_data[ 7: 0]});
			endcase
		end
	end

	wire			f_this_return;

	assign	f_this_return = (f_return_address == f_const_addr);
	always @(*)
	if ((f_cyc)&&(
		((state == DC_READC)
			&&(f_return_address[AW-1:LS] == f_const_addr[AW-1:LS]))
		||(f_this_return))&&(f_cyc))
	begin
		if (f_const_buserr)
			assume(!i_wb_ack);
		else begin
			assume(!i_wb_err);
			assume(i_wb_data == f_const_data);
		end
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(last_tag == f_const_tag)&&(f_const_buserr)
			&&(!f_const_addr[AW]))
		`ASSERT(!last_tag_valid);

	always @(*)
	if (f_const_buserr)
	begin
		`ASSERT((!c_v[f_const_tag_addr])||(f_const_addr[AW])
			||(f_ctag_here != f_const_tag));

		if ((state == DC_READC)&&(wb_start[AW-1:LS] == f_const_tag))
		begin
			`ASSERT(f_nacks <= f_const_tag[LS-1:0]);
			if (f_nacks == f_const_tag[LS-1:0])
				assume(!i_wb_ack);
		end
	end

`endif	// DCACHE

	////////////////////////////////////////////////
	//
	// Checking the lock
	//
	////////////////////////////////////////////////
	//
	//

	always @(*)
		`ASSERT((!lock_gbl)||(!lock_lcl));
	always @(*)
	if (!OPT_LOCK)
		`ASSERT((!lock_gbl)&&(!lock_lcl));

	////////////////////////////////////////////////
	//
	// State based properties
	//
	////////////////////////////////////////////////
	//
	//
	reg	[F_LGDEPTH-1:0]	f_rdpending;

	initial	f_rdpending = 0;
	always @(posedge i_clk)
	if ((i_reset)||(o_err))
		f_rdpending <= 0;
	else case({ (i_pipe_stb)&&(!i_op[0]), o_valid })
	2'b01: f_rdpending <= f_rdpending - 1'b1;
	2'b10: f_rdpending <= f_rdpending + 1'b1;
	default: begin end
	endcase

	wire	f_wb_cachable;
	iscachable #(.ADDRESS_WIDTH(AW))
		f_chkwb_addr(o_wb_addr, f_wb_cachable);


	always @(*)
	if (state == DC_IDLE)
	begin
		`ASSERT(!r_wb_cyc_gbl);
		`ASSERT(!r_wb_cyc_lcl);

		`ASSERT(!cyc);

		if ((r_rd_pending)||(r_dvalid)||(r_svalid))
			`ASSERT(o_busy);

		if (!OPT_PIPE)
		begin
			if (r_rd_pending)
				`ASSERT(o_busy);
			else if (r_svalid)
				`ASSERT(o_busy);
			else if (o_valid)
				`ASSERT(!o_busy);
			else if (o_err)
				`ASSERT(!o_busy);
		end
	end else begin
		`ASSERT(o_busy);
		`ASSERT(cyc);
	end



	always @(posedge i_clk)
	if (state == DC_IDLE)
	begin
		if (r_svalid)
		begin
			`ASSERT(!r_dvalid);
			`ASSERT(!r_rd_pending);
			if (!OPT_PIPE)
				`ASSERT(!o_valid);
			else if (o_valid)
				`ASSERT(f_rdpending == 2);
		end

		if (r_dvalid)
		begin
			`ASSERT(!r_rd_pending);
			`ASSERT(npending == 0);
			`ASSERT(f_rdpending == 1);
		end

		if (r_rd_pending)
		begin
			if ((OPT_PIPE)&&(o_valid))
				`ASSERT(f_rdpending <= 2);
			else
				`ASSERT(f_rdpending == 1);

		end else if ((OPT_PIPE)&&(o_valid)&&($past(r_dvalid|r_svalid)))
				`ASSERT(f_rdpending <= 2);
		else
			`ASSERT(f_rdpending <= 1);
	end

	always @(posedge i_clk)
	if (state == DC_READC)
	begin
		`ASSERT( o_wb_cyc_gbl);
		`ASSERT(!o_wb_cyc_lcl);
		`ASSERT(!o_wb_we);
		`ASSERT(f_wb_cachable);

		`ASSERT(r_rd_pending);
		`ASSERT(r_cachable);
		if (($past(cyc))&&(!$past(o_wb_stb_gbl)))
			`ASSERT(!o_wb_stb_gbl);

		if ((OPT_PIPE)&&(o_valid))
			`ASSERT(f_rdpending == 2);
		else
			`ASSERT(f_rdpending == 1);
	end

	always @(*)
	if (state == DC_READS)
	begin
		`ASSERT(!o_wb_we);

		if (OPT_PIPE)
		begin
			if (o_valid)
				`ASSERT((f_rdpending == npending + 1)
					||(f_rdpending == npending));
			else
				`ASSERT(f_rdpending == npending);
		end
	end else if (state == DC_WRITE)
		`ASSERT(o_wb_we);

	always @(posedge i_clk)
	if ((state == DC_READS)||(state == DC_WRITE))
	begin
		`ASSERT(o_wb_we == (state == DC_WRITE));
		`ASSERT(!r_rd_pending);
		if (o_wb_we)
			`ASSERT(f_rdpending == 0);

		if (OPT_PIPE)
		begin
			casez({ $past(i_pipe_stb), f_stb })
			2'b00: `ASSERT(npending == f_outstanding);
			2'b1?: `ASSERT(npending == f_outstanding + 1);
			2'b01: `ASSERT(npending == f_outstanding + 1);
			endcase

			if (state == DC_WRITE)
				`ASSERT(!o_valid);
		end else
			`ASSERT(f_outstanding <= 1);
	end

	always @(*)
	if (OPT_PIPE)
		`ASSERT(f_rdpending <= 2);
	else
		`ASSERT(f_rdpending <= 1);

	always @(posedge i_clk)
	if ((!OPT_PIPE)&&(o_valid))
		`ASSERT(f_rdpending == 1);
	else if (o_valid)
		`ASSERT(f_rdpending >= 1);


	always @(*)
	if ((!o_busy)&&(!o_err)&&(!o_valid))
		`ASSERT(f_rdpending == 0);

	always @(*)
		`ASSERT(cyc == ((r_wb_cyc_gbl)||(r_wb_cyc_lcl)));

	always @(*)
	if ((!i_reset)&&(f_nreqs == f_nacks)&&(!f_stb))
		`ASSERT(!cyc);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_err)))
		`ASSUME(!i_lock);
	else if ((f_past_valid)&&(OPT_LOCK)&&($past(i_lock))
			&&((!$past(o_valid)) || ($past(i_pipe_stb))))
		`ASSUME($stable(i_lock));


	////////////////////////////////////////////////
	//
	// Ad-hoc properties
	//
	////////////////////////////////////////////////
	//
	//
	always @(*)
	if ((OPT_PIPE)&&(state == DC_WRITE)&&(!i_wb_stall)&&(stb)
			&&(!npending[DP]))
		`ASSERT(!o_pipe_stalled);

	always @(posedge i_clk)
	if (state == DC_WRITE)
		`ASSERT(o_wb_we);
	else if ((state == DC_READS)||(state == DC_READC))
		`ASSERT(!o_wb_we);

	always @(*)
	if (cyc)
		`ASSERT(f_cyc);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(cyc))&&(!c_wr)&&(last_tag_valid)
			&&(!r_rd_pending))
		`ASSERT((c_v[last_tag[(CS-LS-1):0]])
			&&(c_vtags[last_tag[(CS-LS-1):0]] == last_tag));

	always @(*)
	if (!OPT_LOCAL_BUS)
	begin
		`ASSERT(r_wb_cyc_lcl == 1'b0);
		`ASSERT(o_wb_stb_lcl == 1'b0);
		`ASSERT(lock_lcl == 1'b0);
	end

	always @(posedge i_clk)
	if ((state == DC_READC)&&(!stb))
	begin
		`ASSERT(o_wb_addr[LS-1:0] == 0);
		`ASSERT(o_wb_addr[AW-1:CS] == r_addr[AW-1:CS]);
	end else if ((state == DC_READC)&&(stb))
	begin
		`ASSERT(o_wb_addr[AW-1:CS] == r_addr[AW-1:CS]);
		`ASSERT(o_wb_addr[LS-1:0] == f_nreqs[LS-1:0]);
	end

	wire	[CS-1:0]	f_expected_caddr;
	assign	f_expected_caddr = { r_ctag[CS-LS-1:0], {(LS){1'b0}} }-1
					+ f_nacks;
	always @(posedge i_clk)
	if (state == DC_READC)
	begin
		if (LS == 0)
			`ASSERT(end_of_line);
		else if (f_nacks < (1<<LS)-1)
			`ASSERT(!end_of_line);
		else if (f_nacks == (1<<LS)-1)
			`ASSERT(end_of_line);
		`ASSERT(f_nacks <= (1<<LS));
		`ASSERT(f_nreqs <= (1<<LS));
		if (f_nreqs < (1<<LS))
		begin
			`ASSERT(o_wb_stb_gbl);
			`ASSERT(o_wb_addr[(LS-1):0] == f_nreqs[LS-1:0]);
		end else
			`ASSERT(!f_stb);
		`ASSERT((f_nreqs == 0)||(f_nacks <= f_nreqs));
		`ASSERT(c_waddr == f_expected_caddr);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(r_rd)&&(!$past(i_reset)))
	begin
		`ASSERT((o_busy)||(r_svalid));
	end

	always @(posedge i_clk)
	if (!$past(o_busy))
		`ASSERT(!r_dvalid);

	always @(posedge i_clk)
	if ((state == DC_READC)&&(c_wr))
		`ASSERT(c_wsel == 4'hf);

	always @(*)
	if (c_wr)
		`ASSERT((c_wsel == 4'hf)
			||(c_wsel == 4'hc)
			||(c_wsel == 4'h3)
			||(c_wsel == 4'h8)
			||(c_wsel == 4'h4)
			||(c_wsel == 4'h2)
			||(c_wsel == 4'h1));

	always @(*)
	if (!OPT_PIPE)
		`ASSERT(o_pipe_stalled == o_busy);
	else if (o_pipe_stalled)
		`ASSERT(o_busy);

	//
	// Only ever abort on reset
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(cyc))&&(!$past(i_wb_err)))
	begin
		if (($past(i_pipe_stb))&&(!$past(o_pipe_stalled)))
			`ASSERT(cyc);
		else if ($past(f_outstanding > 1))
			`ASSERT(cyc);
		else if (($past(f_outstanding == 1))
				&&((!$past(i_wb_ack))
					||(($past(f_stb))
						&&(!$past(i_wb_stall)))))
			`ASSERT(cyc);
		else if (($past(f_outstanding == 0))
				&&($past(f_stb)&&(!$past(i_wb_ack))))
			`ASSERT(cyc);
	end

	always @(posedge i_clk)
	if ((OPT_PIPE)&&(f_past_valid)&&(!$past(i_reset))&&(state != DC_READC))
	begin
		if ($past(cyc && i_wb_err))
		begin
			`ASSERT(npending == 0);
		end else if (($past(i_pipe_stb))||($past(i_wb_stall && stb)))
			`ASSERT((npending == f_outstanding+1)
				||(npending == f_outstanding+2));
		else
			`ASSERT(npending == f_outstanding);
	end

	always @(posedge i_clk)
	if ((OPT_PIPE)&&(state != DC_READC)&&(state != DC_IDLE))
		`ASSERT(last_ack == (npending <= 1));

	always @(*)
	`ASSERT(stb == f_stb);

	always @(*)
	if (r_rd_pending)
		`ASSERT(!r_svalid);

	always @(*)
	if (o_err)
		`ASSUME(!i_pipe_stb);

	always @(*)
	if (last_tag_valid)
		`ASSERT(|c_v);

	always @(posedge i_clk)
	if ((cyc)&&(state == DC_READC)&&($past(f_nacks > 0)))
		`ASSERT(!c_v[o_wb_addr[CS-1:LS]]);

	always @(*)
	if (last_tag_valid)
	begin
		`ASSERT((!cyc)||(o_wb_we)||(state == DC_READS)
					||(o_wb_addr[AW-1:LS] != last_tag));
	end

	wire	f_cachable_last_tag, f_cachable_r_addr;

	iscachable #(.ADDRESS_WIDTH(AW))
		fccheck_last_tag({last_tag, {(LS){1'b0}}}, f_cachable_last_tag);

	iscachable #(.ADDRESS_WIDTH(AW))
		fccheck_r_cachable(r_addr, f_cachable_r_addr);

	always @(*)
	if ((r_cachable)&&(r_rd_pending))
	begin
		`ASSERT(state != DC_WRITE);
		// `ASSERT(state != DC_READS);
		`ASSERT(f_cachable_r_addr);
		if (cyc)
			`ASSERT(o_wb_addr[AW-1:LS] == r_addr[AW-1:LS]);
	end

	always @(*)
	if (last_tag_valid)
	begin
		`ASSERT(f_cachable_last_tag);
		`ASSERT(c_v[last_tag[CS-LS-1:0]]);
		`ASSERT(c_vtags[last_tag[CS-LS-1:0]]==last_tag);
		`ASSERT((state != DC_READC)||(last_tag != o_wb_addr[AW-1:LS]));
	end


	////////////////////////////////////////////////
	//
	// Cover statements
	//
	////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
		cover(o_valid);

	always @(posedge i_clk)
	if (f_past_valid)
		cover($past(r_svalid));

	generate if (OPT_PIPE)
	begin : PIPE_COVER

		wire		recent_reset;
		reg	[2:0]	recent_reset_sreg;
		initial	recent_reset_sreg = -1;
		always @(posedge i_clk)
		if (i_reset)
			recent_reset_sreg <= -1;
		else
			recent_reset_sreg <= { recent_reset_sreg[1:0], 1'b0 };

		assign recent_reset = (i_reset)||(|recent_reset_sreg);

		//
		//
		wire	f_cvr_cread = (!recent_reset)&&(i_pipe_stb)&&(!i_op[0])
					&&(w_cachable);

		wire	f_cvr_cwrite = (!recent_reset)&&(i_pipe_stb)&&(i_op[0])
				&&(!cache_miss_inow);

		wire	f_cvr_writes = (!recent_reset)&&(i_pipe_stb)&&(i_op[0])
					&&(!w_cachable);
		wire	f_cvr_reads  = (!recent_reset)&&(i_pipe_stb)&&(!i_op[0])
					&&(!w_cachable);
		wire	f_cvr_test  = (!recent_reset)&&(cyc);

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_valid)))
			cover(o_valid);		// !

		always @(posedge i_clk)
		if ((f_past_valid)&&(!$past(i_reset))&&($past(i_pipe_stb)))
			cover(i_pipe_stb);

		always @(posedge i_clk)
		if ((f_past_valid)&&($past(o_valid))&&($past(o_valid,2)))
			cover(o_valid);

		always @(posedge i_clk)
			cover(($past(f_cvr_cread))&&(f_cvr_cread));

		always @(posedge i_clk)
			cover(($past(f_cvr_cwrite))&&(f_cvr_cwrite));

		always @(posedge i_clk)
			cover(($past(f_cvr_writes))&&(f_cvr_writes));

		/*
		* This cover statement will never pass.  Why not?  Because
		* cache reads must be separated from non-cache reads.  Hence,
		* we can only allow a single non-cache read at a time, otherwise
		* we'd bypass the cache read logic.
		*
		always @(posedge i_clk)
			cover(($past(f_cvr_reads))&&(f_cvr_reads));
		*/

		//
		// This is unrealistic, as it depends upon the Wishbone
		// acknoledging the request on the same cycle
		always @(posedge i_clk)
			cover(($past(f_cvr_reads,2))&&(f_cvr_reads));

		always @(posedge i_clk)
			cover(($past(r_dvalid))&&(r_svalid));

		//
		// A minimum of one clock must separate two dvalid's.
		// This option is rather difficult to cover, since it means
		// we must first load two separate cache lines before
		// this can even be tried.
		always @(posedge i_clk)
			cover(($past(r_dvalid,2))&&(r_dvalid));

		//
		// This is the optimal configuration we want:
		//	i_pipe_stb
		// 	##1 i_pipe_stb && r_svalid
		//	##1 r_svalid && o_valid
		//	##1 o_valid
		// It proves that we can handle a 2 clock delay, but that
		// we can also pipelin these cache accesses, so this
		// 2-clock delay becomes a 1-clock delay between pipelined
		// memory reads.
		//
		always @(posedge i_clk)
			cover(($past(r_svalid))&&(r_svalid));

		//
		// While we'd never do this (it breaks the ZipCPU's pipeline
		// rules), it's nice to know we could.
		//	i_pipe_stb && (!i_op[0]) // a read
		//	##1 i_pipe_stb && (i_op[0]) && r_svalid // a write
		//	##1 o_valid
		always @(posedge i_clk)
			cover(($past(r_svalid))&&(f_cvr_writes));

		/* Unreachable
		*
		always @(posedge i_clk)
			cover(($past(f_cvr_writes))&&(o_valid));

		always @(posedge i_clk)
			cover(($past(f_cvr_writes,2))&&(o_valid));

		always @(posedge i_clk)
			cover(($past(f_cvr_writes,3))&&(o_valid));

		always @(posedge i_clk)
			cover(($past(r_dvalid,3))&&(r_dvalid));

		*/

		always @(posedge i_clk)
			cover(($past(f_cvr_writes,4))&&(o_valid));

	end endgenerate

	////////////////////////////////////////////////
	//
	// Carelesss assumption section
	//
	////////////////////////////////////////////////
	//
	//

	//
	// Can't jump from local to global mid lock
	always @(*)
	if((OPT_LOCK)&&(OPT_LOCAL_BUS))
	begin
		if ((i_lock)&&(o_wb_cyc_gbl)&&(i_pipe_stb))
			assume(!(&i_addr[(DW-1):(DW-8)]));
		else if ((i_lock)&&(o_wb_cyc_lcl)&&(i_pipe_stb))
			assume(&i_addr[(DW-1):(DW-8)]);
	end

	always @(*)
	if ((OPT_PIPE)&&(o_busy || i_lock)&&(!o_pipe_stalled))
	begin
		if (i_pipe_stb)
			assume((!OPT_LOCAL_BUS)
				||(f_pending_addr[AW]==(&i_addr[DW-1:DW-8])));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(cyc))&&(!cyc))
		assume((!i_wb_err)&&(!i_wb_ack));

`endif
endmodule
