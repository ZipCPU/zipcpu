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
// Copyright (C) 2016-2018, Gisselquist Technology, LLC
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
`define	DC_IDLE		2'b00
`define	DC_WRITE	2'b01
`define	DC_READS	2'b10	// Read from a non-cachable address
`define	DC_READC	2'b11	// Read a cache line
//
//
module	dcache(i_clk, i_reset, i_pipe_stb, i_lock,
		i_op, i_addr, i_data, i_oreg,
			o_busy, o_pipe_stalled, o_valid, o_err, o_wreg,o_data,
		o_wb_cyc_gbl, o_wb_cyc_lcl, o_wb_stb_gbl, o_wb_stb_lcl,
			o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
		i_wb_ack, i_wb_stall, i_wb_err, i_wb_data);
	parameter	LGCACHELEN = 8,
			ADDRESS_WIDTH=30,
			LGNLINES=5, // Log of the number of separate cache lines
			NAUX=5;	// # of aux d-wires to keep aligned w/memops
	parameter [0:0]	OPT_LOCAL_BUS=1'b1;
	parameter [0:0]	OPT_LOCK=1'b1;
	localparam 	SDRAM_BIT = 26;
	localparam	FLASH_BIT = 22;
	localparam	BLKRAM_BIT= 15;
	localparam	AW = ADDRESS_WIDTH; // Just for ease of notation below
	localparam	CS = LGCACHELEN; // Number of bits in a cache address
	localparam	LS = CS-LGNLINES; // Bits to spec position w/in cline
	localparam	LGAUX = 3; // log_2 of the maximum number of piped data 
	localparam	DW = 32; // Bus data width
	input			i_clk, i_reset;
	// Interface from the CPU
	input			i_pipe_stb, i_lock;
	input	[2:0]		i_op;
	input	[(DW-1):0]	i_addr;
	input	[(DW-1):0]	i_data;
	input	[(NAUX-1):0]	i_oreg;	// Aux data, such as reg to write to
	// Outputs, going back to the CPU
	output	reg		o_busy;
	output	wire		o_pipe_stalled, o_valid, o_err;
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
	input				i_wb_ack, i_wb_stall, i_wb_err;
	input		[(DW-1):0]	i_wb_data;


	reg	cyc, stb, last_ack, end_of_line, last_line_stb;
	reg	r_wb_cyc_gbl, r_wb_cyc_lcl;


	reg	[((1<<LGNLINES)-1):0] c_v;	// One bit per cache line, is it valid?
	reg	[(AW-LS-1):0]	c_vtags	[0:((1<<LGNLINES)-1)];
	reg	[(DW-1):0]	c_mem	[0:((1<<CS)-1)];

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

	assign	i_cline = i_addr[(CS+1):LS+2];
	assign	i_caddr = i_addr[(CS+1):2];

	wire	cache_miss_inow, w_cachable;
	assign	cache_miss_inow = (!last_tag_valid)
					||(last_tag != i_addr[(AW+1):LS+2])
					||(!c_v[i_cline]);
	assign	w_cachable = ((!OPT_LOCAL_BUS)||(i_addr[(DW-1):(DW-8)]!=8'hff))
				&&((!i_lock)||(!OPT_LOCK))
				&&(((SDRAM_BIT>0)&&(i_addr[SDRAM_BIT]))
				  ||((FLASH_BIT>0)&&(i_addr[FLASH_BIT]))
				  ||((BLKRAM_BIT>0)&&(i_addr[BLKRAM_BIT])));

	reg	r_cachable, r_svalid, r_dvalid, r_rd, r_cache_miss,
		r_rd_pending;
	reg	[(AW-1):0]		r_addr;
	wire	[(LGNLINES-1):0]	r_cline;
	wire	[(CS-1):0]		r_caddr;
	wire	[(AW-LS-1):0]		r_ctag;

	assign	r_cline = r_addr[(CS-1):LS];
	assign	r_caddr = r_addr[(CS-1):0];
	assign	r_ctag  = r_addr[(AW-1):LS];

/*
	integer k;
	initial begin
		for(k=0; k<(1<<(LGNLINES)); k=k+1)
			c_vtags[k] <= k;
	end
*/

	reg	wr_cstb, r_iv, in_cache;
	reg	[(AW-LS-1):0]	r_itag;

	//
	// The one-clock delayed read values from the cache.
	//
	initial	r_rd = 1'b0;
	initial	r_cachable = 1'b0;
	initial	r_svalid = 1'b0;
	initial	r_dvalid = 1'b0;
	initial	r_cache_miss = 1'b0;
	initial	r_addr = 0;
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
		r_svalid<= (!i_op[0])&&(!cache_miss_inow)&&(w_cachable)
				&&(i_pipe_stb)&&(!c_wr)&&(!wr_cstb);

		//
		// The two clock in-cache path
		//
		// Some preliminaries that needed to be calculated on the first
		// clock
		if (!o_busy)
		begin
			r_iv   <= c_v[i_cline];
			r_itag <= c_vtags[i_cline];
			r_addr <= i_addr[(AW+1):2];
			r_cachable <= (!i_op[0])&&(w_cachable)&&(i_pipe_stb);
			o_wreg <= i_oreg;
			r_rd_pending <= (i_pipe_stb)&&(!i_op[0]);
		end else begin
			r_iv   <= c_v[r_cline];
			r_itag <= c_vtags[r_cline];
			r_rd_pending <= (r_rd_pending)&&((r_itag != r_ctag)
				||(!r_iv)||(!r_cachable))&&(!r_svalid);
		end
		r_rd <= (i_pipe_stb)&&(!i_op[0]);
		// r_itag contains the tag we didn't have available to us on the
		// last clock, r_ctag is a bit select from r_addr containing a
		// one clock delayed address.
		r_dvalid <= (!r_svalid)&&(r_itag == r_ctag)&&(r_iv)&&(r_cachable)&&(r_rd_pending);
		if ((r_itag == r_ctag)&&(r_iv)&&(r_cachable))
		begin
			last_tag_valid <= 1'b1;
			last_tag <= r_ctag;
		end

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

	reg	[DW/8-1:0]	r_sel;

	initial	r_sel = 4'hf;
	always @(posedge i_clk)
	if (i_reset)
		r_sel <= 4'hf;
	else if (!o_busy)
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

	assign	o_wb_sel = (state == `DC_READC) ? 4'hf : r_sel;

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

	reg	[1:0]	state;

	reg	[(CS-1):0]	wr_addr;

	initial	r_wb_cyc_gbl = 0;
	initial	r_wb_cyc_lcl = 0;
	initial	o_wb_stb_gbl = 0;
	initial	o_wb_stb_lcl = 0;
	initial	c_v = 0;
	initial	cyc = 0;
	initial	c_wr = 0;
	initial	state = `DC_IDLE;
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
		state <= `DC_IDLE;
		last_ack <= 1'b0;
		cyc <= 1'b0;
		state <= `DC_IDLE;
	end else begin
		// By default, update the cache from the write 1-clock ago
		// c_wr <= (wr_cstb)&&(wr_wtag == wr_vtag);
		// c_waddr <= wr_addr[(CS-1):0];
		c_wr <= 0;

		if ((c_wr)&&(!cyc))
			c_v[c_waddr[(CS-1):LS]] <= 1'b1;

		wr_cstb <= 1'b0;

		if (!cyc)
			wr_addr <= r_addr[(CS-1):0];
		else if (i_wb_ack)
			wr_addr <= wr_addr + 1'b1;
		else
			wr_addr <= wr_addr;

		if (LS <= 1)
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
			last_line_stb <= (LS <= 1);
		else if ((stb)&&(!i_wb_stall))
			last_line_stb <= (o_wb_addr[(LS-1):1]=={(LS-1){1'b1}});
		else if (stb)
			last_line_stb <= (o_wb_addr[(LS-1):0]=={(LS){1'b1}});

		//
		//
		if (state == `DC_IDLE)
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
				state <= `DC_WRITE;
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
				last_ack <= 1'b1;

			end else if (r_cache_miss)
			begin
				state <= `DC_READC;
				o_wb_addr <= { r_ctag, {(LS){1'b0}} };

				c_waddr <= { r_ctag[CS-LS-1:0], {(LS){1'b0}} }-1;
				cyc <= 1'b1;
				stb <= 1'b1;
				r_wb_cyc_gbl <= 1'b1;
				o_wb_stb_gbl <= 1'b1;
				last_ack <= (LS == 0);
				wr_addr[LS-1:0] <= 0;
			end else if ((i_pipe_stb)&&(!w_cachable))
			begin // Read non-cachable memory area
				state <= `DC_READS;
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
				last_ack <= 1'b1;
			end // else we stay idle

		end else if (state == `DC_READC)
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

			if (i_wb_ack)
				last_ack <= last_ack || (&wr_addr[LS-1:1]);
			else
				last_ack <= last_ack || (&wr_addr[LS-1:0]);

			if ((i_wb_ack)&&(!end_of_line))
				c_vtags[r_addr[(CS-1):LS]]
						<= r_addr[(AW-1):LS];

			if (((i_wb_ack)&&(end_of_line))||(i_wb_err))
			begin
				state          <= `DC_IDLE;
				cyc <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
				//
			end
		end else if (state == `DC_READS)
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
				state        <= `DC_IDLE;
				cyc          <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
			end
		end else if (state == `DC_WRITE)
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

			if ((stb)&&(!i_wb_stall)&&(i_pipe_stb))
				o_wb_addr <= i_addr[(AW+1):2];
			
			if (((i_wb_ack)&&(last_ack))||(i_wb_err))
			begin
				state        <= `DC_IDLE;
				cyc          <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
			end
		end
	end

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
	reg	[(DW-1):0]	cached_idata, cached_rdata;
	always @(posedge i_clk)
		cached_idata <= c_mem[i_caddr];

	always @(posedge i_clk)
		cached_rdata <= c_mem[r_caddr];

// o_data can come from one of three places:
// 1. The cache, assuming the data was in the last cache line
// 2. The cache, second clock, assuming the data was in the cache at all
// 3. The cache, after filling the cache
// 4. The wishbone state machine, upon reading the value desired.
	wire	[DW-1:0]	pre_data;
	always @(*)
		if (r_svalid)
			pre_data = cached_idata;
		else if (state == `DC_READS)
			pre_data = i_wb_data;
		else
			pre_data = cached_rdata;

	always @(posedge i_clk)
	case(r_sel)
	4'b0001: o_data <= { 24'h0, pre_data[ 7: 0] };
	4'b0010: o_data <= { 24'h0, pre_data[15: 8] };
	4'b0100: o_data <= { 24'h0, pre_data[23:16] };
	4'b1000: o_data <= { 24'h0, pre_data[31:24] };
	4'b0011: o_data <= { 16'h0, pre_data[15: 0] };
	4'b1100: o_data <= { 16'h0, pre_data[31:16] };
	default	o_data <= pre_data;
	endcase

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_valid <= 1'b0;
	else if (state == `DC_READS)
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
	if (i_reset)
		o_busy <= 1'b0;
	else if (i_pipe_stb)
		o_busy <= 1'b1;
	else if (r_rd_pending)
		o_busy <= 1'b1;
	else if (cyc)
		o_busy <= 1'b1;
	else // if ((r_dvalid)||(r_svalid))
		o_busy <= 1'b0;

	//
	// We can use our FIFO addresses to pre-calculate when an ACK is going
	// to be the last_noncachable_ack.


	assign o_pipe_stalled= o_busy;

	reg	lock_gbl, lock_lcl;
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

`ifdef	FORMAL
// ifdef DCACHE
	reg	f_past_valid;
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
		assume(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		// Insist on initial statements matching reset values
		assert(r_rd == 1'b0);
		assert(r_cachable == 1'b0);
		assert(r_svalid == 1'b0);
		assert(r_dvalid == 1'b0);
		assert(r_cache_miss == 1'b0);
		assert(r_addr == 0);
		//
		assert(c_wr == 0);
		assert(c_v  == 0);
		//
		// assert(aux_head == 0);
		// assert(aux_tail == 0);
		//
		assert(lock_gbl == 0);
		assert(lock_lcl == 0);
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
		assume(!i_pipe_stb);

	always @(*)
	if (!f_past_valid)
		assume(!i_pipe_stb);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
		&&($past(i_pipe_stb))&&($past(o_busy)))
	begin
		assume($stable(i_pipe_stb));
		assume($stable(i_op[0]));
		assume($stable(i_addr));
		if (i_op[0])
			assume($stable(i_data));
	end

	////////////////////////////////////////////////
	//
	// Wishbone properties
	//
	////////////////////////////////////////////////
	//
	//
	localparam	F_LGDEPTH=LS+1;
	wire	f_cyc, f_stb;

	assign	f_cyc = (o_wb_cyc_gbl)|(o_wb_cyc_lcl);
	assign	f_stb = (o_wb_stb_gbl)|(o_wb_stb_lcl);
	always @(*)
		assert((!o_wb_cyc_gbl)||(!o_wb_cyc_lcl));

	wire	[(F_LGDEPTH-1):0]	f_nreqs, f_nacks, f_outstanding;

	fwb_master #(
		.AW(AW), .DW(DW), .F_MAX_STALL(1),
			.F_MAX_ACK_DELAY(1),
			.F_LGDEPTH(F_LGDEPTH),
			.F_MAX_REQUESTS((1<<LS)),
			.F_OPT_SOURCE(1'b1),
			.F_OPT_DISCONTINUOUS(0),
			.F_OPT_CLK2FFLOGIC(0)
		) fwb(i_clk, i_reset,
			cyc, f_stb, o_wb_we, o_wb_addr, o_wb_data, o_wb_sel,
				i_wb_ack, i_wb_stall, i_wb_data, i_wb_err,
		f_nreqs, f_nacks, f_outstanding);

	////////////////////////////////////////////////
	//
	// Arbitrary address properties
	//
	////////////////////////////////////////////////
	//
	//
	wire	[AW:0]		f_const_addr;
	wire	[AW-LS-1:0]	f_const_tag, f_ctag_here, f_wb_tag;
	wire	[CS-LS-1:0]	f_const_tag_addr;
	wire			f_const_buserr;
	reg	[DW-1:0]	f_const_data, f_cmem_here;
	reg	[AW:0]		f_pending_addr;
	reg			f_pending_rd;

	assign	f_const_addr   = $anyconst;
	assign	f_const_buserr = $anyconst;
	assign	f_const_tag    = f_const_addr[AW-1:LS];
	assign	f_const_tag_addr = f_const_addr[CS-1:LS];
	assign	f_cmem_here    = c_mem[f_const_addr[CS-1:0]];
	assign	f_ctag_here    = c_vtags[f_const_addr[CS-1:LS]];
	assign	f_wb_tag       = o_wb_addr[AW-1:LS];

	generate if ((AW > DW - 8)&&(OPT_LOCAL_BUS))
	begin

		always @(*)
		if (f_const_addr[AW])
			assume(&f_const_addr[(AW-1):(DW-8)]);
		else
			assume(!&f_const_addr[(AW-1):(DW-8)]);
	end endgenerate

	reg	[AW-1:0]	wb_start;
	assign	wb_start = (f_stb) ? (o_wb_addr - f_nreqs) : o_wb_addr;

	always @(posedge i_clk)
	if ((f_past_valid)&&(!i_reset)&&(!f_const_buserr)) // &&((!$past(i_pipe_stb))||(!$past(i_op))))
	begin
		if ((cyc)&&(o_wb_we)&&(f_stb)
				&&(wb_start[AW-1:0] == f_const_addr[AW-1:0])
				&&(( (o_wb_stb_lcl)&&(f_const_addr[AW]))
				     ||((o_wb_stb_gbl)&&(!f_const_addr[AW])) ))
		begin

			if (o_wb_sel[0])
				assert(o_wb_data[7:0] == f_const_data[7:0]);
			if (o_wb_sel[1])
				assert(o_wb_data[15:8] == f_const_data[15:8]);
			if (o_wb_sel[2])
				assert(o_wb_data[23:16] == f_const_data[23:16]);
			if (o_wb_sel[3])
				assert(o_wb_data[31:24] == f_const_data[31:24]);

		end else if ((!f_const_addr[AW])&&(c_v[f_const_tag_addr])
			&&(f_ctag_here ==f_const_addr[AW-1:LS]))
		begin
			if ((c_wr)&&(c_waddr[CS-1:0] == f_const_addr[CS-1:0]))
			begin
				if (c_wsel[3])
					assert(c_wdata[31:24]
							== f_const_data[31:24]);
				else
					assert(f_cmem_here[31:24]
							== f_const_data[31:24]);
				if (c_wsel[2])
					assert(c_wdata[23:16]
							== f_const_data[23:16]);
				else
					assert(f_cmem_here[23:16] == f_const_data[23:16]);
				if (c_wsel[1])
					assert(c_wdata[15:8]
							== f_const_data[15:8]);
				else
					assert(f_cmem_here[15:8] == f_const_data[15:8]);
				if (c_wsel[0])
					assert(c_wdata[7:0]
							== f_const_data[7:0]);
				else
					assert(f_cmem_here[7:0] == f_const_data[7:0]);
			end else
				assert(f_cmem_here == f_const_data);
		end
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(state == `DC_READC))
	begin
		assert(f_wb_tag == r_ctag);
		if ((wb_start[AW-1:LS] == f_const_tag)
			&&(!c_v[f_const_tag_addr])
			&&(f_const_addr[AW] == r_wb_cyc_lcl)
			&&(f_nacks > f_const_addr[LS-1:0]))
		begin
			// We are reading the cache line containing our
			// constant address f_const_addr.  Make sure the data
			// is correct.
			if ((c_wr)&&(c_waddr[CS-1:0] == f_const_addr[CS-1:0]))
				assert(c_wdata == f_const_data);
			else
				assert(f_cmem_here == f_const_data);
		end

		if (f_nacks > 0)
			assert(!c_v[wb_start[CS-1:LS]]);
	end

	always @(posedge i_clk)
	if ((state == `DC_READC)&&(f_nacks > 0))
	begin
		assert(c_vtags[wb_start[(CS-1):LS]] <= wb_start[(AW-1):LS]);
		assert(c_vtags[wb_start[(CS-1):LS]] <= r_addr[AW-1:LS]);
	end

	wire	[AW-1:0]	f_cache_waddr;
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
	if ((f_past_valid)&&(state == `DC_READC))
	begin
		if ((c_wr)&&(c_waddr[LS-1:0] != 0)&&(f_this_cache_waddr))
			assert(c_wdata == f_const_data);
	end

	always @(posedge i_clk)
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

	initial	f_pending_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_pending_addr <= 0;
	else if (!o_busy)
		f_pending_addr <= { (OPT_LOCAL_BUS)&&(&i_addr[DW-1:DW-8]),
					i_addr[(AW+1):2] };

	initial	f_pending_rd = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_pending_rd <= 0;
	else if ((!o_busy)&&(i_pipe_stb))
		f_pending_rd <= (!i_op[0]);
	else if (o_valid)
		f_pending_rd <= 1'b0;

	always @(*)
	if ((state == `DC_READC)&&(!f_stb))
		assert(f_nreqs == (1<<LS));

	always @(*)
	if ((state == `DC_READC)&&(f_stb))
		assert(f_nreqs == { 1'b0, o_wb_addr[LS-1:0] });

	always @(posedge i_clk)
	if (state == `DC_READC)
	begin
		if ($past(i_wb_ack))
			assert(f_nacks-1 == { 1'b0, c_waddr[LS-1:0] });
		else if (f_nacks > 0)
		begin
			assert(f_nacks-1 == { 1'b0, c_waddr[LS-1:0] });
			assert(c_waddr[CS-1:LS] == o_wb_addr[CS-1:LS]);
		end
	end

	always @(*)
		assert(r_addr == f_pending_addr[AW-1:0]);
	always @(*)
	if (f_pending_addr[AW])
	begin
		assert(state != `DC_READC);
		assert((!o_wb_we)||(!o_wb_cyc_gbl));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_valid)&&($past(f_pending_addr) == f_const_addr))
	begin
		if (f_const_buserr)
			assert(o_err);
		else if (f_pending_rd)
		begin
			case($past(r_sel))
			4'b1111: assert(o_data ==f_const_data);
			4'b0011: assert(o_data =={ 16'h00, f_const_data[15:0]});
			4'b1100: assert(o_data =={ 16'h00, f_const_data[31:16]});
			4'b0001: assert(o_data =={ 24'h00,f_const_data[ 7: 0]});
			4'b0010: assert(o_data =={ 24'h00,f_const_data[15: 8]});
			4'b0100: assert(o_data =={ 24'h00,f_const_data[23:16]});
			4'b1000: assert(o_data =={ 24'h00,f_const_data[31:24]});
			endcase
		end
	end

	wire	[AW:0]		f_return_address;
	wire			f_this_return;

	assign	f_return_address[AW]      = o_wb_cyc_lcl;
	assign	f_return_address[AW-1:LS] = o_wb_addr[AW-1:LS];
	always @(*)
	if (state == `DC_READS)
		f_return_address[LS-1:0] = o_wb_addr[LS-1:0];
	else
		f_return_address[LS-1:0]
				= (o_wb_addr[LS-1:0] - f_outstanding[LS-1:0]);
	assign	f_this_return = (f_return_address == f_const_addr);
	always @(*)
	if ((f_this_return)&&(f_cyc))
	begin
		if (f_const_buserr)
			assume(!i_wb_ack);
		else begin
			assume(!i_wb_err);
			assume(i_wb_data == f_const_data);
		end
	end

	////////////////////////////////////////////////
	//
	// Checking the lock
	//
	////////////////////////////////////////////////
	//
	//

	always @(*)
		assert((!lock_gbl)||(!lock_lcl));
	always @(*)
	if (!OPT_LOCK)
		assert((!lock_gbl)&&(!lock_lcl));

	////////////////////////////////////////////////
	//
	// State based properties
	//
	////////////////////////////////////////////////
	//
	//

	always @(*)
	if (state == `DC_IDLE)
	begin
		assert(!r_wb_cyc_gbl);
		assert(!r_wb_cyc_lcl);
	end

	always @(posedge i_clk)
	if (state == `DC_READC)
	begin
		assert( o_wb_cyc_gbl);
		assert(!o_wb_cyc_lcl);
		assert(!o_wb_we);
		assert(r_rd_pending);
		if (($past(cyc))&&(!$past(o_wb_stb_gbl)))
			assert(!o_wb_stb_gbl);
	end

	always @(*)
	if (state == `DC_READC)
		assert(!o_wb_we);
	else if (state == `DC_READS)
		assert(!o_wb_we);
	else if (state == `DC_WRITE)
		assert(o_wb_we);

	always @(*)
	if (state == `DC_IDLE)
		assert(!cyc);
	else
		assert(cyc);

	always @(*)
	if (state != `DC_IDLE)
		assert(o_busy);

	always @(*)
		assert(cyc == ((r_wb_cyc_gbl)||(r_wb_cyc_lcl)));

	always @(*)
	if ((cyc)&&(o_wb_we))
		assert(!r_rd_pending);

	always @(*)
	if ((f_nreqs == f_nacks)&&(!f_stb))
		assert(!cyc);

	always @(posedge i_clk)
	if (state == `DC_READC)
		assert(((SDRAM_BIT >0)&&(o_wb_addr[SDRAM_BIT-2]))
				||(  (FLASH_BIT >0)&&(o_wb_addr[FLASH_BIT-2]))
				||(  (BLKRAM_BIT>0)&&(o_wb_addr[BLKRAM_BIT-2])));
	else if (state == `DC_READS)
		assert(((lock_gbl)||(i_lock))
			||(r_wb_cyc_lcl)
			||(((SDRAM_BIT==0)||(!o_wb_addr[SDRAM_BIT-2]))
			&&((FLASH_BIT ==0)||(!o_wb_addr[FLASH_BIT-2]))
			&&((BLKRAM_BIT==0)||(!o_wb_addr[BLKRAM_BIT-2]))));

	always @(posedge i_clk)
	if ((f_past_valid)&&(OPT_LOCK)&&($past(i_lock))
			&&((!$past(o_valid)) || ($past(i_pipe_stb))))
		assume($stable(i_lock));


	////////////////////////////////////////////////
	//
	// Ad-hoc properties
	//
	////////////////////////////////////////////////
	//
	//

	always @(*)
	if (cyc)
		assert(f_cyc);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(cyc))&&(!c_wr)&&(last_tag_valid)
			&&(!r_rd_pending))
		assert((c_v[last_tag[(CS-LS-1):0]])
			&&(c_vtags[last_tag[(CS-LS-1):0]] == last_tag));

	always @(posedge i_clk)
	if ((f_past_valid)&&(last_tag == f_const_tag)&&(f_const_buserr)
			&&(!f_const_addr[AW]))
		assert(!last_tag_valid);

	always @(*)
		assert((SDRAM_BIT  == 0)||(SDRAM_BIT  < ADDRESS_WIDTH));
	always @(*)
		assert((FLASH_BIT  == 0)||(FLASH_BIT  < ADDRESS_WIDTH));
	always @(*)
		assert((BLKRAM_BIT == 0)||(BLKRAM_BIT < ADDRESS_WIDTH));

	always @(*)
	if (!OPT_LOCAL_BUS)
	begin
		assert(r_wb_cyc_lcl == 1'b0);
		assert(o_wb_stb_lcl == 1'b0);
		assert(lock_lcl == 1'b0);
	end

	always @(*)
	if (f_const_buserr)
	begin
		assert((!c_v[f_const_tag_addr])||(f_const_addr[AW])
			||(f_ctag_here != f_const_tag));

		if ((state == `DC_READC)&&(wb_start[AW-1:LS] == f_const_tag))
		begin
			assert(f_nacks <= f_const_tag[LS-1:0]);
			if (f_nacks == f_const_tag[LS-1:0])
				assume(!i_wb_ack);
		end
	end

	always @(posedge i_clk)
	if ((state == `DC_READC)&&(!stb))
	begin
		assert(o_wb_addr[LS-1:0] == 0);
		assert(o_wb_addr[AW-1:CS] == r_addr[AW-1:CS]);
	end else if ((state == `DC_READC)&&(stb))
	begin
		assert(o_wb_addr[AW-1:CS] == r_addr[AW-1:CS]);
		assert(o_wb_addr[LS-1:0] == f_nreqs[LS-1:0]);
	end

	always @(posedge i_clk)
	if (state == `DC_READC)
	begin
		if (f_nacks < (1<<LS)-1)
			assert(!end_of_line);
		else if (f_nacks == (1<<LS)-1)
			assert(end_of_line);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(r_rd)&&(!$past(i_reset)))
	begin
		assert((o_busy)||(r_svalid));
	end

	always @(posedge i_clk)
	if (!$past(o_busy))
		assert(!r_dvalid);

	always @(posedge i_clk)
	if ((state == `DC_READC)&&(c_wr))
		assert(c_wsel == 4'hf);

	always @(*)
	if (c_wr)
		assert((c_wsel == 4'hf)
			||(c_wsel == 4'hc)
			||(c_wsel == 4'h3)
			||(c_wsel == 4'h8)
			||(c_wsel == 4'h4)
			||(c_wsel == 4'h2)
			||(c_wsel == 4'h1));

/*
	wire	[LGNLINES-1:0]	f_const_vtag_addr;
	wire	[AW-1:LGNLINES]	f_const_vtag;
	assign	f_const_vtag_addr = $anyconst;
	assign	f_const_vtag = c_vtags[f_const_vtag_addr];
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(f_past_valid)))
		assert(f_const_vtag[LGNLINES-1:0]	
			== f_const_vtag_addr[LGNLINES-1:0]);
*/

	////////////////////////////////////////////////
	//
	// Cover statements
	//
	////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
		cover(o_valid);

	////////////////////////////////////////////////
	//
	// Carelesss assumption section
	//
	////////////////////////////////////////////////
	//
	//
	always @(*)
	if((OPT_LOCK)&&(OPT_LOCAL_BUS))
	begin
		if ((i_lock)&&(o_wb_cyc_gbl)&&(i_pipe_stb))
			assume(!&i_addr[(DW-1):(DW-8)]);
		else if ((i_lock)&&(o_wb_cyc_lcl)&&(i_pipe_stb))
			assume(&i_addr[(DW-1):(DW-8)]);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(cyc))&&(!cyc))
		assume((!i_wb_err)&&(!i_wb_ack));


`endif
endmodule
