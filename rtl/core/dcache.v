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
// Copyright (C) 2016, Gisselquist Technology, LLC
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
module	dcache(i_clk, i_rst, i_pipe_stb, i_lock,
		i_op, i_addr, i_data, i_oreg,
			o_busy, o_pipe_stalled, o_valid, o_err, o_wreg,o_data,
		o_wb_cyc_gbl, o_wb_cyc_lcl, o_wb_stb_gbl, o_wb_stb_lcl,
			o_wb_we, o_wb_addr, o_wb_data,
		i_wb_ack, i_wb_stall, i_wb_err, i_wb_data);
	parameter	LGCACHELEN = 8,
			ADDRESS_WIDTH=32,
			LGNLINES=5, // Log of the number of separate cache lines
			IMPLEMENT_LOCK=0,
			NAUX=5;	// # of aux d-wires to keep aligned w/memops
	localparam 	SDRAM_BIT = 26;
	localparam	FLASH_BIT = 22;
	localparam	BLKRAM_BIT= 15;
	localparam	AW = ADDRESS_WIDTH; // Just for ease of notation below
	localparam	CS = LGCACHELEN; // Number of bits in a cache address
	localparam	LS = CS-LGNLINES; // Bits to spec position w/in cline
	localparam	LGAUX = 3; // log_2 of the maximum number of piped data 
	input			i_clk, i_rst;
	// Interface from the CPU
	input			i_pipe_stb, i_lock;
	input			i_op;
	input	[31:0]		i_addr;
	input	[31:0]		i_data;
	input	[(NAUX-1):0]	i_oreg;	// Aux data, such as reg to write to
	// Outputs, going back to the CPU
	output	wire		o_busy, o_pipe_stalled, o_valid, o_err;
	output reg [(NAUX-1):0]	o_wreg;
	output	reg	[31:0]	o_data;
	// Wishbone bus master outputs
	output	wire		o_wb_cyc_gbl, o_wb_cyc_lcl;
	output	reg		o_wb_stb_gbl, o_wb_stb_lcl;
	output	reg		o_wb_we;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	reg	[31:0]		o_wb_data;
	// Wishbone bus slave response inputs
	input				i_wb_ack, i_wb_stall, i_wb_err;
	input		[31:0]		i_wb_data;


	reg	cyc, stb, last_ack, end_of_line, last_line_stb;


	reg	[((1<<LGNLINES)-1):0] c_v;	// One bit per cache line, is it valid?
	reg	[(AW-LS-1):0]	c_vtags	[0:((1<<LGNLINES)-1)];
	reg	[31:0]		c_mem	[0:((1<<CS)-1)];
	// reg	[((1<<LGNLINES)-1):0]	c_wr; // Is the cache line writable?
	// reg	c_wdata;
	// reg	c_waddr;

	// To simplify writing to the cache, and the job of the synthesizer to
	// recognize that a cache write needs to take place, we'll take an extra
	// clock to get there, and use these c_w... registers to capture the
	// data in the meantime.
	reg			c_wr;
	reg	[31:0]		c_wdata;
	reg	[(CS-1):0]	c_waddr;

	reg	[(AW-LS-1):0]	last_tag;


	wire	[(LGNLINES-1):0]	i_cline;
	wire	[(CS-1):0]	i_caddr;
	wire	[(AW-LS-1):0]	i_ctag;

	assign	i_cline = i_addr[(CS-1):LS];
	assign	i_caddr = i_addr[(CS-1):0];
	assign	i_ctag  = i_addr[(AW-1):LS];

	wire	cache_miss_inow, w_cachable;
	assign	cache_miss_inow = (last_tag != i_addr[31:LS])||(!c_v[i_cline]);
	assign	w_cachable = (i_addr[31:30]!=2'b11)&&(!i_lock)&&(
				((SDRAM_BIT>0)&&(i_addr[SDRAM_BIT]))
				||((FLASH_BIT>0)&&(i_addr[FLASH_BIT]))
				||((BLKRAM_BIT>0)&&(i_addr[BLKRAM_BIT])));

	reg	r_cachable, r_svalid, r_dvalid, r_rd, r_cache_miss, r_rvalid;
	reg	[(AW-1):0]	r_addr;
	reg	[31:0]		r_idata, r_ddata, r_rdata;
	wire	[(LGNLINES-1):0]	r_cline;
	wire	[(CS-1):0]	r_caddr;
	wire	[(AW-LS-1):0]	r_ctag;

	assign	r_cline = r_addr[(CS-1):LS];
	assign	r_caddr = r_addr[(CS-1):0];
	assign	r_ctag  = r_addr[(AW-1):LS];


	reg	wr_cstb, r_iv, pipeable_op, non_pipeable_op, in_cache;
	reg	[(AW-LS-1):0]	r_itag;

	//
	// The one-clock delayed read values from the cache.
	//
	initial	r_rd = 1'b0;
	initial	r_cachable = 1'b0;
	initial	r_svalid = 1'b0;
	initial	r_dvalid = 1'b0;
	always @(posedge i_clk)
	begin
		// The single clock path
		r_idata <= c_mem[i_addr[(CS-1):0]];
		// The valid for the single clock path
		//	Only ... we need to wait if we are currently writing
		//	to our cache.
		r_svalid<= (!i_op)&&(!cache_miss_inow)&&(w_cachable)
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
			r_addr <= i_addr;
			r_cachable <= (!i_op)&&(w_cachable)&&(i_pipe_stb);
		end else begin
			r_iv   <= c_v[r_cline];
			r_itag <= c_vtags[r_cline];
		end
		// r_idata still contains the right answer
		r_rd <= (i_pipe_stb)&&(!i_op);
		r_ddata  <= r_idata;
		// r_itag contains the tag we didn't have available to us on the
		// last clock, r_ctag is a bit select from r_addr containing a
		// one clock delayed address.
		r_dvalid <= (r_itag == r_ctag)&&(r_iv)&&(r_cachable);
		if ((r_itag == r_ctag)&&(r_iv)&&(r_cachable))
			last_tag <= r_ctag;

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

		r_rdata <= c_mem[r_addr[(CS-1):0]];
		r_rvalid<= ((i_wb_ack)&&(last_ack));
	end

`define	DC_IDLE		2'b00
`define	DC_WRITE	2'b01
`define	DC_READS	2'b10
`define	DC_READC	2'b11
	reg	[1:0]	state;

	reg	[(AW-LS-1):0]	wr_wtag, wr_vtag;
	reg	[31:0]		wr_data;
	reg	[(CS-1):0]	wr_addr;
	always @(posedge i_clk)
	begin
		// By default, update the cache from the write 1-clock ago
		c_wr <= (wr_cstb)&&(wr_wtag == wr_vtag);
		c_wdata <= wr_data;
		c_waddr <= wr_addr[(CS-1):0];

		wr_cstb <= 1'b0;
		wr_vtag <= c_vtags[o_wb_addr[(CS-LS-1):0]];
		wr_wtag <= o_wb_addr[(AW-LS-1):0];
		wr_data <= o_wb_data;
		wr_addr <= o_wb_addr[(CS-1):0];


		if (LS <= 1)
			end_of_line <= 1'b1;
		else
			end_of_line<=(cyc)&&((c_waddr[(LS-1):1]=={(LS-1){1'b1}})
				||((i_wb_ack)
				&&(c_waddr[(LS-1):0]=={{(LS-2){1'b1}},2'b01})));

		if (LS <= 1)
			last_line_stb <= 1'b1;
		else
			last_line_stb <= (stb)&&
				((o_wb_addr[(LS-1):1]=={(LS-1){1'b1}})
				||((!i_wb_stall)
					&&(o_wb_addr[(LS-1):0]
						=={{(LS-2){1'b1}},2'b01})));

		//
		if (state == `DC_IDLE)
			pipeable_op <= 1'b0;
		if (state == `DC_IDLE)
			non_pipeable_op <= 1'b0;


		if (state == `DC_IDLE)
		begin
			o_wb_we <= 1'b0;
			o_wb_data <= i_data;
			pipeable_op <= 1'b0;
			non_pipeable_op <= 1'b1;

			cyc <= 1'b0;
			stb <= 1'b0;

			r_wb_cyc_gbl <= 1'b0;
			r_wb_cyc_lcl <= 1'b0;
			o_wb_stb_gbl <= 1'b0;
			o_wb_stb_lcl <= 1'b0;

			in_cache <= (i_op)&&(w_cachable);
			if ((i_pipe_stb)&&(i_op))
			begin // Write  operation
				state <= `DC_WRITE;
				o_wb_addr <= i_addr;
				o_wb_we <= 1'b1;
				pipeable_op <= 1'b1;

				cyc <= 1'b1;
				stb <= 1'b1;

				r_wb_cyc_gbl <= (i_addr[31:30]!=2'b11);
				r_wb_cyc_lcl <= (i_addr[31:30]==2'b11);
				o_wb_stb_gbl <= (i_addr[31:30]!=2'b11);
				o_wb_stb_lcl <= (i_addr[31:30]==2'b11);

			end else if (r_cache_miss)
			begin
				state <= `DC_READC;
				o_wb_addr <= { i_ctag, {(LS){1'b0}} };
				non_pipeable_op <= 1'b1;

				cyc <= 1'b1;
				stb <= 1'b1;
				r_wb_cyc_gbl <= 1'b1;
				o_wb_stb_gbl <= 1'b1;
			end else if ((i_pipe_stb)&&(!w_cachable))
			begin // Read non-cachable memory area
				state <= `DC_READS;
				o_wb_addr <= i_addr;
				pipeable_op <= 1'b1;

				cyc <= 1'b1;
				stb <= 1'b1;
				r_wb_cyc_gbl <= (i_addr[31:30]!=2'b11);
				r_wb_cyc_lcl <= (i_addr[31:30]==2'b11);
				o_wb_stb_gbl <= (i_addr[31:30]!=2'b11);
				o_wb_stb_lcl <= (i_addr[31:30]==2'b11);
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

			if(stb)
				c_v[o_wb_addr[(CS-LS-1):0]] <= 1'b0;

			c_wr <= (i_wb_ack);
			c_wdata <= o_wb_data;
			c_waddr <= ((c_wr)?(c_waddr+1'b1):c_waddr);

			c_vtags[o_wb_addr[(CS-LS-1):0]]<= o_wb_addr[(AW-LS-1):0];

			if (((i_wb_ack)&&(end_of_line))||(i_wb_err))
			begin
				state           <= `DC_IDLE;
				non_pipeable_op <= 1'b0;
				cyc <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
				//
				c_v[o_wb_addr[(CS-LS-1):0]] <= i_wb_ack;
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
				pipeable_op <= 1'b0;
			end

			if ((!i_wb_stall)&&(i_pipe_stb))
				o_wb_addr <= i_data;

			c_wr <= 1'b0;

			if (((i_wb_ack)&&(last_ack))||(i_wb_err))
			begin
				state        <= `DC_IDLE;
				cyc          <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
			end
		end else if (state == `DC_WRITE)
		begin
			// c_wr    <= (c_v[])&&(c_tag[])&&(in_cache)&&(stb);
			c_wdata <= o_wb_data;
			c_waddr <= (state == `DC_IDLE)?i_caddr
				: ((c_wr)?(c_waddr+1'b1):c_waddr);

			if ((!i_wb_stall)&&(!i_pipe_stb))
			begin
				stb          <= 1'b0;
				o_wb_stb_gbl <= 1'b0;
				o_wb_stb_lcl <= 1'b0;
				pipeable_op  <= 1'b0;
			end

			wr_cstb  <= (stb)&&(!i_wb_stall)&&(in_cache);

			if ((stb)&&(!i_wb_stall)&&(i_pipe_stb))
				o_wb_addr <= i_addr;
			if ((stb)&&(!i_wb_stall)&&(i_pipe_stb))
				o_wb_data <= i_data;
			
			if (((i_wb_ack)&&(last_ack))||(i_wb_err))
			begin
				state        <= `DC_IDLE;
				cyc          <= 1'b0;
				r_wb_cyc_gbl <= 1'b0;
				r_wb_cyc_lcl <= 1'b0;
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
			c_mem[c_waddr] <= c_wdata;

	//
	// Reads from the cache
	//
	// Some architectures require that all reads be registered.  We
	// accomplish that here.  Whether or not the result of this read is
	// going to be our output will need to be determined with combinatorial
	// logic on the output.
	//
	reg	[31:0]	cached_idata, cached_rdata;
	always @(posedge i_clk)
		cached_idata <= c_mem[i_caddr];

	always @(posedge i_clk)
		cached_rdata <= c_mem[r_caddr];

// o_data can come from one of three places:
// 1. The cache, assuming the data was in the last cache line
// 2. The cache, second clock, assuming the data was in the cache at all
// 3. The cache, after filling the cache
// 4. The wishbone state machine, upon reading the value desired.
	always @(posedge i_clk)
		if (r_svalid)
			o_data <= cached_idata;
		else if ((i_wb_ack)&&(pipeable_op))
			o_data <= i_wb_data;
		else
			o_data <= cached_rdata;
	always @(posedge i_clk)
		o_valid <= (r_svalid)||((i_wb_ack)&&(pipeable_op))
				||(r_dvalid)||(r_rvalid);
	always @(posedge i_clk)
		o_err <= (cyc)&&(i_wb_err);

	assign	o_busy = (state != `DC_IDLE);


	//
	// Handle our auxilliary data lines.
	//
	// These just go into a FIFO upon request, and then get fed back out
	// upon completion of an OP.
	//
	// These are currently designed for handling bursts of writes or
	// non-cachable  reads.
	//
	// A very similar structure will be used once we switch to using an
	// MMU, in order to make certain memory operations are synchronous
	// enough to deal with bus errors.
	//
	reg	[(LGAUX-1):0]	aux_head, aux_tail;
	reg	[(NAUX-1):0]	aux_fifo [0:((1<<LGAUX)-1)];
	initial	aux_head = 0;
	initial	aux_tail = 0;
	always @(posedge i_clk)
	begin
		if ((i_rst)||(i_wb_err))
			aux_head <= 0;
		else if ((i_pipe_stb)&&(!o_busy))
			aux_head <= aux_head + 1'b1;
		aux_fifo[aux_head] <= i_oreg;
	end
	always @(posedge i_clk)
	begin
		if ((i_rst)||(i_wb_err))
			aux_tail <= 0;
		else if (o_valid) // ||(aux_tail[WBIT])&&(no-mmu-error)
			aux_tail <= aux_tail + 1'b1;
		o_wreg <= aux_fifo[aux_tail];
	end

	//
	// We can use our FIFO addresses to pre-calculate when an ACK is going
	// to be the last_noncachable_ack.


	assign o_pipe_stalled=((pipeable_op)&&(i_wb_stall))||(non_pipeable_op);
	// pipeable_op must become zero when stb goes low

	always @(posedge i_clk)
	begin
		lock_gbl <= (i_lock)&&((r_wb_cyc_gbl)||(lock_gbl));
		lock_lcl <= (i_lock)&&((r_wb_cyc_lcl)||(lock_lcl));
	end

	assign	o_wb_cyc_gbl = (r_wb_cyc_gbl)||(lock_gbl);
	assign	o_wb_cyc_lcl = (r_wb_cyc_lcl)||(lock_lcl);
endmodule
