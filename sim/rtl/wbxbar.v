////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	sim/rtl/wbxbar.v
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	A Configurable wishbone cross-bar interconnect, conforming
//		to the WB-B4 pipeline specification, as described on the
//	ZipCPU blog.
//
// Performance:
//	Throughput: One transaction per clock
//	Latency: One clock to get access to an unused channel, another to
//	place the results on the slave bus, and another to return, or a minimum
//	of three clocks.
//
// Usage: To use, you'll need to set NM and NS to the number of masters
//	(input ports) and the number of slaves respectively.  You'll then
//	want to set the addresses for the slaves in the SLAVE_ADDR array,
//	together with the SLAVE_MASK array indicating which SLAVE_ADDRs
//	are valid.  Address and data widths should be adjusted at the same
//	time.
//
//	Voila, you are now set up!
//
//	Now let's fine tune this:
//
//	LGMAXBURST can be set to control the maximum number of outstanding
//	transactions.  An LGMAXBURST of 6 will allow 63 outstanding
//	transactions.
//
//	OPT_TIMEOUT, if set to a non-zero value, is a number of clock periods
//	to wait for a slave to respond.  Should the timeout expire and the
//	slave not respond, a bus error will be returned and the slave will
//	be issued a bus abort signal (CYC will be dropped).
//
//	OPT_STARVATION_TIMEOUT, if set, applies the OPT_TIMEOUT counter to
//	how long a particular master waits for arbitration.  If the master is
//	"starved", a bus error will be returned.
//
//	OPT_DBLBUFFER is used to increase clock speed by registering all
//	outputs.
//
//	OPT_LOWPOWER is an experimental feature that, if set, will cause any
//	unused FFs to be set to zero rather than flopping in the electronic
//	wind, in an effort to minimize transitions over bus wires.  This will
//	cost some extra logic, for ... an uncertain power savings.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	wbxbar #(
		// i_sstall, i_sack, i_sdata, i_serr);
		// {{{
		parameter	NM = 4, NS=8,
		parameter	AW = 32, DW=32,
		parameter	[NS*AW-1:0]	SLAVE_ADDR = {
				{ 3'b111, {(AW-3){1'b0}} },
				{ 3'b110, {(AW-3){1'b0}} },
				{ 3'b101, {(AW-3){1'b0}} },
				{ 3'b100, {(AW-3){1'b0}} },
				{ 3'b011, {(AW-3){1'b0}} },
				{ 3'b010, {(AW-3){1'b0}} },
				{ 4'b0010, {(AW-4){1'b0}} },
				{ 4'b0000, {(AW-4){1'b0}} } },
		parameter	[NS*AW-1:0]	SLAVE_MASK = (NS <= 1) ? 0
			: { {(NS-2){ 3'b111, {(AW-3){1'b0}} }},
				{(2){ 4'b1111, {(AW-4){1'b0}} }} },
		//
		// LGMAXBURST is the log_2 of the length of the longest burst
		// that might be seen.  It's used to set the size of the
		// internal counters that are used to make certain that the
		// cross bar doesn't switch while still waiting on a response.
		parameter	LGMAXBURST=6,
		//
		// OPT_TIMEOUT is used to help recover from a misbehaving slave.
		// If set, this value will determine the number of clock cycles
		// to wait for a misbehaving slave before returning a bus error.
		// Alternatively, if set to zero, this functionality will be
		// removed.
		parameter	OPT_TIMEOUT = 0, // 1023;
		//
		// If OPT_TIMEOUT is set, then OPT_STARVATION_TIMEOUT may also
		// be set.  The starvation timeout adds to the bus error timeout
		// generation the possibility that a master will wait
		// OPT_TIMEOUT counts without receiving the bus.  This may be
		// the case, for example, if one bus master is consuming a
		// peripheral to such an extent that there's no time/room for
		// another bus master to use it.  In that case, when the timeout
		// runs out, the waiting bus master will be given a bus error.
		parameter [0:0]	OPT_STARVATION_TIMEOUT = 1'b0
						&& (OPT_TIMEOUT > 0),
		//
		// OPT_DBLBUFFER is used to register all of the outputs, and
		// thus avoid adding additional combinational latency through
		// the core that might require a slower clock speed.
		parameter [0:0]	OPT_DBLBUFFER = 1'b0,
		//
		// OPT_LOWPOWER adds logic to try to force unused values to
		// zero, rather than to allow a variety of logic optimizations
		// that could be used to reduce the logic count of the device.
		// Hence, OPT_LOWPOWER will use more logic, but it won't drive
		// bus wires unless there's a value to drive onto them.
		parameter [0:0]	OPT_LOWPOWER = 1'b1
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		// Here are the bus inputs from each of the WB bus masters
		input	wire	[NM-1:0]	i_mcyc, i_mstb, i_mwe,
		input	wire	[NM*AW-1:0]	i_maddr,
		input	wire	[NM*DW-1:0]	i_mdata,
		input	wire	[NM*DW/8-1:0]	i_msel,
		//
		// .... and their return data
		output	wire	[NM-1:0]	o_mstall,
		output	wire	[NM-1:0]	o_mack,
		output	reg	[NM*DW-1:0]	o_mdata,
		output	wire	[NM-1:0]	o_merr,
		//
		//
		// Here are the output ports, used to control each of the
		// various slave ports that we are connected to
		output	reg	[NS-1:0]	o_scyc, o_sstb, o_swe,
		output	reg	[NS*AW-1:0]	o_saddr,
		output	reg	[NS*DW-1:0]	o_sdata,
		output	reg	[NS*DW/8-1:0]	o_ssel,
		//
		// ... and their return data back to us.
		input	wire	[NS-1:0]	i_sstall, i_sack,
		input	wire	[NS*DW-1:0]	i_sdata,
		input	wire	[NS-1:0]	i_serr
		// }}}
	);
	//
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Register declarations
	// {{{
	//
	// TIMEOUT_WIDTH is the number of bits in counter used to check
	// on a timeout.
	localparam	TIMEOUT_WIDTH = $clog2(OPT_TIMEOUT);
	//
	// LGNM is the log (base two) of the number of bus masters
	// connecting to this crossbar
	localparam	LGNM = (NM>1) ? $clog2(NM) : 1;
	//
	// LGNS is the log (base two) of the number of slaves plus one
	// come out of the system.  The extra "plus one" is used for a
	// pseudo slave representing the case where the given address
	// doesn't connect to any of the slaves.  This address will
	// generate a bus error.
	localparam	LGNS = $clog2(NS+1);
	// At one time I used o_macc and o_sacc to put into the outgoing
	// trace file, just enough logic to tell me if a transaction was
	// taking place on the given clock.
	//
	// assign	o_macc = (i_mstb & ~o_mstall);
	// assign	o_sacc = (o_sstb & ~i_sstall);
	//
	// These definitions work with Veri1ator, just not with Yosys
	// reg	[NM-1:0][NS:0]		request;
	// reg	[NM-1:0][NS-1:0]	requested;
	// reg	[NM-1:0][NS:0]		grant;
	//
	// These definitions work with both
	wire	[NS:0]			request		[0:NM-1];
	reg	[NS-1:0]		requested	[0:NM-1];
	reg	[NS:0]			grant		[0:NM-1];
	reg	[NM-1:0]		mgrant;
	reg	[NS-1:0]		sgrant;

	// Verilator lint_off UNUSED
	wire	[LGMAXBURST-1:0]	w_mpending [0:NM-1];
	// Verilator lint_on  UNUSED
	reg	[NM-1:0]		mfull, mnearfull, mempty;
	wire	[NM-1:0]		timed_out;

	localparam	NMFULL = (NM > 1) ? (1<<LGNM) : 1;
	localparam	NSFULL = (1<<LGNS);

	wire	[LGNS-1:0]	mindex		[0:NMFULL-1];
	wire	[LGNM-1:0]	sindex		[0:NSFULL-1];

	wire	[NMFULL-1:0]	m_cyc;
	wire	[NMFULL-1:0]	m_stb;
	wire	[NMFULL-1:0]	m_we;
	wire	[AW-1:0]	m_addr		[0:NMFULL-1];
	wire	[DW-1:0]	m_data		[0:NMFULL-1];
	wire	[DW/8-1:0]	m_sel		[0:NMFULL-1];
	reg	[NM-1:0]	m_stall;
	//
	wire	[NSFULL-1:0]	s_stall;
	wire	[DW-1:0]	s_data		[0:NSFULL-1];
	wire	[NSFULL-1:0]	s_ack;
	wire	[NSFULL-1:0]	s_err;
	wire	[NM-1:0]	dcd_stb;

	localparam [0:0]	OPT_BUFFER_DECODER=(NS != 1 || SLAVE_MASK != 0);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming signal arbitration
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	genvar	N, M;
	integer	iN, iM;
	generate for(N=0; N<NM; N=N+1)
	begin : DECODE_REQUEST
		// {{{
		// Register declarations
		// {{{
		wire			skd_stb, skd_stall;
		wire			skd_we;
		wire	[AW-1:0]	skd_addr;
		wire	[DW-1:0]	skd_data;
		wire	[DW/8-1:0]	skd_sel;
		wire	[NS:0]		decoded;
		wire			iskd_ready;
		// }}}

		skidbuffer #(
			// {{{
			// Can't run OPT_LOWPOWER here, less we mess up the
			// consistency in skd_we following
			//
			// .OPT_LOWPOWER(OPT_LOWPOWER),
			.DW(1+AW+DW+DW/8),
`ifdef	FORMAL
			.OPT_PASSTHROUGH(1),
`endif
			.OPT_OUTREG(0)
			// }}}
		) iskid (
			// {{{
			.i_clk(i_clk),
			.i_reset(i_reset || !i_mcyc[N]),
			.i_valid(i_mstb[N]), .o_ready(iskd_ready),
			.i_data({ i_mwe[N], i_maddr[N*AW +: AW],
					i_mdata[N*DW +: DW],
					i_msel[N*DW/8 +: DW/8] }),
			.o_valid(skd_stb), .i_ready(!skd_stall),
				.o_data({ skd_we, skd_addr, skd_data, skd_sel })
			// }}}
		);

		assign	o_mstall[N] = !iskd_ready;

		addrdecode #(
			// {{{
			// Can't run OPT_LOWPOWER here, less we mess up the
			// consistency in m_we following
			//
			// .OPT_LOWPOWER(OPT_LOWPOWER),
			.NS(NS), .AW(AW), .DW(DW+DW/8+1),
			.SLAVE_ADDR(SLAVE_ADDR),
			.SLAVE_MASK(SLAVE_MASK),
			.OPT_REGISTERED(OPT_BUFFER_DECODER)
			// }}}
		) adcd(
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_valid(skd_stb && i_mcyc[N]), .o_stall(skd_stall),
				.i_addr(skd_addr),
				.i_data({ skd_we, skd_data, skd_sel }),
			.o_valid(dcd_stb[N]), .i_stall(m_stall[N]&&i_mcyc[N]),
			.o_decode(decoded), .o_addr(m_addr[N]),
				.o_data({ m_we[N], m_data[N], m_sel[N] })
			// }}}
		);

		assign	request[N] = (m_cyc[N] && dcd_stb[N]) ? decoded : 0;

		assign	m_cyc[N] = i_mcyc[N];
		assign	m_stb[N] = i_mcyc[N] && dcd_stb[N] && !mfull[N];
		// }}}
	end for(N=NM; N<NMFULL; N=N+1)
	begin : UNUSED_MASTER_SIGNALS
		// {{{
		// in case NM isn't one less than a power of two, complete
		// the set
		assign	m_cyc[N] = 0;
		assign	m_stb[N] = 0;

		assign	m_we[N]   = 0;
		assign	m_addr[N] = 0;
		assign	m_data[N] = 0;
		assign	m_sel[N]  = 0;
		// }}}
	end endgenerate

	// requested
	// {{{
	always @(*)
	begin
		for(iM=0; iM<NS; iM=iM+1)
		begin
			// For each slave
			requested[0][iM] = 0;
			for(iN=1; iN<NM; iN=iN+1)
			begin
				// This slave has been requested if a prior
				// master has requested it
				//
				// This includes any master before the last one
				requested[iN][iM] = requested[iN-1][iM];
				//
				// As well as if the last master has requested
				// this slave.  Only count this request, though,
				// if this master could act upon it.
				if (request[iN-1][iM] &&
					(grant[iN-1][iM]
					|| (!mgrant[iN-1]||mempty[iN-1])))
					requested[iN][iM] = 1;
			end
		end
	end
	// }}}

	generate for(M=0; M<NS; M=M+1)
	begin : SLAVE_GRANT
		// {{{
`define	REGISTERED_SGRANT
`ifdef	REGISTERED_SGRANT
		// {{{
		reg	drop_sgrant;

		// drop_sgrant
		// {{{
		always @(*)
		begin
			drop_sgrant = !m_cyc[sindex[M]];
			if (!request[sindex[M]][M] && m_stb[sindex[M]]
				&& mempty[sindex[M]])
				drop_sgrant = 1;
			if (!sgrant[M])
				drop_sgrant = 0;
			if (i_reset)
				drop_sgrant = 1;
		end
		// }}}

		// sgrant
		// {{{
		initial	sgrant[M] = 0;
		always @(posedge i_clk)
		begin
			sgrant[M] <= sgrant[M];
			for(iN=0; iN<NM; iN=iN+1)
			if (request[iN][M] && (!mgrant[iN] || mempty[iN]))
				sgrant[M] <= 1;
			if (drop_sgrant)
				sgrant[M] <= 0;
		end
		// }}}
		// }}}
`else
		// {{{
		// sgrant
		// {{{
		always @(*)
		begin
			sgrant[M] = 0;
			for(iN=0; iN<NM; iN=iN+1)
			if (grant[iN][M])
				sgrant[M] = 1;
		end
		// }}}
		// }}}
`endif

		assign	s_data[M]  = i_sdata[M*DW +: DW];
		assign	s_stall[M] = o_sstb[M] && i_sstall[M];
		assign	s_ack[M]   = o_scyc[M] && i_sack[M];
		assign	s_err[M]   = o_scyc[M] && i_serr[M];

		// }}}
	end for(M=NS; M<NSFULL; M=M+1)
	begin : UNUSED_SLAVE_SIGNALS
		// {{{
		assign	s_data[M]  = 0;
		assign	s_stall[M] = 1;
		assign	s_ack[M]   = 0;
		assign	s_err[M]   = 1;
		// }}}
	end endgenerate

	//
	// Arbitrate among masters to determine who gets to access a given
	// channel
	generate for(N=0; N<NM; N=N+1)
	begin : ARBITRATE_REQUESTS
		// {{{

		// Register declarations
		// {{{
		wire	[NS:0]		regrant;
		wire	[LGNS-1:0]	reindex;

		// This is done using a couple of variables.
		//
		// request[N][M]
		//	This is true if master N is requesting to access slave
		//	M.  It is combinatorial, so it will be true if the
		//	request is being made on the current clock.
		//
		// requested[N][M]
		//	True if some other master, prior to N, has requested
		//	channel M.  This creates a basic priority arbiter,
		//	such that lower numbered masters have access before
		//	a greater numbered master
		//
		// grant[N][M]
		//	True if a grant has been made for master N to access
		//	slave channel M
		//
		// mgrant[N]
		//	True if master N has been granted access to some slave
		//	channel, any channel.
		//
		// mindex[N]
		//	This is the number of the slave channel that master
		//	N has been given access to
		//
		// sgrant[M]
		//	True if there exists some master, N, that has been
		// 	granted access to this slave, hence grant[N][M] must
		//	also be true
		//
		// sindex[M]
		//	This is the index of the master that has access to
		//	slave M, assuming sgrant[M].  Hence, if sgrant[M]
		//	then grant[sindex[M]][M] must be true
		//
		reg	stay_on_channel;
		reg	requested_channel_is_available;
		// }}}

		// stay_on_channel
		// {{{
		always @(*)
		begin
			stay_on_channel = |(request[N] & grant[N]);

			if (mgrant[N] && !mempty[N])
				stay_on_channel = 1;
		end
		// }}}

		// requested_channel_is_available
		// {{{
		always @(*)
		begin
			requested_channel_is_available =
			|(request[N][NS-1:0]& ~sgrant & ~requested[N][NS-1:0]);

			if (request[N][NS])
				requested_channel_is_available = 1;

			if (NM < 2)
				requested_channel_is_available = m_stb[N];
		end
		// }}}

		// grant, mgrant
		// {{{
		initial	grant[N] = 0;
		initial	mgrant[N] = 0;
		always @(posedge i_clk)
		if (i_reset || !i_mcyc[N])
		begin
			grant[N] <= 0;
			mgrant[N] <= 0;
		end else if (!stay_on_channel)
		begin
			if (requested_channel_is_available)
			begin
				mgrant[N] <= 1'b1;
				grant[N] <= request[N];
			end else if (m_stb[N])
			begin
				mgrant[N] <= 1'b0;
				grant[N]  <= 0;
			end
		end
		// }}}

		if (NS == 1)
		begin : MINDEX_ONE_SLAVE
			// {{{
			assign	mindex[N] = 0;
			assign	regrant = 0;
			assign	reindex = 0;
			// }}}
		end else begin : MINDEX_MULTIPLE_SLAVES
			// {{{
			reg	[LGNS-1:0]	r_mindex;

`define	NEW_MINDEX_CODE
`ifdef	NEW_MINDEX_CODE
			// {{{
			reg	[NS:0]		r_regrant;
			reg	[LGNS-1:0]	r_reindex;

			// r_regrant
			// {{{
			always @(*)
			begin
				r_regrant = 0;
				for(iM=0; iM<NS; iM=iM+1)
				begin
					if (grant[N][iM])
						// Maintain any open channels
						r_regrant[iM] = 1'b1;
					else if (!sgrant[iM]&&!requested[N][iM])
						r_regrant[iM] = 1'b1;

					if (!request[N][iM])
						r_regrant[iM] = 1'b0;
				end

				if (grant[N][NS])
					r_regrant[NS] = 1;
				if (!request[N][NS])
					r_regrant[NS] = 0;

				if (mgrant[N] && !mempty[N])
					r_regrant = 0;
			end
			// }}}

			// r_reindex
			// {{{
			// Verilator lint_off BLKSEQ
			always @(r_regrant, regrant)
			begin
				r_reindex = 0;
				for(iM=0; iM<=NS; iM=iM+1)
				if (r_regrant[iM])
					r_reindex = r_reindex | iM[LGNS-1:0];
				if (regrant == 0)
					r_reindex = r_mindex;
			end
			// Verilator lint_on  BLKSEQ
			// }}}

			always @(posedge i_clk)
				r_mindex <= reindex;

			assign	reindex = r_reindex;
			assign	regrant = r_regrant;
			// }}}
`else
			// {{{
			always @(posedge i_clk)
			if (!mgrant[N] || mempty[N])
			begin

				for(iM=0; iM<NS; iM=iM+1)
				begin
					if (request[N][iM] && grant[N][iM])
					begin
						// Maintain any open channels
						r_mindex <= iM;
					end else if (request[N][iM]
							&& !sgrant[iM]
							&& !requested[N][iM])
					begin
						// Open a new channel
						// if necessary
						r_mindex <= iM;
					end
				end
			end

			// }}}
`endif // NEW_MINDEX_CODE
			assign	mindex[N] = r_mindex;
			// }}}
		end
		// }}}
	end for (N=NM; N<NMFULL; N=N+1)
	begin : UNUSED_MINDEXES
		// {{{
		assign	mindex[N] = 0;
		// }}}
	end endgenerate

	// Calculate sindex.  sindex[M] (indexed by slave ID)
	// references the master controlling this slave.  This makes for
	// faster/cheaper logic on the return path, since we can now use
	// a fully populated LUT rather than a priority based return scheme
	generate for(M=0; M<NS; M=M+1)
	begin : GEN_SINDEX
		// {{{
		if (NM <= 1)
		begin : SINDEX_SINGLE_MASTER
			// {{{
			// If there will only ever be one master, then we
			// can assume all slave indexes point to that master
			assign	sindex[M] = 0;
			// }}}
		end else begin : SINDEX_MORE_THAN_ONE_MASTER
			// {{{
			reg	[LGNM-1:0]	r_sindex;
`define	NEW_SINDEX_CODE
`ifdef	NEW_SINDEX_CODE
			// {{{
			reg	[NM-1:0]	regrant;
			reg	[LGNM-1:0]	reindex;

			always @(*)
			begin
				regrant = 0;
				for (iN=0; iN<NM; iN=iN+1)
				begin
					// Each bit depends upon 6 inputs, so
					// one 6-LUT should be sufficient
					if (grant[iN][M])
						regrant[iN] = 1;
					else if (!sgrant[M]&& !requested[iN][M])
						regrant[iN] = 1;

					if (!request[iN][M])
						regrant[iN] = 0;
					if (mgrant[iN] && !mempty[iN])
						regrant[iN] = 0;
				end
			end

			always @(*)
			begin
				reindex = 0;
				// Each bit in reindex depends upon all of the
				// bits in regrant--should still be one LUT
				// per bit though
				if (regrant == 0)
					reindex = sindex[M];
				else for(iN=0; iN<NM; iN=iN+1)
					if (regrant[iN])
						reindex = reindex | iN[LGNM-1:0];
			end

			always @(posedge i_clk)
				r_sindex <= reindex;

			assign	sindex[M] = r_sindex;
			// }}}
`else
			// {{{
			always @(posedge i_clk)
			for (iN=0; iN<NM; iN=iN+1)
			begin
				if (!mgrant[iN] || mempty[iN])
				begin
					if (request[iN][M] && grant[iN][M])
						r_sindex <= iN;
					else if (request[iN][M] && !sgrant[M]
							&& !requested[iN][M])
						r_sindex <= iN;
				end
			end

			assign	sindex[M] = r_sindex;
			// }}}
`endif
			// }}}
		end
		// }}}
	end for(M=NS; M<NSFULL; M=M+1)
	begin : UNUSED_SINDEXES
		// {{{
		// Assign the unused slave indexes to zero
		//
		// Remember, to full out a full 2^something set of slaves,
		// we may have more slave indexes than we actually have slaves

		assign	sindex[M] = 0;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assign outputs to the slaves
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Part one
	//
	// In this part, we assign the difficult outputs: o_scyc and o_sstb
	generate for(M=0; M<NS; M=M+1)
	begin : GEN_CYC_STB
		// {{{
		initial	o_scyc[M] = 0;
		initial	o_sstb[M] = 0;
		always @(posedge i_clk)
		begin
			if (sgrant[M])
			begin

				if (!i_mcyc[sindex[M]])
				begin
					o_scyc[M] <= 1'b0;
					o_sstb[M] <= 1'b0;
				end else begin
					o_scyc[M] <= 1'b1;

					if (!o_sstb[M] || !s_stall[M])
						o_sstb[M]<=request[sindex[M]][M]
						  && !mfull[sindex[M]];
				end
			end else begin
				o_scyc[M]  <= 1'b0;
				o_sstb[M]  <= 1'b0;
			end

			if (i_reset || s_err[M])
			begin
				o_scyc[M] <= 1'b0;
				o_sstb[M] <= 1'b0;
			end
		end
		// }}}
	end endgenerate

	//
	// Part two
	//
	// These are the easy(er) outputs, since there are fewer properties
	// riding on them
	generate if ((NM == 1) && (!OPT_LOWPOWER))
	begin : ONE_MASTER
		// {{{
		reg			r_swe;
		reg	[AW-1:0]	r_saddr;
		reg	[DW-1:0]	r_sdata;
		reg	[DW/8-1:0]	r_ssel;

		//
		// This is the low logic version of our bus data outputs.
		// It only works if we only have one master.
		//
		// The basic idea here is that we share all of our bus outputs
		// between all of the various slaves.  Since we only have one
		// bus master, this works.
		//
		always @(posedge i_clk)
		begin
			r_swe   <= o_swe[0];
			r_saddr <= o_saddr[0+:AW];
			r_sdata <= o_sdata[0+:DW];
			r_ssel  <=o_ssel[0+:DW/8];

			// Verilator lint_off WIDTH
			if (sgrant[mindex[0]] && !s_stall[mindex[0]])
			// Verilator lint_on  WIDTH
			begin
				r_swe   <= m_we[0];
				r_saddr <= m_addr[0];
				r_sdata <= m_data[0];
				r_ssel  <= m_sel[0];
			end
		end

		//
		// The original version set o_s*[0] above, and then
		// combinatorially the rest of o_s* here below.  That broke
		// Veri1ator.  Hence, we're using r_s* and setting all of o_s*
		// here.
		for(M=0; M<NS; M=M+1)
		begin : FOREACH_SLAVE_PORT
			always @(*)
			begin
				o_swe[M]            = r_swe;
				o_saddr[M*AW +: AW] = r_saddr[AW-1:0];
				o_sdata[M*DW +: DW] = r_sdata[DW-1:0];
				o_ssel[M*DW/8+:DW/8]= r_ssel[DW/8-1:0];
			end
		end
		// }}}
	end else begin : J
	for(M=0; M<NS; M=M+1)
	begin : GEN_DOWNSTREAM
		// {{{
		always @(posedge i_clk)
		begin
			if (OPT_LOWPOWER && !sgrant[M])
			begin
				o_swe[M]              <= 1'b0;
				o_saddr[M*AW   +: AW] <= 0;
				o_sdata[M*DW   +: DW] <= 0;
				o_ssel[M*(DW/8)+:DW/8]<= 0;
			end else if (!s_stall[M]) begin
				o_swe[M]              <= m_we[sindex[M]];
				o_saddr[M*AW   +: AW] <= m_addr[sindex[M]];
				if (OPT_LOWPOWER && !m_we[sindex[M]])
					o_sdata[M*DW   +: DW] <= 0;
				else
					o_sdata[M*DW   +: DW] <= m_data[sindex[M]];
				o_ssel[M*(DW/8)+:DW/8]<= m_sel[sindex[M]];
			end

		end
		// }}}
	end end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assign return values to the masters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (OPT_DBLBUFFER)
	begin : DOUBLE_BUFFERRED_STALL
		// {{{
		reg	[NM-1:0]	r_mack, r_merr;

		for(N=0; N<NM; N=N+1)
		begin : FOREACH_MASTER_PORT
			// m_stall isn't buffered, since it depends upon
			// the already existing buffer within the address
			// decoder
			always @(*)
			begin
				if (grant[N][NS])
					m_stall[N] = 1;
				else if (mgrant[N] && request[N][mindex[N]])
					m_stall[N] = mfull[N] || s_stall[mindex[N]];
				else
					m_stall[N] = m_stb[N];

				if (o_merr[N])
					m_stall[N] = 0;
			end

			initial	r_mack[N]   = 0;
			initial	r_merr[N]   = 0;
			always @(posedge i_clk)
			begin
				// Verilator lint_off WIDTH
				iM = mindex[N];
				// Verilator lint_on  WIDTH
				r_mack[N]   <= mgrant[N] && s_ack[mindex[N]];
				r_merr[N]   <= mgrant[N] && s_err[mindex[N]];
				if (OPT_LOWPOWER && !mgrant[N])
					o_mdata[N*DW +: DW] <= 0;
				else
					o_mdata[N*DW +: DW] <= s_data[mindex[N]];

				if (grant[N][NS]||(timed_out[N] && !o_mack[N]))
				begin
					r_mack[N]   <= 1'b0;
					r_merr[N]   <= !o_merr[N];
				end

				if (i_reset || !i_mcyc[N] || o_merr[N])
				begin
					r_mack[N]   <= 1'b0;
					r_merr[N]   <= 1'b0;
				end
			end

			assign	o_mack[N] = r_mack[N];

			assign	o_merr[N] = (!OPT_STARVATION_TIMEOUT || i_mcyc[N]) && r_merr[N];

		end
		// }}}
	end else if (NS == 1) // && !OPT_DBLBUFFER
	begin : SINGLE_SLAVE
		// {{{
		for(N=0; N<NM; N=N+1)
		begin : FOREACH_MASTER_PORT
			reg	r_mack, r_merr;

			always @(*)
			begin
				m_stall[N] = !mgrant[N] || s_stall[0]
					|| (m_stb[N] && !request[N][0]);
				r_mack     =  mgrant[N] && i_sack[0];
				r_merr     =  mgrant[N] && i_serr[0];
				o_mdata[N*DW +: DW]  = (!mgrant[N] && OPT_LOWPOWER)
					? 0 : i_sdata;

				if (mfull[N])
					m_stall[N] = 1'b1;

				if (timed_out[N] && !r_mack)
				begin
					m_stall[N] = 1'b0;
					r_mack     = 1'b0;
					r_merr     = 1'b1;
				end

				if (grant[N][NS] && m_stb[N])
				begin
					m_stall[N] = 1'b0;
					r_mack     = 1'b0;
					r_merr     = 1'b1;
				end

				if (!m_cyc[N])
				begin
					r_mack = 1'b0;
					r_merr = 1'b0;
				end
			end

			assign	o_mack[N] = r_mack;
			assign	o_merr[N] = r_merr;
		end
		// }}}
	end else begin : SINGLE_BUFFER_STALL
		// {{{
		for(N=0; N<NM; N=N+1)
		begin : FOREACH_MASTER_PORT
			// initial	o_mstall[N] = 0;
			// initial	o_mack[N]   = 0;
			reg	r_mack, r_merr;

			always @(*)
			begin
				m_stall[N] = 1;
				r_mack     = mgrant[N] && s_ack[mindex[N]];
				r_merr     = mgrant[N] && s_err[mindex[N]];
				if (OPT_LOWPOWER && !mgrant[N])
					o_mdata[N*DW +: DW] = 0;
				else
					o_mdata[N*DW +: DW] = s_data[mindex[N]];

				if (mgrant[N])
					// Possibly lower the stall signal
					m_stall[N] = s_stall[mindex[N]]
					    || !request[N][mindex[N]];

				if (mfull[N])
					m_stall[N] = 1'b1;

				if (grant[N][NS] ||(timed_out[N] && !r_mack))
				begin
					m_stall[N] = 1'b0;
					r_mack     = 1'b0;
					r_merr     = 1'b1;
				end

				if (!m_cyc[N])
				begin
					r_mack    = 1'b0;
					r_merr     = 1'b0;
				end
			end

			assign	o_mack[N] = r_mack;
			assign	o_merr[N] = r_merr;
		end
		// }}}
	end endgenerate

	//
	// Count the pending transactions per master
	generate for(N=0; N<NM; N=N+1)
	begin : COUNT_PENDING_TRANSACTIONS
		// {{{
		reg	[LGMAXBURST-1:0]	lclpending;
		initial	lclpending  = 0;
		initial	mempty[N]    = 1;
		initial	mnearfull[N] = 0;
		initial	mfull[N]     = 0;
		always @(posedge i_clk)
		if (i_reset || !i_mcyc[N] || o_merr[N])
		begin
			lclpending <= 0;
			mfull[N]    <= 0;
			mempty[N]   <= 1'b1;
			mnearfull[N]<= 0;
		end else case({ (m_stb[N] && !m_stall[N]), o_mack[N] })
		2'b01: begin
			lclpending <= lclpending - 1'b1;
			mnearfull[N]<= mfull[N];
			mfull[N]    <= 1'b0;
			mempty[N]   <= (lclpending == 1);
			end
		2'b10: begin
			lclpending <= lclpending + 1'b1;
			mnearfull[N]<= (&lclpending[LGMAXBURST-1:2])&&(lclpending[1:0] != 0);
			mfull[N]    <= mnearfull[N];
			mempty[N]   <= 1'b0;
			end
		default: begin end
		endcase

		assign w_mpending[N] = lclpending;
		// }}}
	end endgenerate

	generate if (OPT_TIMEOUT > 0)
	begin : CHECK_TIMEOUT
		// {{{
		for(N=0; N<NM; N=N+1)
		begin : FOREACH_MASTER_PORT

			reg	[TIMEOUT_WIDTH-1:0]	deadlock_timer;
			reg				r_timed_out;

			initial	deadlock_timer = OPT_TIMEOUT;
			initial	r_timed_out = 0;
			always @(posedge i_clk)
			if (i_reset || !i_mcyc[N]
					||((w_mpending[N] == 0) && !m_stb[N])
					||(m_stb[N] && !m_stall[N])
					||(o_mack[N] || o_merr[N])
					||(!OPT_STARVATION_TIMEOUT&&!mgrant[N]))
			begin
				deadlock_timer <= OPT_TIMEOUT;
				r_timed_out <= 0;
			end else if (deadlock_timer > 0)
			begin
				deadlock_timer <= deadlock_timer - 1;
				r_timed_out <= (deadlock_timer <= 1);
			end

			assign	timed_out[N] = r_timed_out;
		end
		// }}}
	end else begin : NO_TIMEOUT
		// {{{
		assign	timed_out = 0;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Parameter consistency check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	begin : PARAMETER_CONSISTENCY_CHECK
		// {{{
		if (NM == 0)
		begin
			$display("ERROR: At least one master must be defined");
			$stop;
		end

		if (NS == 0)
		begin
			$display("ERROR: At least one slave must be defined");
			$stop;
		end

		if (OPT_STARVATION_TIMEOUT != 0 && OPT_TIMEOUT == 0)
		begin
			$display("ERROR: The starvation timeout is implemented as part of the regular timeout");
			$display("  Without a timeout, the starvation timeout will not work");
			$stop;
		end
		// }}}
	end
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used to verify the core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Register declarations
	// {{{
	localparam	F_MAX_DELAY = 4;
	localparam	F_LGDEPTH = LGMAXBURST;
	//
	reg			f_past_valid;
	//
	// Our bus checker keeps track of the number of requests,
	// acknowledgments, and the number of outstanding transactions on
	// every channel, both the masters driving us
	wire	[F_LGDEPTH-1:0]	f_mreqs		[0:NM-1];
	wire	[F_LGDEPTH-1:0]	f_macks		[0:NM-1];
	wire	[F_LGDEPTH-1:0]	f_moutstanding	[0:NM-1];
	//
	// as well as the slaves that we drive ourselves
	wire	[F_LGDEPTH-1:0]	f_sreqs		[0:NS-1];
	wire	[F_LGDEPTH-1:0]	f_sacks		[0:NS-1];
	wire	[F_LGDEPTH-1:0]	f_soutstanding	[0:NS-1];
	// }}}

	initial	assert(!OPT_STARVATION_TIMEOUT || OPT_TIMEOUT > 0);

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid = 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	generate for(N=0; N<NM; N=N+1)
	begin : GRANT_CHECKING
		// {{{
		reg	checkgrant;

		always @(*)
		if (f_past_valid)
		for(iN=N+1; iN<NM; iN=iN+1)
			// Can't grant the same channel to two separate
			// masters.  This applies to all but the error or
			// no-slave-selected channel
			assert((grant[N][NS-1:0] & grant[iN][NS-1:0])==0);

		for(M=1; M<=NS; M=M+1)
		begin
			// Can't grant two channels to the same master
			always @(*)
			if (f_past_valid && grant[N][M])
				assert(grant[N][M-1:0] == 0);
		end


		always @(*)
		if (&w_mpending[N])
			assert(o_merr[N] || m_stall[N]);

		always @(*)
		if (f_past_valid)
		begin
			checkgrant = 0;
			for(iM=0; iM<NS; iM=iM+1)
				if (grant[N][iM])
					checkgrant = 1;
			if (grant[N][NS])
				checkgrant = 1;

			assert(checkgrant == mgrant[N]);
		end
		// }}}
	end endgenerate

	// Double check the grant mechanism and its dependent variables
	generate for(N=0; N<NM; N=N+1)
	begin : CHECK_GRANTS
		// {{{
		for(M=0; M<NS; M=M+1)
		begin
			always @(*)
			if ((f_past_valid)&&grant[N][M])
			begin
				assert(mgrant[N]);
				assert(mindex[N] == M);
				assert(sgrant[M]);
				assert(sindex[M] == N);
			end
		end
		// }}}
	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin : CHECK_SGRANT
		// {{{
		reg	f_sgrant;

		always @(*)
		if (sgrant[M])
			assert(grant[sindex[M]][M]);

		always @(*)
		begin
			f_sgrant = 0;
			for(iN=0; iN<NM; iN=iN+1)
			if (grant[iN][M])
				f_sgrant = 1;
		end

		always @(*)
			assert(sgrant[M] == f_sgrant);
		// }}}
	end endgenerate

	// Double check the timeout flags for consistency
	generate for(N=0; N<NM; N=N+1)
	begin : F_CHECK_TIMEOUT
		// {{{
		always @(*)
		if (f_past_valid)
		begin
			assert(mempty[N] == (w_mpending[N] == 0));
			assert(mnearfull[N]==(&w_mpending[N][LGMAXBURST-1:1]));
			assert(mfull[N] == (&w_mpending[N]));
		end
		// }}}
	end endgenerate

`ifdef	VERIFIC
	// {{{
	// The Verific parser is currently broken, and doesn't allow
	// initial assumes or asserts.  The following lines get us around that
	//
	always @(*)
	if (!f_past_valid)
		assume(sgrant == 0);

	generate for(M=0; M<NS; M=M+1)
	begin
		always @(*)
		if (!f_past_valid)
		begin
			assume(o_scyc[M] == 0);
			assume(o_sstb[M] == 0);
			assume(sgrant[M] == 0);
		end
	end endgenerate

	generate for(N=0; N<NM; N=N+1)
	begin
		always @(*)
		if (!f_past_valid)
		begin
			assume(grant[N] == 0);
			assume(mgrant[N] == 0);
		end
	end endgenerate
	// }}}
`endif

	////////////////////////////////////////////////////////////////////////
	//
	// BUS CHECK
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Verify that every channel, whether master or slave, follows the rules
	// of the WB road.
	//
	generate for(N=0; N<NM; N=N+1)
	begin : WB_SLAVE_CHECK
		// {{{
		fwb_slave #(
			.AW(AW), .DW(DW),
			.F_LGDEPTH(LGMAXBURST),
			.F_MAX_ACK_DELAY(0),
			.F_MAX_STALL(0)
			) slvi(i_clk, i_reset,
				i_mcyc[N], i_mstb[N], i_mwe[N],
				i_maddr[N*AW +: AW], i_mdata[N*DW +: DW],
				i_msel[N*(DW/8) +: (DW/8)],
			o_mack[N], o_mstall[N], o_mdata[N*DW +: DW], o_merr[N],
			f_mreqs[N], f_macks[N], f_moutstanding[N]);

		always @(*)
		if ((f_past_valid)&&(grant[N][NS]))
			assert(f_moutstanding[N] <= 1);

		always @(*)
		if (f_past_valid && grant[N][NS] && i_mcyc[N])
			assert(m_stall[N] || o_merr[N]);

		always @(posedge i_clk)
		if (f_past_valid && $past(!i_reset && i_mstb[N] && o_mstall[N]))
			assume($stable(i_mdata[N*DW +: DW]));
		// }}}
	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin : WB_MASTER_CHECK
		// {{{
		fwb_master #(
			.AW(AW), .DW(DW),
			.F_LGDEPTH(LGMAXBURST),
			.F_MAX_ACK_DELAY(F_MAX_DELAY),
			.F_MAX_STALL(2)
			) mstri(i_clk, i_reset,
				o_scyc[M], o_sstb[M], o_swe[M],
				o_saddr[M*AW +: AW], o_sdata[M*DW +: DW],
				o_ssel[M*(DW/8) +: (DW/8)],
			i_sack[M], i_sstall[M], s_data[M], i_serr[M],
			f_sreqs[M], f_sacks[M], f_soutstanding[M]);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Correlate outstanding numbers
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate for(N=0; N<NM; N=N+1)
	begin : CHECK_OUTSTANDING
		// {{{
		always @(*)
		if (mfull[N])
			assert(m_stall[N]);

		always @(posedge i_clk)
		if (i_mcyc[N])
			assert(f_moutstanding[N] == w_mpending[N]
				+((OPT_BUFFER_DECODER & dcd_stb[N]) ? 1:0));

		reg	[LGMAXBURST:0]	n_outstanding;
		always @(*)
		if (i_mcyc[N])
			assert(f_moutstanding[N] >=
				((OPT_BUFFER_DECODER && dcd_stb[N]) ? 1:0)
				+ (o_mack[N] && OPT_DBLBUFFER) ? 1:0);

		always @(*)
			n_outstanding = f_moutstanding[N]
				- ((OPT_BUFFER_DECODER && dcd_stb[N]) ? 1:0)
				- ((o_mack[N] && OPT_DBLBUFFER) ? 1:0);

		always @(posedge i_clk)
		if (i_mcyc[N] && !mgrant[N] && !o_merr[N])
			assert(f_moutstanding[N]
				== ((OPT_BUFFER_DECODER & dcd_stb[N]) ? 1:0));

		else if (i_mcyc[N] && mgrant[N] && !i_reset)
		for(iM=0; iM<NS; iM=iM+1)
		if (grant[N][iM] && o_scyc[iM] && !i_serr[iM] && !o_merr[N])
			assert(n_outstanding
				== {1'b0,f_soutstanding[iM]}
					+(o_sstb[iM] ? 1:0));

		always @(*)
		if (!i_reset)
		begin
			for(iM=0; iM<NS; iM=iM+1)
			if (grant[N][iM] && i_mcyc[N])
			begin
				if (f_soutstanding[iM] > 0)
					assert(i_mwe[N] == o_swe[iM]);
				if (o_sstb[iM])
					assert(i_mwe[N] == o_swe[iM]);
				if (o_mack[N])
					assert(i_mwe[N] == o_swe[iM]);
				if (o_scyc[iM] && i_sack[iM])
					assert(i_mwe[N] == o_swe[iM]);
				if (o_merr[N] && !timed_out[N])
					assert(i_mwe[N] == o_swe[iM]);
				if (o_scyc[iM] && i_serr[iM])
					assert(i_mwe[N] == o_swe[iM]);
			end
		end

		always @(*)
		if (!i_reset && OPT_BUFFER_DECODER && i_mcyc[N])
		begin
			if (dcd_stb[N])
				assert(i_mwe[N] == m_we[N]);
		end
		// }}}
	end endgenerate

	generate for(M=0; M<NS; M=M+1)
	begin : ASSERT_NOT_CYC_WO_GRANT
		// {{{
		always @(posedge i_clk)
		if (!$past(sgrant[M]))
			assert(!o_scyc[M]);
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CONTRACT SECTION
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	// Here's the contract, in two parts:
	// {{{
	//	1. Should ever a master (any master) wish to read from a slave
	//		(any slave), he should be able to read a known value
	//		from that slave (any value) from any arbitrary address
	//		he might wish to read from (any address)
	//
	//	2. Should ever a master (any master) wish to write to a slave
	//		(any slave), he should be able to write the exact
	//		value he wants (any value) to the exact address he wants
	//		(any address)
	//
	//	special_master	is an arbitrary constant chosen by the solver,
	//		which can reference *any* possible master
	//	special_address	is an arbitrary constant chosen by the solver,
	//		which can reference *any* possible address the master
	//		might wish to access
	//	special_value	is an arbitrary value (at least during
	//		induction) representing the current value within the
	//		slave at the given address
	// }}}
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Now let's pay attention to a special bus master and a special
	// address referencing a special bus slave.  We'd like to assert
	// that we can access the values of every slave from every master.
	(* anyconst *) reg	[(NM<=1)?0:(LGNM-1):0]	special_master;
			reg	[(NS<=1)?0:(LGNS-1):0]	special_slave;
	(* anyconst *) reg	[AW-1:0]	special_address;
			reg	[DW-1:0]	special_value;

	always @(*)
	if (NM <= 1)
		assume(special_master == 0);
	always @(*)
	if (NS <= 1)
		assume(special_slave == 0);

	//
	// Decode the special address to discover the slave associated with it
	always @(*)
	begin
		special_slave = NS;
		for(iM=0; iM<NS; iM = iM+1)
		begin
			if (((special_address ^ SLAVE_ADDR[iM*AW +: AW])
					&SLAVE_MASK[iM*AW +: AW]) == 0)
				special_slave = iM;
		end
	end

	generate if (NS > 1)
	begin : DOUBLE_ADDRESS_CHECK
		// {{{
		//
		// Check that no slave address has been assigned twice.
		// This check only needs to be done once at the beginning
		// of the run, during the BMC section.
		reg	address_found;

		always @(*)
		if (!f_past_valid)
		begin
			address_found = 0;
			for(iM=0; iM<NS; iM = iM+1)
			begin
				if (((special_address ^ SLAVE_ADDR[iM*AW +: AW])
						&SLAVE_MASK[iM*AW +: AW]) == 0)
				begin
					assert(address_found == 0);
					address_found = 1;
				end
			end
		end
		// }}}
	end endgenerate
	//
	// Let's assume this slave will acknowledge any request on the next
	// bus cycle after the stall goes low.  Further, lets assume that
	// it never creates an error, and that it always responds to our special
	// address with the special data value given above.  To do this, we'll
	// also need to make certain that the special value will change
	// following any write.
	//
	// These are the "assumptions" associated with our fictitious slave.
`ifdef	VERIFIC
	always @(*)
	if (!f_past_valid)
		assume(special_value == 0);
`else
	initial	assume(special_value == 0);
`endif
	always @(posedge i_clk)
	if (special_slave < NS)
	begin
		// {{{
		if ($past(o_sstb[special_slave] && !i_sstall[special_slave]))
		begin
			assume(i_sack[special_slave]);

			if ($past(!o_swe[special_slave])
					&&($past(o_saddr[special_slave*AW +: AW]) == special_address))
				assume(i_sdata[special_slave*DW+: DW]
						== special_value);
		end else
			assume(!i_sack[special_slave]);
		assume(!i_serr[special_slave]);

		if (o_scyc[special_slave])
			assert(f_soutstanding[special_slave]
				== i_sack[special_slave]);

		if (o_sstb[special_slave] && !i_sstall[special_slave]
			&& o_swe[special_slave])
		begin
			for(iM=0; iM < DW/8; iM=iM+1)
			if (o_ssel[special_slave * DW/8 + iM])
				special_value[iM*8 +: 8] <= o_sdata[special_slave * DW + iM*8 +: 8];
		end
		// }}}
	end

	//
	// Now its time to make some assertions.  Specifically, we want to
	// assert that any time we read from this special slave, the special
	// value is returned.
	reg	[2:0]	f_read_seq;
	reg		f_read_ack, f_read_sstall;

	initial	f_read_sstall = 0;
	always @(posedge i_clk)
		f_read_sstall <= s_stall[special_slave];

	always @(*)
		f_read_ack = (f_read_seq[2] || ((!OPT_DBLBUFFER)&&f_read_seq[1]
					&& !f_read_sstall));
	initial	f_read_seq = 0;
	always @(posedge i_clk)
	if ((special_master < NM)&&(special_slave < NS)
			&&(i_mcyc[special_master])
			&&(!timed_out[special_master]))
	begin
		f_read_seq <= 0;
		if ((grant[special_master][special_slave])
			&&(m_stb[special_master])
			&&(m_addr[special_master] == special_address)
			&&(!m_we[special_master])
			)
		begin
			f_read_seq[0] <= 1;
		end

		if (|f_read_seq)
		begin
			assert(grant[special_master][special_slave]);
			assert(mgrant[special_master]);
			assert(sgrant[special_slave]);
			assert(mindex[special_master] == special_slave);
			assert(sindex[special_slave] == special_master);
			assert(!o_merr[special_master]);
		end

		if (f_read_seq[0] && !$past(s_stall[special_slave]))
		begin
			assert(o_scyc[special_slave]);
			assert(o_sstb[special_slave]);
			assert(!o_swe[special_slave]);
			assert(o_saddr[special_slave*AW +: AW] == special_address);

			f_read_seq[1] <= 1;

		end else if (f_read_seq[0] && $past(s_stall[special_slave]))
		begin
			assert($stable(m_stb[special_master]));
			assert(!m_we[special_master]);
			assert(m_addr[special_master] == special_address);

			f_read_seq[0] <= 1;
		end

		if (f_read_seq[1] && $past(s_stall[special_slave]))
		begin
			assert(o_scyc[special_slave]);
			assert(o_sstb[special_slave]);
			assert(!o_swe[special_slave]);
			assert(o_saddr[special_slave*AW +: AW] == special_address);
			f_read_seq[1] <= 1;
		end else if (f_read_seq[1] && !$past(s_stall[special_slave]))
		begin
			assert(i_sack[special_slave]);
			assert(i_sdata[special_slave*DW +: DW] == $past(special_value));
			if (OPT_DBLBUFFER)
				f_read_seq[2] <= 1;
		end

		if (f_read_ack)
		begin
			assert(o_mack[special_master]);
			assert(o_mdata[special_master * DW +: DW]
				== $past(special_value,2));
		end
	end else
		f_read_seq <= 0;

	always @(*)
		cover(i_mcyc[special_master] && f_read_ack);

	//
	// Let's try a write assertion now.  Specifically, on any request to
	// write to our special address, we want to assert that the special
	// value at that address can be written.
	reg	[2:0]	f_write_seq;
	reg		f_write_ack, f_write_sstall;

	initial	f_write_sstall = 0;
	always @(posedge i_clk)
		f_write_sstall = s_stall[special_slave];

	always @(*)
		f_write_ack = (f_write_seq[2]
				|| ((!OPT_DBLBUFFER)&&f_write_seq[1]
					&& !f_write_sstall));
	initial	f_write_seq = 0;
	always @(posedge i_clk)
	if ((special_master < NM)&&(special_slave < NS)
			&&(i_mcyc[special_master])
			&&(!timed_out[special_master]))
	begin
		f_write_seq <= 0;
		if ((grant[special_master][special_slave])
			&&(m_stb[special_master])
			&&(m_addr[special_master] == special_address)
			&&(m_we[special_master]))
		begin
			// Our write sequence begins when our special master
			// has access to the bus, *and* he is trying to write
			// to our special address.
			f_write_seq[0] <= 1;
		end

		if (|f_write_seq)
		begin
			assert(grant[special_master][special_slave]);
			assert(mgrant[special_master]);
			assert(sgrant[special_slave]);
			assert(mindex[special_master] == special_slave);
			assert(sindex[special_slave] == special_master);
			assert(!o_merr[special_master]);
		end

		if (f_write_seq[0] && !$past(s_stall[special_slave]))
		begin
			assert(o_scyc[special_slave]);
			assert(o_sstb[special_slave]);
			assert(o_swe[special_slave]);
			assert(o_saddr[special_slave*AW +: AW] == special_address);
			assert(o_sdata[special_slave*DW +: DW]
				== $past(m_data[special_master]));
			assert(o_ssel[special_slave*DW/8 +: DW/8]
				== $past(m_sel[special_master]));

			f_write_seq[1] <= 1;

		end else if (f_write_seq[0] && $past(s_stall[special_slave]))
		begin
			assert($stable(m_stb[special_master]));
			assert(m_we[special_master]);
			assert(m_addr[special_master] == special_address);
			assert($stable(m_data[special_master]));
			assert($stable(m_sel[special_master]));

			f_write_seq[0] <= 1;
		end

		if (f_write_seq[1] && $past(s_stall[special_slave]))
		begin
			assert(o_scyc[special_slave]);
			assert(o_sstb[special_slave]);
			assert(o_swe[special_slave]);
			assert(o_saddr[special_slave*AW +: AW] == special_address);
			assert($stable(o_sdata[special_slave*DW +: DW]));
			assert($stable(o_ssel[special_slave*DW/8 +: DW/8]));
			f_write_seq[1] <= 1;
		end else if (f_write_seq[1] && !$past(s_stall[special_slave]))
		begin
			for(iM=0; iM<DW/8; iM=iM+1)
			begin
				if ($past(o_ssel[special_slave * DW/8 + iM]))
					assert(special_value[iM*8 +: 8]
						== $past(o_sdata[special_slave*DW+iM*8 +: 8]));
			end

			assert(i_sack[special_slave]);
			if (OPT_DBLBUFFER)
				f_write_seq[2] <= 1;
		end

		if (f_write_seq[2] || ((!OPT_DBLBUFFER) && f_write_seq[1]
					&& !$past(s_stall[special_slave])))
			assert(o_mack[special_master]);
	end else
		f_write_seq <= 0;

	always @(*)
		cover(i_mcyc[special_master] && f_write_ack);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// COVER: Full connectivity check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[NM-1:0]	f_m_ackd;
	reg	[NS-1:0]	f_s_ackd;
	reg			f_cvr_aborted;

	initial	f_cvr_aborted = 0;
	always @(posedge i_clk)
	if (!f_past_valid || i_reset)
		f_cvr_aborted <= 0;
	else for(iN=0; iN<NM; iN=iN+1)
	begin
		if (request[iN][NS])
			f_cvr_aborted = 1;
		if ($fell(i_mcyc[iN]))
		begin
			if (f_macks[iN] != f_mreqs[iN])
				f_cvr_aborted = 1;
		end
	end

	initial	f_m_ackd = 0;
	generate for (N=0; N<NM; N=N+1)
	begin : GEN_FM_ACKD

		always @(posedge i_clk)
		if (i_reset)
			f_m_ackd[N] <= 0;
		else if (o_mack[N])
			f_m_ackd[N] <= 1'b1;

	end endgenerate

	always @(posedge i_clk)
		cover(!f_cvr_aborted && (&f_m_ackd));

	generate if (NM > 1)
	begin

		always @(posedge i_clk)
			cover(!f_cvr_aborted && (&f_m_ackd[1:0]));

	end endgenerate

	initial	f_s_ackd = 0;
	generate for (M=0; M<NS; M=M+1)
	begin : GEN_FS_ACKD

		always @(posedge i_clk)
		if (i_reset)
			f_s_ackd[M] <= 1'b0;
		else if (sgrant[M] && o_mack[sindex[M]])
			f_s_ackd[M] <= 1'b1;

	end endgenerate

	always @(posedge i_clk)
		cover(!f_cvr_aborted && (&f_s_ackd[NS-1:0]));

	generate if (NS > 1)
	begin

		always @(posedge i_clk)
			cover(!f_cvr_aborted && (&f_s_ackd[NS-1:0]));

	end endgenerate
	// }}}
`endif
// }}}
endmodule
`ifndef	YOSYS
`default_nettype wire
`endif
