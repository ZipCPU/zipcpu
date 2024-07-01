////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	axilmemsim.h
// {{{
// Project:	Zip CPU -- a small, lightweight, RISC CPU core
//
// Purpose:	This creates a memory like device to act on a AXI-lite bus.
//		It doesn't exercise the bus thoroughly, but does give some
//	exercise to the bus to see whether or not the bus master can control it.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
// }}}
#ifndef	AXILMEMSIM_H
#define	AXILMEMSIM_H

class	AXILMEMSIM {
public:	
	typedef	unsigned int	BUSW;
	typedef	unsigned char	uchar;

	BUSW	*m_mem, m_len, m_mask;
	int	m_nxt_ack;
	BUSW	m_nxt_data;
	bool	m_nxt_rvalid, m_nxt_bvalid;
	BUSW	m_nxt_rdata;
	

	AXILMEMSIM(const unsigned int nwords, BUSW *memp = NULL);
	~AXILMEMSIM(void);
	void	load(const char *fname);
	void	load(const unsigned addr, const char *buf,const unsigned len);

	void	read(const uchar arvalid, uchar &arready,
				const BUSW araddr, const uchar arprot,
			uchar &rvalid, const uchar rready,
				BUSW &rdata, uchar &rresp);
	void	write(const uchar awvalid, uchar &awready, const BUSW awaddr,
				const uchar awprot,
			const uchar wvalid, uchar &wready,
				const BUSW wdata, const BUSW wstrb,
			uchar &bvalid, const uchar bready, uchar &bresp);
	/*
	void	apply(const uchar arvalid, uchar &arready,
				const BUSW araddr,
			uchar &rvalid, BUSW &rdata, uchar &rresp,
			const uchar awvalid, uchar &awready, const BUSW awaddr,
			const uchar wvalid, uchar &wready,
				const BUSW wdata, const BUSW wstrb,
			uchar &bvalid, const uchar bready, uchar &bresp);
	*/

	/*
	void	operator()(const uchar arvalid, const uchar &arready,
				const BUSW araddr,
			const uchar &rvalid, const BUSW &rdata,
				const uchar &rresp,
			const uchar awvalid, const uchar &awready,
				const BUSW awaddr,
			const uchar wvalid, const uchar &wready,
				const BUSW wdata, const BUSW wstrb,
			const uchar &bvalid, const uchar bready,
				const uchar &bresp) {
		apply(arvalid, arready, araddr, rvalid, rdata, rresp,
			awvalid, awwready, awaddr,
			wvalid, wready, wdata, wstrb,
				bvalid, bready, bresp);
	}
	*/
	BUSW &operator[](const BUSW addr) { return m_mem[addr&m_mask]; }
};

#endif
