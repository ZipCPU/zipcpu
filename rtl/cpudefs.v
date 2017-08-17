////////////////////////////////////////////////////////////////////////////////
//
// Filename:	cpudefs.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	Some architectures have some needs, others have other needs.
//		Some of my projects need a Zip CPU with pipelining, others
//	can't handle the timing required to get the answer from the ALU
//	back into the input for the ALU.  As each different projects has
//	different needs, I can either 1) reconfigure my entire baseline prior
//	to building each project, or 2) host a configuration file which contains
//	the information regarding each baseline.  This file is that
//	configuration file.  It controls how the CPU (not the system,
//	peripherals, or other) is defined and implemented.  Several options
//	are available within here, making the Zip CPU pipelined or not,
//	able to handle a faster clock with more stalls or a slower clock with
//	no stalls, etc.
//
//	This file encapsulates those control options.
//
//	The number of LUTs the Zip CPU uses varies dramatically with the
//	options defined in this file.
//
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
`ifndef	CPUDEFS_H
`define	CPUDEFS_H
//
//
// The first couple options control the Zip CPU instruction set, and how
// it handles various instructions within the set:
//
//
// OPT_ILLEGAL_INSTRUCTION is part of a new section of code that is supposed
// to recognize illegal instructions and interrupt the CPU whenever one such
// instruction is encountered.  The goal is to create a soft floating point
// unit via this approach, that can then be replaced with a true floating point
// unit.  As I'm not there yet, it just catches illegal instructions and
// interrupts the CPU on any such instruction--when defined.  Otherwise,
// illegal instructions are quietly ignored and their behaviour is ...
// undefined. (Many get treated like NOOPs ...)
//
// I recommend setting this flag so highly, that I'm likely going to remove
// the option to turn this off in future versions of this CPU.
//
`define	OPT_ILLEGAL_INSTRUCTION
//
//
//
// OPT_MULTIPLY controls whether or not the multiply is built and included
// in the ALU by default.  Set this option and a parameter will be set that
// includes the multiply.  (This parameter may still be overridden, as with
// any parameter ...)  If the multiply is not included and
// OPT_ILLEGAL_INSTRUCTION is set, then the multiply will create an illegal
// instruction that will then trip the illegal instruction trap.
//
// Either not defining this value, or defining it to zero will disable the
// hardware multiply.  A value of '1' will cause the multiply to occurr in one
// clock cycle only--often at the expense of the rest of the CPUs speed.
// A value of 2 will cause the multiply to have a single delay cycle, 3 will
// have two delay cycles, and 4 (or more) will have 3 delay cycles.
//
//
`define	OPT_MULTIPLY	3
//
//
//
// OPT_DIVIDE controls whether or not the divide instruction is built and
// included into the ZipCPU by default.  Set this option and a parameter will
// be set that causes the divide unit to be included.  (This parameter may
// still be overridden, as with any parameter ...)  If the divide is not
// included and OPT_ILLEGAL_INSTRUCTION is set, then the multiply will create
// an illegal instruction exception that will send the CPU into supervisor
// mode.
//
//
`define	OPT_DIVIDE
//
//
//
// OPT_IMPLEMENT_FPU will (one day) control whether or not the floating point
// unit (once I have one) is built and included into the ZipCPU by default.
// At that time, if this option is set then a parameter will be set that
// causes the floating point unit to be included.  (This parameter may
// still be overridden, as with any parameter ...)  If the floating point unit
// is not included and OPT_ILLEGAL_INSTRUCTION is set, then as with the
// multiply and divide any floating point instruction will result in an illegal
// instruction exception that will send the CPU into supervisor mode.
//
//
// `define	OPT_IMPLEMENT_FPU
//
//
//
//
// OPT_SINGLE_FETCH controls whether or not the prefetch has a cache, and
// whether or not it can issue one instruction per clock.  When set, the
// prefetch has no cache, and only one instruction is fetched at a time.
// This effectively sets the CPU so that only one instruction is ever
// in the pipeline at once, and hence you may think of this as a "kill
// pipeline" option.  However, since the pipelined fetch component uses so
// much area on the FPGA, this is an important option to use in trimming down
// used area if necessary.  Hence, it needs to be maintained for that purpose.
// Be aware, though, it will drop your performance by a factor between 2x and
// 3x.
//
// We can either pipeline our fetches, or issue one fetch at a time.  Pipelined
// fetches are more complicated and therefore use more FPGA resources, while
// single fetches will cause the CPU to stall for about 5 stalls each
// instruction cycle, effectively reducing the instruction count per clock to
// about 0.2.  However, the area cost may be worth it.  Consider:
//
//	Slice LUTs		ZipSystem	ZipCPU
//	Single Fetching		2521		1734
//	Pipelined fetching	2796		2046
//	(These numbers may be dated, but should still be representative ...)
//
// I recommend only defining this if you "need" to, if area is tight and
// speed isn't as important.  Otherwise, just leave this undefined.
//
// `define	OPT_SINGLE_FETCH
//
//
// OPT_DOUBLE_FETCH is an alternative to OPT_SINGLE_FETCH.  It is designed to
// increase performance primarily when using an instruction memory which has
// one cost for a random access, and a second (lower) cost for sequential
// access.  The driving example behind this implementation was flash memory
// with 34 clocks for an initial access and 16 clocks for any subsequent access,
// but SDRAM memory with 27 clocks for an initial access and 1 clock for a
// subsequent access is also a good example.  Even block RAM might be a good
// example, if there were any bus delays in getting to the RAM device.  Using
// OPT_DOUBLE_FETCH also increases the pipeline speed, as it allows CIS
// instructions and therefore partial pipelining.  (No work is done to resolve
// pipeline conflicts past the decode stage, as is the case with full pipeline
// mode.
//
// Do not define OPT_DOUBLE_FETCH if you wish to fully pipeline the CPU.  Do
// not define both OPT_DOUBLE_FETCH and OPT_SINGLE_FETCH (the ifndef below
// should prevent that).
//
//
`ifndef	OPT_SINGLE_FETCH
// `define	OPT_DOUBLE_FETCH
`endif
//
//
//
// The ZipCPU ISA defines an optional compressed instruction set (CIS)
// complement.  This compressed instruction format allows two instructions to
// be packed into the same instruction word.  Some instructions can be so
// compressed, although not all.  Compressed instructions take the same time to
// complete--they are just compressed within memory to spare troubles with the
// prefetch.  Set OPT_CIS to include these compressed instructions as part of
// the instruction set.
//
`define OPT_CIS		// COST: about 87 LUTs
//
//
//
//
// OPT_EARLY_BRANCHING is an attempt to execute a BRA statement as early
// as possible, to avoid as many pipeline stalls on a branch as possible.
// With the OPT_TRADITIONAL_PFCACHE, BRA instructions cost only a single
// extra stall cycle, while LJMP instructions cost two (assuming the target is
// in the cache).  Indeed, the result is that a BRA instruction can be used as
// the compiler's branch prediction optimizer: BRA's barely stall, while
// conditional branches will always suffer about 4 stall cycles or so.
//
// I recommend setting this flag, so as to turn early branching on---if you
// have the LUTs available to afford it.
//
`define	OPT_EARLY_BRANCHING
//
//
//
//
// The next several options are pipeline optimization options.  They make no
// sense in a single instruction fetch mode, hence we #ifndef them so they
// are only defined if we are in a full pipelined mode (i.e. OPT_SINGLE_FETCH
// is not defined).
//
`ifndef	OPT_SINGLE_FETCH
`ifndef	OPT_DOUBLE_FETCH
//
//
//
// OPT_PIPELINED is the natural result and opposite of using the single
// instruction fetch unit.  If you are not using that unit, the ZipCPU will
// be pipelined.  The option is defined here more for readability than
// anything else, since OPT_PIPELINED makes more sense than OPT_SINGLE_FETCH,
// well ... that and it does a better job of explaining what is going on.
//
// In other words, leave this define alone--lest you break the ZipCPU.
//
`define	OPT_PIPELINED
//
//
//
// OPT_TRADITIONAL_PFCACHE allows you to switch between one of two prefetch
// caches.  If enabled, a more traditional cache is implemented.  This more
// traditional cache (currently) uses many more LUTs, but it also reduces
// the stall count tremendously over the alternative hacked pipeline cache.
// (The traditional pfcache is also pipelined, whereas the pipeline cache
// implements a windowed approach to caching.)
//
// If you have the fabric to support this option, I recommend including it.
//
`define	OPT_TRADITIONAL_PFCACHE
//
//
//
//
// OPT_PIPELINED_BUS_ACCESS controls whether or not LOD/STO instructions
// can take advantaged of pipelined bus instructions.  To be eligible, the
// operations must be identical (cannot pipeline loads and stores, just loads
// only or stores only), and the addresses must either be identical or one up
// from the previous address.  Further, the load/store string must all have
// the same conditional.  This approach gains the must use, in my humble
// opinion, when saving registers to or restoring registers from the stack
// at the beginning/end of a procedure, or when doing a context swap.
//
// I recommend setting this flag, for performance reasons, especially if your
// wishbone bus can handle pipelined bus accesses.
//
`define	OPT_PIPELINED_BUS_ACCESS
//
//
//
//
//
`endif	// OPT_DOUBLE_FETCH
`endif	// OPT_SINGLE_FETCH
//
//
// [EXPERIMENTAL]
// OPT_MMU determines whether or not an MMU will be included in the ZipSystem
// containing the ZipCPU.  When set, the ZipCPU will route all memory accesses
// through the MMU as an address translator, creating a form of Virtual memory.
//
// `define	OPT_MMU
//
// Now let's talk about peripherals for a moment.  These next two defines
// control whether the DMA controller is included in the Zip System, and
// whether or not the 8 accounting timers are also included.  Set these to
// include the respective peripherals, comment them out not to.
//
`define	INCLUDE_DMA_CONTROLLER
`define	INCLUDE_ACCOUNTING_COUNTERS
//
//
// `define	DEBUG_SCOPE
//
`endif	// CPUDEFS_H
