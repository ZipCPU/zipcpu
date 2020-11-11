# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:
- 32-bit.  All registers, addresses, and instructions are 32-bits in length.  While the byte-size itself was at one time 32-bits, the CPU now handles 8-bit bytes like all other CPUs
- A RISC CPU.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (eventually) floating point instructions.
- A load/store architecture.  Only load and store instructions may access memory.
- Wishbone compliant.  All memory and peripherals are accessed across a single wishbone bus.
- A Von-Neumann architecture, meaning that both instructions and data share a common bus.
- A pipelined architecture, having stages for prefetch, decode, read-operand(s), a combined stage containing the ALU, memory, divide, and floating point units, and then the final write-back stage.
- A two mode machine: supervisor and user, with each mode having a different access level.
- Completely open source, licensed under the GPL.

## Unique features and characteristics

- Only 29 instructions are currently implemented.  Six additional instructions have been reserved for a floating point unit, but such a unit has yet to be implemented.
- (Almost) all instructions can be executed conditionally.  Exceptions include load immediate, the debug break instruction, the bus lock and simulation instructions, and the no-operation instruction.  The assembler will quietly turn a conditional load immediate into a two-instruction equivalent.
- Simplfied wishbone bus.  While the ZipCPU conforms to the Wishbone B4 standard, some simplifications have been made.  All tgx lines have been removed, although the select lines have been kept.  All accesses are (or can be) pipelined.  Finally, the ZipCPU project (and its daughter projects/[peripherals](rtl/peripherals)) assumes that the strobe line is zero whenever the cycle is zero.  This simplifies peripheral processing.
- The CPU makes heavy use of pipelined wishbone processing wherever and whenever it can.  Hence, loading two vaues in a row may cost only one clock more than just loading the one value.
- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.  An [interrupt peripheral](rtl/peripherals/icontrol.v) handles the combining of multiple interrupts into a single interrupt line.

## Getting Started

If you'd like to get started with the ZipCPU, you might wish to know that this
repository contains the [CPU](./rtl/core/zipcpu.v), its [documentation](./doc/spec.pdf), and the [toolchain](./sw).
The CPU implementation found here, though, is just that: a CPU.  This
implementation requires a bus with peripherals hanging off of it, things such
as [RAM](https://github.com/ZipCPU/zbasic/blob/master/rtl/memdev.v),
[flash (ROM)](https://github.com/ZipCPU/zbasic/blob/master/rtl/wbqspiflash.v),
[serial port](https://github.com/ZipCPU/wbuart32), etc.  This is just where
I keep the CPU apart from any necessary peripherals.

So, if you want to try out the CPU, feel free to download and build this
repository (use `git-clone` with a depth of 1--there's a lot of stuff in the
git repo that you don't necessarily need).  You'll need it for the binutils,
GCC, and [newlib](https://sourceware.org/newlib) support provided by it.

Once you've built these tools, then I'd suggest you look into the
[ZBasic repository](https://github.com/ZipCPU/zbasic).  That repository places
the CPU in an environment with
[block RAM](https://github.com/ZipCPU/zbasic/blob/master/rtl/memdev.v),
[QSPI flash](https://github.com/ZipCPU/zbasic/blob/master/rtl/wbqspiflash.v),
and [SD-card (SPI protocol)](https://github.com/ZipCPU/sdspi) access.  From
that repository, you can either tweak the distro
([main.v](https://github.com/ZipCPU/zbasic/blob/master/rtl/main.v),
[regdefs.h](https://github.com/ZipCPU/zbasic/blob/master/sw/host/regdefs.h),
[board.h](https://github.com/ZipCPU/zbasic/blob/master/sw/zlib/board.h),
[board.ld](https://github.com/ZipCPU/zbasic/blob/master/sw/board/board.ld)) to
add the peripherals you want to use the CPU with, or you can use
[autofpga](https://github.com/ZipCPU/autofpga)
to adjust your RAM size, add or remove peripherals and so forth while
maintaining (creating, really) all of these files for you.

Even more than that,
the [ZBasic distribution](https://github.com/ZipCPU/zbasic) has complete
[Verilator support](https://github.com/ZipCPU/zbasic/tree/master/sim/verilated)
so that you can build your design, and simulate it, from
power on reset through bootloader through ... well, however far you'd like to
simulate and your disk has space for.

If you aren't interested in simulating the CPU, there is an assembly level
[debugger](https://github.com/ZipCPU/zbasic/blob/master/sw/host/zipdbg.cpp)
that you can use to stop and step the CPU, as well as an
integrated [wishbone scope](https://github.com/ZipCPU/wbscope) that
you can use to get traces from within the design while it is running.


## Need help?

If you'd like to use the ZipCPU, and don't know where to begin, feel free
to find me on IRC as ZipCPU.  I tend to inhabit the #openarty channel
of the Freenode IRC server.  If you get stuck, I've been known to help folks
out there as well.

## Current Status

I've recently blogged about the ZipCPU at [zipcpu.com](http://zipcpu.com)!
Articles you might find valuable include:

- [An overview of the ZipCPU's ISA](http://zipcpu.com/zipcpu/2018/01/01/zipcpu-isa.html)
- [How-to build the tool-chain, and test the CPU](http://zipcpu.com/zipcpu/2018/01/31/cpu-build.html)
- [Formal properties of a WB bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html)
- [Formally proving the prefetch](http://zipcpu.com/zipcpu/2017/11/18/prefetch.html)

I'm also working on [formally verifying the entire
CPU](http://zipcpu.com/blog/2018/01/22/formal-progress.html).  My goal will be
to [prove, via
yosys-smtbmc](http://zipcpu.com/blog/2017/10/19/formal-intro.html), that the
ZipCPU will never enter into an invalid state.  I've been successful so far
proving the various components of the ZipCPU.  What remains is the CPU
itself.


## Not yet integrated

- An [MMU](rtl/peripherals/zipmmu.v) has been written for the ZipCPU, and even
  integrated into it, but it has not yet been tested.  Using
  [formal methods](http://zipcpu.com/blog/2017/10/19/formal-intro.html),
  I've now proved that this component works.  A
  [test bench](sim/verilator/zipmmu_tb.cpp) also exists
  to exercise it.

- A [data cache](../../tree/master/rtl/core/dcache.v) has been
  written for the ZipCPU, but has yet to be fully optimized.

- I would also like to integrate [SDCard
  support](https://github.com/ZipCPU/sdspi) into the
  [newlib](https://sourceware.org/newlib) C-library to give
  the CPU file access.  If and when this takes place, it will take place as
  part of the [ZBasic repository](https://github.com/ZipCPU/zbasic) first.

- The [ZipOS](https://github.com/ZipCPU/s6soc/tree/master/sw/zipos)
  would greatly speed up and improve the bare bones [newlib](https://sourceware.org/newlib) library--primarily
  by providing "O/S" level interrupt support when using the library.  This
  integration has not (yet) been accomplished.

  On the other hand, if the [MMU](rtl/peripherals/zipmmu.v) is available,
  I might rather just create a Linux distribution.

## Commercial Opportunities

If the [GPLv3 license](https://www.gnu.org/licenses/gpl-3.0.en.html) is
insufficient for your needs, other licenses (for all but the tool-chain) can
be purchased from Gisselquist Technology, LLC.

