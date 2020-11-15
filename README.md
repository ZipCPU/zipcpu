# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:

- 32-bit.  All registers, addresses, and instructions are 32-bits in length.  While the byte-size itself was at one time 32-bits, the CPU now handles 8-bit bytes like all other CPUs

- A RISC CPU.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (eventually) floating point instructions.

  (Note that the ZipCPU is *not* a RISC-V CPU, nor does it copy any other instruction set but its own.)

- A load/store architecture.  Only load and store instructions may access 
  memory.

- Wishbone compliant.  All memory and peripherals are accessed across a single
  wishbone bus. (_DEPRECATED_)

- A Von-Neumann architecture, meaning that both instructions and data share a common bus. (_DEPRECATED_)

- A pipelined architecture, having stages for prefetch, decode, read-operand(s),
  a combined stage containing the ALU, memory, divide, and floating point units,
  and then the final write-back stage.

- A two mode machine: supervisor and user, with each mode having a different
  access level.

- Completely open source, licensed under the GPL.

## The ZipCore branch

This particular branch of the ZipCPU is designed to be bus independent.
Once complete, it will have support for Wishbone, AXI-lite, and AXI buses,
and it will be capable of adding support for additiona buses.  Core CPU
functions have now been moved into a [ZipCore](rtl/core/zipcore.v).  It should
now be possible to generate support for any bus interface meeting the
requirements in either [ffetch](bench/formal/ffetch.v) (for instructions)
or [fmem](bench/formal/fmem.v) (for data).

Status:

- All of the memory units have now been re-verified with the new interface
  property files.

  -- Instruction fetch units (pick one): [prefetch](rtl/core/prefetch.v) (single instruction fetch), [dblfetch](rtl/core/dblfetch.v) (twin instruction fetch), [pfcache](rtl/core/pfcache.v) (WB fetch with cache), [axilfetch](rtl/core/axilfetch.v) (AXI-lite fetch with possible FIFO, allowing multiple instructions to be in the pipeline at once, [axiicache](rtl/core/axiicache.v) (AXI instruction cache)

  -- Data units (pick one): [memops](rtl/core/memops.v) (WB single operation on the bus at a time), [pipemem](rtl/core/pipemem.v) (WB multiple operations allowed to be on the bus), [dcache](rtl/core/dcache.v) (WB data cache), [axilops](rtl/core/axilops.v), [axilpipe](rtl/core/axilpipe.v) (AXI-lite memory unit allowing multiple transactions to be outstanding).  There's no AXI data cache implementation (yet).

  -- Formal verification has been done to guarantee bus functionality.  Not all cores have been checked for full contract handling.

- None of the AXI components support atomic accesses (yet).

- The caches do not snoop the bus for coherency purposes, and so may get out
  of sync.  There's a clear-cache instruction to handle this, but it's a manual
  approach to the problem.

- The [ZipCore](rtl/core/zipcore.v) passes a formal check, but has not yet
  been integrated back into any simulation environments.

- While there exists a [Wishbone wrapper](rtl/core/zipwb.v) for
  the [ZipCore](rtl/core/zipcore.v), the AXI wrapper still needs to be created
  and tested.

  -- The AXI wrapper will no longer include the [ZipSystem](rtl/zipsystem.v) peripherals.  These will instead be placed on the regular bus.  An [AXI-lite peripheral set](rtl/peripherals/axilperiphs.v) has been created for this purpose.

- The AXI components and bus really require that the ZipCPU be a little
  endian machine.  Compiler support doesn't (yet) exist for a little endian
  version.  Several options have been added to the AXI controllers in an attempt
  to make endian support work both ways (even in violation of the AXI spec).
  As with the other things, these haven't (yet) been tested.

Now back to the regular readme.

## Unique features and characteristics

- Only 29 instructions are currently implemented.  Six additional instructions have been reserved for a floating point unit, but such a unit has yet to be implemented.

- (Almost) all instructions can be executed conditionally.  Exceptions include load immediate, the debug break instruction, the bus lock and simulation instructions, and the no-operation instruction.  The assembler will quietly turn a conditional load immediate into a two-instruction equivalent.

- Simplfied wishbone bus.  While the ZipCPU conforms to the Wishbone B4 standard, some simplifications have been made.  All tgx lines have been removed, although the select lines have been kept.  All accesses are (or can be) pipelined.  Finally, the ZipCPU project (and its daughter projects/[peripherals](rtl/peripherals)) assumes that the strobe line is zero whenever the cycle is zero.  This simplifies peripheral processing.

- The CPU makes heavy use of pipelined wishbone processing wherever and whenever it can.  Hence, loading two vaues in a row may cost only one clock more than just loading the one value.

- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.  An [interrupt peripheral](rtl/peripherals/icontrol.v) handles the combining of multiple interrupts into a single interrupt line.

## Getting Started

If you'd like to get started with the ZipCPU, you might wish to know that this
repository contains the [CPU](./rtl/core/zipcore.v), its [documentation](./doc/spec.pdf), and the [toolchain](./sw).
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
[Verilator support](https://github.com/ZipCPU/zbasic/tree/sim/verilator)
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

- FATFS support now exists for the [SDCard](https://github.com/ZipCPU/sdspi),
  it's just not (yet) integrated into the
  [newlib](https://sourceware.org/newlib) C-library.

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

