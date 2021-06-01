# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:

- 32-bit.  All registers, addresses, and instructions are 32-bits in length.  While the byte-size itself was at one time 32-bits, the CPU now handles 8-bit bytes like all other CPUs

- A RISC CPU.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (eventually) floating point instructions.

  (Note that the ZipCPU is *not* a RISC-V CPU, nor does it copy any other instruction set but its own.)

- A load/store architecture.  Only load and store instructions may access
  memory.

- Wishbone compliant.  All memory and peripherals are accessed across a single
  wishbone bus. (_DEPRECATED_)

  This version is now both Wishbone, AXI-lite, and AXI compliant depending upon
  how it is built.  The core of the CPU itself is now bus independent, and
  there exist various wrappers which can be used for each bus option.

- A Von-Neumann architecture, meaning that both instructions and data share a common bus. (_DEPRECATED_)

  This version now has separate buses for instructions and data, although the
  address space is assumed to be common.  In particular, the long jump 
  instruction requires a common address space to make sense.

- A pipelined architecture, having stages for prefetch, decode, read-operand(s),
  a combined stage containing the ALU, memory, divide, and floating point units,
  and then the final write-back stage.

- A two mode machine: supervisor and user, with each mode having a different
  access level.

- Completely open source, licensed under the GPLv3.

## The ZipCore branch

This particular branch of the ZipCPU is designed to be bus independent.
It now has support for Wishbone, AXI-lite, and AXI buses,
and it is capable of supporting additional buses still.  Core CPU
functions have now been moved into a [ZipCore](rtl/core/zipcore.v), rather than
the (now deprecated and deleted) zipcpu.v.  It should now be possible to
generate support for any bus interface meeting the requirements found in either
the [ffetch](bench/formal/ffetch.v) (for instructions) or
[fmem](bench/formal/fmem.v) (for data) property sets.

Status:

- All of the memory units have now been re-verified with the new interface
  property files.

  -- Instruction fetch units (pick one): [prefetch](rtl/core/prefetch.v) (single instruction fetch), [dblfetch](rtl/core/dblfetch.v) (twin instruction fetch), [pfcache](rtl/core/pfcache.v) (WB fetch with cache), [axilfetch](rtl/core/axilfetch.v) (AXI-lite fetch with possible FIFO, allowing multiple instructions to be in the pipeline at once, [axiicache](rtl/core/axiicache.v) (AXI instruction cache)

  -- Data units (pick one): [memops](rtl/core/memops.v) (WB single operation on the bus at a time), [pipemem](rtl/core/pipemem.v) (WB multiple operations allowed to be on the bus), [dcache](rtl/core/dcache.v) (WB data cache), [axilops](rtl/core/axilops.v), [axilpipe](rtl/core/axilpipe.v) (AXI-lite memory unit allowing multiple transactions to be outstanding), [axiops](rtl/core/axiops.v) and [axipipe](rtl/core/axipipe.v) are like their AXI-lite cousins but with atomic access, and [axidcache](rtl/core/axidcache.v) (AXI (full) data cache implementation).

  -- Formal verification has been done to guarantee bus functionality.  Not all cores have been checked for full contract handling.

  -- Both [axiops](rtl/core/axiops.v) and [axipipe](rtl/core/axipipe.v) support atomic accesses, although the [axidcache](rtl/core/axidcache.v) doesn't yet support them.

   -- The caches do not snoop the bus for coherency purposes, and so they may get out of sync with an actual memory if something else, like a DMA, ever writes to it.  There's a clear-cache instruction to handle this problem, but it's a manual approach to the problem.

- Several wrappers now exist which you can use:

  -- There's both the traditional [ZipBones](rtl/zipbones.v) and [ZipSystem](rtl/zipsystem.v) wishbone cores.  These are both based upon a new [Wishbone wrapper](rtl/core/zipwb.v) which combines instruction and data buses together into a common bus access port.

  -- There is both an [AXI wrapper](rtl/zipaxi.v) and an [AXI-lite wrapper](rtl/zipaxil.v).  Neither of these AXI wrappers include support for the [ZipSystem](rtl/zipsystem.v) peripherals.  These will instead need to be placed into an external bus peripheral.  An [AXI-lite peripheral set](rtl/peripherals/axilperiphs.v) has been created for this purpose.  While this seemed like a great solution at the time, it's likely to be a bit of a dead end since any (eventual) MMU support will require a tightly coupled peripheral set.

- The AXI components and bus really require that the ZipCPU be a little
  endian machine.  Compiler support doesn't (yet) exist for a little endian
  version.  Several options have been added to the AXI controllers in an attempt
  to make endian support work both ways (even in violation of the AXI spec).
  Currently, the `SWAP_WSTRB` option has been tested quite successfully.  It
  should work well and consistently with the ZipCPU itself, but may have trouble
  playing with others since it (essentially) renumbers the bytes on the AXI
  bus in order to work.

Now back to the regular readme.

## Unique features and characteristics

- Only 29 instructions are currently implemented.  Six additional instructions have been reserved for a floating point unit, but such a unit has yet to be implemented.

- (Almost) all instructions can be executed conditionally.  Exceptions include load immediate (LDI), the debug break instruction, the bus lock (LOCK) and simulation instructions (SIM), and the no-operation instruction (NOOP).  The assembler will quietly turn a conditional load immediate into a two-instruction equivalent (BREV, LDILO).

- The CPU makes heavy use of pipelining wherever and whenever it can.  Hence, when using a pipelined memory core, loading two vaues in a row may cost only one clock more than just loading the one value.

- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.  An [interrupt peripheral](rtl/peripherals/icontrol.v) handles the combining of multiple interrupts into a single interrupt line.

## Getting Started

If you'd like to get started with the ZipCPU, you might wish to know that this
repository contains the [CPU](rtl/core/zipcore.v), its [documentation](doc/spec.pdf), and the [toolchain](sw).
The CPU implementation found here, though, is just that: a CPU.  This
implementation requires a bus with peripherals hanging off of it, things such
as [RAM](https://github.com/ZipCPU/zbasic/blob/master/rtl/memdev.v),
[flash (ROM)](https://github.com/ZipCPU/zbasic/blob/master/rtl/qflexpress.v),
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
[QSPI flash](https://github.com/ZipCPU/zbasic/blob/master/rtl/qflexpress.v),
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
to find me on IRC as ZipCPU.  I've created a #zipcpu channel on Freenode's
IRC server that I tend to inhabit.  If you get stuck, feel free to drop by
and ask for help.  You can also drop by just to say hi.  Either way, please
introduce yourself and give me some time to respond.

## Current Status

I've recently blogged about the ZipCPU at [zipcpu.com](http://zipcpu.com)!
Articles you might find valuable include:

- [An overview of the ZipCPU's ISA](http://zipcpu.com/zipcpu/2018/01/01/zipcpu-isa.html)
- [How-to build the tool-chain, and test the CPU](http://zipcpu.com/zipcpu/2018/01/31/cpu-build.html)
- [Formal properties of a WB bus](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html)
- [Formally proving the prefetch](http://zipcpu.com/zipcpu/2017/11/18/prefetch.html)


## Not yet integrated

- The [MMU](rtl/peripherals/zipmmu.v) that was written for the ZipCPU now
  needs to be rewritten in order to work in the new ZipCore context.  My
  plan is to place the MMU between the ZipCore and the various bus aware
  wrappers, providing a similar interface to the one offered by the ZipCore.
  That way, caches will be based on physical addressing--solving one of the
  bigger problems I had when using the MMU.

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

The [GPLv3 license](https://www.gnu.org/licenses/gpl-3.0.en.html) should be
sufficient for most (all) academic and hobby purposes, and certainly for all
simulation based purposes.  If you find, however, that the [GPLv3
license](https://www.gnu.org/licenses/gpl-3.0.en.html) is insufficient for
your needs, other licenses can be purchased from Gisselquist Technology, LLC.

This applies to all but the toolchain, for which
[GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html) should work for all
purposes.  (Besides, I don't own the licenses for Binutils, GCC, or newlib.)
