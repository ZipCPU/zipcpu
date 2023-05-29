# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:

- 32-bit.  All registers, addresses, and instructions are 32-bits in length.

- A RISC CPU.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (eventually) floating point instructions.

  (Note that the ZipCPU is *not* a RISC-V CPU, nor does it copy from any other instruction set but its own.)

- A load/store architecture.  Only load and store instructions may access
  memory.

- Includes Wishbone, AXI4-Lite, and AXI4 memory options.

- A (minimally) Von-Neumann architecture

  The Wishbone wrappers share buses for instructions and data, the AXI4-Lite and AXI4 wrappers have separate bus interfaces for each.  The address space itself, however, needs to be common.

- A pipelined architecture, having stages for prefetch, decode, read-operand(s), a combined stage containing the ALU, memory, divide, and floating point units, and then the final write-back stage.

- A two mode machine: supervisor and user, with each mode having a different access level.

- Completely open source, licensed under the GPLv3.

## Unique features and characteristics

- Only 29 instructions are currently implemented.  Six additional instructions have been reserved for a floating point unit, but such a unit has yet to be implemented.

- (Almost) all instructions can be executed conditionally.  Exceptions include load immediate (LDI), the debug break instruction (BREAK), the bus lock (LOCK) and simulation instructions (SIM), and the no-operation instruction (NOOP).  The assembler will quietly turn a conditional load immediate into a two-instruction equivalent (BREV, LDILO).

- The CPU makes heavy use of pipelining wherever and whenever it can.  Hence, when using a pipelined memory core, loading two vaues in a row may cost only one clock more than just loading the one value.

- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.  An optional [interrupt peripheral](rtl/peripherals/icontrol.v) may be used to combine multiple external interrupts into a single interrupt line.

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
[AutoFPGA](https://github.com/ZipCPU/autofpga)
to adjust your RAM size, add or remove peripherals and so forth while
maintaining (creating, really) all of these files for you.

The [sim/](sim/) subdirectory also contains a version of the ZipCPU in a
usable environment for simulation purposes.  This includes the CPU, possibly
more CPU's for a multiprocessor environment, bus interconnect, memory,
a simulated serial port, and a couple more peripherals.

If you aren't interested in simulating the CPU, there is an assembly level
[debugger](https://github.com/ZipCPU/zbasic/blob/master/sw/host/zipdbg.cpp)
that you can use to stop and step the CPU, as well as an
integrated [wishbone scope](https://github.com/ZipCPU/wbscope) that
you can use to get traces from within the design while it is running.


## Need help?

If you'd like to use the ZipCPU, and don't know where to begin, feel free
to find me on IRC as ZipCPU.  I've created a #zipcpu channel on several
IRC servers that I tend to inhabit.  If you get stuck, feel free to drop by
and ask for help.  You can also drop by just to say hi.  Either way, please
introduce yourself and give me some time to respond.

## Current Status

You can also read about the ZipCPU via several blog articles posted at
[zipcpu.com](http://zipcpu.com)!  Articles you might find valuable include:

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
