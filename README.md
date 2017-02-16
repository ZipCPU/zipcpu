# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:
- 32-bit.  All registers, addresses, and instructions are 32-bits in length.  Indeed, the "byte size" for this processor is 32-bits.
- A RISC CPU.  The ZipCPU does not implement any microcode for executing instructions.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (soon) floating point instructions.
- A load/store architecture.  Only load and store instructions may access memory.
- Wishbone compliant.  All memory and peripherals are accessed across a single wishbone bus.
- A Von-Neumann architecture, meaning that both instructions and data share a common bus.
- A pipelined architecture, having stages for prefetch, decode, read-operand(s), a combined stage containing the ALU, memory, divide, and floating point units, and then the final write-back stage.
- A two mode machine: supervisor and user, with each mode having a different access level.
- Completely open source, licensed under the GPL.

## Unique features and characteristics

- Only 26 instructions are currently implemented.  Six additional floating point instructions have been defined, but not (yet) implemented.
- All instructions can be executed conditionally.
- Simplfied wishbone bus.  While the ZipCPU conforms to the Wishbone B4 standard, some simplifications have been made.  All tgx lines have been removed, as have the select lines.  All accesses are (or can be) pipelined.  Finally, the ZipCPU project (and its daughter projects/peripherals) assumes that the strobe line is zero whenever the cycle is zero.  This simplifies peripheral processing.
- Did I mention that the select lines were removed from the wishbone bus?  That means that `sizeof(char)=sizeof(int)`, and both are 32-bit values.
- The CPU makes heavy use of pipelined wishbone processing wherever and whenever it can.  Hence, loading two vaues in a row may cost only one clock more than just loading the one value.
- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.
- There are no instructions for making function calls.  Function calls are accomplished by moving the PC register to R0 and jumping to the function's address.

## Current Status

The ZipCPU is supported by a full build toolchain, found here in this
[repository](tree/master/sw).  This includes binutils, gcc, and a zipdbg
debugger.  GDB has not (yet) been ported to the ZipCPU, neither does the CPU
support any C libraries.  Still, an
[Operating Sysem](../s6soc/tree/master/sw/zipos) has been built using the 
ZipCUP with some success.

Very few changes have been made to the master branch of the CPU recently.
You might even consider it to be a stable version.

However, a *lot* of work is taking place on the
[8-bit byte branch](tree/branch8b).  You might consider this to be the current
development branch for the next major version.  The fundamental characteristic
of the CPU on that branch, though, is four new opcodes offering the CPU
8-bit byte access to bus.  Once the branch stabilizes, and once it has been
proven on the various projects I have that use the ZipCPU such as the
[S6SoC](../s6soc/tree/branch8b), [XuLA2-LX25 SoC](../xulalx25soc/tree/branch8b),
and [OpenArty](../openarty/tree/branch8b), then that branch will be merged into
the mainline.

