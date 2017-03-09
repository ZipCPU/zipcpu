# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:
- 32-bit.  All registers, addresses, and instructions are 32-bits in length.  While the byte-size itself was at one time 32-bits, the CPU now handles 8-bit bytes like all other CPUs
- A RISC CPU.  The ZipCPU does not implement any microcode for executing instructions.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (sometime) floating point instructions.
- A load/store architecture.  Only load and store instructions may access memory.
- Wishbone compliant.  All memory and peripherals are accessed across a single wishbone bus.
- A Von-Neumann architecture, meaning that both instructions and data share a common bus.
- A pipelined architecture, having stages for prefetch, decode, read-operand(s), a combined stage containing the ALU, memory, divide, and floating point units, and then the final write-back stage.
- A two mode machine: supervisor and user, with each mode having a different access level.
- Completely open source, licensed under the GPL.

## Unique features and characteristics

- Only 29 instructions are currently implemented.  Six additional instructions have been reserved for a floating point unit, but such a unit has yet to be implemented.
- (Almost) all instructions can be executed conditionally.  Exceptions include load immediate, the debug break instruction, the bus lock and simulation instructions, and the no-operation instruction.
- Simplfied wishbone bus.  While the ZipCPU conforms to the Wishbone B4 standard, some simplifications have been made.  All tgx lines have been removed, although the select lines have been kept.  All accesses are (or can be) pipelined.  Finally, the ZipCPU project (and its daughter projects/[peripherals](rtl/peripherals) assumes that the strobe line is zero whenever the cycle is zero.  This simplifies peripheral processing.
- The CPU makes heavy use of pipelined wishbone processing wherever and whenever it can.  Hence, loading two vaues in a row may cost only one clock more than just loading the one value.
- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.  An [interrupt peripheral](rtl/peripherals/icontrol.v) handles the combining of multiple interrupts into a single interrupt line.

## Current Status

20170309: The CPU has just been updated for 8-bit byte support.  Several additional changes include:
- The CPU has been rebuilt to add four new instructions, LB (load byte), SB (store byte), LH (load half-word or short), and SH (store half-word or short). 
- The LOD/STO instructions have been renamed LW (load word) and SW (store word) respectively.
- The CPU is now also, as a result, completely big--endian, which it only sort of was before. 
- The maximum wishbone bus address width of the CPU is no longer 32-bits, where each address references a 32-bit number, but rather 30-bits.  The final two bits are used to determine the values of the (new) select lines.  This means that the ZipCPU now suffers from the same 4GB memory limit as all other 32-bit CPUs.
- The instruction set has been reordered--programs written for the 32-bit byte master branch will not work on this 8-bit byte branch.
- The greater than (GT) condition has been replaced by a not-carry (NC) condition, in order to simplify what the compiler needs to do for unsigned numbers.
- The machine ID in the ZipCPU ELF/object files has been changed from 0xdadd to 0xdad1, to reflect this change.  (This is an unregistered ID, so ... there _may_ be other computers out there with this ELF ID ...)
- The ZipCPU supports several new simulation support or SIM instructions.  These can be used to write messages to the simulator console if desired.
- There are now two simulators for the ZipCPU: A [C++ simulator](sim/cpp) that is independent of the Verilog, and a [Verilator](https://www.veripool.org/wiki/verilator) based [simulator](sim/verilated) that exercises the CPUs core logic.
- The two simulators are designed to closely match the performance of a bare-bones [basic ZipCPU system](https://github.com/ZipCPU/zbasic).  Further, the newlib library as built is designed to support this minimum ZipCPU implementation.
- The Assembler now implements the Compressed Instruction Set (CIS) by default when it can.  (This instruction set was formerly and inappropriately named the VLIW instruction set.  It has since been redesigned.)  Instruction words using this format can pack two instructions into a single instruction word.

Unlike the ZipCPU before these changes, newlib now compiles and appears to work with the ZipCPU (without floating point support).

## Not yet integrated

- An [MMU](rtl/peripherals/zipmmu.v) has been written for the ZipCPU, but not yet integrated into it
- Likewise, a [data cache](../../tree/master/rtl/core/dcache.v) has been written for the ZipCPU, but not yet integrated into it
- I would also like to integrate [SDCard support](https://github.com/ZipCPU/sdspi) into the newlib C-library to give the CPU file access
- The [ZipOS](https://github.com/ZipCPU/s6soc/tree/master/sw/zipos) would greatly speed up and improve the bare bones newlib library.

