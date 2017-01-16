# The Zip CPU

The Zip CPU is a small, light-weight, RISC CPU.  Specific design goals include:
- 32-bit.  All registers, addresses, and instructions are 32-bits in length.  ~~Indeed, the "byte size" for this processor is 32-bits.~~  _This particular branch has been built to test out whether or not 8-bit bytes can be done without too much pain_
- A RISC CPU.  The ZipCPU does not implement any microcode for executing instructions.  Instructions nominally complete in one cycle each, with exceptions for multiplies, divides, memory accesses, and (sometime) floating point instructions.
- A load/store architecture.  Only load and store instructions may access memory.
- Wishbone compliant.  All memory and peripherals are accessed across a single wishbone bus.
- A Von-Neumann architecture, meaning that both instructions and data share a common bus.
- A pipelined architecture, having stages for prefetch, decode, read-operand(s), a combined stage containing the ALU, memory, divide, and floating point units, and then the final write-back stage.
- A two mode machine: supervisor and user, with each mode having a different access level.
- Completely open source, licensed under the GPL.

## Unique features and characteristics

- Only 30 instructions are currently implemented.  Six additional floating point instructions have been defined, but not (yet) implemented.
- All instructions can be executed conditionally.
- Simplfied wishbone bus.  While the ZipCPU conforms to the Wishbone B4 standard, some simplifications have been made.  All tgx lines have been removed, ~~as have the select lines~~ although the select lines have been kept.  All accesses are (or can be) pipelined.  Finally, the ZipCPU project (and its daughter projects/peripherals) assumes that the strobe line is zero whenever the cycle is zero.  This simplifies peripheral processing.
- ~~Did I mention that the select lines were removed from the wishbone bus?  That means that `sizeof(char)=sizeof(int)`, and both are 32-bit values.~~ This branch is testing whether or not sizeof(char)x4 can be sizeof(int)
- The CPU makes heavy use of pipelined wishbone processing wherever and whenever it can.  Hence, loading two vaues in a row may cost only one clock more than just loading the one value.
- The CPU has no interrupt vectors, but rather two register sets.  On any interrupt, the CPU just switches from the user register set to the supervisor register set.  This simplifies interrupt handling, since the CPU automatically saves, preserves, and restores the supervisor's context between enabling interrupts and receiving the next interrupt.
- There are no instructions for making function calls.  Function calls are accomplished by moving the PC register to R0 and jumping to the function's address.

## Current Status

This is an 8-bit support branch.  Several changes are being tested in this
branch:
- The CPU has been rebuilt to add four new instructions, LB (load byte), SB (store byte), LH (load half-word or short), and SH (store half-word or short). 
- The LOD/STO instructions have been renamed LW (load word) and SW (store word) respectively.
- The CPU is now also, as a result, completely big--endian, which it sort of was before. 
- The maximum address size of the CPU is no longer 32-bits, where each address
references a 32-bit number, but rather 30-bits.  The final two bits are used to
determine the values of the (new) select lines.
- The instruction set has been reordered--programs written for the 32-bit byte master branch will not work on this 8-bit byte branch.
- The greater than (GT) condition has been replaced by a not-carry (NC) condition, in order to simplify what the compiler needs to do for unsigned numbers.
- The machine ID in the ZipCPU ELF/object files has been changed from 0xdadd to 0xdad1, to reflect this change.  (This is an unregistered ID, so ... there _may_ be other computers out there with this ELF ID ...)

