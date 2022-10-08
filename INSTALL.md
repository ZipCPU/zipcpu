# Welcome to the ZipCPU!
## Installation overview

The ZipCPU repository contains a couple of very basic cabilities, some very necessary to any user, some only necessary to the hard core users, some not so much.

- It contains the [binutils](sw/binutils-2.27-zip) and [GCC compiler with ZipCPU backend](sw/gcc-6.2.0-zip) used by all implementations of the ZipCPU.  *This is very necessary.*

- It contains a copy of [newlib](sw/newlib-2.5.0-zip).  However, the [libgloss](sw/newlib-2.5.0-zip/libgloss/zip) directory within it is specific to the ZBasic architecture.  Right now, the answer is to roll your own libgloss for any new architecture.

- It contains a [specification document](doc/spec.pdf), describing the CPU and its instruction set, together with the sources files to build that specification.  This is different from a user's guide, or a specification document for your particular board implementation.  (The ZipCPU is *very* generic, allowing you to build your bus and place items within it at any address of your choosing.)

- It contains a copy of the Verilog RTL describing the ZipCPU.  This is useful should you ever wish to build your own project using the ZipCPU.  However, if you are just trying to use an existing SoC implementation, you can safely ignore this directory.

- It contains two simulators: [one](sim/cpp) independent of the RTL, the [second](sim/verilator) based upon the RTL.  Neither of these simulators is as good as a proper simulator of a SoC, but they remain here for ... whatever reasons.

- It contains my first attempt at building an Assembler.  Well, it does until I eventually remove it from the repository as unnecessary ...

- It also contains the source code for an example assembly level [debugger](sw/zipdbg).  This will probably be replaced in time with an implementation of gdb, but it remains for the time being.

## Dependencies

Prior to building within the ZipCPU repository directory, you will need to make certain you have a number of prerequisites.  These include: texinfo gcc-dev g++ flex bison libbison-dev verilator libgmp10 libgmp-dev libmpfr-dev libmpc-dev libelf-dev, bc, exuberant-ctags, and libncurses-dev.

These dependencies can be installed using:

> sudo apt install texinfo gcc-dev g++ flex bison libbison-dev verilator libgmp10 libgmp-dev libmpfr-dev libmpc-dev libelf-dev, bc, exuberant-ctags, and libncurses-dev.

## Installation instructions
To build all of the above, type _make_ in the main repository directory.  This will build the tools and place them into a [local install directory](sw/install/cross-tools/bin).  Sadly, this process will currently fail about halfway through.  To get past this, add the [install directory](sw/install/cross-tools/bin) to your path and restart.  _make_ will then pick up where it left off and finish the task.

The ZipCPU build process does not yet install anything into your local system.  All of the tools generated (currently) will be left in the local [install directory](sw/install).
