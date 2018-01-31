## The ZipCPU's Simulator

This directory contains the basic ZipCPU simulator.

Ok, even this isn't the *best* simulator of the ZipCPU.  While this simulator
*is* fully functional, it only simulates the
[ZipCPU](../../rtl/core/zipcpu.v), encased in either the
[ZipSystem](../../rtl/zipsystem.v)
or the [ZipBones](../../rtl/zipbones.v),
plus [memory](memsim.cpp).  This simulator doesn't handle any interactions
with the
[flash](http://opencores.org/project,qspiflash), the
[serial port](https://github.com/ZipCPU/wbuart32), the
[SD-card](https://github.com/ZipCPU/sdspi), etc.  All of these interactions
(and more) are available from the
[simulator](https://github.com/ZipCPU/zbasic/tree/master/sim/verilated)
within the
[ZBasic repository](https://github.com/ZipCPU/zbasic).

However, this simulator *is* very basic to the CPU's functionality.  If you
just want to know if the CPU works by itself, if it can properly execute the
instructions given to it--even to the point of testing
interrupts etc, then this simulation will work.  It's just not fully
functional for testing all of the other peripheral components necessary
to make a CPU useful.
