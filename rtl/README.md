This directory contains three sub-directories:

- [core](core), where all of the actual components to the CPU proper are contained
- [peripherals](peripherals), where several common CPU peripherals are kept.  These aren't really external peripherals per se, although they may be implemented as such.  Rather, these peripherals are components that are important to the CPU's functionality.  As such, they are often distributed with the CPU proper, and used internally by supervisor programs.
- [aux](aux), where some general wishbone cores are kept, such as arbiters, delays, and even where I keep a copy of the formal wishbone properties.

Within this ZipCPU RTL directory are just the two primary wrappers for the
ZipCPU: [ZipBones](zipbones.v) and [ZipSystem](zipsystem.v).  These wrappers
connect an external wishbone slave interface to the debugging port of the
CPU, so that the CPU can be reset, started, stopped, and in general debugged.

The [ZipBones](./zipbones.v) would be the appropriate wrapper if you want the
CPU to fit in the tightest space possible (Ex: Digilent's [CMod
S6](https://github.com/ZipCPU/s6soc)).

Use the [ZipSystem](./zipsystem.v) if you want to give the CPU some
basic peripherals, such as:

- 2x [Interrupt controllers](./peripherals/icontrol.v)
- [Timers](peripherals/ziptimer), and an [experimental timer called zipjiffies](peripherals/zipjiffies.v) that's been with the CPU for some time
- [Performance counters](peripherals/zipcounter.v), to measure your performance
- A [Direct Memory Access Controller](./peripherals/wbdmac.v)
- Or even the [Memory Management Unit](./peripherals/zipmmu.v)

If you are just looking for the CPU's code itself, check out
[zipcpu.v](core/zipcpu.v)
within the
[core](core) subdirectory.
That's of the main core of the ZipCPU itself.

