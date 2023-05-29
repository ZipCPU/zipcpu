This directory contains three sub-directories:

- [core](core), where all of the actual components to the CPU proper are contained
- [peripherals](peripherals), where several common CPU peripherals are kept.  These aren't really external peripherals per se, although they may be implemented as such.  Rather, these peripherals are components that are important to the CPU's functionality.  As such, they are often distributed with the CPU proper, and used internally by supervisor programs.
- [ex](ex), where some general wishbone cores are kept, such as arbiters, delays, and even where I keep a copy of the formal wishbone properties.

Within this ZipCPU RTL directory are four bus wrappers for the [core of the
ZipCPU](core/zipcore.v).  Two of these are Wishbone wrappers:
[ZipBones](zipbones.v) and [ZipSystem](zipsystem.v).  Another two are AXI-lite
and AXI wrappers respectively: [ZipAXIL](zipaxil.v) and [ZipAXI](zipaxi.v).
These wrappers connect an external wishbone or AXI-lite slave interface to
the debugging port of the CPU, so that the CPU can be reset, started, stopped,
stepped, and in general debugged.

The [ZipBones](./zipbones.v) would be the appropriate wrapper if you want the
CPU to fit in the tightest space possible (Ex: Digilent's [CMod
S6](https://github.com/ZipCPU/s6soc)).

Use the [ZipSystem](./zipsystem.v) if you want to couple some peripherals
tightly to the CPU.  These peripherals include:

- 2x [Interrupt controllers](./peripherals/icontrol.v)
- [Timers](peripherals/ziptimer), and an [experimental timer called zipjiffies](peripherals/zipjiffies.v) that's been with the CPU for some time
- [Performance counters](peripherals/zipcounter.v), to measure your performance
- A [Direct Memory Access Controller](./peripherals/wbdmac.v)
- Or even the [Memory Management Unit](./peripherals/zipmmu.v)

Neither [ZipBones](zipbones.v), [ZipAXIL](zipaxil.v), nor [ZipAXI](zipaxi.v)
contain these peripherals.  If you would like to use these peripherals with
these wrappers, they'll need to be located external to the CPU and connected
via your bus interconnect.

If you are just looking for the CPU's code itself, check out
[zipcore.v](core/zipcore.v) within the [core](core) subdirectory.
That's of the main core of the ZipCPU itself.
