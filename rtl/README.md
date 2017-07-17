The ZipCPU RTL directory contains the two primary wrappers for the ZipCPU:
zipbones and zipsystem.  These wrappers connect an external wishbone slave
interface to the debugging port of the CPU, so that the CPU can be reset,
started, stopped, and in general debugged.

The [ZipBones](./zipbones.v) would be the appropriate wrapper if you want the
CPU to fit in the tightest space possible (Ex: Digilent's [CMod
S6](https://github.com/ZipCPU/s6soc)).

Use the [ZipSystem](./zipsystem.v) if you want to give the CPU some
basic peripherals, such as:

- 2x [Interrupt controllers](./peripherals/icontrol.v)
- Timers, and an experimental timer called zipjiffies that's been with the
  CPU for some time
- Performance counters, to measure your performance
- A [Direct Memory Access Controller](./peripherals/wbdmac.v)

If you are just looking for the CPU's code itself, check out
[zipcpu.v](https://github.com/ZipCPU/zipcpu/blob/master/rtl/cores/zipcpu.v)
within the
[cores](https://github.com/ZipCPU/zipcpu/tree/master/rtl/cores) subdirectory.
That's of the main core of the ZipCPU itself.

