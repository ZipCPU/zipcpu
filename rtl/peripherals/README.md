# ZipCPU Peripherals

These are not your normal peripherals, per se, but rather peripherals that
get tightly integrated with the CPU when built with the ZipSystem.  These
include:

- [icontrol.v](./icontrol.v), an interrupt controller

- [zipcounter.v](./zipcounter.v), a *really* simple counter, for estimating CPU performance.  The counter will interrupt the CPU if/when it ever rolls over.

- [ziptimer.v](./ziptimer.v), a similarly simple timer.  It just counts down and creates an interrupt

- [zipjiffies.v](./zipjiffies.v).  Modeled after the Jiffies used within the Linux Kernel, the zipjiffies peripheral counts up one count per clock.  Numbers written to it request an interrupt when the clock gets to the number written.  Hence, you can get really fine grained timing control using this peripheral.

- [wbdmac.v](./wbdmac.v), a direct memory access controller.  This can be used to copy memory, or even copy memory on an interrupt.  Source and destination addresses may or may not increment depending upon how the controller is set.  As of today, though, this controller only handles 32-bit transfers.

- [zipmmu.v](./zipmmu.v), an experimental MMU.  Has only been tested offline.
  An implementation exists which integrates this MMU, however that integration
  has not been tested so there are certainly some integration bugs remaining.

*All of these peripherals* have been formally proven.
   
If you are looking for the more normal peripherals, block RAM, SDRAM, etc.,
feel free to examine some of the distributions that use the ZipCPU.


