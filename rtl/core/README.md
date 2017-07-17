## The Core of the ZipCPU

Here are the core files to the ZipCPU.  In here, you'll find not only the
[main ZipCPU core](./zipcpu.v), but also:

- Several prefetch routines

  o [prefetch.v](./prefetch.v) an older prefetch module that only fetched
    one instruction at a time, and so prevented pipelining

  o [pipefetch.v](./pipefetch.v), my first attempt at building a prefetch with
    cache.  It took a rather unique approach to the cache, implementing it as
    a rolling window in memory.  This file really sticks around for historical
    reasons, but not much more.

  o [dblfetch.v](./dbgfetch.v), fetches two instructions at once (on subsequent
    clocks).  This is designed to increase the speed of the CPU when it isn't
    pipelined, by exploiting the fact that many memory accesses go faster for
    the second access.

  o [pfcache.v](./pfcache.v), this is the current/best instruction cache
    for the CPU.


- [idecode.v](./idecode.v), an instruction decoder

- Several memory access routines

  o [memops.v](./memops.v), a typical/traditional one memory operation at a
    time means of accessing memory.  This was my first approach to memory,
    and the appropriate approach still when the CPU is not running in its
    pipelind mode.

  o [pipemem.v](./pipemem.v), a faster memory access method that groups
    consecutive memory accesses together into a pipelined bus access.
    This routine has so far compensated for the fact that the ZipCPU does not
    (yet) have an integrated data cache.

  o [dcache.v](./dcache.v), is my attempt at building a data cache.  This
    has never been integrated with the CPU, and may not be integrated until
    the MMU is also integrated.

- [div.v](./div.v), the divide unit

- [cpuops.v](./cpuops.v), the ALU unit

The defines within [cpudefs.v](../cpudefs.v) will determine which of these
modules gets linked into your CPU.

