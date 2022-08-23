## The Core of the ZipCPU

Here are the core files to the ZipCPU.  In here, you'll find not only the
[main ZipCPU core](zipcore.v), but also:

- Several prefetch routines

  o [prefetch.v](prefetch.v) an older prefetch module that only fetched
    one instruction at a time, and so prevented pipelining.
    [axilfetch](axilfetch.v) offers a similar version of this prefetch, using
    the AXI-Lite bus protocol, as long as `FETCH_LIMIT <= 1`.

  o [pipefetch.v](pipefetch.v), was first attempt at building a prefetch with
    cache.  It took a rather unique approach to the cache, implementing it as
    a rolling window in memory.  This file is now abandonware.  It only
    remains as part of the repository for historical reasons, but not much more.

  o [dblfetch.v](dbgfetch.v), fetches two instructions at once (on subsequent
    clocks).  This is designed to increase the speed of the CPU when it isn't
    pipelined, by exploiting the fact that many memory accesses go faster for
    the second access.
    [axilfetch](axilfetch.v) offers a similar version of this prefetch, using
    the AXI-Lite bus protocol, as long as `FETCH_LIMIT == 2`.

  o [axilfetch.v](axilfetch.v) is my basic (non-cached) AXI/AXI-Lite fetch
    implementation.  As discussed above, it implements an analog of the
    [prefetch.v](prefetch.v) implementation when `FETCH_LIMIT <= 1`,
    an analog of the [dblfetch.v](dblfetch.v) implementation when
    `FETCH_LIMIT == 2`.  It also implements a FIFO based approach if ever
    `FETCH_LIMIT > 2`.  This approach (currently) has no wishbone analog.

  o [pfcache.v](pfcache.v), this is the current/best Wishbone instruction
    cache for the CPU.  The AXI version of this cache may be found in
    [axiicache.v](axiicache.v).


- [idecode.v](./idecode.v), an instruction decoder

- Several memory access routines

  o [memops.v](./memops.v), a typical/traditional one memory operation at a
    time means of accessing memory.  This was my first approach to memory,
    and the appropriate approach still when the CPU is not running in its
    pipelind mode.  [axilops](axilops.v) and [axiops.v](axiops.v) are
    AXI-Lite and AXI versions of this basic controller respectively.

  o [pipemem.v](./pipemem.v), a faster memory access method that groups
    consecutive memory accesses together into a pipelined bus access.
    This routine has so far compensated for the fact that the ZipCPU does not
    (yet) have an integrated data cache.
    [axilpipe.v](axilpipe.v) and [axipipe.v](axipipe.v) are
    AXI-Lite and AXI versions of this pipelined memory controller respectively.

  o [dcache.v](./dcache.v), is my attempt at building a data cache.
    [axidcache.v](axidcache.v) is an AXI version of this data cache.
    There is no AXI-Lite version of this cache.

- [div.v](./div.v), the divide unit

- [cpuops.v](./cpuops.v), the ALU unit

The defines within [cpudefs.v](../cpudefs.v) will determine which of these
modules gets linked into your CPU.

