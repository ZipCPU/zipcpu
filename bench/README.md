Note: The majority of the testing that was once kept in this directory has
been moved to the [SIM](../sim/) directory.  The biggest exception to this
rule is the [FORMAL](formal/) directory, which is where the formal models
and SymbiYosys scripts are kept.

- [ASM](asm/): Contains a set of assembly language programs once used to test
  the ZipCPU.

- [CPP](cpp/): Contains the remains of a test bench for the data cache.  The
  test bench was a feel good, but frankly the formal proof caught any actual
  bugs in the data cache, and so I doubt I'll use this test bench again.

- [RTL](rtl/): Contains an outdated memory device, and potential MMU test bench.
  Given that the MMU needs to be rewritten, and that another memory device
  model is found in the SIM directory, this directory may be removed at any
  time.

- [MCY](mcy/): At one time, I tried using MCY (Mutation Coverage with Yosys)
  on the ZipCPU.  The tool never matched the ZipCPU's verification very well,
  and so support was never maintained.

