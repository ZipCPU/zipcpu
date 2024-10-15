# Simulation

This directory hosts the ZipCPU's integrated environment and test scripts.
Many simulation tests are [defined here](sim_testcases.txt).

A basic test case consists of both the Verilog environment and a program.
The Verilog environment is one of either the [Wishbone](rtl/wb_tb.v) or
[AXI](rtl/axi_tb) test environments.  These include basic peripherals,
such as a memory, console, ZipCPU peripheral set, and one (or more) ZipCPU's.
The programs then interact with this environment to test whether or not
things within it work as expected.  The simulation environment is parameterized,
allowing multiple bus widths and CPU configurations to be tested.

## Building Software

Prior to any tests, the ZipCPU program for that test needs to be built and
then converted into a hex file.  The [Zip-GCC compiler suite](../sw) can be
used for building the tests into ELF executables, and the
[mkhex](verilator/mkhex.cpp) program can be used to convert these to hex
files suitable for loading in the simulator.

The easiest way of doing all of this is via make.  Make should first be run
in the [SW](../sw) directory to build the compiler suite.  The compiler suite
should then be added to your path.  Running Make in the [Verilator](verilator/)
subdirectory will then build [mkhex](mkhex.cpp) (and some other things).
Finally, runninig make in the [zipsw](zipsw/) directory will build the software
used for the simulation tests found here.

## Running tests

Once all of the prerequisites have been built, the test suite may be run via:

    perl sim_run.pl all

Options exist for running this script under either Icarus Verilog:

    perl sim_run.pl iverilog all

or under Verilator:

    perl sim_run.pl verilator all

There's also an option for running under Verilator and evaluating test
coverage, via:

    perl sim_run.pl cover all

Finishing a cover run requires an additional step using (open source) tools
not found in this repository.


Specific test cases may be run by replacing the `all` argument above with the
name of the test case.  Test case names are defined in the first column of the
[`sim_testcases.txt`](sim_testcases.txt) file.  See that file for more
information regarding its format.
