## ZipCPU Simulation Software

This directory contains a set of files that may be used when running simulation
based tests on the CPU.  These tests include:

- [cputest.c](cputest.c): The primary CPU smoke testing program, designed to
  exercise all features of the CPU in any current configuration.

- [hellosim.s](hellosim.s): Tests the SOUT/NOUT instruction set of the ZipCPU.
  A very basic program.  This will likely succeed and pass even if the
  [cputest.c](cputest.c) does not.

- [hello.c](hello.c): You basic "Hello World" program.  This offers a basic
  (although not complete) test of the C-library.

- [hellostep.c](hellostep.c): A modified "Hello, World" program designed to test
  if the stepping mode of the CPU works.  Specifically, when running this test,
  the supervisor will step the Hello World program one instruction at a time.
  If the program still works, we'll assume stepping worked as designed.

- [lockcheck.c](lockcheck.c): Designed to test the ZipCPU's "LOCK" instruction,
  this test creates a set of ZipCPU tasks, and then tries to execute those
  tasks one instruction at a time.  Each task attempts to grab a MUTEX, and
  then enter a MUTEX controlled section, increment a counter, and then release
  the MUTEX.  Each task is stepped one instruction at a time as an attempt to
  stress this capability.

