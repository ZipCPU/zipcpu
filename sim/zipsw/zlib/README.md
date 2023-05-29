## C-Library, CPU Specific Glue Logic

The CPU library requires some CPU specific glue logic.  This directory
contains that glue logic.  Most of the logic is specific to the *board*
or *design*, rather than the CPU.  When porting to a new design, two
files need to be adjusted:

- [syscalls.c](syscalls.c): Needs to be adjusted for the location and details
  of the console, and any other external peripherals which may be connected
  to the CPU.

- [bootloader.h](bootloader.h): While this file doesn't need to be updated
  per se, the values within it need to be address locations by the linker
  script--not included here--in order for the CPU loader,
  [crt0.c](crt0.c), to work.

