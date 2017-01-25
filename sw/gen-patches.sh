#!/bin/bash

diff -Naur --exclude="*.swp" binutils-2.27/ binutils-2.27-zip/ > gas-zippatch.patch
diff -Naur --exclude="*.swp" gcc-6.2.0/     gcc-6.2.0-zip/     > gcc-zippatch.patch
diff -Naur --exclude="*.swp" newlib-2.5.0/  newlib-2.5.0-zip/  > nlib-zippatch.patch

cp gas-zippatch.patch  `date +%Y%m%d`-gas.patch
cp gcc-zippatch.patch  `date +%Y%m%d`-gcc.patch
cp nlib-zippatch.patch `date +%Y%m%d`-nlib.patch

