#!/bin/bash
################################################################################
##
## Filename:	gcc-script.sh
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To handle all of the GCC configuration options properly.  This
##		both runs the GCC configure script, as well as initially running
##	make on the resulting configured directory.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2016, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
if [[ ! -d gcc-6.2.0-zip ]]
then
  tar -xjf ./gcc-6.2.0.tar.bz2 --transform s,gcc-6.2.0,gcc-6.2.0-zip,
  cd gcc-6.2.0-zip
  patch -p1 <../gcc6-zippatch.patch
  cd ..
  if [[ -d build-gcc ]]
  then
    # Remove any incomplete build projects from ... possibly other versions
    # This way we can reuse the build directory
    rm -rf build-gcc/
  fi
fi

uname -a | grep x86 > /dev/null
if [[ $? != 0 ]]; then
  echo "This build script only works for x86_64 machines"
  echo "You will need to change the CLFS_HOST line if you wish to build"
  echo "on any other type of host."
  exit 1
fi

set +h
set -e
CLFS_HOST="x86_64-cross-linux-gnu"
# CLFS_HOST="arm-unknown-linux-gnueabihf" # For a Raspberry Pi ??
CLFS_TARGET="zip"
INSTALL_BASE=`pwd`/install
mkdir -p ${INSTALL_BASE}/cross-tools
mkdir -p ${INSTALL_BASE}/tools/lib
mkdir -p ${INSTALL_BASE}/usr/include
mkdir -p build-gcc
cd build-gcc

AR_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ar
AS_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-as
LD_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ld
NM_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-nm
OBJCOPY_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-objcopy
OBJDUMP_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-objdump
READELF_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-readelf
STRIP_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-strip

AS=as AR=ar ../gcc-6.2.0-zip/configure --with-gas	\
        --prefix=${INSTALL_BASE}/cross-tools		\
        --target=${CLFS_TARGET} --host=${CLFS_HOST}	\
        --with-pkgversion=zip-gcc-`date +%y%m%d`	\
        --disable-multilib				\
        --disable-threads --disable-tls			\
        --disable-libada --disable-libsanitizer		\
        --disable-libssp --disable-libquadmath		\
        --disable-libgomp --disable-libvtv		\
        --enable-checking --disable-nls			\
        --disable-sjlj-exceptions			\
        --disable-decimal-float --disable-fixed-point	\
        --disable-lto --disable-canonical-system-headers

echo $PATH | grep ${INSTALL_BASE}/cross-tools/bin \
	|| PATH=${INSTALL_BASE}/cross-tools/bin:$PATH
make $* || true
cd gcc; make $* || true
cd ../; make $* all-libcc1 || true
cd libcc1; make $* || true
cd ../gcc; make $* || true
make $* install || true

