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
VERSION=gcc-6.2.0
ZVERSION=gcc-6.2.0-zip
# if [[ ! -d $ZVERSION ]]
# then
  # tar -xjf ./$VERSION.tar.bz2 --transform s,$VERSION,$ZVERSION,
  # if [[ -e ../gcc-zippatch.path ]];
  # then
    # cd gcc-6.2.0-zip
    # patch -p1 <../gcc6-zippatch.patch
    # cd ..
  # else
    # echo "No Patch file!"
    # exit -1;
  # fi
  # if [[ -d build-gcc ]]
  # then
    # # Remove any incomplete build projects from ... possibly other versions
    # # This way we can reuse the build directory
    # rm -rf build-gcc/
  # fi
# fi

set +h
set -e
CLFS_HOST=$MACHTYPE
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

../$ZVERSION/configure --with-gas	\
        --prefix=${INSTALL_BASE}/cross-tools		\
        --target=${CLFS_TARGET}				\
        --with-pkgversion=zip-gcc-`date +%y%m%d`	\
        --disable-multilib				\
        --disable-threads --disable-tls			\
        --disable-libada --disable-libsanitizer		\
        --disable-libssp --disable-libquadmath		\
        --disable-libgomp --disable-libvtv		\
        --enable-checking --disable-nls			\
        --disable-sjlj-exceptions			\
        --disable-decimal-float --disable-fixed-point	\
        --disable-lto --disable-canonical-system-headers \
	--without-fp

echo $PATH | grep ${INSTALL_BASE}/cross-tools/bin \
	|| PATH=${INSTALL_BASE}/cross-tools/bin:$PATH
make
# make $* || true
# cd gcc; make $* || true
# cd ../; make $* all-libcc1 || true
# cd libcc1; make $* || true
# cd ../gcc; make $* || true
# make $* install || true

