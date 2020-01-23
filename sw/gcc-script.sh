#!/bin/bash
################################################################################
##
## Filename:	gcc-script.sh
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To handle all of the GCC configuration options properly.  This
##		runs the GCC configure script, using options known to work
##	with the ZipCPU.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2016-2020, Gisselquist Technology, LLC
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
if [[ -z "$INSTALLD" ]]
then
  INSTALLD=`pwd`/install
fi
if [[ ! $(which zip-as) ]]
then
  echo "GCC-script ERROR: Unable to find zip-as, the ZipCPU assembler, in your path"
  exit -1
fi
INSTALL_BASE=${INSTALLD}
mkdir -p ${INSTALL_BASE}/cross-tools
mkdir -p ${INSTALL_BASE}/tools/lib
mkdir -p ${INSTALL_BASE}/usr/include
mkdir -p build-gcc
cd build-gcc

AS_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-as
AR_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ar
NM_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-nm
LD_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ld

../$ZVERSION/configure --with-gas			\
        --prefix=${INSTALL_BASE}/cross-tools		\
        --target=${CLFS_TARGET}				\
        --with-pkgversion=zip-gcc-`date +%y%m%d`	\
        --disable-multilib				\
        --disable-threads --disable-tls			\
        --enable-checking --disable-nls			\
        --with-newlib

echo $PATH | grep ${INSTALL_BASE}/cross-tools/bin \
	|| export PATH=$PATH:${INSTALL_BASE}/cross-tools/bin
