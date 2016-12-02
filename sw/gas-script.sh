#!/bin/bash
################################################################################
##
## Filename:	gas-script.sh
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To configure binutils to properly build the binutils portion of
##		the ZipCPU toolchain.
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
if [[ ! -d binutils-2.25 ]]
then
  tar -xjf ./binutils-2.25.tar.bz2
  cd binutils-2.25
  patch -p1 <../binutils-2.25.patch
  cd ..
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
# CLFS_HOST="arm-unknown-linux-gnueabihf" # For a Raspberry Pi
CLFS_TARGET="zip"
INSTALL_BASE=`pwd`/install
mkdir -p ${INSTALL_BASE}/cross-tools
mkdir -p build-gas
cd build-gas
AR=ar AS=as	\
../binutils-2.25/configure --with-gas				\
	--prefix=${INSTALL_BASE}/cross-tools			\
	--host=${CLFS_HOST}	--target=${CLFS_TARGET}		\
	--disable-nls		--disable-multilib		\
	--enable-plugins	--enable-threads		\
	--disable-werror

