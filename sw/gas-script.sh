#!/bin/bash
################################################################################
##
## Filename:	sw/gas-script.sh
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To configure binutils to properly build the binutils portion of
##		the ZipCPU toolchain.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2016-2025, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
VERSION=binutils-2.27

## Patch the original version
## {{{
if [[ ! -d $VERSION-zip/ ]]
then
  tar -xjf ./$VERSION.tar.bz2 --transform s,$VERSION,$VERSION-zip,
  if [[ -e gas-zippatch.patch ]]
  then
    cd $VERSION-zip
    patch -p1 <../gas-zippatch.patch
    cd ..
  else
    echo "ZipCPU binutils patch not found"
  fi
fi
## }}}

## Set up a install directory
## {{{
set +h
set -e
CLFS_HOST=$MACHTYPE
CLFS_TARGET="zip"
if [[ -z "$INSTALLD" ]]
then
  INSTALLD=`pwd`/install
fi
INSTALL_BASE=${INSTALLD}
mkdir -p ${INSTALL_BASE}/cross-tools
## }}}

## Setup a build  directory
## {{{
mkdir -p build-gas
echo ../$VERSION-zip/configure
cd build-gas
## }}}

## Configure binutils
## {{{
AR=ar AS=as	\
../$VERSION-zip/configure --with-gas				\
	--prefix=${INSTALL_BASE}/cross-tools			\
	--target=${CLFS_TARGET}					\
	--disable-nls		--disable-multilib		\
	--enable-plugins	--enable-threads		\
	--disable-werror
## }}}
