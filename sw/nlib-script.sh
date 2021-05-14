#!/bin/bash
################################################################################
##
## Filename:	nlib-script.sh
## {{{
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To handle all of the newlib configuration options properly.
##		This runs the newlib C-library configure script, using options
##	that are currently known to work.
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2016-2021, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
VERSION="newlib-4.1.0"
ZVERSION=${VERSION}-zip

## Setup an install environment variable
## {{{
if [[ -z "$INSTALLD" ]]
then
  INSTALLD=`pwd`/install
fi
INSTALL_BASE=${INSTALLD}
if [[ ! -d $INSTALL_BASE ]]
then
  echo "I cant seem to find the install directory," $INSTALL_BASE
  exit -1
fi
## }}}

## Check for GCC, fail if its not found
## {{{
which zip-gcc > /dev/null
if [[ $? != 0 ]]
then
  echo "Nlib-script Error: Unable to find zip-gcc in your path"
  echo "PATH=$PATH"
  exit -1
fi
## }}}

## Download a copy of newlib and expand a directory filled with it
## {{{
if [[ ! -d ${ZVERSION} ]]
then
  if [[ ! -e ${VERSION}.tar.gz ]]
  then
    wget ftp://sourceware.org/pub/newlib/$VERSION.tar.gz
  fi
  tar -xaf $VERSION.tar.gz --transform s,$VERSION,$ZVERSION,
  if [[ -e nlib-zippatch.patch ]]
  then
    cd ${ZVERSION}
    patch -p1 <../nlib-zippatch.patch
    cd ..
  else
    echo "ERR: no patch file!"
    exit -1;
  fi
fi
## }}}

## Always rebuild newlib when running this script
## {{{
if [[ -d build-nlib ]]
then
  rm -rf build-nlib 
fi
## }}}

cp -R $VERSION-zip/newlib/libc/include/* ${INSTALL_BASE}/usr/include

set +h
set -e

mkdir build-nlib
cd build-nlib

## Configure Newlib for a subsequent build
## {{{
CLFS_HOST=$MACHTYPE
CLFS_TARGET="zip"
GCC_BASE=${INSTALL_BASE}/../build-gcc/
# PATH=$PATH:${INSTALL_BASE}/cross-tools/bin:${GCC_BASE}/gcc
../$VERSION-zip/configure --prefix=${INSTALL_BASE}/cross-tools	\
        --target=${CLFS_TARGET}	--host=$MACHTYPE
## }}}
