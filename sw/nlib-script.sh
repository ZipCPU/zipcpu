#!/bin/bash

VERSION="newlib-2.5.0"
INSTALL_BASE=`pwd`/install
if [[ ! -d $INSTALL_BASE ]]
then
  echo "I cant seem to find the install directory," $INSTALL_BASE
  exit;
fi

if [[ ! -d $VERSION/ ]]
then
  tar -xvzf $VERSION.tar.gz
fi

# if [[ ! -d $VERSION-zip ]]
# then
#  tar -xvzf $VERSION.tar.gz --transform s,$VERSION,$VERSION-zip,
#  echo patch ... something here
# fi

if [[ -d build-nlib ]]
then
  rm -rf build-nlib 
fi

cp -R $VERSION-zip/newlib/libc/include/* ${INSTALL_BASE}/usr/include

set +h
set -e

mkdir build-nlib
cd build-nlib

CLFS_HOST=$MACHTYPE
CLFS_TARGET="zip"
INSTALL_BASE=`pwd`/install
GCC_BASE=${INSTALL_BASE}/../build-gcc/
CC_FOR_TARGET=${GCC_BASE}/xgcc
GCC_FOR_TARGET=${GCC_BASE}/xgcc
CXX_FOR_TARGET=${GCC_BASE}/xg++
AR_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ar
AS_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-as
LD_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ld
NM_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-nm
OBJCOPY_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-objcopy
OBJDUMP_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-objdump
RANLIB_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-ranlib
READELF_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-readelf
STRIP_FOR_TARGET=${INSTALL_BASE}/cross-tools/bin/zip-strip
PATH=$PATH:${INSTALL_BASE}/cross-tools/bin:${GCC_BASE}/gcc
../$VERSION-zip/configure --prefix=${INSTALL_BASE}/cross-tools	\
        --target=${CLFS_TARGET}	--host=$MACHTYPE --without-fp

make

