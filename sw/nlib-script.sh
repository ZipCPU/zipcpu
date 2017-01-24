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
GCC_BASE=${INSTALL_BASE}/../build-gcc/
PATH=$PATH:${INSTALL_BASE}/cross-tools/bin:${GCC_BASE}/gcc
../$VERSION-zip/configure --prefix=${INSTALL_BASE}/cross-tools	\
        --target=${CLFS_TARGET}	--host=$MACHTYPE --without-fp

make

