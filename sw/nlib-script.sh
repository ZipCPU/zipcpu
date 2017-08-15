#!/bin/bash

VERSION="newlib-2.5.0"
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
which zip-gcc > /dev/null
if [[ $? != 0 ]]
then
  echo "Nlib-script Error: Unable to find zip-gcc in your path"
  echo "PATH=$PATH"
  exit -1
fi

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

