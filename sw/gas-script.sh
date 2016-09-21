#!/bin/bash

if [[ ! -d binutils-2.25 ]]
then
  tar -xjf ./binutils-2.25.tar.bz2
  cd binutils-2.25
  patch -p1 <../binutils-2.25.patch
  cd ..
fi

set +h
set -e
CLFS_HOST="x86_64-cross-linux-gnu"
CLFS_TARGET="zip"
INSTALL_BASE=`pwd`/install
mkdir -p ${INSTALL_BASE}/cross-tools
mkdir -p ${INSTALL_BASE}/tools/lib
mkdir -p build-gas
cd build-gas
AR=ar AS=as	\
../binutils-2.25/configure --with-gas --prefix=${INSTALL_BASE}/cross-tools \
	--host=${CLFS_HOST}	--target=${CLFS_TARGET}		\
	--with-sysroot=${INSTALL_BASE}				\
	--with-lib-path=${INSTALL_BASE}/tools/lib		\
	--disable-nls --disable-static --disable-multilib	\
	--enable-gold=yes --enable-plugins --enable-threads	\
	--disable-werror

