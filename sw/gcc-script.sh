#!/bin/bash

if [[ ! -d gcc-5.3.0-zip ]]
then
  tar -xjf ./gcc-5.3.0.tar.bz2 --transform s,gcc-5.3.0,gcc-5.3.0-zip,
  cd gcc-5.3.0-zip
  patch -p1 <../gcc-5.3.0-specs-1.patch
  rm gcc/config/rs6000/sysv4.h.orig
  patch -p1 <../gcc-zippatch.patch
  cd ..
fi

set +h
set -e
CLFS_HOST="x86_64-cross-linux-gnu"
CLFS_TARGET="zip"
INSTALL_BASE=`pwd`/install
mkdir -p ${INSTALL_BASE}/cross-tools/bin
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

AS=as AR=ar ../gcc-5.3.0-zip/configure --with-gas      \
        --prefix=${INSTALL_BASE}/cross-tools           \
        --target=${CLFS_TARGET} --host=${CLFS_HOST}    \
        --with-sysroot=${INSTALL_BASE}                 \
        --with-lib-path=${INSTALL_BASE}/tools/lib      \
        --with-local-prefix=${INSTALL_BASE}/usr        \
        --with-pkgversion=zip-gcc-`date +%y%m%d`       \
        --disable-shared --disable-multilib            \
        --disable-threads --disable-tls                \
        --disable-libada --disable-libsanitizer        \
        --disable-libssp --disable-libquadmath         \
        --disable-libgomp --disable-libvtv             \
        --enable-checking --disable-nls                \
        --disable-sjlj-exceptions                      \
        --disable-decimal-float --disable-fixed-point  \
        --disable-lto --disable-canonical-system-headers

echo $PATH | grep ${INSTALL_BASE}/cross-tools/bin \
	|| PATH=$PATH:${INSTALL_BASE}/cross-tools/bin
make || true
cd gcc; make || true
cd ../; make all-libcc1 || true
cd libcc1; make || true
cd ../gcc; make || true
make install || true

