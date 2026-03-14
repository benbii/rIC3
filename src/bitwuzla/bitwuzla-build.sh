#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
jobs="$(nproc 2>/dev/null || sysctl -n hw.logicalcpu)"

test -f gmp.txz || wget -O gmp.txz https://gmplib.org/download/gmp/gmp-6.3.0.tar.xz
test -f mpfr.txz || wget -O mpfr.txz https://www.mpfr.org/mpfr-current/mpfr-4.2.2.tar.xz
test -d gmp-6.3.0 || tar xf gmp.txz
test -d mpfr-4.2.2 || tar xf mpfr.txz

cd gmp-6.3.0
if ! test -f .libs/libgmp.a; then
  CC=clang CFLAGS=-flto ./configure --enable-shared=no
  make -j"$jobs"
fi

cd ../mpfr-4.2.2
if ! test -f src/.libs/libmpfr.a; then
  CC=clang CFLAGS=-flto ./configure --enable-lto --disable-shared \
    --with-gmp-build=../gmp-6.3.0
  make -j"$jobs"
fi

cd ..
cmake -S. -Bbuild \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_FLAGS=-flto \
  -DCMAKE_CXX_FLAGS=-flto
cmake --build build -j"$jobs"
