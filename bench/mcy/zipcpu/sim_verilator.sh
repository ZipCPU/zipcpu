#!/bin/bash

# Pipe standard error stream to stdout
exec 2>&1

# Exit on any non-zero error code along the way
set -ex

VROOT=/usr/local/share/verilator
VINC=${VROOT}/include
INCFILES="-I${VROOT}/include -Iobj_dir"
CFLAGS="-Wall -O3"
# CPPDIR="../../../cpp"
CPPDIR="../.."
OBJ=obj_dir

{
	echo "read_ilang ../../database/design.il"
	while read -r idx mut; do
		echo "mutate -ctrl mutsel 8 ${idx} ${mut#* }"
	done < input.txt
	echo "write_verilog -attr2comment mutated.v"
} > mutate.ys

yosys -ql mutate.log mutate.ys
cp ${CPPDIR}/zipcpu.cpp     .
cp ${CPPDIR}/memsim.h       .
cp ${CPPDIR}/memsim.cpp     .
cp ${CPPDIR}/byteswap.cpp       .
cp ${CPPDIR}/byteswap.h         .
cp ${CPPDIR}/twoc.cpp       .
cp ${CPPDIR}/twoc.h         .
cp ${CPPDIR}/zipelf.cpp     .
cp ${CPPDIR}/zipelf.h       .
cp ${CPPDIR}/testb.h        .
cp ${CPPDIR}/zopcodes.h     .
cp ${CPPDIR}/zopcodes.cpp   .
cp ../../zipbones.v         .
ls ../../../../../
cp ../../cpudefs.v .
cp ../../cpudefs.h .
cp ../../simtest  .

echo "// verilator lint_off UNOPTFLAT"    > zipcpu.v
echo "// verilator lint_off CASEOVERLAP" >> zipcpu.v
echo "// verilator lint_off WIDTH"       >> zipcpu.v
cat mutated.v >> zipcpu.v
verilator -O3 --trace -cc zipbones.v
g++ ${CFLAGS} ${INCFILES} -DMCY -DZIPBONES -c zipcpu.cpp -o ${OBJ}/zipcpu.o
g++ ${CFLAGS} ${INCFILES} -c ${VINC}/verilated.cpp -o ${OBJ}/verilated.o
g++ ${CFLAGS} ${INCFILES} -c ${VINC}/verilated_vcd_c.cpp -o ${OBJ}/verilated_vcd.o
g++ ${CFLAGS} ${INCFILES} -c memsim.cpp -o ${OBJ}/memsim.o
g++ ${CFLAGS} ${INCFILES} -c twoc.cpp   -o ${OBJ}/twoc.o
g++ ${CFLAGS} ${INCFILES} -c zipelf.cpp -o ${OBJ}/zipelf.o
g++ ${CFLAGS} ${INCFILES} -c byteswap.cpp -o ${OBJ}/byteswap.o
g++ ${CFLAGS} ${INCFILES} -c zopcodes.cpp -o ${OBJ}/zopcodes.o
cd obj_dir
make -f Vzipbones.mk
g++ zipcpu.o memsim.o twoc.o zipelf.o byteswap.o zopcodes.o verilated.o verilated_vcd.o Vzipbones__ALL.a -lelf -o ../zipcpu_tb
cd ..

zipcpu_tb 0 ../../simtest > goodsim_${idx}.out || true
good_sum=$(md5sum goodsim_${idx}.out | awk '{ print $1; }')
while read idx mut; do

	zipcpu_tb ${idx} ../../simtest > sim_${idx}.out || true
	this_sum=$(md5sum sim_${idx}.out | awk '{ print $1; }')
	echo "SUM " $this_sum
	if [ $good_sum = $this_sum ]; then
		echo "$idx PASS" >> output.txt
	else
		echo "$idx FAIL" >> output.txt
	fi
done < input.txt
exit 0
