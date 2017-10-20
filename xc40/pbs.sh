#!/bin/bash
#PBS -N smt-exp
#PBS -q XLARGE
#PBS -l select=316:ncpus=36:mpiprocs=36
#PBS -j oe

cd $PBS_O_WORKDIR

module load gcc/6.2.0

export TMPDIR=/work/s1520002

# aprun -n 1 ./veriT ../../QF_NRA/zankl/matrix-1-all-11.smt2 --reduce-path=extern/reduce/bin/redcsl
aprun -n 11376 -N 36 ./run