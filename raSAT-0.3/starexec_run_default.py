#!/usr/bin/env python
# Run: python smt.py filename.smt2 timeout
# timeout is in seconds

import os
import subprocess
import sys
import stat
import time

 
def remove_tmp (filename, version):
  try:
    os.remove(filename + '.' + version + '.tmp')
  except OSError:
    pass
    
  try:
    os.remove(os.path.splitext(filename)[0] + '.' + version +  '.out')
  except OSError:
    pass
    
  try:
    os.remove(os.path.splitext(filename)[0] + '.' + version +  '.in')
  except OSError:
    pass

def run_raSAT (filename, bounds):
  startTime = time.time()  

  raSATResult = "unknown"

  # remove tmps files:
  remove_tmp(filename, "")

  subprocess.call(["./raSAT-0.3", filename, bounds])
  
  # try read output of 0.3
  try:
    with open(filename + '.tmp', 'r') as outfile:
      raSATResult = outfile.read().rstrip()
      outfile.close()
  except IOError:
    pass
  

  return raSATResult

def run(filename, initLowerBound, initUpperBound):
  lowerBound = initLowerBound
  upperBound = initUpperBound
  raSATResult = "unknown"
  startTime = time.time()
  while (raSATResult == 'unknown'):
    raSATResult = run_raSAT(filename, 'lb=' + str(lowerBound) + ' ' + str(upperBound))
    
    if raSATResult == 'unsat':
      raSATResult = run_raSAT(filename, 'lb=-inf inf')  
  print (raSATResult)

  # remove tmps files:
  remove_tmp(filename, "")

# get timeout from environment
timeout = float(os.environ.get('STAREXEC_CPU_LIMIT'))

run(sys.argv[1], -10, 10)