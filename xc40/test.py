import subprocess
from subprocess import TimeoutExpired
import os
import signal
import psutil

command = "ulimit -Sv 4000000; ulimit -St 60; bash -c 'TIMEFORMAT=\"{\\\"CPU time\\\": %3U + %3S, \\\"Wall time\\\": %3R}\"; time timeout " \
    + "60 /work/s1520002/verit/veriT/veriT --disable-banner --disable-print-success --reduce-path=/work/s1520002/verit/veriT/extern/reduce/bin/redcsl" \
    + " /work/s1520002/QF_NRA/zankl/matrix-3-all-9.smt2'"

# command = "ulimit -Sv 4000000; bash -c 'TIMEFORMAT=\"{\\\"CPU time\\\": %3U + %3S, \\\"Wall time\\\": %3R}\"; time timeout " \
#     + "60 /home/tungvx/ownCloud/higher_education/verit/veriT/veriT --disable-banner --disable-print-success --reduce-path=/home/tungvx/ownCloud/higher_education/verit/veriT/extern/reduce/bin/redpsl" \
#     + " /home/tungvx/Downloads/QF_NRA/meti-tarski/sin/problem/7/weak2/sin-problem-7-weak2-chunk-0116.smt2'"

print (command)

RESULT = 'result'

result = {}

def kill(proc_pid):
    process = psutil.Process(proc_pid)
    for proc in process.children(recursive=True):
        proc.kill()
    process.kill()

try:
    proc = subprocess.Popen(command,stdout=subprocess.PIPE, 
                                                stderr=subprocess.PIPE, universal_newlines = True, 
                                                shell=True)
except Exception as e:
    print (e)
    pass   

try:    
    iOut, iErr = proc.communicate(timeout=20)
    errStr = iErr.strip()
except TimeoutExpired:
    result[RESULT] = "Timed out"

    errStr = None
    iOut = None
    iErr = None
    
    try:
        # os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        kill(proc.pid)
    except Exception:
        pass