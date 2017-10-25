import subprocess
from subprocess import TimeoutExpired
import os

command = "ulimit -Sv 4000000; ulimit -St 60; bash -c 'TIMEFORMAT=\"{\\\"CPU time\\\": %3U + %3S, \\\"Wall time\\\": %3R}\"; time timeout " \
    + "60 /work/s1520002/verit/veriT/veriT --disable-banner --disable-print-success --reduce-path=/work/s1520002/verit/veriT/extern/reduce/bin/redcsl" \
    + " /work/s1520002/QF_NRA/zankl/matrix-3-all-9.smt2'"

print (command)

try:
    proc = subprocess.Popen(command,stdout=subprocess.PIPE, 
                                                stderr=subprocess.PIPE, universal_newlines = True, 
                                                shell=True, preexec_fn=os.setsid)
except Exception as e:
    print (e)
    pass   

try:    
    iOut, iErr = proc.communicate(timeout=config[WALL_TIMEOUT])
    errStr = iErr.strip()
except TimeoutExpired:
    result[RESULT] = "Timed out"

    errStr = None
    iOut = None
    iErr = None
    
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
    except Exception:
        pass