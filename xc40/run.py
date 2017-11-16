import sys
from constants import *
import csv
import re
from configure import *
import subprocess
import os
from subprocess import TimeoutExpired
import time
import signal
import psutil

tasks = eval(open("tasks.dict").read())

rank = int(sys.argv[1])
nprocs = int(sys.argv[2])

smt2No = len(tasks)

def kill(proc_pid):
    process = psutil.Process(proc_pid)
    for proc in process.children(recursive=True):
        proc.kill()
    process.kill()

# print (rank, nprocs, smt2No)

with open(str(rank)+".csv", "w+", 1) as outfile:
    spamwriter = csv.DictWriter(outfile, fieldnames=HEADERS, extrasaction='ignore')
    # spamwriter.writeheader()

    for idx in range(smt2No):
        if idx % nprocs == rank:
            # print idx, tasks[idx]
            result= {PROBLEM:tasks[idx]}

            # get status of the benchmark
            try:
                f = open(tasks[idx])
                m = re.search('\(set-info :status (sat|unsat|unknown)\)', f.read())
                if m:
                    result[STATUS]=m.group(1)
            except IOError:
                pass

            startTime = time.time()
            
            command = "ulimit -Sv " + str(config[MAX_MEMORY]) + "; ulimit -St " + str(config[TIMEOUT]) \
                    + "; bash -c 'TIMEFORMAT=\"{\\\"CPU time user\\\": %3U, \\\"Wall time\\\": %3R, \\\"CPU time sys\\\": %3S}\"; time " \
                    + config[TOOL_COMMAND] + " " +  config[FLAGS] + " " + tasks[idx] + "'"

            # command = "ls"

            # print (command)
            # exit()

            # print (command)
            try:
                proc = subprocess.Popen(command,stdout=subprocess.PIPE, 
                                                            stderr=subprocess.PIPE, universal_newlines = True, 
                                                            shell=True)
            except Exception as e:
                print (e)
                pass   

            # proc.wait()

            errStr = None
            iOut = None
            iErr = None

            try:    
                iOut, iErr = proc.communicate(timeout=config[WALL_TIMEOUT])
                errStr = iErr.strip()
            except TimeoutExpired:
                result[RESULT] = "Timed out"
                
                try:
                    # os.killpg(os.getpgid(proc.pid), signal.SIGXCPU)
                    # os.kill(proc.pid, signal.SIGXCPU)
                    # iOut, iErr = proc.communicate(timeout=config[WALL_TIMEOUT])

                    # print (iOut.strip())
                    kill(proc.pid)
                except Exception as e:
                    print (e)
                    pass
                    
                # result[TIME] = time.time() - startTime
                # result[CPU_TIME] = result[TIME]

                # continue


            endTime = time.time()

            print (errStr)

            try:
                result[SOLVED_BY] = re.search("solved_by: (.*)", errStr).group(1)
            except:
                result[SOLVED_BY] = "Failed"

            try:
                m = re.search("\{\"CPU time user\": (.*), \"Wall time\": (.*), \"CPU time sys\": (.*)\}", errStr)
                result[CPU_TIME_USER] = eval(m.group(1))
                result[CPU_TIME_SYS] = eval(m.group(3))
                result[TIME] = eval(m.group(2))
            except Exception:
                result[TIME] = endTime - startTime
                result[CPU_TIME_USER] = "Failed"
                result[CPU_TIME_SYS] = "Failed"

            try:
                result[ICP_TIME] = re.search("icp_time: (\d+\.\d+)", errStr).group(1)
            except:
                result[ICP_TIME] = "Failed"

            try:
                result[PARSING_TIME] = re.search("parsing_time: (\d+\.\d+)", errStr).group(1)
            except:
                result[PARSING_TIME] = "Failed"

            try:
                result[TESTING_TIME] = re.search("testing_time: (\d+\.\d+)", errStr).group(1)
            except:
                result[TESTING_TIME] = "Failed"

            try:
                result[IVT_TIME] = re.search("ivt_time: (\d+\.\d+)", errStr).group(1)
            except:
                result[IVT_TIME] = "Failed"

            try:
                result[DECOMP_TIME] = re.search("decomp_time: (\d+\.\d+)", errStr).group(1)
            except:
                result[DECOMP_TIME] = "Failed"

            try:
                result[REDUCE_TIME] = re.search("reduce_time: (\d+\.\d+)", errStr).group(1)
            except:
                result[REDUCE_TIME] = "Failed"          


            try:
                result[RESULT] = iOut.strip()
            except Exception:
                pass


            spamwriter.writerow(result)

            # execute the program