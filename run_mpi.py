from mpi4py import MPI
import fnmatch
import os
import subprocess
import csv
import concurrent.futures
import re
import time
from subprocess import TimeoutExpired
import signal
import shutil
import io
from time import sleep
import random
import psutil

SMT2=".smt2"
BOUNDED_SMT2 = '.bound'

TIME_OUT = "timeout"
SAT = "sat"
UNSAT = "unsat"
UNKNOWN = "unknown"

PROBLEM='Problem'
TIME='time'
CPU_TIME='CPU time'
RESULT = 'status'
ERROR = 'error'
ICP_TIME = "ICP time"
TESTING_TIME = "Testing time"
DECOMP_TIME = "Decomp time"
REDUCE_TIME = "Reduce time"
IVT_TIME = "IVT time"

LOWER_BOUND = '(- 1000)'
UPPER_BOUND = '1000'

import argparse
parser=argparse.ArgumentParser(description="""Argument Parser""")

parser.add_argument('-change_dir', action='store_true', default=False)
parser.add_argument('-gurobi_key', action='store_true', default=False)
parser.add_argument('-log_error', action='store_true', default=False)
parser.add_argument('-collect_lra', action='store_true', default=False)
parser.add_argument('-scrambling', action='store_true', default=False)
parser.add_argument('-storereducelog', action='store_true', default=False)
parser.add_argument('-cp_to_pwd', action='store_true', default=False)

args = parser.parse_args()

change_dir = args.change_dir
log_error = args.log_error
gurobi_key = args.gurobi_key
collect_lra = args.collect_lra
scrambling = args.scrambling
storereducelog = args.storereducelog
cp_to_pwd = args.cp_to_pwd

def kill(proc_pid):
    process = psutil.Process(proc_pid)
    for proc in process.children(recursive=True):
        proc.kill()
    process.kill()

def gen_bounds(root, filename):
    filePath = os.path.join(root, filename)
    with open(filePath, 'r') as inputFile:
        content = inputFile.read()
        # content = content.replace('(check-sat)', '').strip()
        # content = content.replace('(exit)', '').strip()

        asserts = []
        for m in re.finditer(r"\(declare-fun (.*) \(\) (Real|Int)\)", content):
            asserts.append('(assert (>= {} {}))'.format (m.group(1), LOWER_BOUND))
            asserts.append('(assert (<= {} {}))'.format (m.group(1), UPPER_BOUND))

        # content += '\n' + '\n'.join(asserts)
        # content += '\n(check-sat)\n'
        # content += '(exit)\n'

        # add assertions into the content:
        content = content.replace('(check-sat)', '\n'.join(asserts) + '\n(check-sat)')

        # print (content)

        # Write content into new file:
        with open(filePath + BOUNDED_SMT2, 'w+') as boundFile:
            boundFile.write(content)

        return filename + BOUNDED_SMT2

def process_gurobi_key():
    import socket
    hostname = socket.gethostname()
    
    # check if license exist:
    if not os.path.exists("/work/tungvx/gurobi/%s/gurobi.lic" % (hostname, )):
        with open("/home/s1310007/licenses.gurobi","r") as myfile:
            license = eval(myfile.read())[hostname]
            os.popen("echo /work/tungvx/gurobi/%s | grbgetkey %s" % (hostname, license,))


def generate_if_not_exists(root, smt2Filename, SOLVED_PROBLEM):
    if SMT2 == SOLVED_PROBLEM:
        return smt2Filename
    elif BOUNDED_SMT2 == SOLVED_PROBLEM:
        return gen_bounds(root, smt2Filename)

def remove_file(filePath):
    try:
        os.remove(filePath)
    except OSError:
        pass

def solve(tool, tool_exec, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags):
    filename = generate_if_not_exists(root, smt2Filename, SOLVED_PROBLEM)
    # print timeout

    full_filename = os.path.join(root, filename)

    result= {PROBLEM:os.path.join(root, filename)}

    #try to get the result of the problem:
    try:
        f = open(os.path.join(root, filename))
        m = re.search('\(set-info :status (sat|unsat|unknown)\)', f.read())
        if m:
            result[RESULT]=m.group(1)
    except IOError:
        pass
    
    # command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) + "; ./" + tool + " " +  flags + " " + os.path.join(root, filename)
    # command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) \
    #           + "; /usr/bin/time --format='time %U + %S time' ./" + tool + " " \
    #           +  flags + " " + os.path.join(root, filename)

    startTime = time.time()
    wall_timeout = timeout
    

    import random
    import sys
    seed = random.randrange(0, 2147483647)

    if scrambling:
        command = "rm -rf scrambler.smt2 && ./process " + full_filename \
                    + " " + str(seed) + " > scrambler.smt2 &&"
        new_smtfile = "scrambler.smt2"
    else:   
        command = ""
        new_smtfile = full_filename

    command += "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) \
                    + "; bash -c 'TIMEFORMAT=\"{\\\"CPU time\\\": %3U + %3S, \\\"Wall time\\\": %3R}\"; time timeout " + str(wall_timeout) + " " + tool_exec + " " \
                    +  flags + " " + new_smtfile + "'"
    

    if gurobi_key:
        import socket
        hostname = socket.gethostname()
        command = "export GRB_LICENSE_FILE=/work/tungvx/gurobi/%s/gurobi.lic; " % (hostname, ) + command

    # print (command)


    try:
        proc = subprocess.Popen(command,stdout=subprocess.PIPE, 
                                                    stderr=subprocess.PIPE, universal_newlines = True, 
                                                    shell=True)
    except Exception:
        pass    
    
    try:    
        iOut, iErr = proc.communicate(timeout=wall_timeout)
        errStr = iErr.strip()
    except TimeoutExpired:
        result[TOOL_RESULT] = "Timed out"
        try:
            # os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            kill(proc.pid)
        except Exception:
            pass
    except:
        pass

    # print (result.get(TOOL_RESULT))

    endTime = time.time()
    
    # print ("Returned code:",proc.returncode)

    # print ("ER:" + iErr.strip() + ":End ER")
    # print ("IO:" + iOut.strip() + ":End IO")

    # extract running time from iErr
    try:
        m = re.search("\{\"CPU time\": (.*), \"Wall time\": (.*)\}", errStr)
        result[CPU_TIME] = eval(m.group(1))
        result[TIME] = eval(m.group(2))
    except Exception:
        result[TIME] = endTime - startTime
        result[CPU_TIME] = result[TIME]

    try:
        result[TOOL_RESULT] = iOut.strip()
    except Exception:
        pass

    if not result[TOOL_RESULT]:
        try:    
            if "SIGCHLD" in iErr:
                result[TOOL_RESULT] = "SIGCHLD"
            elif "*** sfto_fctrf: factorization failed" in open("libreduce.log").read():
                result[TOOL_RESULT] = "factorization"
        except Exception:
            result[TOOL_RESULT] = ""
    
    if log_error:
        try:
            result[ERROR]=iErr.strip()
        except Exception:
            result[ERROR]=""

    try:
        result[ICP_TIME] = re.search("icp_time: (\d+\.\d+)", errStr).group(1)
    except:
        result[ICP_TIME] = "Failed"

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

    # print (result[DREAL_RESULT])
    # print (result)
    # remove_file(result[PROBLEM])
    return result

def run(tool, tool_exec, directory, timeout, resultFile, SOLVED_PROBLEM, max_memory=4000000, flags=""):
    comm = MPI.COMM_WORLD
    rank = comm.Get_rank()
    size = comm.Get_size()

    # we need the number of processes to be greater than 1
    assert(size > 1)

    TOOL_RESULT = tool + " result"

    HEADERS = [PROBLEM, RESULT, TOOL_RESULT, CPU_TIME, TIME, ICP_TIME, TESTING_TIME, IVT_TIME, DECOMP_TIME, REDUCE_TIME]

    if rank == 0:

        # create log folder name and send to all other ranks
        import datetime
        import time

        # try to create log folder until succesfull
        while True:
            running_date = datetime.datetime.fromtimestamp(time.time())
            log_folder_name = "logs_" + running_date.strftime('%Y-%m-%d_%H-%M-%S') +"_"+os.path.basename(os.path.normpath(directory))
            
            # create the folder
            try:
                os.makedirs(log_folder_name)
                break
            except FileExistsError:
                # sleep the thread a few
                sleep(random.uniform(0.001, 1))

        # create a README in 
        # if tool == "veriT":
        if False:
            with open(os.path.join(log_folder_name, "README"), "w+") as readme:
                try:
                    reduce_rev = os.popen("cd /work/tungvx/verit/veriT/extern/reduce-new/ && svn info | grep \"Revision\" | awk '{print $2}'").read().rstrip()
                except Exception as e:
                    reduce_rev = ""

                readme.write("Reduce rev: "+ reduce_rev +"\n")

                try:
                    reduce_path = os.popen("echo $VERIT_REDUCE_PATH").read().rstrip()
                except Exception as e:
                    reduce_path = ""

                readme.write("Reduce path: "+ reduce_path +"\n")

                readme.write("Scrambling: " + ("Yes" if scrambling else "No") + "\n");
                
                try:
                    veriT_branch = os.popen("cd /work/tungvx/verit/veriT && git rev-parse --abbrev-ref HEAD").read().rstrip()
                    veriT_rev = os.popen("cd /work/tungvx/verit/veriT && git rev-parse HEAD").read().rstrip()
                except Exception as e:
                    veriT_branch = ""
                    veriT_rev = ""

                readme.write("veriT rev: "+veriT_branch+"-"+veriT_rev+"\n")

                readme.write("Date of running experiment: " + running_date.strftime('%Y-%m-%d_%H:%M:%S')+ "\n")
                readme.write("Timeout: "+ str(timeout)+ " seconds\n")
                readme.write("Memory: "+ str(max_memory)+ " KBs\n")
                readme.write("veriT options: "+ str(flags)+ "\n")


        sent_comms = []
        for index in range(size-1):
            receiving_rank = index + 1
            sent_comms.append(comm.isend(log_folder_name, receiving_rank))

        for sent_comm in sent_comms:
            sent_comm.wait()

        smt2_files = []
        for root, dirnames, filenames in os.walk(directory):
            for filename in filenames:
                if filename.endswith(SMT2): #and "Ultimate" not in root and "Lasso" not in root:
                    smt2_files.append((filename, root));        

        total = len(smt2_files)
        received = 0
        # receiving result:

        sent_comms = []

        full_result_file = os.path.join(log_folder_name, resultFile)
        with open(full_result_file, 'w+', 1) as csvfile:
            spamwriter = csv.DictWriter(csvfile, fieldnames=HEADERS, extrasaction='ignore')
            spamwriter.writeheader()
            
            available_ranks = [i for i in range(1, size)]
            while smt2_files:
                while not available_ranks:
                    (proc_rank, result) = comm.recv(source=MPI.ANY_SOURCE)      
                    available_ranks.append(proc_rank);
                    csvfile.write(result)
                    received += 1

                filename_root = smt2_files.pop();
                proc_rank = available_ranks.pop();
                sent_comms.append(comm.isend(filename_root, proc_rank))

            
            while (received < total):
                (proc_rank, result) = comm.recv(source=MPI.ANY_SOURCE)      
                csvfile.write(result)
                received += 1

        # copy results file into log folder:
        if cp_to_pwd:
            try:
                os.system("cp " + full_result_file + " .");
            except Exception:
                pass

        for i in range(1, size):
            sent_comms.append(comm.isend(("exit", "exit"), i))

        for sent_comm in sent_comms:
            sent_comm.wait()

    else:
        # first, receiving log folder name:
        log_folder_name = comm.recv(source=0)

        # data = comm.recv(source=0)
        # print ("Rank", rank, "receiving", len(data), "problems")

        if gurobi_key:
            process_gurobi_key()

        if change_dir:
            # make sub-dir
            sub_dir = log_folder_name + "/" + str(rank)
            try:
                os.makedirs(sub_dir)
            except FileExistsError:
                pass

            # copy files into sub-dir
            shutil.copy2(tool, sub_dir)
            # shutil.copy2("cvc4", sub_dir)
            if scrambling:
                shutil.copy2("/work/tungvx/scrambler/process", sub_dir)
                shutil.copy2("/work/tungvx/scrambler/scrambler", sub_dir)
            #shutil.copy2("yices-smt2", sub_dir)
            #shutil.copy2("main", sub_dir)
            #shutil.copy2("tropical.py", sub_dir)

            # change working dir:
            os.chdir(sub_dir)

        if change_dir:
            new_log_folder_name = "../"
        else:
            new_log_folder_name = log_folder_name

        sent_comms = []
        # receive problem, solve it and return result:
        while True:
            with io.StringIO() as csvfile:
                spamwriter = csv.DictWriter(csvfile, fieldnames=HEADERS, extrasaction='ignore')
                (smt2Filename, root) = comm.recv(source=0)
                if smt2Filename=="exit" and root == "exit":
                    break

                result = solve(tool, tool_exec, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags)
                for key in result:
                    result[key] = str(result[key])

                spamwriter.writerow(result)
                sent_comms.append(comm.isend((rank, csvfile.getvalue()), 0))

                # cp linear formulas
                if collect_lra:
                    linear_smt_path = ".." +  os.path.abspath(result[PROBLEM].replace(".smt2", "_stropsat.smt2"))
                    linear_smt_folder = os.path.dirname(linear_smt_path)
                    try:
                        os.makedirs(linear_smt_folder)
                    except FileExistsError:
                        pass
                    try:
                        shutil.copy2("test.smt2",linear_smt_path)
                        from tempfile import mkstemp
                        from shutil import move
                        from os import remove, close
                        #Create temp file
                        fh, abs_path = mkstemp()
                        with open(abs_path,'w') as new_file:
                            with open(linear_smt_path) as old_file:
                                for line in old_file:
                                    new_file.write(line.replace("--benchmark--", result[PROBLEM][13:]).replace(";--status--", "(set-info :status {0})".format("unsat" if "unknown" in result[TOOL_RESULT] else ("sat" if "sat" in result[TOOL_RESULT] else "unknown"),)))
                        close(fh)
                        #Remove original file
                        remove(linear_smt_path)
                        #Move new file
                        move(abs_path, linear_smt_path)
                    except Exception as e:
                        pass
                # write error to error file
                if log_error:
                    error_file_path = new_log_folder_name + os.path.abspath(result[PROBLEM])+".err.txt"
                    error_folder = os.path.dirname(error_file_path)
                    try:
                        os.makedirs(error_folder)
                    except FileExistsError:
                        pass

                    try:
                        with open(error_file_path, 'w+', 1) as errFile:
                            errFile.write(result[ERROR])
                    except Exception as e:
                        print (e)
                        pass

                if storereducelog:
                    reduce_log_path=new_log_folder_name + os.path.abspath(result[PROBLEM].replace(".smt2", "_libreduce.log"))
                    reduce_log_folder = os.path.dirname(reduce_log_path)
                    try:
                        os.makedirs(reduce_log_folder)
                    except FileExistsError:
                        pass

                    try:
                        shutil.copy2("libreduce.log",reduce_log_path)
                    except Exception as e:
                        pass
        # remove pwd
        if change_dir:
            shutil.rmtree(os.getcwd())

        for sent_comm in sent_comms:
            sent_comm.wait()


# run("veriT", "/home/tungvx/ownCloud/higher_education/verit/veriT/veriT", "../test", 30, "veriT.csv", SMT2, 4000000, "--disable-banner --disable-print-success --reduce-path=/home/tungvx/ownCloud/higher_education/verit/veriT/extern/reduce/bin/redpsl")        
# run("./veriT", "/work/tungvx/test", 30, "veriT.csv", SMT2, 40000, "--disable-banner --disable-print-success")     
