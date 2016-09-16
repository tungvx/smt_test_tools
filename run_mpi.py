from mpi4py import MPI
import fnmatch
import os
import subprocess
import csv
import concurrent.futures
import re
import time

SMT2=".smt2"
BOUNDED_SMT2 = '.bound'

TIME_OUT = "timeout"
SAT = "sat"
UNSAT = "unsat"
UNKNOWN = "unknown"

PROBLEM='Problem'
TIME='time'
CPU_TIME='CPU time'
RESULT = 'result'
ERROR = 'error'

LOWER_BOUND = '(- 1000)'
UPPER_BOUND = '1000'

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

def solve(tool, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags):
  filename = generate_if_not_exists(root, smt2Filename, SOLVED_PROBLEM)
  # print timeout

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

  command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) \
            + "; bash -c \"TIMEFORMAT='time %3U + %3S time'; time timeout " + str(timeout) + " ./" + tool + " " \
            +  flags + " " + os.path.join(root, filename) + "\""
  
  # print (command)
  proc = subprocess.Popen(command,stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines = True, shell=True)
  iOut, iErr = proc.communicate()

  endTime = time.time()
  
  # print ("Returned code:",proc.returncode)

  # print ("ER:" + iErr.strip() + ":End ER")
  # print ("IO:" + iOut.strip() + ":End IO")

  # extract running time from iErr
  timeRegex = re.search("time (\d+\.\d+ \+ \d+\.\d+) time", iErr.strip())
  try:
    result[CPU_TIME] = eval(timeRegex.group(1))
  except Exception:
    result[CPU_TIME] = "Unparsable output"

  result[TIME] = endTime - startTime

  result[TOOL_RESULT] = iOut.strip()
  result[ERROR]=iErr.strip()

  # print (result[DREAL_RESULT])
  # print (result)
  # remove_file(result[PROBLEM])
  return result

def run(tool, directory, timeout, resultFile, SOLVED_PROBLEM, max_memory=4000000, flags=""):
	comm = MPI.COMM_WORLD
	rank = comm.Get_rank()
	size = comm.Get_size()

	# we need the number of processes to be greater than 1
	assert(size > 1)

	TOOL_RESULT = tool + " result"

	if rank == 0:
		file_index = 0
		sending_data = {}

		for i in range(size):
			if i > 0:
				sending_data[i] = []

		for root, dirnames, filenames in os.walk(directory):
			for filename in filenames:
				if filename.endswith(SMT2):
					receiving_rank = file_index%(size-1) + 1
					try:
						sending_data[receiving_rank].append((filename, root))
					except:
						sending_data[receiving_rank] = [(filename, root)]
					file_index += 1

		for receiving_rank, smt2_problems in sending_data.items():
			# print "Sending", smt2_problems, "to", receiving_rank
			# print (receiving_rank, len(smt2_problems))
			comm.send(smt2_problems, receiving_rank)

		# receiving result:
		import datetime
		import time
		log_folder_name = "logs_" + datetime.datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d_%H:%M:%S')

		TOOL_RESULT = tool + " result"
		HEADERS = [PROBLEM, RESULT, CPU_TIME, TIME, TOOL_RESULT]
		with open(resultFile, 'w+', 1) as csvfile:
			spamwriter = csv.DictWriter(csvfile, fieldnames=HEADERS, extrasaction='ignore')
			spamwriter.writeheader()
			for i in range(file_index):
				result = comm.recv(source=MPI.ANY_SOURCE)
				# write to output file
				spamwriter.writerow(result)

        		# write error to error file
				error_file_path = log_folder_name + os.path.abspath(result[PROBLEM])+".err.txt"
				error_folder = os.path.dirname(error_file_path)
				if not os.path.exists(error_folder):
					os.makedirs(error_folder)

				with open(error_file_path, 'w+', 1) as errFile:
					errFile.write(result[ERROR])

	else:
		data = comm.recv(source=0)
		# print ("Rank", rank, "receiving", len(data), "problems")
		for smt2Filename, root in data:
			result = solve(tool, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags)
			for key in result:
				result[key] = str(result[key])
			comm.send(result, 0)

# run("../veriT", "../test", 30, "veriT.csv", SMT2, 40000, "--disable-banner --disable-print-success")	    
# run("./veriT", "/work/tungvx/test", 30, "veriT.csv", SMT2, 40000, "--disable-banner --disable-print-success")	    
