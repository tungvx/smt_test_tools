import fnmatch
import os
import subprocess
from subprocess import TimeoutExpired
import csv
import concurrent.futures
import re
import time
import signal

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

LOWER_BOUND = '(- 1000)'
UPPER_BOUND = '1000'

import argparse
parser=argparse.ArgumentParser(description="""Argument Parser""")
parser.add_argument('-unsound_finding', action='store_true', default=False)
parser.add_argument('-log_error', action='store_true', default=False)
unsound_finding = parser.parse_args().unsound_finding
log_error = parser.parse_args().log_error

# print (unsound_finding)
# exit()

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

def solve(args):
	(tool, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags) = args

	filename = generate_if_not_exists(root, smt2Filename, SOLVED_PROBLEM)
	filePath = os.path.join(root, filename)

	result= {PROBLEM:filePath}

	if unsound_finding:
		print ('Testing', filePath)

	#try to get the result of the problem:
	try:
		f = open(filePath)
		m = re.search('\(set-info :status (sat|unsat|unknown)\)', f.read())
		if m:
			result[RESULT]=m.group(1)
	except IOError:
		pass
	
	# scramble the benchmark
	# ./process filePath seed

	# command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) + "; ./" + tool + " " +  flags + " " + os.path.join(root, filename)
	# command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) \
	#           + "; /usr/bin/time --format='time %U + %S time' ./" + tool + " " \
	#           +  flags + " " + os.path.join(root, filename)

	startTime = time.time()

	command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) \
							+ "; bash -c \"TIMEFORMAT='time %3U + %3S time'; time timeout " + str(timeout) + " ./" + tool + " " \
							+  flags + " " + filePath + "\""
		
		# print (command + "\n")

	try:
		proc = subprocess.Popen(command,stdout=subprocess.PIPE, 
													stderr=subprocess.PIPE, universal_newlines = True, 
													shell=True, preexec_fn=os.setsid)
	except Exception:
		pass    
	
	try:    
		iOut, iErr = proc.communicate(timeout=timeout)
	except TimeoutExpired:
		try:
			os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
		except Exception:
			pass


	endTime = time.time()
	
	# print ("Returned code:",proc.returncode)

	# print ("ER:" + iErr.strip() + ":End ER")
	# print ("IO:" + iOut.strip() + ":End IO")

	# extract running time from iErr
	try:
		timeRegex = re.search("time (\d+\.\d+ \+ \d+\.\d+) time", iErr.strip())
		result[CPU_TIME] = eval(timeRegex.group(1))
	except Exception:
		result[CPU_TIME] = "Unparsable output"

	result[TIME] = endTime - startTime

	try:
		result[TOOL_RESULT] = iOut.strip()
	except Exception:
		result[TOOL_RESULT] = ""
	
	if log_error:
		try:
			result[ERROR]=iErr.strip()
		except Exception:
			result[ERROR]=""

	# print (result[DREAL_RESULT])
	# print (result)
	# remove_file(result[PROBLEM])
	return result
		

def run(tool, directory, timeout, resultFile, PROCESSES_NUM, SOLVED_PROBLEM, max_memory=4000000, flags=""):
	# generating name of the logs folder
	import datetime
	import time

	if log_error:
		log_folder_name = "logs_" + datetime.datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d_%H:%M:%S')

	TOOL_RESULT = tool + " result"
	HEADERS = [PROBLEM, RESULT, CPU_TIME, TIME, TOOL_RESULT]

	with concurrent.futures.ProcessPoolExecutor(PROCESSES_NUM) as executor:
		with open(resultFile, 'w+', 1) as csvfile:     
			spamwriter = csv.DictWriter(csvfile, fieldnames=HEADERS, extrasaction='ignore')
			spamwriter.writeheader()
			smt2Files = []

			for root, dirnames, filenames in os.walk(directory):
				for filename in filenames:
					if filename.endswith(SMT2):
						smt2Files.append((filename, root))


			futureObjects = []
			for (smt2Filename, root) in smt2Files:
				future = executor.submit(solve, (tool, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags,))
				futureObjects.append(future)
			for future in futureObjects:
				try:
					result = future.result()
				except Exception as e:
					print (e)
					continue
					
				for key in result:
					result[key] = str(result[key])
				
				# write to output file
				spamwriter.writerow(result)
				csvfile.flush()

				# write error to error file
				if log_error:
					error_file_path = log_folder_name + os.path.abspath(result[PROBLEM])+".err.txt"
					error_folder = os.path.dirname(error_file_path)
					if not os.path.exists(error_folder):
						os.makedirs(error_folder)

					with open(error_file_path, 'w+', 1) as errFile:
						errFile.write(result[ERROR])


# run("../veriT", "../test", 30, "veriT.csv", 4, SMT2, 40000, "--disable-banner --disable-print-success")
# run("z3", "Test/test", 30, "z3.csv", 4, SMT2, 1000000)
# run("veriT_reduce", "test", 20, "veriT_reduce.csv", 4, SMT2, 400000, "--disable-banner --disable-print-success")
if unsound_finding:
	run("veriT", 
		"/home/tungvx/raSAT/development_ver/raSAT/Test/smtlib-20140121/QF_NRA/", 
		20, "veriT.csv", 1, SMT2, 400000, "--disable-banner --disable-print-success")
# run("veriT_raSAT", "test", 30, "veriT_raSAT.csv", 4, SMT2, 400000, "--disable-banner --disable-print-success")
