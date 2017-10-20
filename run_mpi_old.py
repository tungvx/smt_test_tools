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

parser.add_argument('-change_dir', action='store_true', default=False)
parser.add_argument('-gurobi_key', action='store_true', default=False)
parser.add_argument('-log_error', action='store_true', default=False)

args = parser.parse_args()

change_dir = args.change_dir
log_error = args.log_error
gurobi_key = args.gurobi_key


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
	wall_timeout = timeout
	
	command = "ulimit -Sv " + str(max_memory) + "; ulimit -St " + str(timeout) \
						+ "; bash -c 'TIMEFORMAT=\"{\\\"CPU time\\\": %3U + %3S, \\\"Wall time\\\": %3R}\"; time timeout " + str(wall_timeout) + " ./" + tool + " " \
						+  flags + " " + os.path.join(root, filename) + "'"
	

	if gurobi_key:
		import socket
		hostname = socket.gethostname()
		command = "export GRB_LICENSE_FILE=/work/tungvx/gurobi/%s/gurobi.lic; " % (hostname, ) + command

	# print (command)
	try:
		proc = subprocess.Popen(command,stdout=subprocess.PIPE, 
													stderr=subprocess.PIPE, universal_newlines = True, 
													shell=True, preexec_fn=os.setsid)
	except Exception:
		pass    
	
	try:    
		iOut, iErr = proc.communicate(timeout=wall_timeout)
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
	result["Mul_time"] = 0
	result["Op_time"] = 0
	try:
		err_msg = eval("[" + iErr.strip() + "]")
		result[CPU_TIME] = err_msg[-1]["CPU time"]
		result[TIME] = err_msg[-1]["Wall time"]
		for ite in err_msg[:-1]:
			result["Mul_time"] += ite["Mul_time"]
			result["Op_time"] += ite["Op_time"]
	except Exception:
		result[CPU_TIME] = timeout
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

def run(tool, directory, timeout, resultFile, SOLVED_PROBLEM, max_memory=4000000, flags=""):
	comm = MPI.COMM_WORLD
	rank = comm.Get_rank()
	size = comm.Get_size()

	# we need the number of processes to be greater than 1
	assert(size > 1)

	TOOL_RESULT = tool + " result"
	if change_dir:
		HEADERS = [PROBLEM, RESULT, CPU_TIME, TIME, "Mul_time", "Op_time", TOOL_RESULT]
	else:
		HEADERS = [PROBLEM, RESULT, CPU_TIME, TIME, TOOL_RESULT]

	if rank == 0:

		# create log folder name and send to all other ranks
		import datetime
		import time
		log_folder_name = "logs_" + datetime.datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d_%H:%M:%S')
		
		# create the folder
		try:
			os.makedirs(log_folder_name)
		except FileExistsError:
			pass

		for index in range(size-1):
			receiving_rank = index + 1
			comm.send(log_folder_name, receiving_rank)

		file_index = 0
		sending_data = {}

		for i in range(size):
			if i > 0:
				sending_data[i] = []

		for root, dirnames, filenames in os.walk(directory):
			for filename in filenames:
				if filename.endswith(SMT2) and "Ultimate" not in root and "Lasso" not in root:
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
		with open(resultFile, 'w+', 1) as csvfile:
			spamwriter = csv.DictWriter(csvfile, fieldnames=HEADERS, extrasaction='ignore')
			spamwriter.writeheader()

			for i in range(size-1):
				proc_rank = comm.recv(source=MPI.ANY_SOURCE)
				# write to output file
				with open(os.path.join(log_folder_name, str(proc_rank)+".csv"), "r") as proc_rank_output:
					csvfile.write(proc_rank_output.read())

	else:
		# first, receiving log folder name:
		log_folder_name = comm.recv(source=0)

		data = comm.recv(source=0)
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
			shutil.copy2("cvc4", sub_dir)
			#shutil.copy2("yices-smt2", sub_dir)
			#shutil.copy2("main", sub_dir)
			#shutil.copy2("tropical.py", sub_dir)

			# change working dir:
			os.chdir(sub_dir)

		if change_dir:
			new_log_folder_name = "../"
		else:
			new_log_folder_name = log_folder_name

		# receiving result:
		with open(os.path.join(new_log_folder_name, str(rank)+".csv"), 'w+', 1) as csvfile:
			spamwriter = csv.DictWriter(csvfile, fieldnames=HEADERS, extrasaction='ignore')
			for smt2Filename, root in data:
				result = solve(tool, smt2Filename, SOLVED_PROBLEM, root, timeout, max_memory, TOOL_RESULT, flags)
				for key in result:
					result[key] = str(result[key])

				# cp linear formulas
				if change_dir:
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

				spamwriter.writerow(result)

		comm.send(rank, 0)

		# remove pwd
		if change_dir:
			shutil.rmtree(os.getcwd())


# run("../veriT", "../test", 30, "veriT.csv", SMT2, 40000, "--disable-banner --disable-print-success")	    
# run("./veriT", "/work/tungvx/test", 30, "veriT.csv", SMT2, 40000, "--disable-banner --disable-print-success")	    
