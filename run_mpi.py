from mpi4py import MPI
import os

SMT2=".smt2"

def run(tool, directory, timeout, resultFile, SOLVED_PROBLEM, max_memory=4000000, flags=""):
	comm = MPI.COMM_WORLD
	rank = comm.Get_rank()
	size = comm.Get_size()

	result = {}
	if rank == 0:
		file_index = 0
		sending_data = {}
		for root, dirnames, filenames in os.walk(directory):
			for filename in filenames:
				if filename.endswith(SMT2):
					receiving_rank = file_index%size
					try:
						sending_data[receiving_rank].append((filename, root))
					except:
						sending_data[receiving_rank] = [(filename, root)]

		for receiving_rank, smt2_problems in sending_data.iteritems():
			print "Sending", smt2_problems, "to", receiving_rank
			comm.isend(smt2_problems, receiving_rank)

	data = comm.recv(source=0)
	print data

run("../veriT", "../test", "veriT.csv", 4, SMT2, 40000, "--disable-banner --disable-print-success")	    