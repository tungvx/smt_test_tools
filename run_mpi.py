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

		for proc_rank in range(size):
			sending_data[proc_rank] = []

		for root, dirnames, filenames in os.walk(directory):
			for filename in filenames:
				if filename.endswith(SMT2):
					receiving_rank = file_index%size

					assert(sending_data.get(receiving_rank))

					sending_data[receiving_rank].append((filename, root))
					file_index += 1

		for receiving_rank, smt2_problems in sending_data.iteritems():
			# print "Sending", smt2_problems, "to", receiving_rank
			comm.isend(smt2_problems[0], receiving_rank)

	data = comm.recv(source=0)
	print rank, "received" ,data

# run("../veriT", "../test", "veriT.csv", 4, SMT2, 40000, "--disable-banner --disable-print-success")	    
run("../veriT", "/work/tungvx/QF_NRA", "veriT.csv", 4, SMT2, 40000, "--disable-banner --disable-print-success")	    