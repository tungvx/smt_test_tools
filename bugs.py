from mpi4py import MPI

comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()

if rank == 0:
	for proc_rank in range(size-1) + 1:
		comm.isend([str(proc_rank),str(proc_rank),str(proc_rank),str(proc_rank),str(proc_rank),str(proc_rank),str(proc_rank),str(proc_rank),str(proc_rank)], proc_rank)
else:
	print ("Rank", rank, "receiving", comm.recv(source=0))