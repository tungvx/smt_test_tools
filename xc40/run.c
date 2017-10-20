#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>

#define BUFSIZE 80

int main(int argc, char **argv)
{
    MPI_Status istat;
    int id, nprocs, myrank;
    char msg[BUFSIZE];

    MPI_Init(&argc, &argv);
    MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
    MPI_Comm_rank(MPI_COMM_WORLD, &myrank);

    char command[BUFSIZE];
    sprintf(command, "python3 run.py %d %d", myrank, nprocs);
    system(command);

    if (myrank == 0) {
        // read smt files and pass to other processes
        
        for (id = 1; id < nprocs; id++) {
            MPI_Recv(msg, BUFSIZE, MPI_CHARACTER,
                     id, 10, MPI_COMM_WORLD, &istat);
            printf("%s\n", msg);
        }

        char command2[BUFSIZE];
        sprintf(command2, "python3 gather_results.py %d", nprocs);
        system(command2);        
    } else {
        sprintf(msg, "NPROCS=%d:MYRANK=%d", nprocs, myrank);
        MPI_Send(msg, BUFSIZE, MPI_CHARACTER, 0, 10, MPI_COMM_WORLD);
    }

    MPI_Finalize();

    return 0;
}