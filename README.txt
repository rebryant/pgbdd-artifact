This archive provides a demonstration version of a proof-generating
SAT solver based on BDDs.  The solver generates proofs in LRAT format.
A checker for this format is included.

The program also generates and tests two benchmark problems: the
mutilated chessboard problem and the pigeonhole problem.

1. System Requirements (Tested with TACAS virtual environment)

       * Python interpreter.  By default, the program runs python3.
         You can change by editing the "INTERP" definition in the
         top-level Makefile

       * C compiler.  The LRAT checker is written in C.  Just about
         any compiler should work.  The default is gcc.

2. Installation and Running Demonstration

All code and benchmark data can be downloaded in two different ways:

A. Using GitHub

   git clone https://github.com/rebryant/pgbdd-artifact

B. Getting the Zip File

   wget http://www.cs.cmu.edu/~bryant/download/pgbdd-artifact.zip
   unzip pgbdd-artifact.zip

Once downloaded, the two demonstrations can be run as:

   cd pgbdd-artifact
   make chess
   make pigeon


3. Makefile options:

install:

  Compiles the LRAT checker.  No other installation steps are required.

chess:

  Generate and test versions of the N x N mutilated chessboard up to
  N=40.  This demonstrates the power of the BDD-based approach plus a
  novel method of organizing the sequencing of conjunction and
  qexistential quantification operations inspired by symbolic model
  checking.

  A lot of stuff gets printed, but the final summary information is
  saved in a file "chess-results.txt" in the top-level directory.

pigeon:

  Generate and test versions of the pigeonhole problem with N holes
  and N+1 pigeons up to N=40.  This demonstrates the power of the
  BDD-based approach plus a novel method of organizing the sequencing
  of conjunction and existential quantification operations inspired by
  symbolic model checking.

  A lot of stuff gets printed, but the final summary information is
  saved in a file "pigeon-results.txt" in the top-level directory.

test:

  Generate and run simple examples of the two benchmarks.  A lot of
  stuff gets printed out, but you should see the statement "VERIFIED"
  for each benchmark.  All runtime data are saved in files named as
  follows:

     benchmark/chess-data/chess-NNN-MMMMMM.data
        NNN: Size of chess board
	MMMMMM: Method used.  linear/bucket/column/noquant

	Of these, column is the most interesting, generating proofs
	with growth O(n^2.7). The files contains lots of information
	about the execution.  The word VERIFIED indicates success.

     benchmark/pigeon-data/pigeon-tseitin-NNN-MMMMMM.data
        NNN: Number of holes
	MMMMMM: Method used.  linear/bucket/column

	Of these, column is the most interesting, generating proofs
	with growth O(n^3). The files contains lots of information
	about the execution.  The word VERIFIED indicates success.


regress:

  Generate and run an extensive set of examples of the two benchmarks
  using different strategies for scheduling operations.  These have
  been scaled down to use less than 30 seconds each.  A lot of stuff
  gets printed out, but you should see the statement "VERIFIED" for
  each benchmark.  The data files are located and named as described
  above.

clean:

  Delete all generated files, except for any benchmark data

superclean:

  Delete all generated files, including the benchmark data

4. Using PGBDD as a standalone SAT solver

The PGBDD SAT solver is available as the program pgbdd.py in the
directory pgbdd-artifact/solver. Its use is documented in the file
pgbdd-artifact/solver/README.txt.
