This archive provides a demonstration version of a proof-generating
SAT solver based on BDDs.  The solver generates proofs in LRAT format.
A checker for this format is included.

The program also generates and tests two benchmark problems: the
mutilated chessboard problem and the pigeonhole problem.

System Requirements (Tested with TACAS virtual environment)

       * Python interpreter.  By default, the program runs python3.
         You can change by editing the "INTERP" definition in the
         top-level Makefile

       * C compiler.  The LRAT checker is written in C.  Just about
         any compiler should work.  The default is gcc.

Makefile options:

test:

  Generate and run simple examples of the two benchmarks.  A lot of
  stuff gets printed out, but you should see the statement "VERIFIED"
  for each benchmark.  All runtime data are saved in files named as follows:

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
	with growth O(n^3). The files contains lots of information about
	the execution.  The word VERIFIED indicates success.


regress:

  Generate and run a set of examples of the two benchmarks.  These
  have been scaled down to use less than 30 seconds each.  A lot of
  stuff gets printed out, but you should see the statement "VERIFIED"
  for each benchmark.  The data files are located and named as
  described above.

clean:

  Delete all generated files, except for any benchmark data

superclean:

  Delete all generated files, including the benchmark data
