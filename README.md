This archive provides a demonstration version of a proof-generating
SAT solver based on BDDs.  The solver generates proofs in LRAT format.
A checker for this format is included.

The program also generates and tests two benchmark problems: the
mutilated chessboard problem and the pigeonhole problem (using a
Tseitin encoding of the AtMost1 constraints).

System Requirements:

       * Python interpreter.  By default, the program runs python3.
         You can change by editing the "INTERP" definition in the
         top-level Makefile

       * C compiler.  The LRAT checker is written in C.  Just about
         any compiler should work.  The default is gcc.

Makefile options:

install: 

  Compile the LRAT checker.  (The solver and benchmark generators are
  written in Python and so do not need compilation.)

test:

  Generate and run simple examples of the two benchmarks.  A lot of
  stuff gets printed out, but you should see the statement "VERIFIED"
  for each benchmark

regress:

  Generate and run a set of examples of the two benchmarks.  These
  have been scaled down to use less than 30 seconds each.  A lot of
  stuff gets printed out, but you should see the statement "VERIFIED"
  for each benchmark.

clean:

  Delete all generated files, except for any benchmark data

superclean:

  Delete all generated files, including the benchmark data

