The pgbdd program uses BDDs to determine whether the provided input
formula (in DIMACS CNF format) is satisfiable.  The expectation is
that the formula is not satisfiable, and it generates a proof to this
effect.

The program is written in Python.  It has been tested in versions 2.7
and 3.7.

./pgbdd.py -h
Usage: ./pgbdd.py [-h] [-b] [-v LEVEL] [-i CNF] [-o file.{proof,lrat,lratb}] [-m t|b|p] [-p PERMUTE] \
       [-s SCHEDULE] [-L logfile]
  -h          Print this message
  -b          Process terms via bucket elimination
  -v LEVEL    Set verbosity level
  -i CNF      Name of CNF input file
  -o pfile    Name of proof output file (.proof = tracecheck, .lrat = LRAT text, .lratb = LRAT binary)
  -m (t|b|p)  Pipe proof to stdout (p = tracecheck, t = LRAT text, b = LRAT binary)
  -p PERMUTE  Name of file specifying mapping from CNF variable to BDD level
  -s SCHEDULE Name of action schedule file
  -L logfile  Append standard error output to logfile

Files:
	bdd.py	     A Python-based BDD package with support for proof generation
	resolver.py  Support for resolution proof generation
	stream.py    Manages I/O
	qbdd.py	     The solver

Format for the schedule file:

The schedule file is a text file with each line providing a command to
a simple, stack-based interpreter.  The commands are as follows:

# ...
        Comment line

c C_1 C_2 ... C_k
        Retrieve specified clauses and push onto stack

a K
        Pop K+1 elements.  Compute their conjunction and push result onto stack

q V_1 V_2 ... V_k
        Pop top element of stack.  Existentially quantify it by
        specified variables and push result onto stack

i Docstring
        Print out BDD information about top element on stack

