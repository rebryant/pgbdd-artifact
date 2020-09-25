Benchmark generation of proof generating SAT solver.


Benchmarks:

1. Mutilated chessboard

./chess.py -h
Usage: ./chess.py [-h] [-c] [-v] [-r ROOT] -n N
  -h       Print this message
  -v       Run in verbose mode
  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule
  -c       Include corners
  -n N     Specify size of board


chess-data: Directory for generating and testing chessboard benchmarks

2. Pigeonhole problem, using Tseitin encoding of AtMost1 constraint for each hole.

./pigeon-tseitin.py -h
Usage: ./pigeon-tseitin.py [-h] [-c] [-v] [-r ROOT] -n N
  -h       Print this message
  -v       Run in verbose mode
  -r ROOT  Specify root name for files.  Will generate ROOT.cnf, ROOT.order, and ROOT.schedule
  -n N     Specify number of holes (pigeons = n+1)

pigeon-data: Directory for generating and testing chessboard benchmarks

