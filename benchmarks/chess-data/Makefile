INTERP = python3
N = 010
VLEVEL = 1

GENERATOR = $(INTERP) ../chess.py
SOLVER = $(INTERP) ../../solver/pgbdd.py
CHECKER = ../../lrat/lrat-check
GRABBER = ../grab_data.py
DDEST = ../../chess-results.txt


test: c

c: chess-$(N)-column.data

nq: chess-$(N)-noquant.data

l: chess-$(N)-linear.data

b: chess-$(N)-bucket.data

install:
	echo "No installation required"

chess-$(N)-column.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-column | tee chess-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-column.cnf -s chess-$(N)-column.schedule \
		-p chess-$(N)-column.order -o chess-$(N)-column.lrat 2>&1 | tee -a chess-$(N)-column.data
	$(CHECKER) chess-$(N)-column.cnf chess-$(N)-column.lrat | tee -a chess-$(N)-column.data

chess-$(N)-noquant.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-noquant | tee chess-$(N)-noquant.data
	grep -v "q" chess-$(N)-noquant.schedule > chess-$(N)-noquant-stripped.schedule
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-noquant.cnf -s chess-$(N)-noquant-stripped.schedule \
		-p chess-$(N)-noquant.order -o chess-$(N)-noquant.lrat 2>&1 | tee -a chess-$(N)-noquant.data
	$(CHECKER) chess-$(N)-noquant.cnf chess-$(N)-noquant.lrat | tee -a chess-$(N)-noquant.data

chess-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-linear | tee chess-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i chess-$(N)-linear.cnf \
		-p chess-$(N)-linear.order -o chess-$(N)-linear.lrat 2>&1 | tee -a chess-$(N)-linear.data
	$(CHECKER) chess-$(N)-linear.cnf chess-$(N)-linear.lrat | tee -a chess-$(N)-linear.data

chess-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r chess-$(N)-bucket | tee chess-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i chess-$(N)-bucket.cnf \
		-p chess-$(N)-bucket.order -o chess-$(N)-bucket.lrat 2>&1 | tee -a chess-$(N)-bucket.data
	$(CHECKER) chess-$(N)-bucket.cnf chess-$(N)-bucket.lrat | tee -a chess-$(N)-bucket.data

chess:
	./gen-column.sh
	echo "Summary of results.  Also stored in $(DDEST)"
	$(GRABBER) chess-*-column.data | tee $(DDEST)

regress:
	./regress.sh

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.data *.order *.schedule $(DDEST)
