INTERP = python3
N = 010
VLEVEL = 1

GENERATOR = $(INTERP) ../chess.py
SOLVER = $(INTERP) ../../solver/pgbdd.py
CHECKER = ../../lrat/lrat-check
GRABBER = ../grab_data.py
DDEST = ../../pigeon-results.txt

test: c

c: pigeon-tseitin-$(N)-column.data
b: pigeon-tseitin-$(N)-bucket.data
l: pigeon-tseitin-$(N)-linear.data

install:
	echo "No installation required"

pigeon-tseitin-$(N)-column.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-column.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf -s pigeon-tseitin-$(N).schedule \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).lrat 2>&1 | tee -a pigeon-tseitin-$(N)-column.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-column.data
	rm -f pigeon-tseitin-$(N).lrat

pigeon-tseitin-$(N)-bucket.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-bucket.data
	$(SOLVER) -b -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).lrat 2>&1 | tee -a pigeon-tseitin-$(N)-bucket.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-bucket.data
	rm -f pigeon-tseitin-$(N).lrat

pigeon-tseitin-$(N)-linear.data:
	$(GENERATOR) -n $(N) -r pigeon-tseitin-$(N) | tee pigeon-tseitin-$(N)-linear.data
	$(SOLVER) -v $(VLEVEL) -i pigeon-tseitin-$(N).cnf \
		-p pigeon-tseitin-$(N).order -o pigeon-tseitin-$(N).lrat 2>&1 | tee -a pigeon-tseitin-$(N)-linear.data
	$(CHECKER) pigeon-tseitin-$(N).cnf pigeon-tseitin-$(N).lrat | tee -a pigeon-tseitin-$(N)-linear.data
	rm -f pigeon-tseitin-$(N).lrat

pigeon:
	./gen-column.sh
	echo "Summary of results.  Also stored in $(DDEST)"
	$(GRABBER) pigeon-tseitin-*-column.data | tee $(DDEST)

regress:
	./regress.sh

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.lrat *.lratb *.data *.order *.schedule $(DDEST)
