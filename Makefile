# Set to the version of Python installed on this machine
INTERP=python3

all:
	install

install:
	cd lrat ; make install

test: install
	cd benchmarks; make test INTERP=$(INTERP)

regress: install
	cd benchmarks; make regress INTERP=$(INTERP)

clean:
	rm -rf *~
	cd benchmarks ; make clean
	cd lrat ; make clean
	cd solver ; make clean

superclean: clean
	cd benchmarks ; make superclean

