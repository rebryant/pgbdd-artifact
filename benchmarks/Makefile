# Set to the version of Python installed on this machine
INTERP=python3

all: install

test:
	cd chess-data ; make test INTERP=$(INTERP)
	cd pigeon-data ; make test  INTERP=$(INTERP)

chess:	
	cd chess-data ; make chess INTERP=$(INTERP)

pigeon:	
	cd pigeon-data ; make pigeon INTERP=$(INTERP)


regress:
	cd chess-data ; make regress INTERP=$(INTERP)
	cd pigeon-data ; make regress INTERP=$(INTERP)

install:
	echo "No installation required"

clean:
	cd chess-data; make clean
	cd pigeon-data; make clean
	rm -f *~ *.pyc
	rm -rf __pycache__

superclean: clean
	cd chess-data; make superclean
	cd pigeon-data; make superclean
