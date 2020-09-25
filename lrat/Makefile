CC=gcc
CFLAGS=-O2 -g

all: install

install: lrat-check

lrat-check: lrat-check.c
	$(CC) $(CFLAGS) lrat-check.c -o lrat-check

clean:
	rm -rf *~ lrat-check *.dSYM

