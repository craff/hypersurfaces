
all:
	dune build --release -j 5

install:
	dune install

clean:
	dune clean

.PHONY: tests
tests: all
	dune exec Hyper --release -- tests/*.txt -b > tests.log 2>&1
