
all:
	dune build --release -j 5

clean:
	dune clean
	cd article && rubber --clean --pdf main.tex

.PHONY: tests
tests: all
	dune exec Hyper --release -- tests/*.txt -b > tests.log 2>&1

pdf:
	cd article && rubber --pdf main.tex
