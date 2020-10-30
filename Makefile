
all:
	dune build

clean:
	dune clean
	cd article && rubber --clean --pdf main.tex

test:
	dune exec Main -- tests/*.txt
