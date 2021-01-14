
all:
	dune build --release -j 5

clean:
	dune clean
	cd article && rubber --clean --pdf main.tex

test:
	dune exec Main --release -- tests/*.txt

pdf:
	cd article && rubber --pdf main.tex
