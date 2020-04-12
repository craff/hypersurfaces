
all:
	ocamlbuild -cflag -g -pkgs zarith,graphics -lflags gmp.cmxa,mpfr.cmxa HyperSurfaces.native TestBernstein.native \
		TestCurves.native TestSurfaces.native TestHyper.native

clean:
	ocamlbuild -clean
