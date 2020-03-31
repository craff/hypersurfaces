
all:
	ocamlbuild -cflag -g -pkgs zarith,graphics HyperSurfaces.native TestBernstein.native \
		TestCurves.native TestSurfaces.native

clean:
	ocamlbuild -clean
