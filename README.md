# An OCaml program for compute discretization of algebraic hypersurfaces

![Screen shot](https://raw.githubusercontent.com/craff/hypersurfaces/master/article/quartic-M-2.png?raw=true "A nice screen shot")

## Introduction

This program allows you to define polynomials and then to compute a
discretization of the zero locus of one or more polynomials. It works in any
dimenstion, co-dimension or degree, with as expected limitations due to the
complexity of the problem.

Note: currently, the program will loop if the variety is not smooth.

## Authors

* [Christophe Raffalli](https://raffalli.eu)

## Installation

If you have a modern installation of OCaml using opam, just
install `dune, gles3, pacomb` and type `make && make install`.

## Documentation

WORK IN PROGRESS

**To run the examples:**

You can run the examples in the `tests` folder by typing `Hyper tests/filename`.
