# Coinduction

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/damien-pous/coinduction/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/damien-pous/coinduction/actions?query=workflow:"Docker%20CI"

A library for doing proofs by (enhanced) coinduction.

Initially based on the notion of 'companion' from the paper
Coinduction All the Way Up. 
Damien Pous. 
In Proc. LICS, 2016.

Now using ideas from
Tower Induction and Up-to Techniques for CCS with Fixed Points. 
Steven Schäfer, Gert Smolka. 
In Proc. RAMiCS 2017


It contains:
 - enhancements of the coinductive proof method
 - second order coinduction reasonning about enhancements
 - parametrised coinduction, as proposed by Hur et al.
 - powerful symmetry arguments
 - compatibility and respectfulness

Examples on how to use the library may be found in the associated rocq-coinduction-examples package: 
 - a formalisation of Hur et al's toy example on divergence 
 - a formalisation of Rutten's stream calculus
 - a formalisation of Milner's calculus of communicating systems (CCS)
 - a formalisation of Automata and regular expression equivalence
 
## Modules
 + `lattice.v`     : complete lattices, monotone functions in such lattices
 + `tower.v`       : abstract theory of coinduction via tower induction
 + `rel.v`         : tools for the complete lattice of binary relations
 + `tactics.v`     : tactics for coinductive predicates/relations
 + `companion.v`   : abstract theory of the companion (no longer used)
 + `tests.v`       : sanity checks
 + `all.v`         : single module to load the library (despite the name, excludes companion and tests)

## Meta

- Author(s):
  - Damien Pous (initial)
- Rocq-community maintainer(s):
  - Damien Pous ([**@damien-pous**](https://github.com/damien-pous))
- License: [GNU LGPL3+]
- Rocq namespace: `Coinduction`
- Related publication(s):
  - [Coinduction All the Way Up](https://hal.archives-ouvertes.fr/hal-01259622) doi:[10.1145/2933575.2934564](http://dx.doi.org/10.1145/2933575.2934564)

## Building and installation instructions

The easiest way to install the latest released version of Coinduction
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-coinduction
```

To instead build and install manually, do:

``` shell
git clone https://github.com/damien-pous/coinduction.git
cd coinduction
make
make install
```

Starting from v1.23, due to the dependency on rocq-elpi,
recall to add "elpi_elpi elpi" in the le stanza ``theories'' of your project if you want to compile it with dune.


## Compatibility and dependencies

- version v1.23 compiles with Rocq 9.2 - 9.3 and needs rocq-elpi
- version v1.22 compiles with Rocq 9.2 - 9.3
- version v1.21 compiles with Rocq 9.0 - 9.2 without transition packages
- version v1.20 compiles with Coq 8.20 and Rocq 9.0 with transition packages
- versions v1.6, v1.7 and v1.8 all compile with Coq 8.16.1, 8.17.1 and 8.18.0
- v1.7 is feature equivalent but not backward-compatible with v1.6
- the master branch of this git repository should compile with Coq master
