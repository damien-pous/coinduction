# Coinduction

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/damien-pous/coinduction/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/damien-pous/coinduction/actions?query=workflow:"Docker%20CI"

A library for doing proofs by (enhanced) coinduction.

It is based on the notion of 'companion' from the paper
Coinduction All the Way Up. Damien Pous. In Proc. LICS, 2016.

It contains:
 - enhancements of the coinductive proof method
 - second order coinduction reasonning about enhancements
 - parametrised coinduction, as proposed by Hur et al.
 - powerful symmetry arguments
 - compatibility and respectfulness

Examples on how to use the library may be found in the associated coq-coinduction-examples package: 
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
- Coq-community maintainer(s):
  - Damien Pous ([**@damien-pous**](https://github.com/damien-pous))
- License: [GNU LGPL3+]
- Coq namespace: `Coinduction`
- Related publication(s):
  - [Coinduction All the Way Up](https://hal.archives-ouvertes.fr/hal-01259622) doi:[10.1145/2933575.2934564](http://dx.doi.org/10.1145/2933575.2934564)

## Building and installation instructions

The easiest way to install the latest released version of Coinduction
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coinduction
```

To instead build and install manually, do:

``` shell
git clone https://github.com/damien-pous/coinduction.git
cd coinduction
make
make install
```

## Compatibility

- version v1.6 compiles with both Coq 8.16 and 8.17
- so does version v1.7, which is feature equivalent but not backward-compatible with v1.6
- the master branch of this git repository should compile with Coq master
