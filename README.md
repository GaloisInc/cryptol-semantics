# Cryptol Semantics [![Build Status](https://travis-ci.org/GaloisInc/cryptol-semantics.svg?branch=master)](https://travis-ci.org/GaloisInc/cryptol-semantics)
## Motivation
The goal of this project is to provide a Coq model of the Semantics of the Cryptol language.

[Cryptol](https://cryptol.net/) is [Galois'](http://galois.com/) specification language for cryptography. Cryptol has a variety of uses:

- Write cryptography in a style that looks like offical specs (RFCs, Standards etc...)
- Allow for reasoning about properties of cryptography through connections to SMT solvers
- Prove correctness of C and Java programs with [SAW](http://saw.galois.com)

Simply stated, Cryptol shows the correctness of cryptography. By presenting a formal semantics we will

- Give confidence that programs that look correct have the expected meaning in cryptol 
- Open the door to a huge range of analysis, including cryptographic properties of the sort proved in [FCF](https://github.com/adampetcher/fcf)
- Take a necessary step on the road to verifying SAW
- Create a point to anchor trust for verified compilation of Cryptol to a variety of hardware

## Project Organization

- **src:** contains the main development
- **HMAC:** contains files related to verification of equivalence between cryptol HMAC and the HMAC spec from FCF
- **verif:** contains various interesting other proofs
- **examples:** example cryptol and microcryptol files to target
- **script:** A script to generate makefiles, called by [configure](configure)

## Build Instructions
WARNING: This project is its infancy, and under active development.

### Dependencies

- [Coq 8.6](https://coq.inria.fr/download)
- Z3 (dependency of Cryptol)
- Haskell Platform (dependency of Cryptol)

### Instructions

1. Make sure the version of cryptol you are running is as new or newer than [this commit](https://github.com/GaloisInc/cryptol/commit/ca2136fab9cbfd1fcdb8377c50869d9240748575)
1. Clone and enter this repository
1. `cd cryptol-semantics`
1. `./configure`
1. `make`

NOTE: `make` will only build the coq files in the `src` directory. In order to build everything, use `make verif`. When building everything, it is recommended that you build in parallel using `make -jN` for some appropriate N.

## Using the evaluation model

1. Use cryptol to load your favorite cryptol program: `cryptol <filename>`
1. In the interactive prompt type `:extract-coq` to print out an AST of every current top level declaration
1. Copy the output and paste it as the right hand side of a variable declaration in Coq
1. Use the `eval_expr` or `eager_eval_expr` relation to construct arguments that your terms evaluate to what you want

