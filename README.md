# cryptol-semantics
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
- **examples:** example cryptol and microcryptol files to target
- **script:** A script to generate makefiles, called by [configure](configure)

## Build Instructions
WARNING: This project is its infancy, and under active development.

### Dependencies

- [Coq 8.6](https://coq.inria.fr/download)
- Z3 (dependency of Cryptol)
- Haskell Platform (dependency of Cryptol)

### Instructions

1. Clone and build the [cryptol fork](https://github.com/sliverdragon37/cryptol) capable of printing AST that can be imported by Coq
1. Clone and enter this repository
1. `cd cryptol-semantics`
1. `./configure`
1. `make`

## Using the evaluation model

1. Use the cryptol fork to load your favorite cryptol program: `cryptol <filename>`
1. In the interactive prompt type `:all` to print out an AST of every current top level declaration
1. Copy the output and paste it as the right hand side of a variable declaration in Coq
1. Currently literals are represented as (EVar 0), change them to the literal you want (e.g. 32 should be `(lit 32)`)
1. Currently Types are printed out but not parsed (will be fixed)
1. Use the `eval_expr` relation to construt arguments that your terms evaluate to what you want

