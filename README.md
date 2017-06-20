# cryptol-semantics
## Motivation
The goal of this project is to provide a Coq model of the Semantics of the Cryptol language.

## Build Instructions
WARNING: This project is its infancy, and under active development.

1. Check out [my fork of cryptol](https://github.com/sliverdragon37/cryptol)
1. Build my fork of cryptol
1. Check out this repository
1. `cd cryptol-semantics`
1. `./configure`
1. `make`

## Using the evaluation model

1. Use my fork of cryptol to load your favorite cryptol program
1. In the interactive prompt type `:all` to print out an AST of every current top level declaration
1. Copy the output and paste it as the right hand side of a variable declaration in Coq
1. Currently literals are represented as (EVar 0), change them to the literal you want
1. Currently Types are printed out but not parsed (will be fixed)
1. Use the `eval_expr` relation to construt arguments that your terms evaluate to what you want

