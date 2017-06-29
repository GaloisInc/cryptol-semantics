Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.


Lemma eval_exp :
  eval_expr ge empty (EVar (247,"exp")) (bits (v 128)).
Proof.
Admitted. (* TODO: implement exponentiation *)


Lemma eval_lgtest :
  eval_expr ge empty (EVar (248,"lgtest")) (bits (v 7)).
Proof.
Admitted. (* TODO: implement lg2 *)

