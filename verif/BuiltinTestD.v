Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.


Lemma eval_div :
  eval_expr ge empty (EVar (245,"div")) (bits (v 5)).
Proof.
  repeat e.
  Unshelve.
  all: exact nz.
Qed.
