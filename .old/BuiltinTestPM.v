Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.


Lemma eval_p :
  eval_expr ge empty (EVar (249,"p")) (bits (v 5)).
Proof.
  repeat e.
  Unshelve.
  all: exact nz.
Qed.

Lemma eval_m :
  eval_expr ge empty (EVar (250,"m")) (bits (v 5)).
Proof.
  repeat e.
  Unshelve.
  all: exact nz.
Qed.
