Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.


Lemma eval_times :
  eval_expr ge empty (EVar (244,"times")) (bits (v 30)).
Proof.
  repeat e.
  Unshelve.
  all: exact nz.
Qed.
