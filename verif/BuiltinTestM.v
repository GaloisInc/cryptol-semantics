Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.


Lemma eval_mod :
  eval_expr ge empty (EVar (246,"mod")) (bits (v 5)).
Proof.
  repeat e.
  Unshelve.
  all: exact nz.
Qed.
