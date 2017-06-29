Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.
Require Import Bitvectors.

Lemma eval_neg :
  eval_expr ge empty (EVar (251,"neg")) (bits (v 5)).
Proof.
  repeat e.
  eapply unsigned_eq.
  simpl. reflexivity.

  Unshelve.
  all: exact nz.
Qed.

Lemma eval_comp :
  eval_expr ge empty (EVar (252,"comp")) (bits (v 5)).
Proof.                            
  repeat e.
  Unshelve.
  all: exact nz.
Qed.


