Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import BuiltinSem.
Require Import Values.        

Require Import EvalTac.

Require Import SplitAt.

Lemma eval_b :
  eval_expr ge empty b (bits (v 2)).
Proof.
  g.
  e. e. e. e. e. g.
  e. e. e. e. e. g.
  e. e. e. e. g.
  e. e. e. e. g.
  e. e. e. e. g.
  e. e. e. repeat e. e.
  repeat e.
  e. e. e. e. e. e.
  e. e. e. e.
  e. simpl. reflexivity.
  e. e. e. g.
  e. e. e. e. e. e. e. e.
  e.
  e. repeat e.
  e.
  eapply select_slice. e.
  reflexivity.
  e. e.
  e. e.
  Unshelve.
  all: try exact nz; simpl; unfold Pos.to_nat; simpl; try congruence.
Qed.  
