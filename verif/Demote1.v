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

Import HaskellListNotations.
Open Scope string.


Require Import Demote.

Lemma eval_y :
  exists v,
    eval_expr ge empty (EVar y) v /\ force_list ge empty v (@from_bitv 9 (@repr 9 1)).
Proof.
  eexists. split.
  e. e. e. g.
  e. e. e. e. e. e.
  g. e. e. e. e. e. e. e. e.
  e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e.
  e. e. e. g.
  e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e. e. e.
  e. e. e. e.
  repeat e.
  repeat e.
  repeat e.
  repeat e. simpl. instantiate (2 := 9%nat). reflexivity.
  reflexivity.
  repeat e.

  Unshelve.
  simpl; reflexivity.
Qed.