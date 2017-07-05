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

Require Import Basic.

Import HaskellListNotations.
Open Scope string.

Definition z : ident := (244,"z").


Lemma eval_z :
  exists v,
    eval_expr ge empty (EVar z) v /\ force_list ge empty v ([bit true, bit true]).
Proof.
  eexists. split.
  e.
  e. e. e. g.
  e. e.
  e. e. e. e. g.
  e. e. g.
  e. e. e. g.
  e. e. e.
  e. g. e.
  e. g. e. e. e. g.
  e. e. e.
  e.

  repeat e.
  instantiate (2 := 2%nat). simpl. reflexivity.
  simpl. reflexivity.
  repeat e.

  Unshelve. simpl; auto.
Qed.
