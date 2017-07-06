
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

Require Import Zero.

Lemma t1_zero :
  exists v,
    eval_expr ge empty (EVar t1) v /\ force_list ge empty v (repeat (bit false) 16).
Proof.
  eexists; split.
  e. e. e. e. e. e. e. e. e. e. e. e. g.
  e. e. e.
  e. e. e. e. e.
  e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. e.
  repeat e.
Qed.
