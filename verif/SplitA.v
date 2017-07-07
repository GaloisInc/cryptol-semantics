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

Require Import Split.


Lemma eval_a :
  exists v,
    eval_expr ge empty (EVar a) v /\ force_list ge empty v (@from_bitv 8 (@repr 8 1)).
Proof.
  init_globals ge.
  eexists; split.
  g.
  repeat e. g.
  repeat e. g.
  repeat e.
  instantiate (2 := O). reflexivity.
  repeat e.
  instantiate (2 := O). reflexivity.
  repeat e.
  repeat e.
Qed.
