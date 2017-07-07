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

Require Import Width.

Lemma eval_x :
  exists v,
    eval_expr ge empty (EVar (242,"x")) v /\ force_list ge empty v (@from_bitv 8 (@repr 8 8)).
Proof.
  init_globals ge.
  eexists. split.
  g.
  e. e. e. e. g.
  all: repeat e.
Qed.  