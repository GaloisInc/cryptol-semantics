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

Require Import Eager.

(*
Lemma eval_a :
  exists v,
    eager_eval_expr ge tempty sempty (EVar a) (* 8 *)
Proof.
  init_globals ge.
  eexists; split.
  g.
  e. e. e. e. e. g. e. e.
  e. repeat e.
  e. repeat e.
  e. e. e. e. e. e. g.
  e. repeat e.
  e. repeat e.
  e. repeat e.
  e. g.
  e. e. e. e. g. e.
  repeat e.
  e. repeat e.
  e. repeat e.
  e. g.
  
Qed.
*)