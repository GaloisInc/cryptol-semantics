Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.

Require Import Cryptol.AST.
Require Import Cryptol.Semantics.
Require Import Cryptol.Utils.
Require Import Cryptol.Builtins.
Require Import Cryptol.BuiltinSem.
Require Import Cryptol.Values.        

Require Import Cryptol.EvalTac.

Import HaskellListNotations.
Open Scope string.

Require Import CryptolVerif.Split.

Require Import Cryptol.Eager.

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