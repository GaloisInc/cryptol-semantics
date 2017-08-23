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

Require Import CryptolVerif.Width.

Lemma eval_x :
  exists v,
    eval_expr ge tempty empty (EVar (242,"x")) v /\ force_list ge tempty empty v (@from_bitv 8 (@repr 8 8)).
Proof.
Admitted.
(*  init_globals ge.
  eexists. split.
  g.
  e. e. e. e. g.
  all: repeat e.
Qed.  *)