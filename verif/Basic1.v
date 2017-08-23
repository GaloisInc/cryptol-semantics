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
Require Import Cryptol.BuiltinSyntax.
Require Import Cryptol.Values.        

Require Import Cryptol.EvalTac.
Require Import Cryptol.Eager.

Require Import CryptolVerif.Basic.

Import HaskellListNotations.
Open Scope string.

Definition z : ident := (244,"z").

Require Import Cryptol.EvalTac.

Lemma eager_eval_z :
    eager_eval_expr ge tempty sempty (EVar z) (to_sval (eseq [ebit true, ebit true])).
Proof.
  init_globals ge.
  g. e. e. e. g.
  e. e. g.
  e. g. e.
  reflexivity.
  g. e.
  reflexivity.
  e.
  g. e.
  g. e.
  reflexivity.
  g. e.
  reflexivity.

  e.
  lv. lv.

  reflexivity.
Qed.


(*
Lemma eval_z :
  exists v,
    eval_expr ge tempty empty (EVar z) v /\ force_list ge tempty empty v ([bit true, bit true]).
Proof.
  init_globals ge.
  eexists. split.
  g.
  e. e. e. g.
  e. e.
  e. e. e. g.
  e. e. g. e. e.
  e. g. e. e. e.
  e. g. e. e. g.
  e. e. e. g. e. e. e.
  e.
  (* need to model Plus *)
Admitted.
*)