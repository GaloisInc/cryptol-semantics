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
Require Import BuiltinSyntax.
Require Import Values.        

Require Import EvalTac.
Require Import Eager.

Require Import Basic.

Import HaskellListNotations.
Open Scope string.

Definition z : ident := (244,"z").

Require Import EvalTac.

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