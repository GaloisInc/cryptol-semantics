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

Import HaskellListNotations.
Open Scope string.


Require Import Demote.
(*
Lemma eval_y :
  exists v,
    eval_expr ge empty (EVar y) v /\ force_list ge empty v (@from_bitv 9 (@repr 9 1)).
Proof.
  assert (Hplus : ge (1,"+") = Some (mb 1 2 Plus)) by reflexivity.
  assert (Htrue : ge (9, "True") = Some (mb 0 0 true_builtin)) by reflexivity.  
  assert (Hfalse : ge (10, "False") = Some (mb 0 0 false_builtin)) by reflexivity.  
  assert (Hdemote : ge (0, "demote") = Some (mb 2 0 Demote)) by reflexivity.
  eexists. split.
  e. e. e. g.
  e. e. e. e. e. e.
  g. e. e. e. e. e. e. e. e.
  e. e. e. e. e. simpl. 
  e. e. e. e. e. e. e. e. e.
  e. e. e. e.
  e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. e. e. e.
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
*)