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

Require Import Comp.
Require Import Eager.

Lemma eval_t1 :
  eager_eval_expr ge tempty sempty (EVar t1) (sbit true).
Proof.
  init_globals ge.
  g. e. e. e. g.
  repeat e. e.
  e. e. e. e. e. g.
  e.
  e. e. e. g.
  e.
  e. congruence.
  e. congruence. e.
  e. e. e. g.
  repeat e. e. e. repeat e. repeat e. simpl. reflexivity.
  e. e. e. g. e.
  e. e. repeat e. e. simpl. reflexivity.
  e.
  simpl. reflexivity.
  e. e. e. e. e. g;
  repeat e.
  repeat e. repeat e.
  e. e. e. g.
  repeat e. repeat e. repeat e.
  e.
  reflexivity.
  e. e. congruence.
  e. e. e. e. g.
  e. e. e. repeat e.
  repeat e. reflexivity.
  e. e. e. g.
  e. e. e. repeat e.
  simpl. e. reflexivity.
  e. reflexivity.
  e. e. e. e. e.
  g. repeat e.
  e. e. repeat e.
  e. reflexivity.
  e. e. e. g. e.
  e. e. repeat e.
  e. reflexivity.
  e. e. e. g.
  e. e. e. repeat e.
  e. reflexivity.
  e. reflexivity.
  simpl. repeat e.
  e. e. e. g.
  e. e. e. repeat e.
  e. reflexivity.
  e. repeat e.
  e. e. e. e. e.

  (* model At *)

Admitted.
  
  
(*
Lemma eval_t1 :
  eval_expr ge empty (EVar t1) (bit true).
Proof.
  assert (Hdemote : ge (0,"demote") = Some (mb 2 0 Demote)) by reflexivity.
  assert (Heq : ge (17,"==") = (Some (mb 1 2 Eq))) by reflexivity.
  assert (Hat : ge (40, "@") = Some (mb 3 2 At)) by reflexivity.
  g. e.
  e. e. e. unfold mb. simpl. e.
  repeat e.
  repeat e.
  repeat e; simpl; repeat e.
  g. e. e.
  e. eapply idx_first. eapply idx_last. e. e. e.
  repeat (simpl; e).
  repeat e. 

  e. e. e. e. e. e. e.
  simpl. e. e. e. e. e.

  e. 
  repeat e; simpl; repeat e.
  repeat e. reflexivity.
  e.
  eapply idx_first. eapply idx_last.
  repeat e; simpl; repeat e.

  repeat e; simpl; repeat e.
  repeat e.
  repeat e.
  instantiate (2 := O). reflexivity.
  repeat e.
  repeat e.
  repeat e.
  repeat e.
Qed.  
*)