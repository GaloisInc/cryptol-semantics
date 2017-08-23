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

Import HaskellListNotations.
Open Scope string.

Require Import CryptolVerif.Comp.
Require Import Cryptol.Eager.

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
  ec. congruence.
  ec. congruence. e.
  e. e. fg. 
  repeat e. e. e. reflexivity.
  e. e. fg. e.
  e. e. reflexivity. reflexivity.
  ec.
  e. e. e. fg. e. e. e.
  reflexivity.
  e. e. fg.
  e. e. e. reflexivity. reflexivity.
  ec. ec.
  congruence.
  e. e. e. fg.
  e. e. e. reflexivity.
  e. e. fg. e. e. e.
  reflexivity. reflexivity.
  ec. e. e. e. fg.
  e. e. e. reflexivity.
  e. e. fg.
  e. e. e. reflexivity.
  e. e. fg.
  e. e. e. reflexivity. reflexivity.
  f2; try e; try lv.
  e. e. e. fg.
  e. e. e. reflexivity.
  e. lv. lv.

  (* TODO: model At *)

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