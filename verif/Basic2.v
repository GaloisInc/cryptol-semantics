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

Require Import Basic.

Import HaskellListNotations.
Open Scope string.

Definition zz : ident := (247,"zz").
(*
Lemma eval_z :
  exists v v',
    eval_expr ge empty (EVar zz) v /\ force_list ge empty v [v'] /\ force_list ge empty v' ([bit true, bit true]).
Proof.
  assert (Hplus : ge (1,"+") = Some (mb 1 2 Plus)) by reflexivity.
  assert (ge (9, "True") = Some (mb 0 0 true_builtin)) by reflexivity.  
  assert (ge (10, "False") = Some (mb 0 0 false_builtin)) by reflexivity.  
  eexists. eexists. split.

  e. e. e. e. g.
  e. e. e. g. repeat e.
  repeat e.
  simpl. repeat e. g.

  e. e. repeat e. repeat e.
  repeat e. repeat e. g.
  repeat e. e.
  eapply eval_lift_binary_builtin.
  e. 
  instantiate (3 := (EVar (3,"")) :: nil). reflexivity.
  repeat e. 
  instantiate (2 := 2%nat). reflexivity. reflexivity.
  simpl. split.
  e. eapply eval_lift_binary_nil; e.
  repeat e.
  repeat e.

  Unshelve. simpl; auto.
Qed.
*)