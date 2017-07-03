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

Require Import Basic.

Import HaskellListNotations.
Open Scope string.

Definition zz : ident := (247,"zz").

Lemma eval_z :
  exists v v',
    eval_expr ge empty (EVar zz) v /\ force_list ge empty v [v'] /\ force_list ge empty v' ([bit true, bit true]).
Proof.
  eexists. eexists. split.

  e. e. e. e. g.
  e. e. e. e. e. e. e. e. g.
  e. e. e. e. g.
  e. e. e. g.
  e. e. e. e.
  e. g.
  e. e. e. e. g.
  e. e. e. g.
  e. e. e. e.

  e.
  eapply eval_lift_binary_builtin.
  solve [simpl; auto].
  instantiate (3 := (EVar (3,"")) :: nil).
  simpl. reflexivity.

  e. e.
  e. e. e. e. e.
  e.

  repeat e.
  repeat e.
  instantiate (2 := 2%nat). simpl. reflexivity.
  simpl. reflexivity. 
  split.
  e. eapply eval_lift_binary_nil.
  e. e.
  e. e. e. e. e.
  e.
Qed.
