
(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.

Import HaskellListNotations.
Open Scope string_scope.

Definition inflist := (NonRecursive
                         (Decl 245 (DExpr
                                      (EApp (EApp
                                               (ETApp (EVar 52) (TCon (TC (TCNum 8)) []))
                                               (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])))
                                            (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])))))).

Definition finlist := (NonRecursive (Decl 246 (DExpr (EList [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) []))])))).

Definition elem := (NonRecursive (Decl 247 (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar 40) (TCon (TC (TCNum 3)) [])) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (TCon (TC (TCNum 1)) [])) (EVar 246)) (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 1)) [])))))).

Definition rec := (NonRecursive (Decl 246 (DExpr (ERec [("x",(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) []))),("y",(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 5)) [])) (TCon (TC (TCNum 8)) [])))])))).

Definition rec_select := (NonRecursive (Decl 247 (DExpr (ESel (EVar 246) (RecordSel "x"))))).

Definition rec_ge := bind_decl_group rec (bind_decl_group rec_select gempty).

Lemma nz :
  8%nat <> 0%nat.
Proof.
  congruence.
Qed.

Definition three := bits (@repr 8 nz 3).

Lemma rec_eval :
  eval_expr rec_ge empty (EVar 247) (bits (@repr 8 nz 3)).
Proof.
  eapply eval_global_var. reflexivity. unfold rec_ge.
  simpl. reflexivity.
  econstructor. eapply eval_global_var. reflexivity.
  unfold rec_ge. simpl. reflexivity.
  econstructor. simpl.
  repeat econstructor.
  simpl. unfold zrepr.
  f_equal. f_equal.
  match goal with
  | [ |- ?X = ?Y ] => destruct (@eq_spec _ nz X Y); try congruence
  end.
  Unshelve.
  all: omega.
Qed.

Definition tup := (NonRecursive (Decl 248 (DExpr (ETuple [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 4)) [])) (TCon (TC (TCNum 8)) []))])))).

Definition tupsel := (NonRecursive (Decl 249 (DExpr (ESel (EVar 248) (TupleSel 2))))).

Definition tupsel_ge := bind_decl_group tup (bind_decl_group tupsel gempty).

Lemma tupsel_eval :
  eval_expr tupsel_ge empty (EVar 249) three.
Proof.
  eapply eval_global_var; try reflexivity.
  econstructor.
  eapply eval_global_var; try reflexivity.
  econstructor; eauto.
  repeat (econstructor; eauto).
  simpl. f_equal. unfold three. f_equal.
  unfold zrepr.
  match goal with
  | [ |- ?X = ?Y ] => destruct (@eq_spec _ nz X Y); try congruence
  end.
  Unshelve.
  all: omega.
Qed.
