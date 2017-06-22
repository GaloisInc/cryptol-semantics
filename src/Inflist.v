
(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import Tactics.

Import HaskellListNotations.
Open Scope string_scope.

Definition inflist := (NonRecursive
                         (Decl 245 (DExpr
                                      (EApp (EApp
                                               (ETApp (EVar 52) (TCon (TC (TCNum 8)) []))
                                               (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])))
                                            (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])))))).

Definition finlist := (NonRecursive (Decl 246 (DExpr (EList [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) []))])))).

Definition finlist_sel_exp := ESel (EVar 246) (ListSel ((ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])))).

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
  simpl. reflexivity.
  Unshelve.
  all: unfold Z.to_nat; unfold Pos.to_nat; simpl; try congruence.
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
  Unshelve.
  all: unfold Z.to_nat; unfold Pos.to_nat; simpl; try congruence.
Qed.

Definition one := bits (@repr 8 nz 1).
Definition two := bits (@repr 8 nz 2).

Lemma finlist_sel_eval :
  eval_expr (bind_decl_group finlist gempty) empty finlist_sel_exp three.
Proof.
  e. e.
  match goal with
  | [ |- select_list _ _ ?N _ _ ] => replace N with (S (S O)) by (simpl; reflexivity)
  end.
  econstructor.
  global. e.
  repeat econstructor. simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. econstructor. simpl. reflexivity.
  Unshelve.
  all: exact nz.
Qed.


Definition where_decl := (NonRecursive (Decl 250 (DExpr (EWhere (EVar 259) [(NonRecursive (Decl 259 (DExpr (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])))))])))).

Lemma where_eval :
  eval_expr (bind_decl_group where_decl gempty) empty (EVar 250) three.
Proof.
  global.
  e. e. global.
  e.
Qed.

Definition listcomp := (NonRecursive (Decl 251 (DExpr (EAbs 261 (EWhere (EVar 262) [(NonRecursive (Decl 262 (DExpr (EComp (EApp (EApp (ETApp (EVar 1) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EVar 263)) (EVar 264)) [[(From 263 (EVar 261))],[(From 264 (EList [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 3)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 4)) [])) (TCon (TC (TCNum 8)) []))]))]]))))]))))). 

Definition comp_idx_expr : Expr := ESel (EApp (EVar 251) (EVar 246)) (ListSel (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) []))).

Definition six := bits (@repr 8 nz 6).

Lemma listcomp_eval :
  eval_expr (bind_decl_groups (listcomp :: finlist :: plus_decl :: nil) gempty) empty comp_idx_expr six.
Proof.
  unfold comp_idx_expr.
  e.
  e.
  eapply select_comp.
  e. global. e. global. e.
  repeat econstructor. e.
  global. e.
  
  econstructor. econstructor.
  econstructor.
  econstructor. simpl. reflexivity.

  econstructor. econstructor.
  reflexivity.
  eapply select_zero. econstructor. reflexivity.
  econstructor. econstructor. 
  econstructor. econstructor.
  
  repeat econstructor. reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. econstructor.
  econstructor. e. global. econstructor. econstructor.
  reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. econstructor. reflexivity.
  econstructor. reflexivity.
  econstructor. omega.
  Unshelve.
  all: exact nz.
Qed.

  
Definition gf28Add := (NonRecursive (Decl 249 (DExpr (ETAbs 331 (EAbs 255 (EWhere (EApp (EApp (ETApp (ETApp (ETApp (EVar 42) (TCon (TF TCAdd) [TCon (TC (TCNum 1)) [],TVar (TVBound 331 KNum)])) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (TCon (TC (TCNum 0)) [])) (EVar 256)) (ETApp (ETApp (EVar 0) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 0)) []))) [(Recursive [(Decl 256 (DExpr (EApp (EApp (ETApp (ETApp (ETApp (EVar 34) (TCon (TC (TCNum 1)) [])) (TVar (TVBound 331 KNum))) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EList [(ETApp (EVar 29) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []]))])) (EComp (EApp (EApp (ETApp (EVar 28) (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])) (EVar 257)) (EVar 258)) [[(From 257 (EVar 255))],[(From 258 (EVar 256))]]))))])])))))).

Definition add_call := (NonRecursive (Decl 250 (DExpr (EApp (ETApp (EVar 249) (TCon (TC (TCNum 2)) [])) (EList [(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 8)) [])),(ETApp (ETApp (EVar 0) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 8)) []))]))))).

Definition gf28_add_ge := bind_decl_groups (gf28Add :: add_call :: plus_decl :: nil) gempty.


Lemma eval_gf28_add :
  eval_expr gf28_add_ge empty (EVar 250) three.
Proof.
  unfold gf28_add_ge. unfold bind_decl_groups.
  global.
  e.
  e. global.
  e. e. e. repeat econstructor.
  e. e. e. e. e. e. eapply eval_global_var.
  unfold extend. simpl. reflexivity.
  (* TODO *)
  
Admitted.  