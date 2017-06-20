Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.

(* right side of this generated from cryptol implementation *)

Definition id_cry : DeclGroup := (NonRecursive (Decl 242 (DExpr (EAbs 243 (EWhere (EApp (EVar 244) (EVar 243)) [(Recursive [(Decl 244 (DExpr (EAbs 245 (EIf (EApp (EApp (EVar 17) (EVar 245)) (EVar 0)) (EVar 0) (EApp (EApp (EVar 1) (EVar 0)) (EApp (EVar 244) (EApp (EApp (EVar 1) (EVar 245)) (EApp (EVar 11) (EVar 0)))))))))])]))))).

Definition width : nat := 32.

Lemma nz :
  width <> O.
Proof.
  unfold width. congruence.
Qed.

Definition lit (z : Z) : Expr :=
  ELit (@repr width nz z).

(* 17 -> eq *)
(* 1 -> plus *)
Definition id_cry_hand_mod : DeclGroup := (NonRecursive (Decl 242 (DExpr (EAbs 243 (EWhere (EApp (EVar 244) (EVar 243)) [(Recursive [(Decl 244 (DExpr (EAbs 245 (EIf (EApp (EApp (EVar 17) (EVar 245)) (lit 0)) (lit 0) (EApp (EApp (EVar 1) (lit 1)) (EApp (EVar 244) (EApp (EApp (EVar 1) (EVar 245)) (lit (-1)))))))))])]))))).

Definition add_1_2 := EApp (EApp (EVar 1) (lit 1)) (lit 2).

Definition plus_decl := builtin_binop 1 Plus.

Definition three_ge := bind_decl_group plus_decl gempty.

Lemma to_three :
  eval_expr three_ge empty add_1_2 (bits (@repr width nz 3) ).
Proof.
  econstructor. unfold three_ge.
  econstructor.
  eapply eval_global_var.
  unfold empty. reflexivity.
  simpl. reflexivity.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
Qed.
  
Definition eq_decl := builtin_binop 17 Eq.


Definition id_ge := bind_decl_group id_cry_hand_mod
                                    (bind_decl_group eq_decl
                                                     (bind_decl_group plus_decl gempty)).
Definition E := extend empty 12 (bits (@repr width nz 2)).

Lemma eval_id :
  eval_expr id_ge E (EApp (EVar 242) (EVar 12)) (bits (@repr width nz 2)).
Proof.
  econstructor. unfold id_ge.
  simpl. eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. auto.
  simpl. reflexivity.
  econstructor. econstructor. unfold E. unfold extend. simpl. reflexivity.
  econstructor.
  simpl. econstructor.
  eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. auto.
  simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  eapply eval_if_f.
  econstructor. econstructor.
  eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. auto.
  simpl. unfold id_ge. unfold bind_decl_group. simpl. reflexivity.
  econstructor; eauto.
  econstructor; eauto. unfold extend. simpl. reflexivity.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto. unfold extend. simpl. reflexivity.
  econstructor; eauto. unfold extend. simpl. reflexivity.
  econstructor; eauto; exact nz.

  econstructor. econstructor. eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. reflexivity.
  simpl. unfold id_ge. simpl. reflexivity.

  econstructor. econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_global_var; eauto. simpl. reflexivity.
  econstructor; eauto.
  econstructor. econstructor.
  eapply eval_global_var; eauto. simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor.
  unfold extend. simpl. reflexivity.
  econstructor. econstructor. econstructor. econstructor.
  unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.

  eapply eval_if_f. econstructor.
  econstructor. eapply eval_global_var; eauto. simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor. unfold E. unfold extend. simpl. reflexivity.

  econstructor. econstructor.
  econstructor;
    try econstructor; try unfold extend; simpl; eauto.
  econstructor; exact nz.
  
  econstructor.
  econstructor. eapply eval_global_var; eauto. simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor.
  econstructor. econstructor.
  eapply eval_global_var. simpl. unfold id_ge. simpl. reflexivity. simpl. reflexivity.
  econstructor. econstructor. econstructor. eapply eval_global_var.
  simpl. unfold id_ge. simpl. reflexivity. simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. econstructor.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
  eapply eval_if_t. econstructor. econstructor.
  eapply eval_global_var. unfold extend. simpl. unfold E. unfold extend. simpl. unfold empty.
  reflexivity.
  simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. econstructor. econstructor; try unfold extend; try econstructor; simpl; eauto.
  econstructor; eauto; exact nz.
  econstructor.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
  Unshelve.
  all: exact nz.
Qed.
  


