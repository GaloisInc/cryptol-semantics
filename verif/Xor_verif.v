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
Require Import Bitstream.

Require Import EvalTac.
Require Import Eager.

Import HaskellListNotations.
Open Scope string.

Require Import Xor.

(* expects a type variable, but ignores it *)
Definition decrypt : Expr := (ETApp (EVar (243,"decrypt")) (ETyp (TCon (TC (TCNum 3)) nil))).
Definition encrypt : Expr := (ETApp (EVar (242,"encrypt")) (ETyp (TCon (TC (TCNum 3)) nil))).

(* Notation "eval_expr* GE E V" := (eval_expr GE _ E V) (at level 99, only printing). *)
(* Notation "vcons* V EXP" := (vcons V EXP _) (at level 98, only printing). *)
(* Notation "force_list* V VS" := (force_list _ _ V VS) (at level 97, only printing). *)

Lemma single_bit_roundtrip :
  forall (b b' : bool),
    (if (if b then (if b' then false else true) else b') then (if b' then false else true) else b') = b.
Proof.
  intros. destruct b; destruct b'; simpl; auto.
Qed.

Definition match_val {A B : Type} (a : A) (b : B) : Prop := True. (* TODO *)

Lemma n_bits_destr :
  forall n x,
    n_bits (S n) x ->
    exists b x',
      x = (bit b) :: x' /\ n_bits n x'.
Proof.
  intros. inversion H. subst. eauto.
Qed.

(* we need an eager eqivalent for n_bits *)

Ltac nb_destr :=
  repeat (match goal with
          | [ H : n_bits _ _ |- _ ] => eapply n_bits_destr in H
          end);
  repeat (match goal with
         | [ H : exists _, _ |- _ ] => destruct H
          end);
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end;
  try match goal with
      | [ H : n_bits O _ |- _ ] => inversion H; clear H
      end.
         
Definition sempty : ident -> option strictval := fun x => None.



Lemma n_bits_eval :
  forall n x,
    n_bits n x ->
    exists v,
      eager_eval_expr ge sempty (EList (map EValue x)) v.
Proof.
  induction 1; intros.
  eexists. econstructor; eauto. simpl. econstructor.
  destruct IHn_bits.
  inversion H0.
  eexists. simpl. econstructor. simpl. econstructor. econstructor. econstructor.
  eauto. reflexivity.
Qed.


Lemma xor_bits_roundtrip :
  forall n x y,
    n <> O ->
    n_bits n x ->
    n_bits n y ->
    forall vx vy,
      eager_eval_expr ge sempty (EList (map EValue x)) vx ->
      eager_eval_expr ge sempty (EList (map EValue y)) vy ->
      exists halfway,
        xor_sem vx vy = Some halfway /\ xor_sem halfway vy = Some vx.
Proof.
  induction n; intros. congruence.
  destruct n.
  clear IHn. 
  - (* base case *)
    inversion H0. subst. inversion H5. subst.
    inversion H1. subst. inversion H6. subst.
    clear H5 H6.
    inversion H2. inversion H3. subst. inversion H5. inversion H10.
    subst. inversion H9. inversion H15. subst. inversion H7. inversion H13.
    subst. inversion H8. inversion H16. subst. unfold strict_list.
    simpl. eexists; split. reflexivity.
    simpl. rewrite single_bit_roundtrip. reflexivity.
  - inversion H0. subst. clear H0.
    inversion H1. subst. clear H1.
    simpl in H2. simpl in H3.
    inversion H2. inversion H3. subst.
    inversion H1. inversion H10. subst.
    
    edestruct IHn. congruence. eapply H5. eapply H4. 
    econstructor. eassumption. reflexivity.
    econstructor. eassumption. reflexivity.
    destruct H0.
    simpl. rewrite H0.
    inversion H7. inversion H13. subst.
    inversion H12. inversion H18. subst. simpl.
    eexists; split; try reflexivity.
    simpl. rewrite H6.
    rewrite single_bit_roundtrip. reflexivity.
Qed.
    

Lemma xor_roundtrip_eager :
  forall pt,
    Forall (n_bits 8%nat) pt ->
    forall k,
      n_bits (8%nat) k ->
      exists pt',
        eager_eval_expr ge sempty (EApp (EApp decrypt (EList (map EValue k))) (EApp (EApp encrypt (EList (map EValue k))) (EList (map EList (map (map EValue) pt))))) pt' /\ match_val pt pt'.
Proof.
  induction 1; intros.
  - repeat nb_destr; subst.
    eexists; split.
    unfold decrypt.
    econstructor. econstructor. 
    econstructor. eapply eager_eval_global_var.
    simpl; eauto. unfold ge; unfold extend; simpl. reflexivity.
    econstructor.
    repeat econstructor; eauto.
    econstructor.
    econstructor. simpl.
    repeat econstructor. reflexivity.
    econstructor. e. e. unfold encrypt.
    e. eapply eager_eval_global_var. reflexivity. reflexivity.
    e. repeat e. e. repeat e.
    e. e. e.
    
    e. repeat e. simpl. repeat e.
    e. repeat e. simpl. repeat e.
    (* TODO *)
    simpl. unfold match_val. auto.

  - remember H1 as Hkey; clear HeqHkey.
    eapply IHForall in H1.
    clear IHForall. destruct H1. destruct H1.
    inversion H1. subst. clear H1.
    unfold decrypt in *. unfold encrypt in *.
    inversion H7. subst. clear H7.
    inversion H4. subst. clear H4.
    inversion H6. subst. clear H6.
    inversion H4. subst. clear H4.
    unfold sempty in *. congruence.
    subst. clear H4.
    clear H3.
    unfold ge in H6; unfold extend in H6; simpl in H6; inversion H6; subst; clear H6.
    inversion H12. subst. clear H12.
    inversion H6. subst. clear H6.
    inversion H14. subst. clear H14.
    inversion H15. subst. clear H15.
    inversion H13. subst. clear H13.
    inversion H11. subst. clear H11.
    inversion H4; try congruence. subst. clear H4.
    inversion H6; try congruence. subst. clear H6.
    inversion H11. subst. clear H11.
    Focus 2. subst. unfold extend in H3. simpl in H3. congruence.
    unfold extend in H4. simpl in H4. inversion H4. subst. clear H4.
    inversion H8. subst. clear H8.
    
    inversion H5. subst. clear H5.
    inversion H6. subst. clear H6.
    inversion H5. subst. clear H5.
    unfold sempty in H6. simpl in H6. congruence.
    subst. clear H5. clear H4.
    unfold ge in H6. unfold extend in H6. simpl in H6. inversion H6; subst; clear H6.
    inversion H15. subst. clear H15.
    inversion H16. subst. clear H16.
    inversion H12. subst. clear H12.
    inversion H6. subst. clear H6.
    inversion H14. subst. clear H14.
    rewrite list_of_strictval_of_strictlist in H13. inversion H13. subst. clear H13.
    inversion H9. subst. clear H9.
    inversion H5; try congruence. subst. clear H5.
    inversion H6; try congruence. subst. clear H6.
    inversion H9. subst. clear H9.
    Focus 2. subst. unfold extend in H4. simpl in H4. congruence.
    unfold extend in H5. simpl in H5. inversion H5. clear H5. subst.
    rewrite list_of_strictval_of_strictlist in H13. inversion H13. subst. clear H13.
    assert (av = av1). {
      repeat nb_destr; subst.
      inversion H11. subst. clear H11.
      inversion H10. subst. clear H10.
      clear -H1 H4.
      repeat (match goal with
              | [ H : Forall2 _ _ _ |- _ ] => inversion H; subst; clear H
              end).
      repeat match goal with
             | [ H : eager_eval_expr _ _ (EValue _) _ |- _ ] => inversion H; subst; clear H
             end.
      repeat match goal with
             | [ H : strict_eval_val _ (vcons _ _ _) _ |- _ ] => inversion H; subst; clear H
             | [ H : strict_eval_val _ (bit _) _ |- _ ] => inversion H; subst; clear H
             | [ H : strict_eval_val _ vnil _ |- _ ] => inversion H; subst; clear H
             end.
      reflexivity.

    } idtac.
    subst. clear H11.
    
    (* need this *)
    assert (exists x', eager_eval_expr ge sempty (EList (map EValue x)) x'). {
      eapply n_bits_eval; eauto.
    } idtac.
    destruct H1.
    
    

    
    assert (exists halfway, xor_sem x0 av1 = Some halfway /\ xor_sem halfway av1 = Some x0). {
      eapply xor_bits_roundtrip. Focus 4. eassumption. Focus 4. eassumption.
      Focus 2. eassumption.
      Focus 2. eassumption.
      congruence.
    } idtac.
    destruct H4. destruct H4.
    
    eexists; split.

    e. e. e. eapply eager_eval_global_var. reflexivity. reflexivity.
    e. repeat e.
    e. eassumption.
    e. simpl. e. e. e.
    eapply eager_eval_global_var. reflexivity. reflexivity.
    e. repeat e.
    e. eassumption. e. e. econstructor.
    eassumption.
    eassumption. (* apply (part of) inductive hypothesis *)
    
    e. e. e. e. simpl. rewrite list_of_strictval_of_strictlist. reflexivity.
    simpl. econstructor.
    * econstructor.
      econstructor. econstructor. eapply (eager_eval_global_var); try reflexivity.
      unfold mb. simpl. econstructor. econstructor. econstructor. reflexivity.
      econstructor. econstructor. econstructor. econstructor. reflexivity.
      econstructor. econstructor. reflexivity.
      econstructor. repeat econstructor. simpl. eassumption.
    * eapply eager_eval_other_envs. eassumption.
      clear -lv.
      {
        admit. (* tis true *)
      }
    * e. e. e. e. rewrite list_of_strictval_of_strictlist. reflexivity.
      simpl. econstructor.
      econstructor. econstructor. econstructor.
      eapply (eager_eval_global_var); try reflexivity.
      unfold mb. simpl. econstructor. econstructor. econstructor. reflexivity.
      econstructor. econstructor. econstructor. econstructor. reflexivity.
      econstructor. econstructor. reflexivity.
      econstructor. repeat econstructor. simpl.
      eassumption.
      eapply eager_eval_other_envs. eassumption.
      {
        admit. (* this is true, prove later *)
      }
    * unfold match_val. auto. (* TODO *)

Admitted.
    


Lemma xor_roundtrip :
  forall pt,
    Forall (n_bits 8%nat) pt ->
    forall k,
      n_bits (8%nat) k ->
      exists pt',
        strict_eval_expr ge empty (EApp (EApp decrypt (EList (map EValue k))) (EApp (EApp encrypt (EList (map EValue k))) (EList (map EList (map (map EValue) pt))))) pt' /\ match_val pt pt'.
Proof.
  intros. eapply xor_roundtrip_eager in H0; eauto.
  destruct H0. destruct H0.
  eapply eager_to_strict_lazy in H0; eauto.
  unfold match_env. intros. unfold empty. unfold sempty. econstructor.
Qed.
