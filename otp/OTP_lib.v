Require Import Cryptol.Coqlib.
Require Import Cryptol.BvectorExt.
Require Import Cryptol.Bitstream.
Require Import Cryptol.Eager.
Require Import Cryptol.Semantics.
Require Import Cryptol.AST.

Require Import otp.FCF.
Require Import otp.OTP_FCF.
Require Import otp.OTP_verif.
Require Import otp.OTP_cryptol.

Lemma same_otp' :
  forall key msg bvkey bvmsg,
    has_type key byte -> 
    has_type msg byte ->
    to_bvector 8%nat key = Some bvkey ->
    to_bvector 8%nat msg = Some bvmsg ->
    otp_encrypt key msg = eseq (bv_to_extval' (OTP_encrypt bvkey bvmsg)).
Proof.
  intros.
  inversion H. inversion H0. subst.
  do 9 (destruct l; try solve [simpl in *; omega]).
  do 9 (destruct l0; try solve [simpl in *; omega]).
  clear H. clear H0.
  repeat match goal with
         | [ H : Forall _ _ |- _ ] => inversion H; clear H
         | [ H : has_type ?X tbit |- _ ] => inversion H; subst X; clear H
         end;
    subst.
  simpl in H2. inversion H2. subst.
  simpl in H1. inversion H1. subst.
  clear H1 H2.
  simpl. reflexivity.
Qed.

Lemma same_otp :
  forall key msg bvkey bvmsg,
    has_type key byte -> 
    has_type msg byte ->
    to_bvector 8%nat key = Some bvkey ->
    to_bvector 8%nat msg = Some bvmsg ->
    to_bvector 8%nat (otp_encrypt key msg) = Some (OTP_encrypt bvkey bvmsg).
Proof.
  intros.
  inversion H. inversion H0. subst.
  do 9 (destruct l; try solve [simpl in *; omega]).
  do 9 (destruct l0; try solve [simpl in *; omega]).
  clear H. clear H0.
  repeat match goal with
         | [ H : Forall _ _ |- _ ] => inversion H; clear H
         | [ H : has_type ?X tbit |- _ ] => inversion H; subst X; clear H
         end;
    subst.
  simpl in H2. inversion H2. subst.
  simpl in H1. inversion H1. subst.
  clear H1 H2.
  reflexivity.
Qed.

Lemma to_bvector_succeeds' :
  forall v len,
    has_type v (tseq len tbit) ->
    exists (bv : Bvector len),
      to_bvector len v = Some bv.
Proof.
  intros. inversion H.
  subst.
  eapply to_bvector_succeeds; eauto.
Qed.

Lemma has_type_xor_ext' :
  forall len a b,
    has_type a (tseq len tbit) ->
    has_type b (tseq len tbit) ->
    has_type (xor_ext' a b) (tseq len tbit).
Proof.
  induction len; intros;
  inversion H; inversion H0;
  destruct l; try solve [simpl in *; omega];
    destruct l0; try solve [simpl in *; omega];
      subst.
  simpl. econstructor; eauto.
  inversion H3. inversion H7.
  subst x l1 x0 l2.
  inversion H6. inversion H11.
  subst e e0.
  eapply is_seq in H8.
  eapply is_seq in H12.
  simpl in H1. simpl in H5. inversion H1. inversion H5.
  rewrite H9 in *. rewrite H4 in *.
  eapply (IHlen (eseq l) (eseq l0)) in H8; eauto.
  clear -H8 H4 H9.
  inversion H8.
  destruct (xor_ext l l0) eqn:?; try congruence.
  inversion H. subst.
  unfold xor_ext'. unfold xor_ext. fold xor_ext.
  rewrite Heqo.
  simpl.
  replace (S (length l)) with (length (ebit (xorb b b0) :: l2)).
  econstructor; eauto.
  econstructor. econstructor; eauto.
  eauto.
  simpl. f_equal.
  assumption.
Qed.

