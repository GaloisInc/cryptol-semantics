
Require Import AST.

(* any finite bitstream *)
(* use to state correctness of crypto functions *)
Inductive finite_bitstream : list val -> Prop :=
| empty_stream :
    finite_bitstream nil
| one_more :
    forall b l,
      finite_bitstream l ->
      finite_bitstream (bit b :: l).

(* bits with length encoded *)
Inductive n_bits : nat -> list val -> Prop :=
| empty_bits :
    n_bits O nil
| another_bit :
    forall n l b,
      n_bits n l ->
      n_bits (S n) (bit b :: l).


Require Import Eager.
Require Import List.


Lemma strict_list_injective :
  forall x y,
    strict_list x = strict_list y ->
    x = y.
Proof.
  induction x; intros. simpl in *.
  destruct y; simpl in H; try congruence.
  simpl in H. destruct y; simpl in H; try congruence.
  inversion H. subst. eapply IHx in H2. congruence.
Qed.

Lemma n_bits_eval :
  forall n x ge TE E,
    n_bits n x ->
    exists vs,
      eager_eval_expr ge TE E (EList (map EValue x)) (strict_list vs) /\ length vs = n.
Proof.
  induction 1; intros.
  eexists. split. econstructor; eauto. simpl. econstructor. reflexivity.
  destruct IHn_bits. destruct H0.
  inversion H0.
  eexists. split. simpl. econstructor. simpl. econstructor. econstructor. econstructor.
  eauto. reflexivity.
  simpl. subst.
  eapply strict_list_injective in H6; eauto. congruence.
Qed.
