
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


Lemma n_bits_eval :
  forall n x ge,
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
