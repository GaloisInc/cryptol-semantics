Require Import String.
Require Import AST.
Require Import List.
Require Import Values.
Require Import Semantics.
Require Import Bvector. 

(* We need easy ways of writing down inputs to cryptol functions *)
(* They only need base type bit, and structures *)

(* make some kind of type, convertible to val and strictval *)

Lemma map_snd_to_sval_lp :
  forall f,
    map snd (to_sval_list_pair f) = map to_sval (map snd f).
Proof.
  induction f; intros; simpl; auto.
  destruct a. simpl. f_equal. auto.
Qed.

Lemma map_snd_to_val_lp :
  forall f,
    map snd (to_val_list_pair f) = map to_val (map snd f).
Proof.
  induction f; intros; simpl; auto.
  destruct a. simpl. f_equal. auto.
Qed.

Lemma to_sval_lp_fst :
  forall f,
    map fst (to_sval_list_pair f) = map fst f.
Proof.
  induction f; simpl; intros; auto; destruct a; simpl; f_equal; auto.
Qed.

Lemma to_val_lp_fst :
  forall f,
    map fst (to_val_list_pair f) = map fst f.
Proof.
  induction f; simpl; intros; auto; destruct a; simpl; f_equal; auto.
Qed.

Lemma strict_eval_list :
  forall l ge,
    Forall (fun v => strict_eval_val ge (to_val v) (to_sval v)) l ->
    strict_eval_val ge (thunk_list (map to_val l)) (strict_list (map to_sval l)).
Proof.
  induction l; intros.
  simpl. econstructor; eauto.
  simpl.
  inversion H. subst. eapply IHl in H3.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma Forall2_map_Forall :
  forall {A B C : Type} P (f1 : A -> B) (f2 : A -> C) (l : list A),
    Forall (fun x => P (f1 x) (f2 x)) l ->
    Forall2 P (map f1 l) (map f2 l).
Proof.
  induction 1; intros.
  simpl. econstructor.
  simpl. econstructor; eauto.
Qed.

Lemma separate_combine :
  forall {A B : Type} (l : list (A * B)),
    l = combine (map fst l) (map snd l).
Proof.
  induction l; intros; simpl; auto.
  destruct a; simpl; f_equal; eauto.
Qed.

Lemma strict_eval_rec :
  forall ge f,
    Forall (fun ev : ext_val => strict_eval_val ge (to_val ev) (to_sval ev)) (map snd f) ->
    strict_eval_val ge (to_val (erec f)) (to_sval (erec f)).
Proof.
  induction f; intros.
  simpl.
  rewrite (@separate_combine string strictval) at 1. econstructor.
  econstructor. reflexivity.

  simpl in H. inversion H. subst.
  specialize (IHf H3).
  destruct a. simpl in H2.
  simpl. fold to_val_list_pair.
  fold to_sval_list_pair.
  econstructor. simpl. econstructor. eassumption.
  instantiate (1 := (map snd (to_sval_list_pair f))).
  rewrite map_snd_to_val_lp.
  rewrite map_snd_to_sval_lp.
  eapply Forall2_map_Forall.
  eapply H3.
  simpl. f_equal.
  rewrite (separate_combine (to_sval_list_pair f)) at 1.
  f_equal.
  rewrite to_val_lp_fst.
  rewrite to_sval_lp_fst.
  reflexivity.
Qed.

Lemma strict_eval_val_to_val :
  forall ge (ev : ext_val),
    strict_eval_val ge (to_val ev) (to_sval ev).
Proof.
  induction ev using ext_val_ind_mut; intros;
    try solve [econstructor; eauto].
  simpl.
  eapply strict_eval_list; eauto.
  simpl.
  econstructor.
  eapply Forall2_map_Forall; eauto.
  eapply strict_eval_rec; eauto.
Qed.



Inductive ext_type :=
| tbit
| tseq (len : nat) (t : ext_type)
| ttup (l : list ext_type)
| trec (l : list (string * ext_type))
.

Inductive has_type : ext_val -> ext_type -> Prop :=
| is_bit :
    forall b,
      has_type (ebit b) tbit
| is_seq :
    forall l t,
      Forall (fun x => has_type x t) l ->
      has_type (eseq l) (tseq (length l) t)
| is_tup :
    forall l lt,
      Forall2 has_type l lt ->
      has_type (etup l) (ttup lt)
| is_rec :
    forall l lt,
      Forall2 has_type (map snd l) lt ->
      has_type (erec l) (trec (combine (map fst l) lt))
.

Definition byte : ext_type := tseq 8 tbit.
Definition bytestream (n : nat) := tseq n byte.
Definition word : ext_type := tseq 64 tbit.


Fixpoint to_bvector (w : nat) (e : ext_val) : option (Bvector w) :=
  match e,w with
  | eseq (ebit b :: r),S n =>
    match to_bvector n (eseq r) with
    | Some bv => 
      Some (Vector.cons bool b n bv)
    | _ => None
    end
  | eseq nil, O => Some (Vector.nil bool)
  | _,_ => None
  end.

Lemma to_bvector_succeeds :
  forall l n,
    has_type (eseq l) (tseq n tbit) ->
    exists bv,
      to_bvector n (eseq l) = Some bv.
Proof.
  induction l; intros.

  * inversion H. subst. simpl.
    eauto.

  * inversion H. subst. inversion H2.
    subst.
    edestruct IHl. econstructor; eauto.
    inversion H3. subst.
    simpl. rewrite H0.
    eauto.
Qed.




Definition n_bits (n : nat) (v : val) : Prop :=
  exists ev,
    has_type ev (tseq n tbit) /\ to_val ev = v.

Definition sn_bits (n : nat) (v : strictval) : Prop :=
  exists ev,
    has_type ev (tseq n tbit) /\ to_sval ev = v.
    

(*
Inductive n_bits : nat -> list val -> Prop :=
| empty_bits :
    n_bits O nil
| another_bit :
    forall n l b,
      n_bits n l ->
      n_bits (S n) (bit b :: l).
*)

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

(*
Lemma n_bits_eval :
  forall n x ge TE E,
    n_bits n x ->
    exists vs,
      eager_eval_expr ge TE E (EValue x) (strict_list vs) /\ length vs = n.
Proof.
  induction n; intros;
    unfold n_bits in *;
    destruct H. destruct H.
  inversion H. destruct l; simpl in *; try congruence. subst.
  eexists; split. simpl. econstructor; eauto. instantiate (1 := nil). econstructor; eauto. reflexivity.

  destruct H. inversion H. subst.
  destruct l; simpl in *; try congruence.
  inversion H3.
  subst. inversion H4.
  subst. inversion H1. subst.
  edestruct IHn; eauto.
  eexists; split; eauto.
  econstructor. eauto.
  destruct H0.

  
  eexists; split; eauto.
  simpl. inversion H0. subst.
  econstructor. instantiate (1 := (sbit b :: x)).
  simpl. econstructor; eauto.
  econstructor. econstructor.
  simpl. congruence.

  Unshelve. exact tempty.
  exact sempty.
Qed.

*)