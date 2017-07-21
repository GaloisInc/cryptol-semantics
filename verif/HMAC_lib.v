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
Require Import Eager.
Require Import Bitstream.

Require Import EvalTac.

Import HaskellListNotations.
Open Scope string.

Require Import HMAC.


(* TODO: is this the right definition of a good hash? *)
Definition good_hash (h : Expr) (ge : genv) (T : tenv) (SE : senv) (hf : strictval -> strictval) : Prop :=
  (exists id exp TE E,
      eager_eval_expr ge T SE h (sclose id exp TE E) /\ (* can evaluate the hash to a closure *)
      forall n v,
        sn_bits n v ->
        eager_eval_expr ge TE (extend E id v) exp (hf v) (* can evaluate that closure applied to a value *)
  ).

Lemma good_hash_eval :
  forall h GE T SE hf,
    good_hash h GE T SE hf ->
    exists id exp TE E,
      eager_eval_expr GE T SE h (sclose id exp TE E).
Proof.
  intros. unfold good_hash in *.
  do 5 destruct H. eauto.
Qed.

(* lowercase is concrete, uppercase is abstract *)
(* wf_env lets this proof be used over a variety of environments that meet the proper constraints *)
Definition wf_env (ge GE : genv) (TE : tenv) (SE : senv) : Prop :=
  forall id,
    ge id <> None -> (TE id = None /\ SE id = None /\ ge id = GE id).

Lemma wf_env_global :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      GE id = Some exp.
Proof.
  intros. unfold wf_env in *.
  destruct (H id); try congruence.
  destruct H2. congruence.
Qed.

Lemma wf_env_not_local :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      SE id = None.
Proof.
  intros. unfold wf_env in *.
  destruct (H id); try congruence.
  destruct H2. congruence.
Qed.

Lemma wf_env_not_type :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      TE id = None.
Proof.
  intros. unfold wf_env in *.
  destruct (H id); try congruence.
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



(* Eager tactics *)
(* TODO: standardize *)
Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac fg := eapply eager_eval_global_var; [ reflexivity | eassumption | idtac].
Ltac g := eapply eager_eval_global_var; try eassumption; try reflexivity.
Ltac ag := g; [eapply wf_env_not_local; eauto; reflexivity | eapply wf_env_global; eauto; simpl; reflexivity | idtac].

Ltac et :=
  match goal with
  | [ |- eager_eval_type _ _ _ _ ] => solve [repeat econstructor; eauto]
  end.

Ltac e :=
  match goal with
  | [ |- eager_eval_expr ?GE _ ?E (EVar ?id) _ ] =>
    (try fg); (try reflexivity);
    (try solve [eapply eager_eval_local_var; reflexivity]);
    fail 1 "couldn't figure out variable"
  | [ |- _ ] => ec; try solve [et]
  end.


(* Model of hmac, given model of hash *)
Definition hmac_model (hf : strictval -> strictval) (key msg : strictval) : option strictval := None. (* TODO *)

Definition typenum (n : Z) : Expr := ETyp (TCon (TC (TCNum n)) []).

Ltac abstract_globals ge :=
  repeat match goal with
         | [ H : ge _ = _ |- _ ] => eapply wf_env_global in H; eauto
         end.
