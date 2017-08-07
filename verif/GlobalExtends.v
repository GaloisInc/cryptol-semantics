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
Require Import Lib.


Definition name_irrel {A : Type} (E : ident -> option A) : Prop :=
  forall id id',
    if ident_eq id id' then E id = E id' else True.

Lemma name_irrel_diff_results :
  forall {A} E id id',
    @name_irrel A E ->
    E id <> E id' ->
    exists p,
      ident_eq id id' = right p.
Proof.
  intros.
  unfold name_irrel in H.
  specialize (H id id').
  destruct (ident_eq id id') eqn:?.
  congruence.
  exists n. eauto.
Qed.

Definition same_values (ge GE : genv) : Prop :=
  forall id v,
    ge id = Some v ->
    GE id = Some v.

Definition finite (ge : genv) : Prop :=
  exists l,
  forall id,
    ge id <> None <-> In id l.

Fixpoint make_ge (l : list (ident * Expr)) (ge : genv) : genv :=
  match l with
  | nil => ge
  | (id,exp) :: l' =>
    let ge' := make_ge l' ge in
    extend ge' id exp
  end.

Definition finite' (ge : genv) (l : list (ident * Expr)) : Prop :=
  forall id,
    ge id = make_ge l gempty id.

Fixpoint id_In (ide : (ident * Expr)) (l : list (ident * Expr)) : Prop :=
  match l with
  | nil => False
  | (id,e) :: l =>
    match ide with
    | (id',e') => (fst id = fst id' /\ e = e') \/ id_In (id',e') l
    end
  end.

(* lowercase is concrete, uppercase is abstract *)
(* wf_env lets this proof be used over a variety of environments that meet the proper constraints *)
Definition wf_env (ge GE : genv) (TE : tenv) (SE : senv)  : Prop :=
  name_irrel ge /\ name_irrel GE /\ name_irrel TE /\ name_irrel SE /\ (*finite GE /\*)
  (forall id,
      ge id <> None -> (TE id = None /\ SE id = None /\ ge id = GE id)).

Definition global_extends (ge GE : genv) : Prop :=
  same_values ge GE /\
  finite ge /\ finite GE /\
  name_irrel ge.

(* TODO *)
(*
Definition global_extends (ge GE : genv) : Prop :=
  (forall id v,
    ge id = Some v ->
    GE id = Some v) /\
(*  (forall TE SE expr v,
      eager_eval_expr ge TE SE expr v ->
      eager_eval_expr GE TE SE expr v) /\*)
  exists l, (forall id x, ge id = Some x -> In x l) /\
              exists l',
                (forall id x, GE id = Some x -> In x l') /\
                (forall x, In x l -> In x l').
                                           
*)

Lemma global_extends_refl :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    global_extends GE GE.
Proof.
  intros.
  unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  unfold global_extends. split; auto.
  unfold same_values.
  intros. auto.
Admitted.

Lemma global_extends_extend_r :
  forall ge ge',
    global_extends ge ge' ->
    forall id exp,
      ge id = None ->
      global_extends ge (extend ge' id exp).
Proof.
  intros.
  unfold global_extends in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  split; auto; [idtac | split; auto].
  unfold same_values in *.
  intros.
  destruct (ident_eq id0 id) eqn:?; auto.
  unfold name_irrel in *. 
  specialize (H3 id0 id). rewrite Heqs in H3.
  congruence.
  unfold extend.
  rewrite Heqs.
  eapply H; eauto.
  split; auto.
  
  admit. (* finite extends to finite *)
  
Admitted.

(*
Inductive eager_eval_expr_listenv (ge : list (ident * Expr)) : tenv -> senv -> Expr -> strictval -> Prop :=
| eval_bind_list :
    forall TE SE e v,
      eager_eval_expr (make_ge ge gempty) TE SE e v ->
      eager_eval_expr_listenv ge TE SE e v.

Lemma eval_with_list_same :
  forall ge TE SE e v,
    eager_eval_expr (make_ge ge gempty) TE SE e v <->
    eager_eval_expr_listenv ge TE SE e v.
Proof.
  intros; split.
  intros. econstructor; eauto.
  intros.
  inversion H. eauto.
Qed.
 *)

Lemma name_irrel_extend :
  forall {A} E id (x : A),
    name_irrel E ->
    name_irrel (extend E id x).
Proof.
  intros. unfold name_irrel in *.
  intros.
  specialize (H id0 id').
  destruct (ident_eq id0 id') eqn:?; auto.
  unfold extend.
  destruct (ident_eq id0 id);
    destruct (ident_eq id' id); auto.
  rewrite e in e0. congruence.
  rewrite e in n. congruence.
Qed.

Lemma name_irrel_erase :
  forall {A} (E : ident -> option A) id,
    name_irrel E ->
    name_irrel (fun x => if ident_eq x id then None else E x).
Proof.
  intros.
  unfold name_irrel in *.
  intros.
  specialize (H id0 id').
  destruct (ident_eq id0 id'); auto.
  rewrite H.
  destruct (ident_eq id0 id);
    destruct (ident_eq id' id);
    auto; congruence.
Qed.


Lemma finite'_id_In :
  forall l ge id exp,
    ge id = Some exp ->
    finite' ge l ->
    id_In (id,exp) l.
Proof.
  induction l; intros;
    unfold finite' in H0;
    erewrite H0 in H. simpl in H. unfold gempty in *.  congruence.
  simpl in H. destruct a.
  unfold extend in H.
  destruct (ident_eq id i). simpl. left. split; congruence.
  simpl. right. eapply IHl; eauto.
  unfold finite'. intros. reflexivity.
Qed.


Lemma make_ge_id_in :
  forall l id exp,
    make_ge l gempty id = Some exp ->
    id_In (id,exp) l.
Proof.
  induction l; intros.
  simpl in H. unfold gempty in H. congruence.
  simpl in H. destruct a.
  unfold extend in H. destruct (ident_eq id i).
  simpl. left. split; congruence.
  simpl. right.
  eapply IHl; eauto.
Qed.

Lemma free_ge :
  forall expr ge TE SE v,  
    eager_eval_expr ge TE SE expr v ->
    forall ge',
      (forall id e, ge id = Some e ->
                    ge' id = Some e /\
                    forall TE SE v,
                      eager_eval_expr ge TE SE e v ->
                      eager_eval_expr ge' TE SE e v
      ) ->
      eager_eval_expr ge' TE SE expr v.
Proof.
  intro.
  eapply Expr_ind_useful with (e := expr); intros.
  Focus 8.
  inversion H. subst.
  econstructor; eauto.
  subst.
  eapply H0 in H3. destruct H3.
  eapply H3 in H6. eapply eager_eval_global_var; eauto.

  inversion H0. subst.
  econstructor; eauto.
  admit. admit.

  inversion H0. subst.
  econstructor; eauto.
  unfold Pl in H.
  eapply Forall_Forall2_implies; try eassumption.
  intros. simpl in H2.
  eapply H2; eauto.

  (* This is true, can finish proof if needed *)
Admitted.



Lemma eager_eval_expr_from_make_ge :
  forall expr l ge TE SE v,
    finite' ge l ->
    (forall id exp',
        id_In (id,exp') l ->
        forall v',
          eager_eval_expr (make_ge l gempty) TE SE exp' v' ->
          eager_eval_expr ge TE SE exp' v') ->
    eager_eval_expr (make_ge l gempty) TE SE expr v ->
    eager_eval_expr ge TE SE expr v.
Proof.
  intro.
  eapply Expr_ind_useful with (e := expr); intros;
    try solve [
           try (match goal with
                 | [ H : eager_eval_expr _ _ _ _ _ |- _ ] => inversion H; clear H
                 end);
          econstructor; eauto].
  Focus 7.
  inversion H1. subst.
  econstructor; eauto.
  subst. eapply eager_eval_global_var; eauto.
  unfold finite' in *. rewrite H. eauto.
  eapply H0; eauto.
  eapply finite'_id_In.
  unfold finite' in H. rewrite <- H in H4.
  eassumption. eauto.

  inversion H2. subst. econstructor; eauto.
  (* this is provable *)

  
Admitted.


Lemma eager_eval_expr_make_ge :
  forall expr l ge TE SE v,
    finite' ge l ->
    (forall id exp',
        id_In (id,exp') l ->
        forall v',
          eager_eval_expr ge TE SE exp' v' ->
          eager_eval_expr (make_ge l gempty) TE SE exp' v') ->
    eager_eval_expr ge TE SE expr v ->
    eager_eval_expr (make_ge l gempty) TE SE expr v.
Proof.
  intro.
  eapply Expr_ind_useful with (e := expr); intros.

  unfold Pl in *. inversion H2; subst; econstructor; eauto.
  admit. admit.

  admit. admit. admit. admit.
  admit. admit. 

  subst. inversion H1; try solve [econstructor; eauto]. subst. eapply eager_eval_global_var; eauto.
  unfold finite' in *. rewrite H in H4. eauto.
  eapply H0; eauto.
  instantiate (1 := id).
  eapply finite'_id_In; eauto.

  admit. admit. admit.
  admit. admit. admit.

  (* This one's true, will take a while to prove *)  
Admitted.


(* at the end of the day I need this fact *)
Lemma global_extends_eager_eval :
    forall expr v ge TE SE,
      eager_eval_expr ge TE SE expr v ->
      forall GE,
        global_extends ge GE ->
        eager_eval_expr GE TE SE expr v.
Proof.
  intros.
  unfold global_extends in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  unfold finite in *.
  destruct H1 as [l]. destruct H2 as [l'].
  unfold same_values in *.
  assert (forall id, In id l -> In id l').
  intros. eapply H2.
  destruct (ge id) eqn:?.
  eapply H0 in Heqo. congruence.
  erewrite <- H1 in H4. congruence.
  
  
  
Admitted.



(*
(* is this necessary? *)
Lemma finite_make_ge :
  forall ge,
    finite ge ->
    name_irrel ge ->
    exists l,
      forall id,
        ge id  = make_ge l gempty id.
Proof.
  intros. unfold finite in *.
  destruct H.
  generalize dependent ge.
  induction x; intros. exists nil.
  simpl in H. intros.
  destruct (ge id) eqn:?.
  assert (ge id <> None) by congruence.
  erewrite H in H1. inversion H1.
  simpl. unfold gempty. reflexivity.

  destruct (ge a) eqn:?.
  Focus 2.
  assert (In a (a :: x)) by (simpl; left; reflexivity).
  erewrite <- H in H1. congruence.

  remember (fun id => if ident_eq id a then None else ge id) as ge'.
  assert (forall id, ge' id <> None <-> In id x). {
    admit. (* idents ignore second part, which is hard *)
    (* this is not quite true both ways, backwards In id x -> ge' id <> None is hard *)
  }

  eapply IHx in H1.
  destruct H1 as [l'].
  exists ((a,e) :: l').
  intros.
  simpl. unfold extend.
  unfold name_irrel in H0.
  specialize (H0 id a).
  destruct (ident_eq id a) eqn:?.
  congruence.
  rewrite <- H1.
  subst ge'.
  rewrite Heqs. reflexivity.
  subst ge'.
  eapply name_irrel_erase; eauto.
Admitted.
*)


(*  intros. eapply global_extends_eager_eval'; eauto.
Qed.*)

(* Add a list to the GE that is all the things that GE contains *)
(*
Lemma eager_eval_expr_ident_irrel :
  forall ge id,
    ge id = None ->
    (forall id' exp',
        ge id' = Some exp' ->
        forall id0 exp0 TE SE v,
          eager_eval_expr ge TE SE exp' v ->
          eager_eval_expr (extend ge id0 exp0) TE SE exp' v) ->
    name_irrel ge ->
    forall expr TE SE v,
      eager_eval_expr ge TE SE expr v ->
      forall v',
        eager_eval_expr (extend ge id v') TE SE expr v.
Proof. 
  intros ge id Hnon Hnirr expr.
  eapply Expr_ind_useful with (e := expr); intros.
  * inversion H0. subst.
    econstructor; eauto.
    admit. admit.

  * inversion H0. subst.
    econstructor; eauto.
    unfold Pl in H.
    eapply Forall_Forall2_implies; try eapply H2; try eapply H.
    intros. eauto.

  * admit.

  * admit.

  * admit.
  * admit.
  * admit.
  * inversion H.
    subst. econstructor; eauto.
    subst.
    edestruct (@name_irrel_diff_results Expr); try eassumption; try congruence.
    instantiate (1 := id). instantiate (1 := id0).
    congruence.
    eapply eager_eval_global_var. eauto.
    unfold extend. rewrite H0.
    eauto.
    
    
Admitted.

Lemma eager_eval_expr_ident_irrel_parallel :
  forall expr ge ge' TE SE v,
    (eager_eval_expr ge TE SE expr v -> 
    eager_eval_expr ge' TE SE expr v) ->
    forall id exp,
      eager_eval_expr (extend ge id exp) TE SE expr v ->
      eager_eval_expr (extend ge' id exp) TE SE expr v.
Proof.
Admitted.
 *)

(*  intros.
  unfold global_extends in *.
  destruct H. split.
  intros.
  unfold extend.
  remember H3 as Hsome.
  clear HeqHsome.
  eapply H in H3.
  rewrite H3.
  destruct (ident_eq id0 id) eqn:?; auto.
  unfold name_irrel in *.
  specialize (H0 id0 id).
  rewrite Heqs in H0. congruence.

  intros.
  eapply eager_eval_expr_ident_irrel in H1; eauto.
  eapply H2 in H3.
  eapply eager_eval_expr_ident_irrel_parallel.
  eapply H2. eauto.
Qed.
*)
