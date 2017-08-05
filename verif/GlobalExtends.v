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


Definition global_extends (ge GE : genv) : Prop := True.
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
  forall ge,
    global_extends ge ge.
Proof.
Admitted.
(*
  unfold global_extends.
  split. auto.
  split. auto.
  admit. (* TODO: we'll need to pass this in *)
Admitted.
*)
(*
Lemma global_extends_eager_eval' :
    forall expr TE SE ge GE,
      global_extends ge GE ->
      forall v,
        eager_eval_expr ge TE SE expr v ->
        eager_eval_expr GE TE SE expr v.
Proof.
  intros. unfold global_extends in *.
  destruct H. destruct H1.
  eapply H1; eauto.
Qed.*)

Lemma global_extends_eager_eval :
    forall expr v ge TE SE,
      eager_eval_expr ge TE SE expr v ->
      forall GE,
        global_extends ge GE ->
        eager_eval_expr GE TE SE expr v.
Proof.
Admitted.
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

Lemma global_extends_extend_r :
  forall ge ge',
    global_extends ge ge' ->
    name_irrel ge ->
    forall id exp,
      ge id = None ->
      global_extends ge (extend ge' id exp).
Proof.
Admitted.
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
