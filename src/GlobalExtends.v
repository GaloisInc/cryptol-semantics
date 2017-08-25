Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.

Require Import Cryptol.AST.
Require Import Cryptol.Semantics.
Require Import Cryptol.Utils.
Require Import Cryptol.Builtins.
Require Import Cryptol.BuiltinSem.
Require Import Cryptol.BuiltinSyntax.
Require Import Cryptol.Values.        
Require Import Cryptol.Eager.
Require Import Cryptol.Bitstream.
Require Import Cryptol.Lib.
Require Import Cryptol.EagerEvalInd.

Definition global_extends (ge ge' : genv) : Prop :=
  forall id v,
    ge id = Some v ->
    ge' id = Some v.


Lemma global_extends_refl :
  forall GE,
    global_extends GE GE.
Proof.
  intros.
  unfold global_extends. auto.
Qed.


Definition name_irrel {A : Type} (E : ident -> option A) : Prop :=
  forall id id',
    if ident_eq id id' then E id = E id' else True.

Lemma global_extends_extend_r :
  forall ge ge',
    global_extends ge ge' ->
    name_irrel ge ->
    forall id exp,
      ge id = None ->
      global_extends ge (extend ge' id exp).
Proof.
  intros.
  unfold global_extends in *.
  intros.
  unfold extend. unfold name_irrel in *.
  specialize (H0 id0 id).
  destruct (ident_eq id0 id).
  congruence. eapply H; eauto.
Qed.

Lemma global_extends_extend_parallel :
  forall ge GE,
    global_extends ge GE ->
    forall id e,
      global_extends (extend ge id e) (extend GE id e).
Proof.
  intros. unfold global_extends in *.
  intros. unfold extend in *.
  destruct (ident_eq id0 id); eauto.
Qed.

Lemma global_extends_declare_parallel :
  forall l ge GE,
    global_extends ge GE ->
    global_extends (declare l ge) (declare l GE).
Proof.
  induction l; intros.
  simpl. assumption.
  simpl. destruct a. destruct d.
  eapply IHl. eapply global_extends_extend_parallel; eauto.
  destruct (lookup_prim id).
  eapply IHl. eapply global_extends_extend_parallel; eauto.
  eapply IHl; eauto.
Qed.

Lemma global_extends_bind_decl_groups :
  forall decls ge GE,
    global_extends ge GE ->
    global_extends (bind_decl_groups decls ge) (bind_decl_groups decls GE).
Proof.
  induction decls; intros.
  simpl. assumption.
  simpl. eapply IHdecls; eauto.
  destruct a; simpl;
    try destruct d; try destruct d; simpl;
      [ idtac | idtac | destruct (lookup_prim id) eqn:? ];
      eauto;
      try solve [eapply global_extends_extend_parallel; eauto].
  eapply global_extends_declare_parallel; eauto.
Qed.


Lemma Forall_not_types :
  forall P l,
    Forall P l ->
    Forall P (not_types l).
Proof.
  induction 1; intros.
  simpl. econstructor.
  destruct x; simpl; try econstructor; eauto.
Qed.

Lemma Forall2_Forall2_eq :
  forall {A B} (P : A -> B -> Prop) (l : list A) (vs : list B),
    Forall2 (fun (x : A) (y : B) => forall b, P x b -> y = b) l vs ->
    forall vs',
      Forall2 P l vs ->
      Forall2 P l vs' ->
      vs = vs'.
Proof.
  induction 1; intros.
  inversion H. inversion H0. auto.
  inversion H1. inversion H2.
  subst. f_equal; eauto.
Qed.

Lemma eager_eval_type_determ :
  forall ge TE t v,
    eager_eval_type ge TE t v ->
    forall v',
      eager_eval_type ge TE t v' ->
      v = v'.
Proof.
  induction 1 using eager_eval_type_ind_useful; intros;
    try solve [match goal with
               | [ H : eager_eval_type _ _ _ _ |- _ ] => inversion H; subst; eauto; try congruence
               end].
  
  * inversion H2. subst. f_equal.
    eapply list_pair_parts_eq. congruence.
    eapply Forall2_Forall2_eq; eauto.
  * inversion H2. subst. f_equal.
    eapply Forall2_Forall2_eq; eauto.
  * subst. inversion H2. subst.
    inversion H3. subst.
    f_equal; eauto.
  * inversion H1. subst.
    f_equal; eauto.
    subst.
    f_equal; eauto.
    inversion H7.
    inversion H9.
  * inversion H1. subst.
    inversion H0. inversion H9.
    f_equal; eauto.
  * inversion H2. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H2. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H2. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H3. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H3. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H2. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H2. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H2. subst.
    assert (tvnum a = tvnum a0) by eauto.
    assert (tvnum b = tvnum b0) by eauto.
    congruence.
  * inversion H0.
    subst.
    assert (tvnum n = tvnum n0) by eauto.
    congruence.
Qed.

Lemma Forall2_eager_eval_type_determ :
  forall ge TE l targs,
    Forall2 (eager_eval_type ge TE) l targs ->
    forall targs',
      Forall2 (eager_eval_type ge TE) l targs' ->
      targs = targs'.
Proof.
  induction 1; intros.
  inversion H. auto.
  inversion H1. subst.
  f_equal.
  eapply eager_eval_type_determ; eauto.
  eapply IHForall2; eauto.
Qed.

Lemma eager_eval_expr_determ :
  forall e ge TE SE v,
    eager_eval_expr ge TE SE e v ->
    forall v',
      eager_eval_expr ge TE SE e v' ->
      v = v'.
Proof.
  remember (fun ge TE SE llm llidv =>
              eager_par_match ge TE SE llm llidv ->
              forall llidv',
                eager_par_match ge TE SE llm llidv' ->
                llidv = llidv') as Ppm.
  remember (fun ge TE SE lm llidv =>
              eager_index_match ge TE SE lm llidv ->
              forall llidv',
                eager_index_match ge TE SE lm llidv' ->
                llidv = llidv') as Pm.
  
  induction 1 using eager_eval_expr_ind_useful with
      (Pm := Pm) (Ppm := Ppm); intros.

  
  * inversion H1;
    subst.
    f_equal.
    eapply Forall2_Forall2_eq; eauto.
  * inversion H1. subst.
    assert (stuple l = stuple l0) by eauto.
    inversion H2.
    congruence.
  * inversion H1. subst.
    f_equal. f_equal.
    eapply Forall2_Forall2_eq; eauto.
  * inversion H1. subst.
    assert (srec l = srec l0) by eauto.
    inversion H2.
    congruence.
  * inversion H0. subst. eauto.
  * inversion H1. subst.
    assert (sbit b = sbit b0) by eauto.
    inversion H2.
    subst. destruct b0. eauto. eauto.
  * inversion H0; try congruence.
  * inversion H2; try congruence.
    subst.
    eapply IHeager_eval_expr; congruence.
  * inversion H. subst.
    reflexivity.
  * inversion H. subst. reflexivity.
  * inversion H2. subst.
    eapply IHeager_eval_expr1 in H5. inversion H5.
    subst. eapply IHeager_eval_expr2 in H8. subst.
    eauto.
  * inversion H2. subst.
    eapply IHeager_eval_expr1 in H5. inversion H5.
    subst.
    assert (t = t0). {
      eapply eager_eval_type_determ; eauto.
    }
    subst.
    eauto. 
  * inversion H0. congruence.
  * inversion H2. subst. f_equal.
    eapply Forall2_Forall2_eq; eauto.
  * inversion H3. subst.
    f_equal.
    specialize (IHeager_eval_expr H).
    eapply IHeager_eval_expr in H6. subst.
    eapply Forall2_Forall2_eq; eauto.
    simpl. eapply H1.
  * inversion H3. subst.
    simpl in H2. congruence.
    assert (targs = targs0) by (eapply Forall2_eager_eval_type_determ; eauto).
    subst targs0.
    assert (args = args0). {
      clear H10. clear H2.
      generalize dependent args0.
      induction H1; intros.
      inversion H7. auto.
      inversion H0. subst.
      inversion H7. subst.
      f_equal; eauto.
    }
    congruence.
  * subst Ppm.
    intros.
    inversion H0; try congruence; subst.
    inversion H1; try congruence; subst.
    eapply IHeager_eval_expr; eauto.
  * subst Ppm.
    intros.
    inversion H2; try congruence. subst.
    inversion H3; try congruence. subst.
    rewrite H6 in *.
    f_equal. eauto. eauto.
  * subst Pm. intros.
    inversion H2; subst; try congruence.
    f_equal. assert (vs = vs0) by eauto.
    congruence.
  * subst Pm. intros.
    inversion H4; subst; try congruence.
    f_equal. f_equal.
    assert (vs = vs0) by eauto. congruence.
    eauto.
Qed.


Lemma eager_eval_type_swap_ge :
  forall ge GE TE te t,
    eager_eval_type ge TE te t ->
    eager_eval_type GE TE te t.
Proof.
  induction 1 using eager_eval_type_ind_useful; intros; econstructor; eauto.
Qed.  

Lemma global_extends_eager_eval :
    forall expr v ge TE SE,
      eager_eval_expr ge TE SE expr v ->
      forall GE,
        global_extends ge GE ->
        eager_eval_expr GE TE SE expr v.
Proof.
  remember (fun ge TE SE llm llidv =>
             eager_par_match ge TE SE llm llidv ->
             forall GE,
               global_extends ge GE ->
               eager_par_match GE TE SE llm llidv) as Ppm.
  remember (fun ge TE SE lm llidv =>
             eager_index_match ge TE SE lm llidv ->
             forall GE,
               global_extends ge GE ->
               eager_index_match GE TE SE lm llidv) as Pm.

  induction 1 using eager_eval_expr_ind_useful with
      (Pm := Pm) (Ppm := Ppm); intros;
    try solve [econstructor; eauto];
    subst Pm Ppm.

  * econstructor.
    induction H0; intros; econstructor; inversion H; eauto.
  * econstructor.
    induction H0; intros; econstructor; inversion H; eauto.
  * econstructor.
    eapply IHeager_eval_expr; eauto.
    eapply global_extends_bind_decl_groups; eauto.
  * econstructor; eauto.
    eapply eager_eval_type_swap_ge; eauto.
  * econstructor; eauto.
    clear H1.
    induction H0; intros.
    econstructor; eauto.
    inversion H. econstructor; eauto.
  * econstructor; eauto.
    clear H2.
    induction H1; intros. econstructor.
    inversion H0. subst.
    econstructor; eauto.
  * 
    econstructor; eauto.
    clear H2.
    induction H; intros; econstructor; eauto.
    eapply eager_eval_type_swap_ge; eauto.
    clear H2. clear H.
    induction H0; intros.
    econstructor.
    inversion H1. subst.
    econstructor; eauto.
    intro. subst bi. simpl in *. congruence.
  * econstructor; eauto.
  * intros. 
    eapply IHeager_eval_expr in H0; try eassumption.
    eapply IHeager_eval_expr0 in H1; try eassumption.
    econstructor; eauto.
  * intros. eapply IHeager_eval_expr in H2.
    econstructor; eauto.
  * intros. econstructor; eauto.
Qed.    

(* lowercase is concrete, uppercase is abstract *)
(* wf_env lets this proof be used over a variety of environments that meet the proper constraints *)
Definition wf_env (ge GE : genv) (TE : tenv) (SE : senv)  : Prop :=
  name_irrel ge /\ name_irrel GE /\ name_irrel TE /\ name_irrel SE /\ (*finite GE /\*)
  (forall id,
      ge id <> None -> (TE id = None /\ SE id = None /\ ge id = GE id)).


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

Lemma wf_env_global' :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      GE id = Some exp.
Proof.
  intros. unfold wf_env in *.
  destruct H. destruct H1.
  destruct H2. destruct H3.
  destruct (H4 id); try congruence.
  intuition.
  congruence.
Qed.

Lemma wf_env_not_local :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      SE id = None.
Proof.
  intros. unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  destruct (H4 id); try congruence.
  intuition.
Qed.

Lemma wf_env_global :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      GE id = Some exp /\ SE id = None.
Proof.
  intros. split.
  eapply wf_env_global'; eauto.
  eapply wf_env_not_local; eauto.
Qed.

Lemma wf_env_not_type :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      TE id = None.
Proof.
  intros. unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  destruct (H4 id); try congruence.
Qed.

Lemma wf_env_name_irrel_GE :
  forall ge GE TE SE ,
    wf_env ge GE TE SE ->
    name_irrel GE.
Proof.
  intros. unfold wf_env in *. intuition.
Qed.

Lemma wf_env_extend_GE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = None ->
      wf_env ge (extend GE id exp) TE SE.
Proof.
  intros.
  unfold wf_env in *.
  intros.
  destruct H.
  destruct H1.
  destruct H2. destruct H3.
  split; auto.
  split; auto.

  eapply name_irrel_extend; eauto.
  
  split; auto.
  split; auto.
  
  
  intros.
  remember H5 as Hcontra.
  clear HeqHcontra.
  eapply H4 in H5.
  intuition.
  rewrite H8.
  edestruct (name_irrel_diff_results _ id0 id H); try congruence.
  unfold extend. erewrite H7.
  reflexivity.
Qed.

Lemma wf_env_extend_TE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = None ->
      wf_env ge GE (extend TE id exp) SE.
Proof.
  intros.
  unfold wf_env in *.
  intros.
  destruct H. destruct H1.
  destruct H2. destruct H3.
  split; auto.
  split; auto.
  split; auto.
  eapply name_irrel_extend; eauto.
  
  split; auto.

  intros.
  
  remember H5 as Hcontra.
  clear HeqHcontra.
  eapply H4 in H5.
  intuition.
  edestruct (name_irrel_diff_results _ id0 id H); try congruence.  

  unfold extend. erewrite H7.
  assumption.
Qed.

Lemma wf_env_extend_SE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = None ->
      wf_env ge GE TE (extend SE id exp).
Proof.
  intros.
  unfold wf_env in *.
  intros.
  destruct H. destruct H1.
  destruct H2. destruct H3.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  eapply name_irrel_extend; eauto.

  intros.

  remember H5 as Hcontra.
  clear HeqHcontra.
  eapply H4 in H5.
  intuition.
  edestruct (name_irrel_diff_results _ id0 id H); try congruence.  

  unfold extend. erewrite H7.
  assumption.
Qed.

Lemma wf_env_erase_SE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id,
      wf_env ge GE TE (fun x => if ident_eq x id then None else SE x).
Proof.
  intros. unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  eapply name_irrel_erase; eauto.

  intros. remember H4 as Hcontra.
  clear HeqHcontra.
  eapply H3 in H4.
  split; intuition.
  
  rewrite H4.

  destruct (ident_eq id0 id); auto.

Qed.
