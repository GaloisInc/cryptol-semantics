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
Require Import EagerEvalInd.

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
    assert (t = t0) by admit. subst. (* determinacy of eager_eval_type *)
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
    admit. (* enough here to prove, get_types/not_types, need determinacy of eval_type *)
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
    
Admitted.

(* TODO: change EValue to use ext_vals *)

Lemma eager_eval_type_swap_ge :
  forall ge GE TE te t,
    eager_eval_type ge TE te t ->
    eager_eval_type GE TE te t.
Proof.
  induction 1; intros; econstructor; eauto.
Admitted. (* needs special induction scheme for eager_eval_type *)


Lemma Forall2_modus_ponens :
  forall {A B : Type} (P Q : A -> B -> Prop) (l : list A) (l' : list B),
    Forall2 P l l' ->
    Forall2 (fun x y => P x y -> Q x y) l l' ->
    Forall2 Q l l'.
Proof.
  induction 1; intros. econstructor; eauto.
  inversion H1. subst.
  econstructor; eauto.
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
  * econstructor; eauto.
    clear H2.
    induction H; intros; econstructor; eauto.
    eapply eager_eval_type_swap_ge; eauto.
    clear H2. clear H.
    induction H0; intros.
    econstructor.
    inversion H1. subst.
    econstructor; eauto.
    
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

