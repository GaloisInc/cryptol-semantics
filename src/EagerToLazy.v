Require Import Semantics.
Require Import Eager.
Require Import EagerEvalInd.
Require Import List.
Require Import AST.
Require Import Lib.

(* The two different eval_type relations should be merged *)
Lemma eager_to_strict_lazy_type :
  forall t tv ge TE,
    eager_eval_type ge TE t tv ->
    eval_type ge TE t tv.
Proof.
  induction 1 using eager_eval_type_ind_useful; intros;
    econstructor; eauto.
Qed.

Lemma Forall2_strict_eval_inv :
  forall ge TE E l vs,
    Forall2 (strict_eval_expr ge TE E) l vs ->
    exists lv,
      Forall2 (eval_expr ge TE E) l lv /\
      Forall2 (strict_eval_val ge) lv vs.
Proof.
  induction 1; intros.
  exists nil. split; eauto.
  destruct IHForall2. inversion H.
  destruct H1. subst.
  eexists; split; econstructor; eauto.
Qed.

Lemma nth_error_Forall2 :
  forall {A B : Type} l R l',
    Forall2 R l' l ->
    forall n (v : A),          
      nth_error l n = Some v ->
      exists (v' : B),
        nth_error l' n = Some v' /\ R v' v.
Proof.
  induction 1; intros.
  destruct n; simpl in H; congruence.
  destruct n; simpl in H1. inversion H1. subst.
  exists x. split; eauto.
  eapply IHForall2 in H1.
  destruct H1. exists x0.
  destruct H1.
  split; simpl; auto.
Qed.      

Lemma eager_to_strict_lazy :
  forall exp ge TE SE sv,
    eager_eval_expr ge TE SE exp sv ->
    forall E,
      match_env ge E SE ->
      strict_eval_expr ge TE E exp sv.
Proof.
  (* TODO *)
  remember (fun ge TE SE llm llidv =>
              eager_par_match ge TE SE llm llidv ->
              forall E,
                match_env ge E SE ->
                True) as Ppm.
  (* TODO *)
  remember (fun ge TE SE lm llidv =>
              eager_index_match ge TE SE lm llidv ->
              forall E,
                match_env ge E SE ->
                True) as Pm.
  
  induction 1 using eager_eval_expr_ind_useful with (Pm := Pm) (Ppm := Ppm); intros.

  * assert (Forall2 (strict_eval_expr ge TE E0) l vs). {
      eapply Forall2_implies_1. eapply H0. simpl. eauto.
    } idtac.
    eapply Forall2_strict_eval_inv in H2. destruct H2.
    destruct H2.
    econstructor; econstructor; eauto.

  * eapply IHeager_eval_expr in H1.
    inversion H1. subst.
    inversion H3. subst.
    eapply nth_error_Forall2 in H0; eauto. destruct H0.
    destruct H0.
    
    econstructor; [econstructor | eassumption]; eassumption.
  * 
  
  
  
Admitted.

