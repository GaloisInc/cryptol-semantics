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

Lemma map_fst_combine :
  forall {A B : Type} (l : list A) (l' : list B),
    length l = length l' ->
    map fst (combine l l') = l.
Proof.
  induction l; intros; destruct l'; simpl in *; try congruence.
  f_equal. eauto.
Qed.

Lemma map_snd_combine :
  forall {A B : Type} (l : list A) (l' : list B),
    length l = length l' ->
    map snd (combine l l') = l'.
Proof.
  induction l; intros; destruct l'; simpl in *; try congruence.
  f_equal. eauto.
Qed.

Lemma Forall2_length :
  forall {A B} (P : A -> B -> Prop) l l',
    Forall2 P l l' ->
    length l = length l'.
Proof.
  induction 1; intros; simpl; eauto.
Qed.

Lemma lookup_Forall2_back :
  forall {A B : Type} (X : list A) (Y : list B) (P : A -> B -> Prop),
    Forall2 P X Y ->
    forall str strs v',
      lookup str (combine strs Y) = Some v' ->
      exists v,
        lookup str (combine strs X) = Some v /\ P v v'.
Proof.
  induction 1; intros;
    destruct strs; try solve [simpl in *; congruence].
  simpl in H1.
  destruct (String.string_dec str s) eqn:?.
  inversion H1. subst. eexists. simpl.
  rewrite Heqs0. eauto.
  simpl. rewrite Heqs0.
  eapply IHForall2 in H1; eauto.
Qed.

Lemma combine_map_fst_map_snd :
  forall {A B : Type} (l : list (A * B)),
    combine (map fst l) (map snd l) = l.
Proof.
  induction l; intros; simpl; eauto.
  destruct a; simpl; f_equal; eauto.
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
  * assert (Forall2 (strict_eval_expr ge TE E0) (map snd l) vs).
    eapply Forall2_implies_1. eapply H0. simpl. eauto.
    eapply Forall2_strict_eval_inv in H2.
    destruct H2.
    destruct H2.
    econstructor. econstructor; eauto.
    econstructor.
    rewrite map_snd_combine. eauto.
    rewrite map_length.
    eapply Forall2_length in H2.
    rewrite map_length in *.
    eassumption.
    
    rewrite map_fst_combine. eauto.
    rewrite map_length.
    eapply Forall2_length in H2.
    rewrite map_length in *.
    eassumption.

  * eapply IHeager_eval_expr in H1. inversion H1.
    subst. inversion H3. subst.

    eapply lookup_Forall2_back in H0; eauto.
    
    destruct H0. destruct H0.
    rewrite combine_map_fst_map_snd in H0.
    
    econstructor. econstructor; eauto.
    assumption.

  * assert (match_env (bind_decl_groups decls ge) (erase_decl_groups decls E0) (erase_decl_groups decls E)).
    admit.
    (* This case could be our downfall *)
    eapply IHeager_eval_expr in H1.
    inversion H1.
    subst.
    econstructor. econstructor; eauto.
    (* Here we run into the unfortunate reality that Where uses the global environment *)
    (* making the ge not static *)
    admit.

  * specialize (IHeager_eval_expr1 _ H1).
    specialize (IHeager_eval_expr2 _ H1).
    inversion IHeager_eval_expr1.
    inversion IHeager_eval_expr2.
    inversion H3.
    subst.
    
    econstructor; eauto. econstructor; eauto.
  * unfold match_env in *.
    specialize (H0 id). rewrite H in H0. inversion H0. 
    econstructor.
    econstructor; eauto.
    eauto.
  * specialize (IHeager_eval_expr _ H2). inversion IHeager_eval_expr. subst.
    unfold match_env in *.
    specialize (H2 id). rewrite H in H2. inversion H2.
    
    econstructor.
    eapply eval_global_var; eauto.
    eauto.

  * econstructor. econstructor; eauto. econstructor; eauto.
  * econstructor. econstructor; eauto. econstructor; eauto.
  * specialize (IHeager_eval_expr1 _ H2).
    specialize (IHeager_eval_expr2 _ H2).
    inversion IHeager_eval_expr1.
    inversion IHeager_eval_expr2.
    subst.
    inversion H4. subst.
    assert (match_env ge (extend E1 id v1) (extend E' id av)) by admit.
    specialize (IHeager_eval_expr3 _ H5).
    inversion IHeager_eval_expr3.
    econstructor. econstructor; eauto.
    eauto.
  * specialize (IHeager_eval_expr1 _ H2).
    inversion IHeager_eval_expr1. subst.
    inversion H4. subst.
    assert (match_env ge E1 E') by admit.
    specialize (IHeager_eval_expr2 _ H5).
    inversion IHeager_eval_expr2.
    subst.

    econstructor; eauto.
    econstructor; eauto.
    eapply eager_to_strict_lazy_type; eauto.

  * 
  
Admitted.

