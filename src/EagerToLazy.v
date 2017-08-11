Require Import Semantics.
Require Import Eager.
Require Import EagerEvalInd.
Require Import List.
Require Import AST.
Require Import Lib.

(* not sure why there are 2 versions of eval_type *)
Lemma eager_to_strict_lazy_type :
  forall t tv ge TE,
    eager_eval_type ge TE t tv ->
    eval_type ge TE t tv.
Proof.
  induction 1 using eager_eval_type_ind_useful; intros;
    econstructor; eauto.
Qed.

Lemma eager_to_strict_lazy :
  forall exp ge TE SE sv,
    eager_eval_expr ge TE SE exp sv ->
    forall E,
      match_env ge E SE ->
      strict_eval_expr ge TE E exp sv.
Proof.
  (* In order to do this, we need to reconstruct par_match to be closer to eager_par_match *)
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

  econstructor.
  econstructor; eauto.
  eapply Forall2_implies_1; eauto.
  Focus 2.
  instantiate (1 := fun x => match_env ge x E). simpl. auto.
  simpl.
  
  
Admitted.

