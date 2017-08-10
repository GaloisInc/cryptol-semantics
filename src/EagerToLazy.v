Require Import Semantics.
Require Import Eager.
Require Import EagerEvalInd.

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
  (*  induction 1 using eager_eval_expr_ind_useful; intros.*)
Admitted.

