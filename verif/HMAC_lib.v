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
Definition good_hash (h : Expr) (ge : genv) (T : tenv) (SE : senv) (hf : ext_val -> ext_val) : Prop :=
  (exists id exp TE E,
      eager_eval_expr ge T SE h (sclose id exp TE E) /\ (* can evaluate the hash to a closure *)
      forall n v,
        has_type v (bytestream n) ->
        eager_eval_expr ge TE (extend E id (to_sval v)) exp (to_sval (hf v)) (* can evaluate that closure applied to a value *)
  ).

Lemma good_hash_eval :
  forall h GE T SE hf,
    good_hash h GE T SE hf ->
    exists id exp TE E,
      eager_eval_expr GE T SE h (sclose id exp TE E).
Proof.
  intros. unfold good_hash in *.
  do 5 destruct H.
  eauto.
Qed.

Lemma good_hash_complete_eval :
  forall h GE T SE hf,
    good_hash h GE T SE hf ->
    exists id exp TE E,
      eager_eval_expr GE T SE h (sclose id exp TE E) /\
      forall n v,
        has_type v (bytestream n) ->
        eager_eval_expr GE TE (extend E id (to_sval v)) exp (to_sval (hf v)).
Proof.
  intros. unfold good_hash in *.
  do 5 destruct H.
  repeat eexists. eauto. eauto.
Qed.

Definition global_extends (ge GE : genv) : Prop :=
  forall id v,
    ge id = Some v ->
    GE id = Some v.

Lemma global_extends_eager_eval :
  forall ge GE,
    global_extends ge GE ->
    forall TE SE expr v,
      eager_eval_expr ge TE SE expr v ->
      eager_eval_expr GE TE SE expr v.
Proof.
Admitted. (* needs crazy induction *)
  

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



Definition typenum (n : Z) : Expr := ETyp (TCon (TC (TCNum n)) []).

Ltac abstract_globals ge :=
  repeat match goal with
         | [ H : ge _ = _ |- _ ] => eapply wf_env_global in H; eauto
         end.
