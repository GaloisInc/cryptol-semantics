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

Require Import HMAC_spec.
Require Import Kinit_eval.

(* Require Import Bvector.*)


(* Eager tactics *)
(* TODO: standardize *)
Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac fg := eapply eager_eval_global_var; [ reflexivity | eassumption | idtac].
Ltac g := eapply eager_eval_global_var; try eassumption; try reflexivity.


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
Definition pwBytes := typenum 64.
Definition blockLength := typenum 64.
Definition digest := typenum 0.
Definition msgBytes := typenum 64.


Definition good_hash (h : Expr) (ge : genv) (T : tenv) (SE : senv) (hf : strictval -> strictval) : Prop :=
  (exists id exp TE E,
      eager_eval_expr ge T SE h (sclose id exp TE E) /\ (* can evaluate the hash to a closure *)
      forall n v,
        sn_bits n v ->
        eager_eval_expr ge TE (extend E id v) exp (hf v) (* can evaluate that closure applied to a value *)
  ).

Lemma Hmac_eval :
  forall k,
    n_bits 64 k ->
    forall h,
      (exists id exp TE E,
          eager_eval_expr ge tempty sempty h (sclose id exp TE E)) ->
      forall m,
        n_bits 64 m ->
        exists v,
          eager_eval_expr ge tempty sempty (apply (tapply (EVar hmac) (msgBytes :: pwBytes :: blockLength :: digest :: nil)) (h :: h :: h :: (EValue k) :: (EValue m) :: nil)) v.
Proof.
  intros. do 4 destruct H0.
  remember H as Hnbk. clear HeqHnbk.
  remember H1 as Hnbm. clear HeqHnbm.
  eapply n_bits_eval with (ge := ge) (E := sempty) (TE := tempty) in H1. destruct H1. destruct H1.
  eapply n_bits_eval with (ge := ge) (E := sempty) (TE := tempty) in H. destruct H. destruct H.

  inversion H1. subst. inversion H. subst.

  init_globals ge.
  eexists.

  unfold apply. unfold tapply. e. e. e. e. e. e. e. e. e.
  g. e. e. e. e. e. eassumption.
  e. eassumption.
  e. eassumption.
  e. e.
  eassumption. e. eassumption.
  e. e. e. e. e. e. e. e. g.
  e. e. e. e. 
  g. e. e. e. g.
  (* TODO: apply kinit theorem here *)
(*  edestruct kinit_eval. Focus 10.
  destruct H4. unfold apply in H4. unfold tapply in H4. apply H4.*)


  e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e. e. g.
  e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. g. e.
  e. e. e. e. e. e. e. g. e. e. e. e.
  e. e. e.
  (* here we evaluate the hash to something *)
  admit.
  e. e. e. e. e. e. e. e.
  (* what we got back from the hash splits *)
  admit.
  e. e. g. e. e. e. e. e. simpl. reflexivity.
  e. e. e. e. e. e. e. e. e. e.

  (* append nil to the end *)
  admit.

  e. g. e. g. e. e. e. e. g. e. e. e. e. e. e. e. e. e. e. e. e. e.

  (* now we can split the thing *)
  admit.

  (* project the tuple *)
  admit.

  (* make a list of it *)
  admit.

  (* evaluate elements of that list *)
  admit.

  e. g. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e.
  e. g. e. e. e. e. g. e. e. e. g.
  e. e. e. e. e. g. e. e. e. e. e. e.
  e. e. e. e. e. g. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. simpl. reflexivity. e. e.
  e. e. g. e. e. e. e. e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. g. e. e. e. e. e.
  e. e.

  (* evaluate the hash to something (again) *)
  admit.

  e. e. e. e. e. e. e. e. 
  
  (* what we got back from the hash splits *)
  admit.
  e. e. g. e. e. e. e. e. simpl. reflexivity.
  e. e. e. e. e. e. e. e. e. e.

  (* append nil to the end *)
  admit.

  e. g. e. g. e. e. e. e. g. e. e. e. e. e. e. e. e. e. e. e. e. e.

  (* now we can split the thing *)
  admit.

  (* project the tuple *)
  admit.

  (* make a list of it *)
  admit.

  (* evaluate elements of that list *)
  admit.
  (* now we can split the thing *)
  admit.

  e. e. e. 

  (* evaluate the hash to something (again) *)
  admit.

  e. e. e. e. e. e. e. e.

  (* split something *)
  admit.

  e. e. e. e. e. e. e. e. e. e.

  (* final append *)
  admit.

  (* evaluate the hash one final time *)
  admit.

  
Admitted.  

  

  (*
Lemma kinit_eval :
  forall k,
    n_bits 64 k ->
    forall h,
      (exists hv,
          eager_eval_expr ge tempty sempty h hv) ->
    exists v,
      eager_eval_expr ge tempty sempty (apply (tapply (EVar kinit) (pwBytes :: blockLength :: digest ::  nil)) (h :: (EList (map EValue k)) :: nil)) v /\ eager_eval_expr ge tempty sempty (EList (map EValue k)) v.
Proof.
  init_globals ge.
  intros.
  remember H as Hnb; clear HeqHnb.
  eapply n_bits_eval in H; eauto.
  destruct H. instantiate (3 := ge) in H.
  instantiate (1 := sempty) in H.
  instantiate (1 := tempty) in H.
  destruct H.
  inversion H. subst.
  destruct H0.
  eexists. split; try eassumption. unfold apply.
  
  e. e.
  e. e. e.
  
  g.
  e. e. repeat e.
  e. repeat e.
  e. repeat e.
  eassumption.
  e. 
  eassumption.
  e. e. e. e. g. e. repeat e.
  e. e. e. g. e.
  repeat e. repeat e.
  simpl. repeat e.
  simpl. e. repeat e.
  repeat e. repeat e. 
  

  
  e. e. e. fg. repeat e.
  e. repeat e. e. repeat e. repeat e.
  repeat e. repeat e.
  simpl.

  e. e. e. e. g.
  repeat e. repeat e.
  e. repeat e.
  e. repeat e.
  e. e. e. e. e. e. g.
  repeat e. e. e. repeat e.
  e. repeat e. e. e. e. e. g.
  repeat e. repeat e.
  repeat e. repeat e.

  rewrite append_strict_list. reflexivity.  
  
  e. g. e. g.
  e. e. e. e. g.
  all: try solve [repeat e].
  e. repeat e. repeat e.


  replace (tnum 64) with (tnum (Z.of_nat (Datatypes.length x))).
  rewrite splitAt_len. reflexivity.
  
  f_equal. omega.
  simpl. reflexivity.

Qed.
*)

  

