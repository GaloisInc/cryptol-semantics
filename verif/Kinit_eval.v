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

(* Require Import Bvector.*)


(* Eager tactics *)
(* TODO: standardize *)
Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac fg := eapply eager_eval_global_var; [ reflexivity | eassumption | idtac].
Ltac g := eapply eager_eval_global_var; try eassumption; try reflexivity.


Ltac e :=
  match goal with
  | [ |- eager_eval_expr ?GE _ ?E (EVar ?id) _ ] =>
    (try fg); (try reflexivity);
    (try solve [eapply eager_eval_local_var; reflexivity]);
    fail 1 "couldn't figure out variable"
  | [ |- _ ] => ec
  end.

Definition typenum (n : Z) : Expr := ETyp (TCon (TC (TCNum n)) []).
Definition pwBytes := typenum 64.
Definition blockLength := typenum 64.
Definition digest := typenum 0.

Ltac find_rw :=
  match goal with
  | [ H : ?X = _ |- ?X = _ ] => rewrite H
  end.



Lemma kinit_eval :
  forall k,
    n_bits 64 k ->
    forall h TE SE GE,
      GE kinit = ge kinit ->
      GE (14, ">") = ge (14,">") ->
      GE (0, "demote") = ge (0, "demote") ->
      GE (61, "take") = ge (61, "take") ->
      GE (35, "splitAt") = ge (35, "splitAt") ->
      GE (29, "zero") = ge (29, "zero") ->
      GE (34, "#") = ge (34, "#") ->
      SE kinit = None ->
      SE (14, ">") = None ->
      SE (34, "#") = None ->
      SE (0, "demote") = None ->
      SE (29, "zero") = None ->
      SE (61, "take") = None ->
      SE (35, "splitAt") = None ->
      (exists hv,
          eager_eval_expr GE TE SE h hv) ->
    exists v,
      eager_eval_expr GE TE SE (apply (tapply (EVar kinit) (pwBytes :: blockLength :: digest ::  nil)) (h :: (EList (map EValue k)) :: nil)) v /\ eager_eval_expr GE TE SE (EList (map EValue k)) v.
Proof.
  init_globals ge.
  intros.
  remember H as Hnb; clear HeqHnb.
  eapply n_bits_eval in H; eauto.
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  end.
  instantiate (3 := GE) in H.
  instantiate (1 := SE) in H.
  instantiate (1 := TE) in H.
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end.
  inversion H. subst.
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  end.
  eexists. split; try eassumption. unfold apply.
  
  e. e.
  e. e. e.
  
  g. find_rw.
  reflexivity.
  e. e. repeat e.
  e. repeat e.
  e. repeat e.
  eassumption.
  e. e. 
  eassumption.
  e. e. e. e. g.
  find_rw. eassumption.
  e. repeat e.
  e. e. e. g.
  find_rw. eassumption.
  e.
  repeat e. repeat e.
  simpl. repeat e.
  simpl. e. repeat e.
  repeat e. repeat e. 
  

  
  e. e. e.
  g.
  repeat e.
  find_rw. eassumption.
  e. repeat e. e. repeat e.
  e. repeat e.
  repeat e. simpl. reflexivity.
  repeat e.
  
  
  e. e. e. e. g.
  find_rw. reflexivity.
  repeat e. repeat e.
  e. repeat e.
  e. repeat e.
  e. e. e. e. e. e. g.
  repeat e.
  find_rw. eassumption.
  e. e. repeat e.
  e. repeat e. e. e. e. e. e.
  e. e.
  g. find_rw. eassumption.
  e. repeat e. e. repeat e. repeat e.
  reflexivity. e. e. repeat e.
  repeat e. repeat e. 

  
  rewrite append_strict_list. reflexivity.  
  
  e. g. e. g.
  e. e. e. e. g.
  
  simpl. unfold extend. simpl.
  find_rw. eassumption.
  e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. e. e. e. e.
  
  replace (tnum 64) with (tnum (Z.of_nat (Datatypes.length x))).
  eapply strict_list_injective in H20. subst.
  rewrite splitAt_len. reflexivity.
  
  f_equal. omega.
  simpl.
  eapply strict_list_injective in H20; eauto.
  congruence.

Qed.

