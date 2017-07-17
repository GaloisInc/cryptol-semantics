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




