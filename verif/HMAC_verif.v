Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.

Require Import AST.
(*Require Import Semantics.*)
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
  | [ |- eager_eval_expr _ ?E (EVar ?id) _ ] =>
    try fg; try reflexivity;
    try solve [eapply eager_eval_local_var; reflexivity]
  | [ |- _ ] => ec
  end.

Definition typenum (n : Z) : Expr := ETyp (TCon (TC (TCNum n)) []).
Definition pwBytes := typenum 64.
Definition blockLength := typenum 64.
Definition digest := typenum 0.

Fixpoint apply (e : Expr) (l : list Expr) : Expr :=
  match l with
  | nil => e
  | f :: r => apply (EApp e f) r
  end.

Fixpoint tapply (e : Expr) (l : list Expr) : Expr :=
  match l with
  | nil => e
  | f :: r => tapply (ETApp e f) r
  end.


Lemma kinit_eval :
  forall k,
    n_bits 64 k ->
    forall h,
    exists v,
      eager_eval_expr ge sempty (apply (tapply (EVar kinit) (pwBytes :: blockLength :: digest ::  nil)) (h :: (EList (map EValue k)) :: nil)) v.
Proof.
  init_globals ge.
  intros.
  remember H as Hnb; clear HeqHnb.
  eapply n_bits_eval in H; eauto.
  destruct H. instantiate (1 := ge) in H.
  
  eexists. unfold apply.
  e. e.
  e. e. e. g. e. repeat e.
  e. repeat e.
  e. repeat e.
  e.
  admit. (* hash evaluates to some closure *)
  e. 
  eassumption.
  e. e. e. e. g. e. repeat e.
  e. e. e. e. repeat e. repeat e.
  simpl. repeat e. repeat e. repeat e.
  
  e. e. e. e. e. repeat e.
  e. repeat e. e. repeat e. simpl. reflexivity.
  e. repeat e.
  simpl. reflexivity.
  simpl. e.
  e. e. e. g. e. repeat e.
  e. repeat e.
  e. repeat e. e. e. e. repeat e.
  e. e. e. g. e. repeat e. repeat e.
  e. repeat e.


  (* TODO: Prove that append works for x *)
  (* TODO: add eager evaluation of where *)
  
  
Admitted.