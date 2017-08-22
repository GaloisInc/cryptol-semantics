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
Require Import Bitstream.
Require Import GlobalExtends.

Require Import EvalTac.
Require Import Eager.
Require Import Lib.

Import HaskellListNotations.

Require Import HMAC.

Require Import HMAC_spec.

Require Import HMAC_lib.
Require Import Prims.

Require Import List.
Import ListNotations.


Lemma kinit_eval :
  forall GE TE SE,
    wf_env ge GE TE SE ->
    forall (key : ext_val) keylen,
      has_type key (bytestream keylen) ->
      forall h hf,
        good_hash h GE TE SE hf ->
        forall digest t1 t2 t3 kexpr,
          eager_eval_type GE TE t1 (tvnum (Z.of_nat keylen)) ->
          eager_eval_type GE TE t2 (tvnum (Z.of_nat keylen)) ->
          eager_eval_type GE TE t3 (tvnum digest) ->
          eager_eval_expr GE TE SE kexpr (to_sval key) ->
          eager_eval_expr GE TE SE (apply (tapply (EVar kinit) (ETyp t1 :: ETyp t2 :: ETyp t3 ::  nil)) (h :: kexpr :: nil)) (to_sval key).
Proof.
  intros.
  eapply good_hash_eval in H1. do 4 destruct H1.

  
  unfold bytestream in H0. inversion H0. subst.
  gen_global (0,"demote").
  gen_global (14,">").
  gen_global (61,"take").
  gen_global (34,"#").
  gen_global (29,"zero").
  gen_global (35,"splitAt").
  
  e. e. e. e. e.
  gen_global kinit.
  ag.
  e. e. e. e. 
  e. 
  e. e. e. e.

  ag. 
  
  e. e. e. e.
  ag.

  e. e. e.

  reflexivity. e. e. e.

  ag.

  e. e. e.
  reflexivity.
  e. lv. lv.
  simpl. unfold strictnum.

  rewrite gt_not_refl; reflexivity.
  simpl.

  
  use take_eval.
  use append_eval.

  instantiate (1 := l). simpl. lv.

  e. 
  ag.

  e. e. 

  simpl.
  f_equal. instantiate (1 := (repeat (eseq (repeat (ebit false) 8)) (length l))).
  simpl.
  f_equal.
  rewrite map_repeat. simpl.
  rewrite Nat2Z.id.
  reflexivity.
  reflexivity.
  rewrite app_length.
  rewrite Nat2Z.inj_add. omega.

  unfold take_model.
  rewrite Nat2Z.id.

  simpl. f_equal.
  rewrite firstn_app.
  rewrite firstn_all.
  replace (Datatypes.length l - Datatypes.length l)%nat with O by omega.
  rewrite firstn_O. rewrite app_nil_r.
  reflexivity.
Qed.

