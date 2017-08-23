Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.

Require Import Cryptol.AST.
Require Import Cryptol.Semantics.
Require Import Cryptol.Utils.
Require Import Cryptol.Builtins.
Require Import Cryptol.BuiltinSem.
Require Import Cryptol.BuiltinSyntax.
Require Import Cryptol.Values.        
Require Import Cryptol.Bitstream.
Require Import Cryptol.Lib.
Require Import Cryptol.GlobalExtends.
Require Import Cryptol.GetEachN.

Require Import Cryptol.EvalTac.
Require Import Cryptol.Eager.

Require Import Cryptol.Prims.
Require Import SHA256.SHA256.

Definition Ch_spec (x y z : ext_val) : ext_val :=
  match x,y,z with
  | eseq x, eseq y, eseq z =>
    eseq (xor_ev (and_ev x y) (and_ev (not_ev x) z))
  | _,_,_ => eseq []
  end.

Definition w32 := tseq 32 tbit.

Lemma Ch_eval :
  forall x y z,
    has_type x w32 ->
    has_type y w32 ->
    has_type z w32 ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ex ey ez res,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        eager_eval_expr GE TE SE ey (to_sval y) ->
        eager_eval_expr GE TE SE ez (to_sval z) ->
        res = (to_sval (Ch_spec x y z)) ->
        eager_eval_expr GE TE SE (EApp (EApp (EApp (EVar Ch) ex) ey) ez) res.
Proof.
  intros. subst res.
  gen_global Ch.
  gen_global (28,"^").
  gen_global (26,"&&").
  gen_global (12,"complement").
  e. e. e. ag.
  e. e. e.
  unfold w32 in *.
  inversion H. inversion H0. inversion H1. subst.
  use xor_eval.
  use and_eval; try lv; try reflexivity.
  eassumption.
  eassumption.
  use and_eval.
  use complement_eval; try lv; try reflexivity.
  eassumption.
  lv. reflexivity.
  eapply has_type_not; eauto.
  eassumption.
  reflexivity.

  eapply has_type_and; eauto.
  eapply has_type_and; try eapply has_type_not; eauto.
  
Qed.

Definition Maj_spec (x y z : ext_val) : ext_val :=
  match x,y,z with
  | eseq x, eseq y, eseq z =>
    eseq (xor_ev (xor_ev (and_ev x y) (and_ev x z)) (and_ev y z))
  | _,_,_ => eseq nil
  end.

Lemma Maj_eval :
  forall x y z,
    has_type x w32 ->
    has_type y w32 ->
    has_type z w32 ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ex ey ez res,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        eager_eval_expr GE TE SE ey (to_sval y) ->
        eager_eval_expr GE TE SE ez (to_sval z) ->
        res = (to_sval (Maj_spec x y z)) ->
        eager_eval_expr GE TE SE (EApp (EApp (EApp (EVar Maj) ex) ey) ez) res.
Proof.
  intros. subst res.
  gen_global Maj.
  gen_global (28,"^").
  gen_global (26,"&&").
  e. e. e. ag.
  e. e. e.
  unfold w32 in *.
  inversion H. inversion H0. inversion H1. subst.
  use xor_eval. use xor_eval.
  use and_eval; try lv; try reflexivity; try eassumption.
  use and_eval; try lv; try reflexivity; try eassumption.
  reflexivity. eapply has_type_and; eauto.
  eapply has_type_and; eauto.
  use and_eval; try lv; try reflexivity; try eassumption.
  simpl. reflexivity.
  eapply has_type_xor.
  eapply has_type_and. eassumption.
  eassumption.
  eapply has_type_and; eassumption.
  eapply has_type_and; eassumption.
Qed.



Definition S0_spec (x : ext_val) : ext_val :=
  match x with
  | eseq x => eseq (xor_ev (xor_ev (rotr_ev x 2) (rotr_ev x 13)) (rotr_ev x 22))
  | _ => eseq nil
  end.

Lemma S0_eval :
  forall x,
    has_type x w32 ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ex res,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        res = (to_sval (S0_spec x)) ->
        eager_eval_expr GE TE SE (EApp (EVar S0) ex) res.
Proof.
  intros.
  gen_global (33,">>>").
  gen_global (28,"^").
  gen_global S0.
  gen_global (0,"demote").
  inversion H. subst.
  e. ag.
  e. use xor_eval.
  use xor_eval.
  use rotr_eval.
  lv.

  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: nil).
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := S (S O)).
  simpl. reflexivity. reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  use rotr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit true) :: (ebit false) :: (ebit true) :: nil).
  reflexivity.
  instantiate (2 := 4%nat). reflexivity.
  reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.


  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.

  use rotr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: (ebit true) :: (ebit true) :: (ebit false) :: nil).
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 5%nat).
  reflexivity.
  reflexivity.
  eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.
  eapply has_type_xor.
  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.
Qed.  


Definition S1_spec (x : ext_val) : ext_val :=
  match x with
  | eseq x => eseq (xor_ev (xor_ev (rotr_ev x 6) (rotr_ev x 11)) (rotr_ev x 25))
  | _ => eseq nil
  end.

Lemma S1_eval :
  forall x,
    has_type x w32 ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ex res,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        res = (to_sval (S1_spec x)) ->
        eager_eval_expr GE TE SE (EApp (EVar S1) ex) res.
Proof.
  intros.
  gen_global (33,">>>").
  gen_global (28,"^").
  gen_global S1.
  gen_global (0,"demote").
  inversion H. subst.
  e. ag.
  e. use xor_eval.
  use xor_eval.
  use rotr_eval.
  lv.

  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit true) :: (ebit false) :: nil).
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 3%nat).
  simpl. reflexivity. reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  use rotr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: (ebit true) :: (ebit true) :: nil).
  reflexivity.
  instantiate (2 := 4%nat). reflexivity.
  reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.

  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.

  use rotr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit true) :: (ebit false) :: (ebit false) :: (ebit true) :: nil).
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 5%nat).
  reflexivity.
  reflexivity.
  eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.
  eapply has_type_xor.
  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.
Qed.

Definition s0_spec (x : ext_val) : ext_val :=
  match x with
  | eseq x => eseq (xor_ev (xor_ev (rotr_ev x 7) (rotr_ev x 18)) (shiftr_ev x 3))
  | _ => eseq nil
  end.

Lemma s0_eval :
  forall x,
    has_type x w32 ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ex res,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        res = (to_sval (s0_spec x)) ->
        eager_eval_expr GE TE SE (EApp (EVar s0) ex) res.
Proof.
  intros.
  gen_global (33,">>>").
  gen_global (31,">>").
  gen_global (28,"^").
  gen_global s0.
  gen_global (0,"demote").
  inversion H. subst.
  e. ag.
  e. use xor_eval.
  use xor_eval.
  use rotr_eval.
  lv.

  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit true) :: (ebit true) :: nil).
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 3%nat).
  simpl. reflexivity. reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  use rotr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: (ebit false) :: (ebit true) :: (ebit false) :: nil).
  reflexivity.
  instantiate (2 := 5%nat). reflexivity.
  reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.

  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.

  use shiftr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit true) :: nil). 
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 2%nat).
  reflexivity.
  reflexivity.
  eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.
  eapply has_type_xor.
  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.
  eapply has_type_shiftr. eassumption.
Qed.


Definition s1_spec (x : ext_val) : ext_val :=
  match x with
  | eseq x => eseq (xor_ev (xor_ev (rotr_ev x 17) (rotr_ev x 19)) (shiftr_ev x 10))
  | _ => eseq nil
  end.

Lemma s1_eval :
  forall x,
    has_type x w32 ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ex res,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        res = (to_sval (s1_spec x)) ->
        eager_eval_expr GE TE SE (EApp (EVar s1) ex) res.
Proof.
  intros.
  gen_global (33,">>>").
  gen_global (31,">>").
  gen_global (28,"^").
  gen_global s1.
  gen_global (0,"demote").
  inversion H. subst.
  e. ag.
  e. use xor_eval.
  use xor_eval.
  use rotr_eval.
  lv.

  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: (ebit false) :: (ebit false) :: (ebit true) :: nil).
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 5%nat).
  simpl. reflexivity. reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  use rotr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: (ebit false) :: (ebit true) :: (ebit true) :: nil).
  reflexivity.
  instantiate (2 := 5%nat). reflexivity.
  reflexivity. eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.

  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.

  use shiftr_eval; try lv.
  use demote_eval.
  simpl. f_equal.
  unfold strictnum. f_equal.
  unfold strictval_from_bitv.
  instantiate (1 := (ebit true) :: (ebit false) :: (ebit true) :: (ebit false) :: nil). 
  reflexivity.
  unfold ExtToBitvector.to_bitv. simpl.
  instantiate (2 := 4%nat).
  reflexivity.
  reflexivity.
  eassumption.
  solve [repeat econstructor; eauto].
  reflexivity.
  eapply has_type_xor.
  eapply has_type_rotr. eassumption.
  eapply has_type_rotr. eassumption.
  eapply has_type_shiftr. eassumption.
Qed.



