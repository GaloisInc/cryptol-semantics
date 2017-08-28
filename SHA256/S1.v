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

Definition w32 := tseq 32 tbit.

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
