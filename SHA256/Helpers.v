Require Import List.
Import ListNotations.

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
Require Import Lib.
Require Import GlobalExtends.
Require Import GetEachN.

Require Import EvalTac.
Require Import Eager.

Require Import Prims.
Require Import SHA256.

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
      forall ex ey ez,
        eager_eval_expr GE TE SE ex (to_sval x) ->
        eager_eval_expr GE TE SE ey (to_sval y) ->
        eager_eval_expr GE TE SE ez (to_sval z) ->
        eager_eval_expr GE TE SE (EApp (EApp (EApp (EVar Ch) ex) ey) ez) (to_sval (Ch_spec x y z)).
Proof.
  intros.
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
