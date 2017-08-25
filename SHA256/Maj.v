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
