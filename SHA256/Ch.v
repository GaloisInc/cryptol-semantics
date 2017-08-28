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

Definition Ch_spec (x y z : ext_val) : ext_val :=
  match x,y,z with
  | eseq x, eseq y, eseq z =>
    eseq (xor_ev (and_ev x y) (and_ev (not_ev x) z))
  | _,_,_ => eseq []
  end.

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
