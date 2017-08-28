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
Require Import Cryptol.SimpleValues.        
Require Import Cryptol.Bitstream.
Require Import Cryptol.Lib.
Require Import Cryptol.GlobalExtends.
Require Import Cryptol.GetEachN.

Require Import Cryptol.EvalTac.
Require Import Cryptol.Eager.

Require Import Cryptol.Prims.
Require Import SHA256.SHA256.

Definition preprocess_spec (padding msglen : Z) (msg : ext_val) : ext_val :=
  match msg with
  | eseq l => 
    (split_ev (Z.to_nat 512)
            (eseq
               (l ++
                  [ebit true] ++
                  repeat (ebit false) (Z.to_nat padding) ++
                  from_bitlist ext_val ebit (Z.to_nat 64) msglen)))
  | _ => eseq nil
  end.

Lemma strict_ext_from_bitlist :
  forall T1 T2 b1 b2 f width v,
    (forall b, f (b1 b) = b2 b) ->
    SimpleValues.from_bitlist T2 b2 width v = map f (SimpleValues.from_bitlist T1 b1 width v).
Proof.
  induction width; intros; simpl; auto.
  rewrite H. f_equal. eauto.
Qed.
  
Lemma from_bitlist_ext_type :
  forall width v,
    Forall (fun x => has_type x tbit) (from_bitlist ext_val ebit width v).
Proof.
  induction width; intros; repeat econstructor; eauto.
Qed.

Lemma preprocess_eval :
  forall msg len,
    has_type msg (tseq len tbit) ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ta1 ta2 ta3 ta4 msglen contentlen chunks padding emsg,
        eager_eval_type GE TE ta1 (tvnum msglen) ->
        eager_eval_type GE TE ta2 (tvnum contentlen) ->
        eager_eval_type GE TE ta3 (tvnum chunks) ->
        eager_eval_type GE TE ta4 (tvnum padding) ->
        eager_eval_expr GE TE SE emsg (to_sval msg) ->
        forall res,
          res = to_sval (preprocess_spec padding msglen msg) ->
          eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (ETApp (EVar preprocess) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) (ETyp ta4)) emsg) res.
Proof.
  intros.
  gen_global preprocess.
  gen_global (37,"split").
  gen_global (34,"#").
  gen_global (29,"zero").
  gen_global (0,"demote").
  gen_global (9,"True").
  inversion H. subst len msg t.
  e. e. e. e. e. ag.
  e. e. e. e. 
  all: clear H7.

  e.
  use split_eval.

  use append_eval; try lv.
  use append_eval; try lv.
  simpl.
  instantiate (1 := (ebit true) :: nil).
  simpl. e.
  ag.
  e. reflexivity. reflexivity.

  use append_eval; try lv.
  use zero_eval; try lv.

  simpl. reflexivity.
  use demote_eval; try lv.
  simpl. unfold strictnum.
  f_equal. f_equal.

  erewrite strict_ext_from_bitlist.

  reflexivity. instantiate (1 := ebit). intros. reflexivity.
  reflexivity. 
  reflexivity.
  reflexivity.
  econstructor.
  eapply Forall_app; split.
  inversion H. eauto.
  eapply Forall_app; split.
  repeat econstructor.
  eapply Forall_app; split.
  eapply repeat_Forall. econstructor.


  eapply from_bitlist_ext_type; eauto.

  subst res.
  reflexivity.
  
Qed.


    