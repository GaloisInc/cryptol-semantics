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

Definition preprocess_spec (padding msglen : Z) (msg : ext_val) : ext_val :=
  match msg with
  | eseq l => 
    (split_ev (Z.to_nat 512)
            (eseq
               (l ++
                  [ebit true] ++
                  repeat (ebit false) (Z.to_nat padding) ++
                  @ExtToBitvector.from_bitv (Z.to_nat 64) (repr msglen))))
  | _ => eseq nil
  end.

Lemma from_bitv_ext_type :
  forall y x (bv : BitV x),
    Forall (fun x => has_type x tbit) (ExtToBitvector.from_bitv' x y bv).
Proof.
  induction y; intros.
  simpl.
  econstructor.
  simpl.
  econstructor.
  econstructor.
  eauto.
Qed.

Lemma strictval_from_bitv_ext :
  forall y x (bv : BitV x),
    strictval_from_bitv' x y bv = map to_sval (ExtToBitvector.from_bitv' x y bv).
Proof.
  induction y; intros;
    simpl. reflexivity.
  f_equal.
  eauto.
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

  instantiate (1 := ExtToBitvector.from_bitv (repr msglen)).
  unfold strictval_from_bitv.
  unfold ExtToBitvector.from_bitv.
  instantiate (1 := Z.to_nat 64).

  eapply strictval_from_bitv_ext.

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


  eapply from_bitv_ext_type; eauto.

  subst res.
  unfold ExtToBitvector.from_bitv.
  reflexivity.
  
Qed.


    