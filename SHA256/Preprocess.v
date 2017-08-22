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

(* TODO *)
Definition preprocess_spec (msg : ext_val) : ext_val := eseq nil.


Lemma preprocess_eval :
  forall msg len,
    has_type msg (tseq len tbit) ->
    forall GE TE SE,
      wf_env ge GE TE SE ->
      forall ta1 ta2 ta3 ta4 tv1 tv2 tv3 padding emsg,
        eager_eval_type GE TE ta1 tv1 ->
        eager_eval_type GE TE ta2 tv2 ->
        eager_eval_type GE TE ta3 tv3 ->
        eager_eval_type GE TE ta4 (tvnum padding) ->
        eager_eval_expr GE TE SE emsg (to_sval msg) ->
        forall res,
          res = to_sval (preprocess_spec msg) ->
          eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (ETApp (EVar preprocess) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) (ETyp ta4)) emsg) res.
Proof.
  intros.
  gen_global preprocess.
  gen_global (37,"split").
  gen_global (34,"#").
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
  gen_global (9,"True").
  ag.
  e. reflexivity. reflexivity.

  use append_eval; try lv.
  
  
  
Admitted.  


    