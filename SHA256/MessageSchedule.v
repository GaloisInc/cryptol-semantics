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
Require Import SHA256.Helpers.

Definition schedule_ev (e : ext_val) : ext_val := eseq nil.

Lemma SHA256MessageSchedule_eval :
  forall GE TE SE,
    wf_env ge GE TE SE ->
    forall a v res,
      eager_eval_expr GE TE SE a (to_sval v) ->
      has_type v (tseq 16 (tseq 32 tbit)) ->
      res = to_sval (schedule_ev v) ->
      eager_eval_expr GE TE SE (EApp (EVar SHA256MessageSchedule) a) res.
Proof.
  intros.
  gen_global SHA256MessageSchedule.
  gen_global (0,"demote").
  gen_global (1,"+").
  gen_global (2,"-").
  gen_global (34,"#").
  gen_global (40,"@").
  gen_global (49,"fromTo").
  inversion H1. subst v t.
  e. ag.
  all: clear H3.
  e. e. g.
  use append_eval.
  lv.
  e.
  ec. ec.




Admitted.

