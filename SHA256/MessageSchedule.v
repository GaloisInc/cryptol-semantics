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

Definition schedule_ev (fuel : nat) (e : ext_val) : ext_val := eseq nil.



(* This one is fun, since it has a recursive list comprehension in it *)
Lemma SHA256MessageSchedule_eval :
  forall n GE TE SE,
    wf_env ge GE TE SE ->
    forall a v res,
      eager_eval_expr GE TE SE a (to_sval v) ->
      has_type v (tseq 16 (tseq 32 tbit)) ->
      res = to_sval (schedule_ev n v) ->
      eager_eval_expr GE TE SE (EApp (EVar SHA256MessageSchedule) a) res.
Proof.
  induction n; intros.
  gen_global SHA256MessageSchedule.
  gen_global (0,"demote").
  gen_global (1,"+").
  gen_global (2,"-").
  gen_global (34,"#").
  gen_global (40,"@").
  gen_global (49,"fromTo").
(*  inversion H1. subst v t.
  remember (zrange 16 64) as rng.
  remember rng as rng2. rewrite Heqrng2 in Heqrng.
  rewrite Heqrng in Heqrng2.
  assert (rng = rng2) by congruence.
  repeat (rewrite zrange_eq in Heqrng;
          match goal with
          | [ H : context[Z_lt_dec ?X ?Y] |- _ ] => destruct (Z_lt_dec X Y) eqn:?; try omega; [idtac]
          end).
  clear -GE TE SE H a res l rng Heqrng H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H12 H10 H11 Heqrng2.
  simpl in Heqrng.
  e. ag.
  all: clear H3.
  e. e. g.*)



  
  
Admitted.

