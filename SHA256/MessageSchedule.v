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

Import HaskellListNotations.
Definition W_expr : Expr := (EApp
             (EApp
              (ETApp
               (ETApp
                (ETApp
                 (EVar (34,"#"))
                 (ETyp (TCon (TC (TCNum 16)) [])))
                (ETyp (TCon (TC (TCNum 48)) [])))
               (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
              (EVar (272,"M")))
             (EComp
              (EApp
               (EApp
                (ETApp
                 (EVar (1,"+"))
                 (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                (EApp
                 (EApp
                  (ETApp
                   (EVar (1,"+"))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                  (EApp
                   (EApp
                    (ETApp
                     (EVar (1,"+"))
                     (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                    (EApp
                     (EVar (247,"s1"))
                     (EApp
                      (EApp
                       (ETApp
                        (ETApp
                         (ETApp
                          (EVar (40,"@"))
                          (ETyp (TCon (TC (TCNum 64)) [])))
                         (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                        (ETyp (TCon (TC (TCNum 8)) [])))
                       (EVar (273,"W")))
                      (EApp
                       (EApp
                        (ETApp
                         (EVar (2,"-"))
                         (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                        (EVar (274,"j")))
                       (ETApp
                        (ETApp
                         (EVar (0,"demote"))
                         (ETyp (TCon (TC (TCNum 2)) [])))
                        (ETyp (TCon (TC (TCNum 8)) [])))))))
                   (EApp
                    (EApp
                     (ETApp
                      (ETApp
                       (ETApp
                        (EVar (40,"@"))
                        (ETyp (TCon (TC (TCNum 64)) [])))
                       (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                      (ETyp (TCon (TC (TCNum 8)) [])))
                     (EVar (273,"W")))
                    (EApp
                     (EApp
                      (ETApp
                       (EVar (2,"-"))
                       (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                      (EVar (274,"j")))
                     (ETApp
                      (ETApp
                       (EVar (0,"demote"))
                       (ETyp (TCon (TC (TCNum 7)) [])))
                      (ETyp (TCon (TC (TCNum 8)) [])))))))
                 (EApp
                  (EVar (246,"s0"))
                  (EApp
                   (EApp
                    (ETApp
                     (ETApp
                      (ETApp
                       (EVar (40,"@"))
                       (ETyp (TCon (TC (TCNum 64)) [])))
                      (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                     (ETyp (TCon (TC (TCNum 8)) [])))
                    (EVar (273,"W")))
                   (EApp
                    (EApp
                     (ETApp
                      (EVar (2,"-"))
                      (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                     (EVar (274,"j")))
                    (ETApp
                     (ETApp
                      (EVar (0,"demote"))
                      (ETyp (TCon (TC (TCNum 15)) [])))
                     (ETyp (TCon (TC (TCNum 8)) []))))))))
               (EApp
                (EApp
                 (ETApp
                  (ETApp
                   (ETApp
                    (EVar (40,"@"))
                    (ETyp (TCon (TC (TCNum 64)) [])))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                  (ETyp (TCon (TC (TCNum 8)) [])))
                 (EVar (273,"W")))
                (EApp
                 (EApp
                  (ETApp
                   (EVar (2,"-"))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (EVar (274,"j")))
                 (ETApp
                  (ETApp
                   (EVar (0,"demote"))
                   (ETyp (TCon (TC (TCNum 16)) [])))
                  (ETyp (TCon (TC (TCNum 8)) []))))))
              [[(From (274,"j") (ETApp
                                 (ETApp
                                  (ETApp
                                   (EVar (49,"fromTo"))
                                   (ETyp (TCon (TC (TCNum 16)) [])))
                                  (ETyp (TCon (TC (TCNum 63)) [])))
                                 (ETyp (TCon (TC (TCNum 8)) []))))]])).

Definition base_case (M : ext_val) (idx : nat) : ext_val :=
  match M with
  | eseq l =>
    match nth_error l idx with
    | Some v => v
    | None => eseq nil
    end
  | _ => eseq nil
  end.

Fixpoint W_ev (fuel : nat) (M : ext_val) {struct fuel} : ext_val :=
  match fuel with
  (* if idx >= 16 *) 
  | S (S fuel2) =>
    match fuel2 with
    | S (S (S (S (S fuel7)))) =>
      match fuel7 with
      | S (S (S (S (S (S (S (S fuel15))))))) =>
        match fuel15 with
        | S fuel16 =>
          (* then (s1 (W@(idx-2)) (W@(idx-7))) + (s0 (W@(j-15)) (W@(j-16))) *)
          let W2 := W_ev fuel2 M in
          let W7 := W_ev fuel7 M in
          let W15 := W_ev fuel15 M in
          let W16 := W_ev fuel16 M in
          plus_ev (s1_spec (plus_ev W2 W7)) (s0_spec (plus_ev W15 W16))
        | _ => base_case M fuel
        end
      | _ => base_case M fuel
      end
    | _ => base_case M fuel
    end
    | _ => base_case M fuel
  end.


(*
Lemma W_eval :
  forall n wid GE TE SE,
    GE (wid,"W") = Some W_expr ->
    SE (wid,"W") = None ->
*)    



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

