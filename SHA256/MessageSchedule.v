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
Require Import SHA256.SS0.
Require Import SHA256.SS1.

Import HaskellListNotations.

Definition W_expr : Expr :=             (EAbs (357,"n")
             (EIf (EApp
                   (EApp
                    (ETApp
                     (EVar (13,"<"))
                     (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                    (EVar (357,"n")))
                   (ETApp
                    (ETApp
                     (EVar (0,"demote"))
                     (ETyp (TCon (TC (TCNum 16)) [])))
                    (ETyp (TCon (TC (TCNum 8)) []))))
              (EApp
               (EApp
                (ETApp
                 (ETApp
                  (ETApp
                   (EVar (40,"@"))
                   (ETyp (TCon (TC (TCNum 16)) [])))
                  (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])))
                 (ETyp (TCon (TC (TCNum 8)) [])))
                (EVar (354,"M")))
               (EVar (357,"n")))
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
                      (EVar (355,"W"))
                      (EApp
                       (EApp
                        (ETApp
                         (EVar (2,"-"))
                         (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                        (EVar (357,"n")))
                       (ETApp
                        (ETApp
                         (EVar (0,"demote"))
                         (ETyp (TCon (TC (TCNum 2)) [])))
                        (ETyp (TCon (TC (TCNum 8)) [])))))))
                   (EApp
                    (EVar (355,"W"))
                    (EApp
                     (EApp
                      (ETApp
                       (EVar (2,"-"))
                       (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                      (EVar (357,"n")))
                     (ETApp
                      (ETApp
                       (EVar (0,"demote"))
                       (ETyp (TCon (TC (TCNum 7)) [])))
                      (ETyp (TCon (TC (TCNum 8)) [])))))))
                 (EApp
                  (EVar (246,"s0"))
                  (EApp
                   (EVar (355,"W"))
                   (EApp
                    (EApp
                     (ETApp
                      (EVar (2,"-"))
                      (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                     (EVar (357,"n")))
                    (ETApp
                     (ETApp
                      (EVar (0,"demote"))
                      (ETyp (TCon (TC (TCNum 15)) [])))
                     (ETyp (TCon (TC (TCNum 8)) []))))))))
               (EApp
                (EVar (355,"W"))
                (EApp
                 (EApp
                  (ETApp
                   (EVar (2,"-"))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (EVar (357,"n")))
                 (ETApp
                  (ETApp
                   (EVar (0,"demote"))
                   (ETyp (TCon (TC (TCNum 16)) [])))
                  (ETyp (TCon (TC (TCNum 8)) [])))))))).


Definition base_case (M : ext_val) (idx : nat) : ext_val :=
  match M with
  | eseq l =>
    match nth_error l idx with
    | Some v => v
    | None => eseq nil
    end
  | _ => eseq nil
  end.

(* calculate a single element of W, given an M *)
Fixpoint W_elt_ev (fuel : nat) (M : ext_val) {struct fuel} : ext_val :=
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
          let W2 := W_elt_ev fuel2 M in
          let W7 := W_elt_ev fuel7 M in
          let W15 := W_elt_ev fuel15 M in
          let W16 := W_elt_ev fuel16 M in
          plus_ev (s1_spec (plus_ev W2 W7)) (s0_spec (plus_ev W15 W16))
        | _ => base_case M fuel
        end
      | _ => base_case M fuel
      end
    | _ => base_case M fuel
    end
    | _ => base_case M fuel
  end.

(* calculate all of W, given a max element *)
Fixpoint W_ev (fuel : nat) (M : ext_val) : ext_val :=
  match fuel with
  | O => eseq nil
  | S n =>
    match W_ev n M with
    | eseq l =>
      eseq (l ++ [(W_elt_ev n M)])
    | _ => eseq nil
    end
  end.

Definition ext_to_nat (l : list ext_val) : option nat :=
  match ExtToBitvector.to_bitv l with
  | Some bv => Some (Z.to_nat (@unsigned (Datatypes.length l) bv))
  | _ => None
  end.

Definition extnum (val width : Z) : list ext_val :=
  ExtToBitvector.from_bitv (@repr (Z.to_nat width) val).

(* we can evaluate W @ n to an answer modeled by W_ev *)
Lemma W_eval_inductive :
  forall GE TE SE,
    wf_env ge GE TE SE ->
    GE (355,"W") = Some (W_expr) ->
    SE (355,"W") = None ->
    forall k n M idx l,
      (n < k)%nat ->
      SE (354,"M") = Some (to_sval M) ->
      SE (357,"n") = Some (to_sval (eseq l)) ->
      has_type M (tseq 16 (tseq 32 tbit)) ->
      has_type (eseq l) (tseq (length l) tbit) ->
      eager_eval_expr GE TE SE idx (to_sval (eseq l)) ->
      ext_to_nat l = Some n ->
      forall res,
        res = to_sval (W_elt_ev n M) ->
        eager_eval_expr GE TE SE (EApp (EVar (355,"W")) idx) res.
Proof.
  intros GE TE SE Hwf HgeW HseW.
  gen_global (13,"<").
  gen_global (0,"demote").
  gen_global (1,"+").
  gen_global (2,"-").
  (* strong induction *)
  induction k; intros n M idx l Hbound Hm Hn HtypeM HtypeN HevalN Hext_to_nat res Hres; try omega.
  
  assert (Hcases : (n < 16 \/ n >= 16)%nat) by omega.
  destruct Hcases.

  * (* base case *)
    clear IHk.
    unfold ext_to_nat in *.
    destruct (ExtToBitvector.to_bitv l) eqn:?; try congruence.
    inversion Hext_to_nat.
    e. ag. e. e.
    use lt_eval.
    lv.
    use demote_eval.
    instantiate (1 := extnum 16 8).
    reflexivity.
    assumption.
    unfold extnum. simpl.
    repeat (econstructor; eauto).
    unfold lt_ev. rewrite Heqo. simpl.
    instantiate (1 := true).
    destruct (zlt (unsigned b) 16); auto.
    assert (Z.to_nat 16 <= Z.to_nat (unsigned b))%nat.
    eapply Z2Nat.inj_le; try omega.
    rewrite H5 in H4. simpl in H4. unfold Pos.to_nat in *.
    simpl in *. omega.
    simpl.
    subst res.
    (* TODO: at_eval *)
    admit.
    
  * (* inductive case *)
    e. ag. e.

    e. instantiate (1 := false).
    use lt_eval. lv.
    use demote_eval.
    instantiate (1 := extnum 16 8).
    reflexivity.
    assumption.
    unfold extnum. simpl.
    repeat (econstructor; eauto).
    unfold lt_ev.
    admit. (* works out *)

    simpl.

    eapply plus_eval.
    intuition; eassumption.
    intuition; eassumption.
    et.

    eapply plus_eval.
    intuition; eassumption.
    intuition; eassumption.
    et.

    eapply plus_eval.
    intuition; eassumption.
    intuition; eassumption.
    et.

    
    
    
    idtac.
Admitted.



