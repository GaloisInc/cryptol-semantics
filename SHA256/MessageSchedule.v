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
  match to_bitlist ext_val (fun x => match x with | ebit b => Some b |_ => None end) (length l) l with
  | Some z => Some (Z.to_nat z)
  | _ => None
  end.

Definition extnum (val width : Z) : list ext_val :=
  from_bitlist ext_val ebit (Z.to_nat width) val.

(*
Lemma tobit_frombit_id :
  forall {w} (bv : BitV w),
    ExtToBitvector.to_bitv (ExtToBitvector.from_bitv bv) = Some bv.
Proof.
Admitted.

Lemma from_bitv_length :
  forall w (bv : BitV w),
    Datatypes.length (@from_bitv w bv) = w.
Proof.
Admitted.
 *)

(* Goal: get the proof in this file done *)
(* in order to do this, you probably need to rework to_bitv and from_bitv *)
(* at least get the plus_ev and minus_ev semantics to use something else *)


(* we can evaluate W @ n to an answer modeled by W_ev *)
Lemma W_eval_inductive :
  forall k GE TE SE,
    wf_env ge GE TE SE ->
    GE (355,"W") = Some (W_expr) ->
    SE (355,"W") = None ->
    forall n M idx l,
      (n < k)%nat ->
      SE (354,"M") = Some (to_sval M) ->
      has_type M (tseq 16 (tseq 32 tbit)) ->
      has_type (eseq l) (tseq 8 tbit) ->
      eager_eval_expr GE TE SE idx (to_sval (eseq l)) ->
      ext_to_nat l = Some n ->
      forall res,
        res = to_sval (W_elt_ev n M) ->
        eager_eval_expr GE TE SE (EApp (EVar (355,"W")) idx) res.
Proof.
  (* strong induction *)
  induction k; intros GE TE SE Hwf HgeW HseW n M idx l Hbound Hm HtypeM HtypeN HevalN Hext_to_nat res Hres; try omega.
  gen_global (13,"<").
  gen_global (40,"@").
  gen_global (0,"demote").
  gen_global (1,"+").
  gen_global (2,"-").
  unfold ext_to_nat in *.
  match goal with
  | [ H : (match ?X with | Some _ => _ | None => _  end) = _ |- _ ] => destruct X eqn:?; try congruence
  end.
  assert (Hcases : (n < 16 \/ n >= 16)%nat) by omega.
  destruct Hcases.

  * (* base case *)
    clear IHk.
    e. ag. e. e.
    use lt_eval.
    lv.
    use demote_eval.
    instantiate (1 := extnum 16 8).
    reflexivity.
    inversion HtypeN. rewrite H6.
    assumption.
    unfold extnum. simpl.
    repeat (econstructor; eauto).
    unfold lt_ev.
    repeat rewrite Heqo.
    unfold extnum. simpl.
    replace (length l) with 8%nat by (inversion HtypeN; congruence).
    simpl. inversion Hext_to_nat.
    subst n. unfold two_power_nat. simpl.
    instantiate (1 := true).
    
    destruct (zlt z 16); auto.
    assert (Z.to_nat 16 <= Z.to_nat z)%nat.
    eapply Z2Nat.inj_le; try omega.
    simpl in H5. unfold Pos.to_nat in *.
    simpl in H5. omega.
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
    inversion HtypeN. congruence.
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
    

    use s1_eval.
    instantiate (1 := eseq (extnum (Z.of_nat ((n-2)%nat)) 8)).
    admit. (* lemma *)

    eapply wf_env_extend_SE; try reflexivity; try eassumption.

    all: try reflexivity.
    
    eapply IHk.
    eapply wf_env_extend_SE; try reflexivity; try eassumption.
    assumption.
    unfold extend. simpl. assumption.
    Focus 5.
    eapply minus_eval.
    intuition; eassumption.
    intuition; eassumption.
    et. lv.
    use demote_eval.
    instantiate (1 := extnum 2 8).
    reflexivity.
    unfold minus_ev. unfold binop_ev.

    unfold extnum.
    inversion HtypeN.

    unfold Z.to_nat. unfold Pos.to_nat.
    simpl.
    rewrite H6.
    subst.
    
    (* TODO: need lemma *)
    admit.



    
    
      
    idtac.      
Admitted.



