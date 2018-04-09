(* This file serves no purpose *)
(* Just a playground for a thing to try out *)
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

Require Import Cryptol.ExtToBitvector.
Require Import Cryptol.Prims.

Import HaskellListNotations.
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string.

Definition W_expr :=               (EAbs (245,"x")
             (EIf (EApp
                   (EApp
                    (ETApp
                     (EVar (17,"=="))
                     (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                    (EVar (245,"x")))
                   (ETApp
                    (ETApp
                     (EVar (0,"demote"))
                     (ETyp (TCon (TC (TCNum 0)) [])))
                    (ETyp (TCon (TC (TCNum 8)) []))))
              (EVar (245,"x"))
              (EApp
               (EApp
                (ETApp
                 (EVar (1,"+"))
                 (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                (ETApp
                 (ETApp
                  (EVar (0,"demote"))
                  (ETyp (TCon (TC (TCNum 1)) [])))
                 (ETyp (TCon (TC (TCNum 8)) []))))
               (EApp
                (EVar (244,"W"))
                (EApp
                 (EApp
                  (ETApp
                   (EVar (2,"-"))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (EVar (245,"x")))
                 (ETApp
                  (ETApp
                   (EVar (0,"demote"))
                   (ETyp (TCon (TC (TCNum 1)) [])))
                  (ETyp (TCon (TC (TCNum 8)) [])))))))).

Definition W_decl :=        [(Recursive
         [(Decl (244,"W")
           (DExpr W_expr))])].

Definition rec_id : Expr :=
     (EAbs (243,"M")
      (EWhere
       (EApp
        (EVar (244,"W"))
        (EVar (243,"M")))
       W_decl
)).


(* recursive model of identity *)
Fixpoint rec_model (fuel : nat) (e : ext_val) : ext_val :=
  match fuel with
  | O => e
  | S fuel' =>
    match e with
    | eseq l =>
      match to_bitv l with
      | Some bv => rec_model fuel' (eseq (@from_bitv (Datatypes.length l) (add bv mone)))
      | None => eseq nil
      end
    | _ => eseq nil
    end
  end.




(* Lemma eval_W_id : *)
(*   forall n GE TE SE, *)
(*     GE (244,"W") = Some W_expr -> *)
(*     SE (244,"W") = None -> *)
(*     GE (17,"==") = Some (mb 1 2 Eq) -> *)
(*     SE (17,"==") = None -> *)
(*     GE (1,"+") = Some (mb 1 2 Plus) -> *)
(*     SE (1,"+") = None -> *)
(*     GE (2,"-") = Some (mb 1 2 Minus) -> *)
(*     SE (2,"-") = None -> *)
(*     GE (0,"demote") = Some (mb 2 0 Demote) -> *)
(*     SE (0,"demote") = None -> *)
(*     forall l bv, *)
(*       has_type (eseq l) (tseq 8 tbit) -> *)
(*       @to_bitv (Datatypes.length l) l = Some bv -> *)
(*       n = Z.to_nat (unsigned bv) -> *)
(*       forall argexp res, *)
(*         eager_eval_expr GE TE SE argexp (to_sval (eseq l)) -> *)
(*         res = to_sval (rec_model n (eseq l)) -> *)
(*         eager_eval_expr GE TE SE (EApp (EVar (244,"W")) argexp) res. *)
(* Proof. *)
(*   induction n; intros. *)

(*   * e. ag. e. e.  *)
(*     use eq_eval. *)
(*     instantiate (1 := eseq l). *)
(*     lv. *)
(*     instantiate (1 := eseq (repeat (ebit false) 8)). *)
(*     simpl. *)
(*     use demote_eval. *)
(*     instantiate (1 := true). *)
(*     admit. (* We have enough information *) *)

(*     simpl. subst res. unfold rec_model. *)
(*     lv. *)
(*   * *)
(*     assert (Hlen : Datatypes.length l = 8%nat). { *)
(*       inversion H9; eauto. *)
(*     }  *)
    
(*     e. ag. e. e. *)
(*     use eq_eval. *)
    
(*     instantiate (1 := eseq l). *)
(*     lv. *)
(*     instantiate (1 := eseq (repeat (ebit false) 8)). *)
(*     simpl. *)
(*     use demote_eval. *)
(*     instantiate (1 := false). *)
(*     admit. (* We have enough information *) *)
(*     simpl. *)
(*     eapply plus_eval. *)
(*     intuition; eassumption. *)
(*     unfold extend; simpl; intuition; eassumption. *)
(*     et. *)
(*     use demote_eval. *)
(*     simpl. *)
(* Admitted. *)
(*    instantiate (1 := (extnum 1 8)).
    reflexivity.

    eapply IHn.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    intuition; eassumption.
    Focus 4.
    eapply minus_eval.
    intuition; eassumption.
    intuition; eassumption.
    et. lv.
    use demote_eval.
    instantiate (1 := extnum 1 8).
    reflexivity.
    eassumption.
    unfold extnum.
    instantiate (1 := repr 1).
    repeat rewrite Hlen.
    rewrite tobit_frombit_id.
    reflexivity.
    reflexivity.
    admit. (* it's true, just type *)
    simpl.

    (* we want (bv - 1) *)
    (* but dependent types are awful *)
    
    admit.
    admit.

    f_equal.
    unfold rec_model.*)

    (* It all works, modulo bit widths being terrible *)
    (* dependent types are kinda the worst *)

    (* TODO: rewrite semantics of add/sub/mul/etc to not use BitV *)
    (* BitV makes reasoning about these programs too complicated *)
    (* It would be much easier with simple types and options *)


(* Lemma eval_rec_id : *)
(*   forall n GE TE SE, *)
(*     GE (244,"W") = Some W_expr -> *)
(*     SE (244,"W") = None -> *)
(*     GE (17,"==") = Some (mb 1 2 Eq) -> *)
(*     SE (17,"==") = None -> *)
(*     GE (1,"+") = Some (mb 1 2 Plus) -> *)
(*     SE (1,"+") = None -> *)
(*     GE (2,"-") = Some (mb 1 2 Minus) -> *)
(*     SE (2,"-") = None -> *)
(*     GE (0,"demote") = Some (mb 2 0 Demote) -> *)
(*     SE (0,"demote") = None -> *)
(*     forall l bv, *)
(*       has_type (eseq l) (tseq 8 tbit) -> *)
(*       @to_bitv (Datatypes.length l) l = Some bv -> *)
(*       n = Z.to_nat (unsigned bv) -> *)
(*       forall argexp res, *)
(*         eager_eval_expr GE TE SE argexp (to_sval (eseq l)) -> *)
(*         res = to_sval (rec_model n (eseq l)) -> *)
(*         eager_eval_expr GE TE SE (EApp rec_id argexp) res. *)
(* Proof. *)
(*   induction n; intros. *)

(*   * e. e. e. e. g. e. lv. *)
(*     e. *)
(*     use eq_eval. *)
(*     instantiate (1 := eseq l). *)
(*     lv. *)
(*     instantiate (1 := eseq (repeat (ebit false) 8)). *)
(*     simpl. *)
(*     use demote_eval. *)
(*     instantiate (1 := true). *)
(*     admit. (* We have enough information *) *)

(*     simpl. subst res. unfold rec_model. *)
(*     lv. *)
(*   * *)
(*     assert (Hlen : Datatypes.length l = 8%nat). { *)
(*       inversion H9; eauto. *)
(*     }  *)
    
(*     e. e. e. e. g. e. lv. *)
(*     e. *)
(*     use eq_eval. *)
    
(*     instantiate (1 := eseq l). *)
(*     lv. *)
(*     instantiate (1 := eseq (repeat (ebit false) 8)). *)
(*     simpl. *)
(*     use demote_eval. *)
(*     instantiate (1 := false). *)
(*     admit. (* We have enough information *) *)
(*     simpl. *)
(*     eapply plus_eval. *)
(*     intuition; eassumption. *)
(*     unfold extend; simpl; intuition; eassumption. *)
(*     et. *)
(*     use demote_eval. *)
(*     simpl. *)

(* (*    instantiate (1 := (extnum 1 8)). *)
(*     reflexivity. *)

(*     e. g. e. *)
(*     eapply minus_eval. *)
(*     intuition; eassumption. *)
(*     unfold extend; simpl; intuition; eassumption. *)
(*     et. *)
(*     instantiate (1 := l). lv. *)
(*     instantiate (1 := extnum 1 8). *)
(*     use demote_eval. rewrite H10. reflexivity. *)
(*     instantiate (1 := @repr (Datatypes.length l) 1). *)
(*     rewrite Hlen. reflexivity. *)
(*     reflexivity. *)
    
(*   *)   *)

(* Admitted.     *)
  



    

Definition where_test : Expr :=
  (EAbs (243,"M")
      (EWhere
       (EVar (244,"W"))
       [(Recursive
         [(Decl (244,"W")
           (DExpr
            (EApp
             (EApp
              (ETApp
               (ETApp
                (ETApp
                 (EVar (34,"#"))
                 (ETyp (TCon (TC (TCNum 8)) [])))
                (ETyp (TCon (TC (TCNum 8)) [])))
               (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
              (EVar (243,"M")))
             (EComp
              (EApp
               (EApp
                (ETApp
                 (EVar (1,"+"))
                 (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                (EApp
                 (EApp
                  (ETApp
                   (ETApp
                    (ETApp
                     (EVar (40,"@"))
                     (ETyp (TCon (TC (TCNum 16)) [])))
                    (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                   (ETyp (TCon (TC (TCNum 8)) [])))
                  (EVar (244,"W")))
                 (EApp
                  (EApp
                   (ETApp
                    (EVar (2,"-"))
                    (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                   (EVar (245,"j")))
                  (ETApp
                   (ETApp
                    (EVar (0,"demote"))
                    (ETyp (TCon (TC (TCNum 1)) [])))
                   (ETyp (TCon (TC (TCNum 8)) []))))))
               (EApp
                (EApp
                 (ETApp
                  (ETApp
                   (ETApp
                    (EVar (40,"@"))
                    (ETyp (TCon (TC (TCNum 16)) [])))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (ETyp (TCon (TC (TCNum 8)) [])))
                 (EVar (244,"W")))
                (EApp
                 (EApp
                  (ETApp
                   (EVar (2,"-"))
                   (ETyp (TCon (TC TCSeq) [TCon (TC (TCNum 8)) [],TCon (TC TCBit) []])))
                  (EVar (245,"j")))
                 (ETApp
                  (ETApp
                   (EVar (0,"demote"))
                   (ETyp (TCon (TC (TCNum 8)) [])))
                  (ETyp (TCon (TC (TCNum 8)) []))))))
              [[(From (245,"j") (ETApp
                                 (ETApp
                                  (ETApp
                                   (EVar (49,"fromTo"))
                                   (ETyp (TCon (TC (TCNum 8)) [])))
                                  (ETyp (TCon (TC (TCNum 15)) [])))
                                 (ETyp (TCon (TC (TCNum 8)) []))))]]))))])])).

Lemma test_eval :
  forall GE TE SE,
    GE (34, "#") = Some (mb 3 2 Append) /\ SE (34,"#") = None ->
    GE (49, "fromTo") = Some (mb 3 0 fromTo) /\ SE (49,"fromTo") = None ->
    forall n xv,
    has_type xv (tseq n (tseq 8 tbit)) ->
    forall x,
    eager_eval_expr GE TE SE x (to_sval xv) ->
    exists v,
      eager_eval_expr GE TE SE (EApp where_test x) v.
Proof.
  induction n; intros.
  inversion H1. subst.
  destruct l; try solve [simpl in *; congruence].
  
(*  eexists.
  unfold where_test.
  e. e.
  e. g.
  use append_eval.
  eapply eager_eval_local_var; eauto. simpl.
  unfold extend. simpl.
  instantiate (1 := nil).
  reflexivity.
  e. 
  ec. ec. simpl.
  use fromTo_eval.
  unfold extend. simpl. intuition.
  reflexivity.
  unfold fromTo_ev. unfold to_sval. fold to_sval.
  rewrite list_of_strictval_of_strictlist.
  reflexivity.
  repeat fold to_sval.*)

  Focus 2.
  
  
  
  
Admitted.
  