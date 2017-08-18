Require Import List.
Import ListNotations.
Require Import String.

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

Import HaskellListNotations.
Require Import List.


Definition splitAt_model (n : nat) (l : list ext_val) : list ext_val :=
  let f := firstn n l in
  let r := list_drop n l in
  (eseq f) :: (eseq r) :: nil.

Definition take_model (n : nat) (l : list ext_val) : ext_val :=
  eseq (firstn n l).

Lemma splitAt_sem_res :
  forall l n,
    0 <= n <= Z.of_nat (length l) ->
    splitAt_sem (tnum n) (strict_list (map to_sval l)) =
    Some (stuple [strict_list (map to_sval (firstn (Z.to_nat n) l)), strict_list (map to_sval (list_drop (Z.to_nat n) l))]).
Proof.
  induction l; intros.
  assert (n = 0) by (simpl in *; omega).
  subst n.
  simpl. reflexivity.
  simpl in H.
  rewrite Zpos_P_of_succ_nat in *.
  rewrite map_cons.
  unfold strict_list. fold strict_list.
  assert (0 <= (n - 1) <= Z.of_nat (length l) \/ n = 0) by omega.
  destruct H0; try solve [subst n; simpl; reflexivity].

  simpl. erewrite IHl; eauto.
  
  destruct n; try reflexivity.
  Focus 2.    remember (Pos2Z.neg_is_neg p) as HH. omega.
  f_equal. f_equal.

  assert (exists n, Z.to_nat (Z.pos p) = S n). {
    eapply Pos2Nat.is_succ.
  }
  destruct H1.
  assert (Z.to_nat (Z.pos p -1) = x). {
    rewrite Z.sub_1_r.
    rewrite Z2Nat.inj_pred.
    rewrite H1. simpl. reflexivity.
  }

  f_equal.

  rewrite H1. unfold firstn. fold (@firstn ext_val).
  rewrite H2.
  reflexivity.
  rewrite H1. rewrite H2. reflexivity.
Qed.  


Lemma splitAt_eval :
  forall GE TE SE,
    GE (35, "splitAt") = Some (mb 3 1 splitAt) ->
    SE (35, "splitAt") = None ->
    forall va ta1 ta2 ta3 l n tr2 tr3,
      eager_eval_type GE TE ta1 (tnum n) ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va (to_sval (eseq l)) ->
      0 <= n <= Z.of_nat (Datatypes.length l) ->
      eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (EVar (35,"splitAt")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va)
                      (stuple (map to_sval (splitAt_model (Z.to_nat n) l))).
Proof.
  intros. 
  e. e. e. e. ag.
  e. e. e. e. e. lv.
  simpl.
  eapply splitAt_sem_res; eauto.
Qed.


Lemma take_eval :
  forall GE TE SE,
    GE (61, "take") =
    Some
      (ETAbs (214, "front")
             (ETAbs (215, "back")
                    (ETAbs (216, "elem")
                           (EAbs (212, "__p1")
                                 (EWhere (EVar (214, "x"))
                                         [NonRecursive
                                            (Decl (213, "__p2")
                                                  (DExpr
                                                     (EApp
                                                        (ETApp
                                                           (ETApp (ETApp (EVar (35, "splitAt")) (ETyp (TVar (TVBound 214 KNum))))
                                                                  (ETyp (TVar (TVBound 215 KNum)))) (ETyp (TVar (TVBound 216 KType))))
                                                        (EVar (212, "__p1"))))),
                                          NonRecursive (Decl (214, "x") (DExpr (ESel (EVar (213, "__p2")) (TupleSel 0)))),
                                          NonRecursive (Decl (215, "__p0") (DExpr (ESel (EVar (213, "__p2")) (TupleSel 1))))]))))) ->
    SE (61, "take") = None ->
    GE (35, "splitAt") = Some (mb 3 1 splitAt) ->
    SE (35, "splitAt") = None ->
    forall va ta1 ta2 ta3 tr2 tr3 n l,
      eager_eval_type GE TE ta1 (tnum n) ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va (to_sval (eseq l)) ->
      0 <= n <= Z.of_nat (Datatypes.length l) ->
      forall res,
        res = (to_sval (take_model (Z.to_nat n) l)) ->
      eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (EVar (61,"take")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va) res.
Proof.
  intros. subst res.

  e. e. e. e. ag.
  e. e. e. e.
  e. g. e. g.
  eapply splitAt_eval; eauto; try et.
  lv. unfold splitAt_model. simpl.
  reflexivity.
Qed.

(*
Lemma append_eval :
  forall GE TE SE,
    GE (34, "#") = Some (mb 3 2 Append) ->
    SE (34, "#") = None ->
    forall 

*)
