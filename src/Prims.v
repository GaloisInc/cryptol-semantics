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

Require Import ExtToBitvector.

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


Lemma append_eval :
  forall GE TE SE,
    GE (34, "#") = Some (mb 3 2 Append) ->
    SE (34, "#") = None ->
    forall va1 va2 l l' ta1 ta2 ta3 tr1 tr2 tr3 res,
      eager_eval_type GE TE ta1 tr1 ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      res = to_sval (eseq (l ++ l')) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (ETApp (ETApp (EVar (34,"#")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va1) va2) res.
Proof.
  intros.
  subst res.
  e. e. e. e. e. ag.
  e. e. e. e. e. e. lv. lv.

  rewrite append_strict_list.
  simpl. rewrite map_app. reflexivity.
Qed.
                                                                
(* bitwise operations *)
Fixpoint bitwise_ext_val (f : bool -> bool -> bool) (l l' : list ext_val) : list ext_val :=
  match l,l' with
  | (ebit b :: r1),(ebit b' :: r2) =>
    (ebit (f b b')) :: bitwise_ext_val f r1 r2
  | _,_ => nil
  end.

Definition and_ev := bitwise_ext_val andb.
Definition or_ev := bitwise_ext_val orb.
Definition xor_ev := bitwise_ext_val xorb.

Fixpoint not_ev (l : list ext_val) : list ext_val :=
  match l with
  | (ebit b) :: r => (ebit (negb b)) :: not_ev r
  | _ => nil
  end.

Definition rotr_ev (l : list ext_val) (n : nat) : list ext_val :=
  let n := (length l - n)%nat in
  list_drop n l ++ firstn n l.

(* sanity check *)
Lemma rotr_0_id :
  forall l,
    rotr_ev l O = l.
Proof.
  intros.
  unfold rotr_ev.
  replace (length l - 0)%nat with (length l) by omega.
  rewrite firstn_all.
  rewrite list_drop_all. simpl. reflexivity.
Qed.

Definition shiftr_ev (l : list ext_val) (n : nat) : list ext_val :=
  firstn (length l - n)%nat l.

Lemma demote_eval :
  forall id GE TE SE,
    GE (id, "demote") = Some (mb 2 0 Demote) ->
    SE (id, "demote") = None ->
    forall ta1 tr1 ta2 tr2 res,
      eager_eval_type GE TE ta1 tr1 ->
      eager_eval_type GE TE ta2 tr2 ->
      demote_sem tr1 tr2 = Some res ->
      eager_eval_expr GE TE SE (ETApp (ETApp (EVar (id,"demote")) (ETyp ta1)) (ETyp ta2)) res.
Proof.
  intros.
  e. e. ag.
  e. e. e. simpl. assumption.
Qed.

Lemma rotr_eval :
  forall id GE TE SE,
    GE (id, ">>>") = Some (mb 3 2 Rotr) ->
    SE (id, ">>>") = None ->
    forall va1 va2 l l' ta1 ta2 ta3 tr1 tr2 tr3 res len len' (bv : BitV len'),
      eager_eval_type GE TE ta1 tr1 ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      to_bitv l' = Some bv ->
      res = to_sval (eseq (rotr_ev l (Z.to_nat (unsigned bv)))) ->
      has_type (eseq l) (tseq len tbit) ->
      has_type (eseq l') (tseq len' tbit) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (ETApp (ETApp (EVar (id,">>>")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va1) va2) res.
Proof.
  intros.
  e. e. e. e. e. ag.
  e. e. e. e. e. e.
  lv. lv.
  (* TODO: model Rotr *)
Admitted.

Lemma xor_sem_ev :
  forall l l' len,
    has_type (eseq l) (tseq len tbit) ->
    has_type (eseq l') (tseq len tbit) ->
    xor_sem (strict_list (map to_sval l)) (strict_list (map to_sval l')) = Some (strict_list (map to_sval (xor_ev l l'))).
Proof.
  induction l; intros; simpl.
  inversion H. subst. inversion H0. subst.
  destruct l'; simpl in *; try omega.
  reflexivity.
  inversion H; inversion H0; subst.
  destruct l'; simpl in H6; try congruence.
  inversion H3. inversion H7.
  subst.
  inversion H4. inversion H10.
  subst.
  simpl.
  erewrite IHl; eauto.
  f_equal. f_equal. destruct b; destruct b0; simpl; auto.
  econstructor; eauto.
  inversion H6. econstructor; eauto.
Qed.

Lemma xor_eval :
  forall id GE TE SE,
    GE (id, "^") = Some (mb 1 2 Xor) ->
    SE (id, "^") = None ->
    forall va1 va2 l l' ta tr res len,
      eager_eval_type GE TE ta tr ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      res = to_sval (eseq (xor_ev l l')) ->
      has_type (eseq l) (tseq len tbit) ->
      has_type (eseq l') (tseq len tbit) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"^")) (ETyp ta)) va1) va2) res.
Proof.
  intros.
  e. e. e. ag.
  e. e. e. e. lv. lv.
  subst res.
  simpl.
  eapply xor_sem_ev; eauto.
Qed.

Lemma and_eval :
  forall id GE TE SE,
    GE (id, "&&") = Some (mb 1 2 And) ->
    SE (id, "&&") = None ->
    forall va1 va2 l l' ta tr res len,
      eager_eval_type GE TE ta tr ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      res = to_sval (eseq (and_ev l l')) ->
      has_type (eseq l) (tseq len tbit) ->
      has_type (eseq l') (tseq len tbit) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"&&")) (ETyp ta)) va1) va2) res.
Proof.
  intros.
  e. e. e. ag.
  e. e. e. e; try lv.
  subst res.
  simpl.
  (* TODO: model And *)
Admitted. 

Lemma or_eval :
  forall id GE TE SE,
    GE (id, "||") = Some (mb 1 2 Or) ->
    SE (id, "||") = None ->
    forall va1 va2 l l' ta tr res len,
      eager_eval_type GE TE ta tr ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      res = to_sval (eseq (or_ev l l')) ->
      has_type (eseq l) (tseq len tbit) ->
      has_type (eseq l') (tseq len tbit) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"||")) (ETyp ta)) va1) va2) res.
Proof.
  intros.
  e. e. e. ag.
  e. e. e. e; try lv.
  subst res.
  simpl.
  (* TODO: model Or *)
Admitted.

Lemma complement_eval :
  forall id GE TE SE,
    GE (id, "complement") = Some (mb 1 1 Compl) ->
    SE (id, "complement") = None ->
    forall va1 l ta tr res len,
      eager_eval_type GE TE ta tr ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      res = to_sval (eseq (not_ev l)) ->
      has_type (eseq l) (tseq len tbit) ->
      eager_eval_expr GE TE SE (EApp (ETApp (EVar (id,"complement")) (ETyp ta)) va1) res.
Proof.
  intros. e. e. ag.
  e. e. e. lv.
  simpl.
  (* TODO: model complement *)
Admitted.

Lemma has_type_not :
  forall l len,
    has_type (eseq l) (tseq len tbit) ->
    has_type (eseq (not_ev l)) (tseq len tbit).
Proof.
  induction l; intros;
    try solve [simpl; auto].
  inversion H. subst. inversion H2. subst.
  
  assert (has_type (eseq l) (tseq (length l) tbit)).
  econstructor; eauto.
  eapply IHl in H0.
  inversion H0. subst.

  replace (S (length (not_ev l))) with (length (not_ev (a :: l))).
  econstructor.
  inversion H3. subst.
  simpl. econstructor. econstructor.
  eassumption.

  simpl. inversion H3.
  simpl. reflexivity.
Qed.

Lemma has_type_and :
  forall l l' len,
    has_type (eseq l) (tseq len tbit) ->
    has_type (eseq l') (tseq len tbit) ->
    has_type (eseq (and_ev l l')) (tseq len tbit).
Proof.
  induction l; intros;
    try solve [simpl; auto].
  inversion H. inversion H0. subst.
  destruct l'; try solve [simpl in *; omega].
  inversion H3. inversion H7.
  assert (has_type (eseq l) (tseq (length l) tbit)).
  econstructor; eauto.
  assert (has_type (eseq l') (tseq (length l') tbit)).
  econstructor; eauto.
  simpl in H6. inversion H6.
  rewrite H15 in *.
  subst.
  eapply IHl in H13; try solve [econstructor; eauto].
  inversion H13.
  subst.
  inversion H4. inversion H10.
  subst. unfold and_ev. simpl.
  fold and_ev.
  replace (S (length (and_ev l l'))) with (length (ebit (b && b0) :: and_ev l l')).
  econstructor. econstructor; eauto.
  econstructor.
  simpl. reflexivity.
Qed.

Lemma has_type_xor :
  forall l l' len,
    has_type (eseq l) (tseq len tbit) ->
    has_type (eseq l') (tseq len tbit) ->
    has_type (eseq (xor_ev l l')) (tseq len tbit).
Proof.
  induction l; intros;
    try solve [simpl; auto].
  inversion H. inversion H0. subst.
  destruct l'; try solve [simpl in *; omega].
  inversion H3. inversion H7.
  assert (has_type (eseq l) (tseq (length l) tbit)).
  econstructor; eauto.
  assert (has_type (eseq l') (tseq (length l') tbit)).
  econstructor; eauto.
  simpl in H6. inversion H6.
  rewrite H15 in *.
  subst.
  eapply IHl in H13; try solve [econstructor; eauto].
  inversion H13.
  subst.
  inversion H4. inversion H10.
  subst. unfold xor_ev. simpl.
  fold xor_ev.
  replace (S (length (xor_ev l l'))) with (length (ebit (xorb b b0) :: xor_ev l l')).
  econstructor. econstructor; eauto.
  econstructor.
  simpl. reflexivity.
Qed.

Lemma has_type_rotr :
  forall l len t,
    has_type (eseq l) (tseq len t) ->
    forall n,
      (n <= (length l))%nat ->
      has_type (eseq (rotr_ev l n)) (tseq len t).
Proof.
  induction l; intros.
  assert (n = O) by (simpl in H0; omega).
  subst n. unfold rotr_ev. simpl.
  inversion H. subst. eauto.
  assert (n <= length l \/ n = S (length l))%nat by (simpl in *; omega).
  clear H0. destruct H1.
  remember H0 as H1. clear HeqH1.
  eapply IHl in H0. Focus 2.
  inversion H. subst. inversion H4.
  subst. econstructor. eassumption.
  (* This might be the wrong path *)
  
Admitted.
