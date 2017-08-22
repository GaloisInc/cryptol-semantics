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
    splitAt_sem (tvnum n) (strict_list (map to_sval l)) =
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
      eager_eval_type GE TE ta1 (tvnum n) ->
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
      eager_eval_type GE TE ta1 (tvnum n) ->
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

Definition shiftr_ev (l : list ext_val) (n : nat) : list ext_val :=
  let n' := (length l - n)%nat in
  let n := Init.Nat.min n (length l) in
  (repeat (ebit false) n) ++ firstn n' l.

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

Lemma same_bitv :
  forall l {w} (bv : BitV w),
    to_bitv l = Some bv ->
    StrictToBitvector.to_bitv (map to_sval l) = Some bv.
Proof.
  induction l; intros.
  unfold to_bitv in *.
  destruct w. simpl in *. auto. congruence.
  destruct w; simpl in H; try congruence.

  destruct a; congruence.
  
  simpl. destruct a; simpl in *; try congruence.
  destruct (to_bitv l) eqn:?; try congruence.
  erewrite IHl; eauto.
Qed.

Lemma shiftr_eval :
  forall id GE TE SE,
    GE (id, ">>") = Some (mb 3 2 Shiftr) ->
    SE (id, ">>") = None ->
    forall va1 va2 l l' ta1 ta2 ta3 tr1 tr2  res len len' (bv : BitV len'),
      eager_eval_type GE TE ta1 tr1 ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tvbit ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      to_bitv l' = Some bv ->
      res = to_sval (eseq (shiftr_ev l (Z.to_nat (unsigned bv)))) ->
      has_type (eseq l) (tseq len tbit) ->
      has_type (eseq l') (tseq len' tbit) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (ETApp (ETApp (EVar (id,">>")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va1) va2) res.
Proof.
  intros.
  eapply same_bitv in H6.
  e. e. e. e. e. ag.
  e. e. e. e. e.
  e; try lv.
  simpl.
  subst res.
  unfold shiftr_sem.
  simpl.
  repeat rewrite list_of_strictval_of_strictlist.
  assert (len' = length (map to_sval l')).
  inversion H9. erewrite map_length; eauto.
  subst len'.
  rewrite H6.
  f_equal.
  unfold shiftr_ev. f_equal.
  rewrite map_app.
  f_equal.
  rewrite map_repeat. simpl.
  f_equal.
  f_equal. erewrite map_length; eauto.
  rewrite <- firstn_map.
  f_equal.
  assert (Z.to_nat (unsigned bv) <= length (map to_sval l) \/ Z.to_nat (unsigned bv) > length (map to_sval l))%nat by omega.
  destruct H7.
  rewrite min_l by omega. erewrite map_length; eauto.
  erewrite min_r by omega. erewrite map_length; eauto.
  erewrite map_length in *.

  omega.
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
  eapply same_bitv in H6.
  e. e. e. e. e. ag.
  e. e. e. e. e. e.
  lv. lv.
  simpl. subst res.
  unfold rotr_ev. unfold rotr_sem.
  repeat rewrite list_of_strictval_of_strictlist.
  assert (len' = length (map to_sval l')) by (erewrite map_length; inversion H9; eauto).
  subst len'.
  rewrite H6.
  f_equal.
  simpl. f_equal.
  rewrite map_app. f_equal.
  rewrite list_map_drop. f_equal.
  f_equal. repeat erewrite map_length in *.
  reflexivity.
  
  repeat erewrite map_length in *.
  rewrite firstn_map. reflexivity.
Qed.

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

Lemma and_sem_ev :
  forall l,
    has_type (eseq l) (tseq (length l) tbit) ->
    forall l',
      has_type (eseq l') (tseq (length l') tbit) ->
      length l = length l' ->
      and_sem (strict_list (map to_sval l)) (strict_list (map to_sval l')) =
      Some (strict_list (map to_sval (and_ev l l'))).
Proof.
  induction l; intros.
  destruct l'; simpl in *; try congruence.
  destruct l'; simpl in *; try congruence.
  assert (has_type (eseq l') (tseq (length l') tbit)). {
    econstructor. inversion H0. subst. inversion H4. eauto.
  }
  inversion H. inversion H0.
  inversion H8. inversion H5.
  subst. inversion H11. inversion H15.
  subst. simpl.
  erewrite IHl; eauto.
  econstructor; eauto.
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
  inversion H5. inversion H6.
  subst.
  eapply and_sem_ev; eauto.
  congruence.
Qed.

Lemma or_sem_ev :
  forall l,
    has_type (eseq l) (tseq (length l) tbit) ->
    forall l',
      has_type (eseq l') (tseq (length l') tbit) ->
      length l = length l' ->
      or_sem (strict_list (map to_sval l)) (strict_list (map to_sval l')) =
      Some (strict_list (map to_sval (or_ev l l'))).
Proof.
  induction l; intros.
  destruct l'; simpl in *; try congruence.
  destruct l'; simpl in *; try congruence.
  assert (has_type (eseq l') (tseq (length l') tbit)). {
    econstructor. inversion H0. subst. inversion H4. eauto.
  }
  inversion H. inversion H0.
  inversion H8. inversion H5.
  subst. inversion H11. inversion H15.
  subst. simpl.
  erewrite IHl; eauto.
  econstructor; eauto.
Qed.

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
  inversion H5. inversion H6.
  subst.
  eapply or_sem_ev; eauto.
  congruence.
Qed.

Lemma compl_sem_ev :
  forall l len,
    has_type (eseq l) (tseq len tbit) ->
    compl_sem (strict_list (map to_sval l)) = Some (to_sval (eseq (not_ev l))).
Proof.
  induction l; intros.
  reflexivity.
  inversion H. subst.
  inversion H2. subst. inversion H3.
  subst. simpl.
  erewrite IHl; eauto.
  econstructor; eauto.
Qed.

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
  subst res.
  eapply compl_sem_ev; eauto.
Qed.
  
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


Lemma rotr_ev_length :
  forall l n,
    length (rotr_ev l n) = length l.
Proof.
  intros. unfold rotr_ev.
  rewrite app_length.
  rewrite firstn_length.
  rewrite Min.min_l by omega.
  rewrite list_drop_length_eq by omega.
  omega.
Qed.

Lemma rotr_ev_Forall :
  forall P l,
    Forall P l ->
    forall n,
      Forall P (rotr_ev l n).
Proof.
  induction 1; intros.
  unfold rotr_ev.
  destruct n; simpl; econstructor.
  unfold rotr_ev.
  rewrite Forall_app. split.
  eapply list_drop_Forall; eauto.
  eapply firstn_Forall; eauto.
Qed.      

Lemma has_type_rotr :
  forall l len t,
    has_type (eseq l) (tseq len t) ->
    forall n,
      has_type (eseq (rotr_ev l n)) (tseq len t).
Proof.
  intros.
  inversion H.
  subst.
  erewrite <- (rotr_ev_length l); try econstructor; try omega.
  eapply rotr_ev_Forall; eauto.
Qed.

Lemma repeat_Forall :
  forall {A} (P : A -> Prop) x,
    P x ->
    forall n,
      Forall P (repeat x n).
Proof.
  induction n; intros.
  simpl. econstructor.
  simpl. econstructor; eauto.
Qed.

Lemma shiftr_ev_length :
  forall l n,
    length (shiftr_ev l n) = length l.
Proof.
  intros. unfold shiftr_ev.
  rewrite app_length.
  rewrite firstn_length.
  rewrite repeat_length.
  assert (n <= length l \/ n > length l)%nat by omega.
  destruct H.
  repeat rewrite Min.min_l by omega. omega.
  rewrite Min.min_r by omega.
  rewrite Min.min_l by omega.
  omega.
Qed.

Lemma shiftr_ev_Forall :
  forall P l,
    Forall P l ->
    forall n,
      P (ebit false) ->
      Forall P (shiftr_ev l n).
Proof.
  induction 1; intros.
  unfold shiftr_ev.
  destruct n; simpl; econstructor; eauto.
  
  unfold shiftr_ev.
  rewrite Forall_app. split.
  eapply repeat_Forall; eauto.
  eapply firstn_Forall; eauto.
Qed.      

Lemma has_type_shiftr :
  forall l len,
    has_type (eseq l) (tseq len tbit) ->
    forall n,
      has_type (eseq (shiftr_ev l n)) (tseq len tbit).
Proof.
  intros.
  inversion H.
  subst.
  erewrite <- (shiftr_ev_length l); try econstructor; try omega.
  eapply shiftr_ev_Forall; eauto.
  econstructor; eauto.
Qed.

