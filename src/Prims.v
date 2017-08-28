Require Import String.

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

Require Import Cryptol.ExtToBitvector.

Import HaskellListNotations.
Require Import List.
Import ListNotations.
Require Import Cryptol.Builtins.
Require Import Program.

Fixpoint lt_ev (l r : ext_val) : ext_val :=
  match l, r with
  | eseq l, eseq r =>
    let f x : option bool := match x with | ebit b => Some b | _ => None end in
    match to_bitlist ext_val f (length l) l, to_bitlist ext_val f (length l) r with
    | Some a, Some b => if zlt a b then (ebit true) else (ebit false)
    | _,_ => eseq nil
    end
  | _,_ => eseq nil
  end.

Lemma lt_eval :
  forall id GE TE SE,
    GE (id,"<") = Some (mb 1 2 Lt) ->
    SE (id,"<") = None ->
    forall ta tv a1 a2 v1 v2,
      eager_eval_type GE TE ta tv ->
      eager_eval_expr GE TE SE a1 (to_sval (eseq v1)) ->
      eager_eval_expr GE TE SE a2 (to_sval (eseq v2)) ->
      has_type (eseq v1) (tseq (length v1) tbit) ->
      has_type (eseq v2) (tseq (length v2) tbit) ->
      forall res,
        res = to_sval (lt_ev (eseq v1) (eseq v2)) ->
        eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"<")) (ETyp ta)) a1) a2) res.
Proof.
  intros.
  e. e. e. ag.
  e. e. e. e; try lv; try congruence.
  simpl. subst res.

  (* TODO: this proof *)
Admitted.
  

Fixpoint eq_ev (l r : ext_val) : ext_val :=
  let fix list_eq_ev x y :=
      match x,y with
      | nil,nil => ebit true
      | a :: aa, b :: bb =>
        match eq_ev a b, list_eq_ev aa bb with
        | ebit true, ebit true => ebit true
        | _ , _ => ebit false
        end
      | _ , _ => ebit false
      end in
  let fix list_pair_eq_ev x y :=
      match x,y with
      | nil,nil => ebit true
      | (_,a) :: aa, (_,b) :: bb =>
        match eq_ev a b, list_pair_eq_ev aa bb with
        | ebit true, ebit true => ebit true
        | _ , _ => ebit false
        end
      | _ , _ => ebit false
      end in
  match l,r with
  | ebit b, ebit b' => ebit (eqb b b')
  | eseq l', eseq r' => list_eq_ev l' r'
  | etup l', etup r' => list_eq_ev l' r'
  | erec sl', erec sr' => list_pair_eq_ev sl' sr'
  | _,_ => ebit false
  end.

(* TODO: update eq_sem so this is true *)
Lemma eq_sem_equiv :
  forall ev1 ev2,
    eq_sem (to_sval ev1) (to_sval ev2) = Some (to_sval (eq_ev ev1 ev2)).
Proof.
Admitted.

Lemma eq_eval :
  forall id GE TE SE,
    GE (id,"==") = Some (mb 1 2 Eq) ->
    SE (id,"==") = None ->
    forall ta tv a1 a2 v1 v2,
      eager_eval_type GE TE ta tv ->
      eager_eval_expr GE TE SE a1 (to_sval v1) ->
      eager_eval_expr GE TE SE a2 (to_sval v2) ->
      forall res,
        res = to_sval (eq_ev v1 v2) ->
        eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"==")) (ETyp ta)) a1) a2) res.
Proof.
  intros. e. e. e. ag.
  e. e. e. e; try lv.
  simpl. subst res.
  eapply eq_sem_equiv; eauto.
Qed.

Definition fromTo_ev (lo hi width : Z) : ext_val :=
  eseq (map eseq (map from_bitv (map (@repr (Z.to_nat width)) (zrange lo (hi + 1))))).


Lemma strict_list_to_sval_map :
  forall l,
    map strict_list (map (map to_sval) l) = map to_sval (map eseq l).
Proof.
  induction l; intros.
  simpl. auto.
  simpl. f_equal. auto.
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

Lemma same_from_bitv :
  forall {w} (l : BitV w),
    StrictToBitvector.from_bitv l = map to_sval (from_bitv l).
Proof.
  intros. remember (from_bitv l) as x.
  symmetry in Heqx.
  rewrite <- tobit_frombit_equiv in Heqx.
  rewrite <- StrictToBitvector.tobit_frombit_equiv.
  eapply same_bitv; eauto.
Qed.

Lemma strict_from_bitv :
  forall w (l : list (BitV w)),
    map StrictToBitvector.from_bitv l = map (map to_sval) (map from_bitv l).
Proof.
  induction l; intros;
    simpl; auto.
  f_equal; eauto.
  eapply same_from_bitv; eauto.
Qed.

Definition binop_ev (op : Z -> Z -> Z) (l r : ext_val) : ext_val :=
  match l,r with
  | eseq l, eseq r => 
    let f x : option bool := match x with | ebit b => Some b | _ => None end in
    match binop ext_val f ebit op (length l) l r with
    | Some res => eseq res
    | _ => eseq nil
    end
  | _,_ => eseq nil
  end.

Definition plus_ev := binop_ev Z.add.

  

Lemma to_bitv_succeeds :
  forall l,
    has_type (eseq l) (tseq (Datatypes.length l) tbit) ->
    exists (bv : BitV (Datatypes.length l)),
      to_bitv l = Some bv.
Proof.
  induction l; intros.
  simpl. eauto.
  simpl. edestruct IHl.
  inversion H. inversion H2.
  econstructor; eauto.
  inversion H. subst. inversion H3.
  subst.
  inversion H4. subst.
  rewrite H0. eauto.
Qed.


Lemma to_bitlist_succeeds :
  forall T f l,
    Forall (fun x => f x <> None) l ->
    exists x,
      to_bitlist T f (length l) l = Some x.
Proof.
  induction l; intros.
  simpl. eauto.
  simpl. inversion H. subst.
  destruct (f a) eqn:?; try congruence.
  eapply IHl in H3. destruct H3.
  rewrite H0. eauto.
Qed.

Lemma to_bitlist_sval :
  forall l,
    has_type (eseq l) (tseq (length l) tbit) ->
    exists x,
      to_bitlist strictval (fun x => match x with | sbit b => Some b | _ => None end) (length (map to_sval l)) (map to_sval l) = Some x.
Proof.
  induction l; intros.
  simpl. eauto.
  simpl.
  inversion H.
  subst.
  inversion H2.
  subst.
  inversion H3. subst.
  simpl.
  edestruct IHl; eauto.
  econstructor; eauto.
  rewrite H0. eauto.
Qed.

Lemma has_type_seq :
  forall l len t,
    Forall (fun x => has_type x t) l ->
    len = length l ->
    has_type (eseq l) (tseq len t).
Proof.
  intros. subst. econstructor; eauto.
Qed.

Lemma binop_ev_succeeds :
  forall l l',
    has_type (eseq l) (tseq (length l) tbit) ->
    has_type (eseq l') (tseq (length l) tbit) ->
    forall op,
    exists l0,
      binop_ev op (eseq l) (eseq l') = eseq l0 /\ has_type (eseq l0) (tseq (length l) tbit).
Proof.
  induction l; intros.
  simpl in *. inversion H0. subst.
  destruct l'; simpl in *; try congruence.
  eauto.
  inversion H. inversion H0.
  subst.
  destruct l'; simpl in *; try congruence.
  inversion H3. inversion H6. subst.
  unfold binop. simpl.
  inversion H4. subst. simpl.
  inversion H10. subst.
  edestruct to_bitlist_succeeds.
  Focus 2. erewrite H1.
  edestruct to_bitlist_succeeds.
  Focus 2.
  inversion H5.
  erewrite H2.
  eexists; split. reflexivity.
  simpl.
  eapply has_type_seq.
  econstructor. econstructor.
  admit. (* it's true *)
  simpl. f_equal.
  admit. (* also true *)
Admitted.  
  
  
Lemma plus_ev_succeeds :
  forall l l',
    has_type (eseq l) (tseq (length l) tbit) ->
    has_type (eseq l') (tseq (length l) tbit) ->
    exists l0,
      plus_ev (eseq l) (eseq l') = eseq l0 /\ has_type (eseq l0) (tseq (length l) tbit).
Proof.
  unfold plus_ev.
  intros.
  eapply binop_ev_succeeds; eauto.
Qed.

Lemma plus_eval :
  forall id GE TE SE,
    GE (id,"+") = Some (mb 1 2 Plus) ->
    SE (id,"+") = None ->
    forall ta tv a1 a2 v1 v2 len,
      eager_eval_type GE TE ta tv ->
      eager_eval_expr GE TE SE a1 (to_sval (eseq v1)) ->
      eager_eval_expr GE TE SE a2 (to_sval (eseq v2)) ->
      has_type (eseq v1) (tseq len tbit) ->
      has_type (eseq v2) (tseq len tbit) ->
      forall res,
        res = to_sval (plus_ev (eseq v1) (eseq v2)) ->
        eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"+")) (ETyp ta)) a1) a2) res.
Proof.
  intros.
  assert (len = (length v1)) by (inversion H4; congruence).
  assert (len = (length v2)) by (inversion H5; congruence).
  rewrite H7 in H4.
  rewrite H8 in H5.
  eapply to_bitlist_sval in H4.
  eapply to_bitlist_sval in H5.
  destruct H4. destruct H5.
  subst.

  e. e. e. ag.
  e. e. e. e; try lv.

  unfold strict_builtin_sem.
  unfold plus_sem.
  unfold binop_sem.
  repeat rewrite list_of_strictval_of_strictlist.
  unfold plus_ev.
  unfold binop.
  rewrite H4.
  replace (length (map to_sval v1)) with (length (map to_sval v2)) by (repeat rewrite map_length; congruence).
  rewrite H5.
  unfold binop_ev.
  f_equal.
  unfold binop.

  (* admit for now, very provable though, probably want to use a general lemma about binop *)
  (* that will let us prove this for lots of things *)
Admitted.


Definition minus_ev := binop_ev Z.sub.

Lemma minus_ev_succeeds :
  forall l l',
    has_type (eseq l) (tseq (length l) tbit) ->
    has_type (eseq l') (tseq (length l) tbit) ->
    exists l0,
      minus_ev (eseq l) (eseq l') = eseq l0 /\ has_type (eseq l0) (tseq (length l) tbit).
Proof.
  intros.
  eapply binop_ev_succeeds; eauto.
Qed.

Lemma minus_eval :
  forall id GE TE SE,
    GE (id,"-") = Some (mb 1 2 Minus) ->
    SE (id,"-") = None ->
    forall ta tv a1 a2 v1 v2 len,
      eager_eval_type GE TE ta tv ->
      eager_eval_expr GE TE SE a1 (to_sval (eseq v1)) ->
      eager_eval_expr GE TE SE a2 (to_sval (eseq v2)) ->
      has_type (eseq v1) (tseq len tbit) ->
      has_type (eseq v2) (tseq len tbit) ->
      forall res,
        res = to_sval (minus_ev (eseq v1) (eseq v2)) ->
        eager_eval_expr GE TE SE (EApp (EApp (ETApp (EVar (id,"-")) (ETyp ta)) a1) a2) res.
Proof.
  intros.
  e. e. e. ag.
  e. e. e. e; try lv.
  simpl.

  (* Proof should work once minus_sem is implemented *)
(*  unfold minus_sem.
  repeat rewrite list_of_strictval_of_strictlist.
  repeat rewrite map_length.
  repeat erewrite same_bitv by eassumption.
  f_equal. subst.
  simpl.
  erewrite same_from_bitv; eauto.*)
Admitted.

Lemma fromTo_eval :
  forall id GE TE SE,
    GE (id,"fromTo") = Some (mb 3 0 fromTo) ->
    SE (id,"fromTo") = None ->
    forall ta1 ta2 ta3 lo hi width res,
      eager_eval_type GE TE ta1 (tvnum lo) ->
      eager_eval_type GE TE ta2 (tvnum hi) ->
      eager_eval_type GE TE ta3 (tvnum width) ->
      res = to_sval (fromTo_ev lo hi width) ->
      eager_eval_expr GE TE SE (ETApp (ETApp (ETApp (EVar (id,"fromTo")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) res.
Proof.
  intros.
  e. e. e. ag.
  e. e. e. e.
  
  simpl.
  subst res. unfold fromTo_sem.
  unfold fromTo_ev.
  f_equal.
  simpl. f_equal.
  rewrite <- strict_list_to_sval_map. f_equal.
  rewrite strict_from_bitv; eauto.
Qed.

Fixpoint zero_ev (t : Tval) : ext_val :=
  match t with
  | tvrec lst => eseq nil
  (*srec (combine (map fst lst) (map zero_sem (map snd lst)))*)
  | tvtup l => eseq nil
  (*stuple (map zero_sem l)*)
  | tvseq (tvnum n) t' => eseq (repeat (zero_ev t') (Z.to_nat n))
  | tvseq _ _ => eseq nil
  | tvfun _ _ => eseq nil
  | tvnum _ => eseq nil
  | tvbit => (ebit false)
  | tvinf => eseq nil
  end.

Lemma zero_eval :
  forall id GE TE SE,
    GE (id,"zero") = Some (mb 1 0 Zero) ->
    SE (id,"zero") = None ->
    forall ta n res,
      eager_eval_type GE TE ta (tvseq (tvnum n) tvbit) ->
      res = to_sval (zero_ev (tvseq (tvnum n) tvbit)) ->
      eager_eval_expr GE TE SE (ETApp (EVar (id,"zero")) (ETyp ta)) res.
Proof.
  intros.
  e. ag.
  e. e.
  subst res. simpl. f_equal. f_equal.
  rewrite map_repeat.
  reflexivity.
Qed.

Definition split_ev (n : nat) (l : ext_val) : ext_val :=
  match l with
  | eseq l =>
    eseq (map eseq (get_each_n n l))
  | _ => eseq nil
  end.


Lemma split_eval :
  forall id GE TE SE,
    GE (id,"split") = Some (mb 3 1 split) ->
    SE (id,"split") = None ->
    forall ta1 ta2 ta3 n tv1 tv3 exp v t len,
      eager_eval_type GE TE ta1 tv1 ->
      eager_eval_type GE TE ta2 (tvnum n) ->
      eager_eval_type GE TE ta3 tv3 ->
      eager_eval_expr GE TE SE exp (to_sval v) ->
      has_type v (tseq len t) ->
        forall res,
          res = to_sval (split_ev (Z.to_nat n) v) ->
          eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (EVar (id,"split")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) exp) res.
Proof.
  intros.
  inversion H5. subst.
  e. e. e. e. ag.
  e. e. e. e. e. lv.
  simpl.
  rewrite list_of_strictval_of_strictlist.
  f_equal. f_equal.
  rewrite get_each_n_map_commutes.
  eapply strict_list_to_sval_map.
Qed.

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
  forall id GE TE SE,
    GE (id, "splitAt") = Some (mb 3 1 splitAt) ->
    SE (id, "splitAt") = None ->
    forall va ta1 ta2 ta3 l n tr2 tr3,
      eager_eval_type GE TE ta1 (tvnum n) ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va (to_sval (eseq l)) ->
      0 <= n <= Z.of_nat (Datatypes.length l) ->
      eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (EVar (id,"splitAt")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va)
                      (stuple (map to_sval (splitAt_model (Z.to_nat n) l))).
Proof.
  intros. 
  e. e. e. e. ag.
  e. e. e. e. e. lv.
  simpl.
  eapply splitAt_sem_res; eauto.
Qed.




Lemma take_eval :
  forall tid sid fid bid eid p1id xid p2id p0id GE TE SE,
    GE (tid, "take") =
    Some
      (ETAbs (fid, "front")
             (ETAbs (bid, "back")
                    (ETAbs (eid, "elem")
                           (EAbs (p1id, "__p1")
                                 (EWhere (EVar (xid, "x"))
                                         [NonRecursive
                                            (Decl (p2id, "__p2")
                                                  (DExpr
                                                     (EApp
                                                        (ETApp
                                                           (ETApp (ETApp (EVar (sid, "splitAt")) (ETyp (TVar (TVBound fid KNum))))
                                                                  (ETyp (TVar (TVBound bid KNum)))) (ETyp (TVar (TVBound eid KType))))
                                                        (EVar (p1id, "__p1"))))),
                                          NonRecursive (Decl (xid, "x") (DExpr (ESel (EVar (p2id, "__p2")) (TupleSel 0)))),
                                          NonRecursive (Decl (p0id, "__p0") (DExpr (ESel (EVar (p2id, "__p2")) (TupleSel 1))))]))))) ->
    SE (tid, "take") = None ->
    GE (sid, "splitAt") = Some (mb 3 1 splitAt) ->
    SE (sid, "splitAt") = None ->
    xid <> p0id ->
    p2id <> p0id ->
    p1id <> p0id ->
    p1id <> xid ->
    p2id <> xid ->
    p1id <> p2id ->
    sid <> p0id ->
    sid <> xid ->
    sid <> p2id ->
    sid <> p1id ->
    fid <> eid ->
    fid <> bid ->
    bid <> eid ->
    forall va ta1 ta2 ta3 tr2 tr3 n l,
      eager_eval_type GE TE ta1 (tvnum n) ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va (to_sval (eseq l)) ->
      0 <= n <= Z.of_nat (Datatypes.length l) ->
      forall res,
        res = (to_sval (take_model (Z.to_nat n) l)) ->
      eager_eval_expr GE TE SE (EApp (ETApp (ETApp (ETApp (EVar (tid,"take")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va) res.
Proof.
  intros. subst res.

  e. e. e. e. ag.
  e. e. e. e.
  e. g. simpl.
  break_if; simpl in *; try congruence.
  break_if; simpl in *; try congruence.
  simpl.
  unfold extend.
  break_if; simpl in *; try congruence.
  break_if; simpl in *; try congruence.
  reflexivity.
  e. g.
  simpl.
  break_if; simpl in *; try congruence.
  break_if; simpl in *; try congruence.
  break_if; simpl in *; try congruence.
  simpl. unfold extend.
  break_if; simpl in *; try congruence.
  break_if; simpl in *; try congruence.
  break_if; simpl in *; try congruence.
  reflexivity.
  
  eapply splitAt_eval; eauto; try et.
  simpl. unfold extend.
  repeat (break_if; simpl in *; try congruence).
  simpl. unfold extend.
  repeat (break_if; simpl in *; try congruence).
  simpl. unfold extend.
  econstructor.
  repeat (break_if; simpl in *; try congruence).
  simpl. unfold extend.
  econstructor.
  repeat (break_if; simpl in *; try congruence);
  reflexivity.
  simpl. unfold extend.
  econstructor.
  break_if; simpl in *; try congruence.
  reflexivity.
  simpl. unfold extend.
  eapply eager_eval_local_var.
  repeat (break_if; simpl in *; try congruence).

  unfold splitAt_model. simpl.
  reflexivity.
Qed.


Lemma append_eval :
  forall id GE TE SE,
    GE (id, "#") = Some (mb 3 2 Append) ->
    SE (id, "#") = None ->
    forall va1 va2 l l' ta1 ta2 ta3 tr1 tr2 tr3 res,
      eager_eval_type GE TE ta1 tr1 ->
      eager_eval_type GE TE ta2 tr2 ->
      eager_eval_type GE TE ta3 tr3 ->
      eager_eval_expr GE TE SE va1 (to_sval (eseq l)) ->
      eager_eval_expr GE TE SE va2 (to_sval (eseq l')) ->
      res = to_sval (eseq (l ++ l')) ->
      eager_eval_expr GE TE SE (EApp (EApp (ETApp (ETApp (ETApp (EVar (id,"#")) (ETyp ta1)) (ETyp ta2)) (ETyp ta3)) va1) va2) res.
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

