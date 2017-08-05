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
Require Import Eager.
Require Import Bitstream.
Require Import GlobalExtends.
Require Import Lib.
Require Import GetEachN.

Require Import EvalTac.

Import HaskellListNotations.
Open Scope string.

Require Import HMAC.



(* Model of HMAC *)
(* Now we can use ext_val to characterize the inputs to HMAC *)
(* As well, we can simply write HMAC over ext_val *)

Fixpoint xor_const_list (idx : Z) (const : Z) (l : list ext_val) : list ext_val :=
  match l with
  | nil => nil
  | (ebit b) :: r =>
    let r' := xor_const_list (idx - 1) const r in
    let b' := Z.testbit const idx in
    (ebit (xorb b b')) :: r'
  | _ => nil
  end.

Definition xor_const (const : Z) (e : ext_val) : ext_val :=
  match e with
  | eseq l => eseq (xor_const_list ((Z.of_nat ((Datatypes.length l)) - 1)) const l)
  | _ => ebit false
  end.


(* Model of hmac, given model of hash *)
Definition hmac_model (hf : ext_val -> ext_val) (key msg : ext_val) :=
    match key, msg with
    | eseq keyl, eseq msgl =>
      match hf (eseq ((map (fun x => xor_const 54 x) keyl) ++ msgl)) with
      | eseq x3 =>
        Some (hf (eseq (map (xor_const 92) keyl ++ map eseq (get_each_n (Pos.to_nat 8) x3))))
      | _ => None
      end
    | _,_ => None
    end.
  

(* TODO: is this the right definition of a good hash? *)
(* *)
Definition good_hash (h : Expr) (ge : genv) (T : tenv) (SE : senv) (hf : ext_val -> ext_val) : Prop :=
  (exists id exp TE E,
      eager_eval_expr ge T SE h (sclose id exp TE E) /\ (* can evaluate the hash to a closure *)
      forall n v,
        has_type v (bytestream n) ->
        eager_eval_expr ge TE (extend E id (to_sval v)) exp (to_sval (hf v)) /\ exists n, has_type (hf v) (tseq n tbit)
  
  ) /\ (    forall x l,
      hf x = eseq l ->
      Nat.divide 8 (Datatypes.length l)).


(* TODO: massage into good_hash defn *)
Lemma good_hash_fully_padded :
  forall h GE TE SE hf,
    good_hash h GE TE SE hf ->
    forall x l,
      hf x = eseq l ->
      Nat.divide 8 (Datatypes.length l).
Proof.
  intros. unfold good_hash in H. destruct H. eauto.
Qed.

Lemma good_hash_eval :
  forall h GE T SE hf,
    good_hash h GE T SE hf ->
    exists id exp TE E,
      eager_eval_expr GE T SE h (sclose id exp TE E).
Proof.
  intros. unfold good_hash in *.
  do 6 destruct H.
  eauto.
Qed.

Lemma good_hash_complete_eval :
  forall h GE T SE hf,
    good_hash h GE T SE hf ->
    exists id exp TE E,
      eager_eval_expr GE T SE h (sclose id exp TE E) /\
      forall n v,
        has_type v (bytestream n) ->
        eager_eval_expr GE TE (extend E id (to_sval v)) exp (to_sval (hf v)) /\ exists n, has_type (hf v) (tseq n tbit).
Proof.
  intros. unfold good_hash in *.
  do 6 destruct H.
  do 4 eexists. split; eauto.
Qed.



(* lowercase is concrete, uppercase is abstract *)
(* wf_env lets this proof be used over a variety of environments that meet the proper constraints *)
Definition wf_env (ge GE : genv) (TE : tenv) (SE : senv)  : Prop :=
  name_irrel ge /\ name_irrel GE /\ name_irrel TE /\ name_irrel SE /\
  (forall id,
      ge id <> None -> (TE id = None /\ SE id = None /\ ge id = GE id)).

Lemma wf_env_name_irrel_GE :
  forall ge GE TE SE ,
    wf_env ge GE TE SE ->
    name_irrel GE.
Proof.
  intros. unfold wf_env in *. intuition.
Qed.

Lemma good_hash_same_eval :
  forall h GE TE SE hf,
    good_hash h GE TE SE hf ->
    forall v,
      eager_eval_expr GE TE SE h v ->
      forall GE' TE' SE' h',
        eager_eval_expr GE' TE' SE' h' v ->
        good_hash h' GE' TE' SE' hf.
Proof.
  (* needs determinacy of eager_eval_expr, which is true but unproven *)
Admitted.

Lemma name_irrel_extend :
  forall {A} E id (x : A),
    name_irrel E ->
    name_irrel (extend E id x).
Proof.
  intros. unfold name_irrel in *.
  intros.
  specialize (H id0 id').
  destruct (ident_eq id0 id') eqn:?; auto.
  unfold extend.
  destruct (ident_eq id0 id);
    destruct (ident_eq id' id); auto.
  rewrite e in e0. congruence.
  rewrite e in n. congruence.
Qed.


Lemma name_irrel_erase :
  forall {A} (E : ident -> option A) id,
    name_irrel E ->
    name_irrel (fun x => if ident_eq x id then None else E x).
Proof.
  intros.
  unfold name_irrel in *.
  intros.
  specialize (H id0 id').
  destruct (ident_eq id0 id'); auto.
  rewrite H.
  destruct (ident_eq id0 id);
    destruct (ident_eq id' id);
    auto; congruence.
Qed.

(*
Lemma extend_other_name_irrel :
  forall {A} l id0 GE,
    Forall (fun id => GE id = None) l ->
    ~ In (fst id0) (map fst l) ->
    forall (v : A),
      Forall (fun id => extend GE id0 v id = None) l.
Proof.
  induction 1; intros.
  econstructor.
  destruct id0. unfold map in H1. fold (map fst l) in H1.
  destruct x. unfold fst in H1. fold (@fst Z string) in H1.
  erewrite not_in_cons in H1.
  destruct H1.
  econstructor; try eapply IHforall; eauto.
  
  unfold extend. destruct (ident_eq (z0,s0) (z,s)); try congruence.
  simpl in e. congruence.
Qed.
*)

Lemma wf_env_extend_GE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = None ->
      wf_env ge (extend GE id exp) TE SE.
Proof.
  intros.
  unfold wf_env in *.
  intros.
  destruct H.
  destruct H1.
  destruct H2. destruct H3.
  split; auto.
  split; auto.

  eapply name_irrel_extend; eauto.
  
  split; auto.
  split; auto.

  intros.
  remember H5 as Hcontra.
  clear HeqHcontra.
  eapply H4 in H5.
  intuition.
  rewrite H8.
  edestruct (name_irrel_diff_results _ id0 id H); try congruence.
  unfold extend. erewrite H7.
  reflexivity.
Qed.

Lemma wf_env_extend_TE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = None ->
      wf_env ge GE (extend TE id exp) SE.
Proof.
  intros.
  unfold wf_env in *.
  intros.
  destruct H. destruct H1.
  destruct H2. destruct H3.
  split; auto.
  split; auto.
  split; auto.
  eapply name_irrel_extend; eauto.
  
  split; auto.

  intros.
  
  remember H5 as Hcontra.
  clear HeqHcontra.
  eapply H4 in H5.
  intuition.
  edestruct (name_irrel_diff_results _ id0 id H); try congruence.  

  unfold extend. erewrite H7.
  assumption.
Qed.

Lemma wf_env_extend_SE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = None ->
      wf_env ge GE TE (extend SE id exp).
Proof.
  intros.
  unfold wf_env in *.
  intros.
  destruct H. destruct H1.
  destruct H2. destruct H3.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  eapply name_irrel_extend; eauto.

  intros.

  remember H5 as Hcontra.
  clear HeqHcontra.
  eapply H4 in H5.
  intuition.
  edestruct (name_irrel_diff_results _ id0 id H); try congruence.  

  unfold extend. erewrite H7.
  assumption.
Qed.

Lemma wf_env_erase_SE :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id,
      wf_env ge GE TE (fun x => if ident_eq x id then None else SE x).
Proof.
  intros. unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  eapply name_irrel_erase; eauto.

  intros. remember H4 as Hcontra.
  clear HeqHcontra.
  eapply H3 in H4.
  split; intuition.
  
  rewrite H4.

  destruct (ident_eq id0 id); auto.

Qed.

Lemma wf_env_global :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      GE id = Some exp.
Proof.
  intros. unfold wf_env in *.
  destruct H. destruct H1.
  destruct H2. destruct H3.
  destruct (H4 id); try congruence.
  intuition.
  congruence.
Qed.

Lemma wf_env_not_local :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      SE id = None.
Proof.
  intros. unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  destruct (H4 id); try congruence.
  intuition.
Qed.

Lemma wf_env_not_type :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      TE id = None.
Proof.
  intros. unfold wf_env in *.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         end.
  destruct (H4 id); try congruence.
Qed.


(* Eager tactics *)
(* TODO: standardize *)
Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac fg := eapply eager_eval_global_var; [ reflexivity | eassumption | idtac].
Ltac g := eapply eager_eval_global_var; try eassumption; try reflexivity.
Ltac ag := g; [eapply wf_env_not_local; eauto; reflexivity | eapply wf_env_global; eauto; simpl; reflexivity | idtac].

Ltac et :=
  match goal with
  | [ |- eager_eval_type _ _ _ _ ] => solve [repeat econstructor; eauto]
  end.

Ltac e :=
  match goal with
  | [ |- eager_eval_expr ?GE _ ?E (EVar ?id) _ ] =>
    (try fg); (try reflexivity);
    (try solve [eapply eager_eval_local_var; reflexivity]);
    fail 1 "couldn't figure out variable"
  | [ |- _ ] => ec; try solve [et]
  end.



Definition typenum (n : Z) : Expr := ETyp (TCon (TC (TCNum n)) []).

Ltac abstract_globals ge :=
  repeat match goal with
         | [ H : ge _ = _ |- _ ] => eapply wf_env_global in H; eauto
         end.




Lemma eager_eval_bind_senvs :
  forall l model GE TE exp SE id,
    (Forall (fun x => has_type x byte) l) ->
    (forall ev, has_type ev byte -> eager_eval_expr GE TE (extend SE id (to_sval ev)) exp (model ev)) ->
    Forall2 (fun se => eager_eval_expr GE TE se exp)
            (bind_senvs SE (map (fun sv => [(id,sv)]) (map to_sval l))) (map model l).
Proof.
  induction l; intros.
  econstructor; eauto.
  
  inversion H. subst.
  eapply IHl in H4.
  simpl. econstructor; [idtac | eassumption].
  eapply H0. eauto.
  intros. eapply H0. eauto.
Qed.


Lemma strictval_from_bitv'_widen :
  forall a b n z,
    (a >= n)%nat ->
    (b >= n)%nat ->
    strictval_from_bitv' a n (@repr a z) = strictval_from_bitv' b n (@repr b z).
Proof.
  induction n; intros.
  simpl. reflexivity.

  simpl.
  f_equal. f_equal.
  assert (Z.of_nat (S n) > Z.of_nat n).
  simpl. rewrite Zpos_P_of_succ_nat. omega.
  erewrite testbit_widen.
  symmetry.
  erewrite testbit_widen.
  reflexivity.
  eassumption.
  assumption.
  eassumption.
  assumption.
  eapply IHn; eauto; omega.
Qed.

Lemma strictval_from_bitv_norm :
  forall x n z,
    (x >= n)%nat ->
    strictval_from_bitv' x n (@repr x z) = strictval_from_bitv' n n (@repr n z).
Proof.
  intros.
  erewrite strictval_from_bitv'_widen; eauto.
Qed.


Lemma testbit_unsigned_repr :
  forall w z idx,
    Z.of_nat w > idx ->
    Z.testbit (@unsigned w (@repr w z)) idx = Z.testbit z idx.
Proof.
  induction w; intros;
    simpl.
  * assert (idx < 0) by (simpl in H; omega).
    destruct idx; simpl in H0; try omega.
    remember (Zgt_pos_0 p) as HH. omega.
    simpl. reflexivity.
  * rewrite Z_mod_modulus_eq; try omega.
    unfold modulus.
    rewrite two_power_nat_equiv.
    rewrite Z.mod_pow2_bits_low;
      try omega.
    reflexivity.
Qed.



Lemma xor_num :
  forall  l n z,
    has_type (eseq l) (tseq (Datatypes.length l) tbit) ->
    n = Datatypes.length l ->
    xor_sem (strict_list (map to_sval l)) (strict_list (strictval_from_bitv (@repr n z))) = Some (to_sval (xor_const z (eseq l))).
Proof.
  induction l; intros.
  simpl in *.
  unfold strictval_from_bitv. subst n.
  simpl. reflexivity.

  assert (has_type (eseq l) (tseq (Datatypes.length l) tbit)).
  {
    inversion H. econstructor; eauto. inversion H3. auto.
    
  }
  inversion H. subst.
  inversion H4. subst.
  inversion H3. subst.
  
  unfold strictval_from_bitv in *.
  unfold strictval_from_bitv'. fold strictval_from_bitv'.
  repeat rewrite length_cons.
  repeat rewrite map_cons.
  unfold strict_list. fold strict_list.
  unfold to_sval at 1.   unfold xor_sem. fold xor_sem.
  unfold strictval_from_bitv'. fold strictval_from_bitv'.
  unfold strict_list. fold strict_list.
  
  repeat rewrite strictval_from_bitv_norm by (eauto; try omega).
  repeat match goal with
         | [ |- context[(Z.of_nat (?X - 0))] ] => 
           replace (X - 0)%nat with X by omega
         end.
  rewrite IHl; eauto.
  f_equal.
  unfold xor_const. rewrite length_cons.
  unfold xor_const_list.
  fold xor_const_list.
  unfold to_sval.
  unfold strict_list.
  fold strict_list.
  fold to_sval.
  rewrite map_cons.
  unfold strict_list.
  fold strict_list.
  repeat rewrite succ_nat_pred.
  f_equal.
  
  unfold xorb.
  unfold testbit.
  rewrite testbit_unsigned_repr by (simpl; rewrite Zpos_P_of_succ_nat; omega).
  destruct b; try reflexivity.
  destruct (Z.testbit z (Z.of_nat (Datatypes.length l))); reflexivity.
Qed.



Lemma ext_val_list_of_strictval :
  forall ev n t,
    has_type ev (tseq n t) ->
    exists l,
      list_of_strictval (to_sval ev) = Some (map to_sval l).
Proof.
  intros.
  destruct ev; try solve [inversion H].
  simpl. rewrite list_of_strictval_of_strictlist.
  eauto.
Qed.

Lemma xor_const_list_length_pres :
  forall l z n,
    Forall (fun b => has_type b tbit) l ->
    Datatypes.length (xor_const_list z n l) = Datatypes.length l.
Proof.
  induction l; intros;
    simpl. reflexivity.
  destruct a; simpl. rewrite IHl; eauto.
  inversion H. eauto.
  inversion H. inversion H2.
  inversion H. inversion H2.
  inversion H. inversion H2.
Qed.


Lemma xor_const_byte :
  forall ev,
    has_type ev byte ->
    forall n,
      has_type (xor_const n ev) byte.
Proof.
  intros.
  inversion H.
  subst.
  do 9 (destruct l; simpl in H0; try omega).
  clear H0.
  repeat match goal with
         | [ H : Forall _ _ |- _ ] => inversion H; clear H; subst
         end.
  repeat match goal with
         | [ H : has_type _ tbit |- _ ] => inversion H; clear H
         end; subst.
  
  unfold xor_const.
  unfold byte.
  replace 8%nat with (Datatypes.length [ebit b6, ebit b5, ebit b4, ebit b3, ebit b2, ebit b1, ebit b0, ebit b]) by (simpl; auto).
  erewrite <- xor_const_list_length_pres.
  econstructor.
  simpl.
  repeat econstructor; eauto.
  repeat econstructor; eauto.
Qed.




Lemma strict_list_map_to_sval :
  forall l,
    strict_list (map to_sval l) = to_sval (eseq l).
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma map_strict_list_map_map_to_sval :
  forall l,
    map strict_list (map (map to_sval) l) = map to_sval (map eseq l).
Proof.
  induction l; intros; simpl; auto.
  f_equal. assumption.
Qed.


Lemma to_sval_list_pair_equiv :
  forall f,
    to_sval_list_pair f = combine (map fst f) (map to_sval (map snd f)).
Proof.
  induction f; intros; simpl; auto.
  destruct a. simpl. f_equal. auto.
Qed.


Lemma to_sval_injective :
  forall ev1 ev2,
    to_sval ev1 = to_sval ev2 ->
    ev1 = ev2.
Proof.
  induction ev1 using ext_val_ind_mut; intros; simpl in *;
    destruct ev2; simpl in *; try congruence;
      try solve [
            destruct l; simpl in *; try congruence].
  f_equal.
  eapply strict_list_injective in H0.
  eapply map_injective_function; eauto.
  destruct l0; simpl in H0; congruence.
  inversion H0. f_equal.
  eapply map_injective_function; eauto.
  fold to_sval_list_pair in *.
  inversion H0. clear H0.
  f_equal.
  repeat erewrite to_sval_list_pair_equiv in *.
  eapply combine_injective in H2; repeat rewrite list_length_map; auto.
  destruct H2.
  eapply map_injective_function in H1; eauto.
  eapply list_pair_parts_eq; eauto.
Qed.

Lemma list_of_strictval_to_sval :
  forall l' l,
    list_of_strictval (to_sval l) = Some (map to_sval l') ->
    l = eseq l'.
Proof.
  induction l'; intros; simpl in *; try congruence.
  * destruct l; simpl in H; try congruence.
    rewrite list_of_strictval_of_strictlist in H. inversion H.
    destruct l; simpl in H1; congruence.
  * destruct l; simpl in H; try congruence.
    rewrite list_of_strictval_of_strictlist in H. inversion H.
    f_equal.
    destruct l; simpl in *; try congruence.
    specialize (IHl' (eseq l)).
    simpl in IHl'.
    rewrite list_of_strictval_of_strictlist in IHl'.
    assert (eseq l = eseq l'). eapply IHl'. f_equal. inversion H1. eauto.
    inversion H0. f_equal.
    inversion H1.
    eapply to_sval_injective; eauto.
Qed.

Lemma has_type_seq_append :
  forall l l' t,
    (exists n, has_type (eseq l) (tseq n t)) ->
    (exists n, has_type (eseq l') (tseq n t)) ->
    (exists n, has_type (eseq (l ++ l')) (tseq n t)).
Proof.
  induction l; intros.
  simpl; auto.
  simpl. destruct H. destruct H0.
  inversion H. inversion H3.
  subst.
  inversion H0. subst.
  eexists. econstructor.
  econstructor; eauto.
  eapply Forall_app; eauto.
Qed.

Lemma eq_is_refl :
  forall {ws} (bv : BitV ws),
    eq_sem (strict_list (strictval_from_bitv bv)) (strict_list (strictval_from_bitv bv)) = Some (sbit true).
Proof.
  unfold strictval_from_bitv.
  induction ws; intros. simpl. reflexivity.
  
  destruct bv. replace ({| intval := intval; intrange := intrange |}) with (@repr (S ws) intval).
      
  simpl.
  destruct (testbit (repr intval) (Z.of_nat ws));
    erewrite strictval_from_bitv_norm by omega;
    erewrite IHws; eauto.

  eapply unsigned_eq. simpl.
  rewrite Z_mod_modulus_eq by congruence.
  unfold modulus.
  eapply Zdiv.Zmod_small.
  omega.
Qed.

Lemma lt_not_refl :
  forall {ws} (bv : BitV ws),
    lt_sem (strict_list (strictval_from_bitv bv)) (strict_list (strictval_from_bitv bv)) = Some (sbit false).
Proof.
  unfold strictval_from_bitv.
  induction ws; intros. simpl. reflexivity.
  
  destruct bv. replace ({| intval := intval; intrange := intrange |}) with (@repr (S ws) intval).
      
  simpl.
  destruct (testbit (repr intval) (Z.of_nat ws));
    erewrite strictval_from_bitv_norm by omega;
    erewrite IHws; eauto.

  eapply unsigned_eq. simpl.
  rewrite Z_mod_modulus_eq by congruence.
  unfold modulus.
  eapply Zdiv.Zmod_small.
  omega.
Qed.

Lemma gt_not_refl :
  forall {ws} (bv : BitV ws),
    gt_sem (strict_list (strictval_from_bitv bv)) (strict_list (strictval_from_bitv bv)) = Some (sbit false).
Proof.
  unfold strictval_from_bitv.
  induction ws; simpl; auto; intros.
  destruct bv. replace ({| intval := intval; intrange := intrange |}) with (@repr (S ws) intval).
  simpl.
  destruct (testbit (repr intval) (Z.of_nat ws));
    erewrite strictval_from_bitv_norm by omega;


  replace (strictval_from_bitv' ws ws (repr intval)) with (@strictval_from_bitv ws (repr intval)) by (unfold strictval_from_bitv; eauto);
  erewrite lt_not_refl; eauto;
    erewrite eq_is_refl; eauto.

  
  eapply unsigned_eq. simpl.
  rewrite Z_mod_modulus_eq by congruence.
  unfold modulus.
  eapply Zdiv.Zmod_small.
  omega.
Qed.  

Lemma has_type_cons :
  forall f l n t,
    has_type (eseq l) (tseq n t) ->
    has_type f t ->
    has_type (eseq (f :: l)) (tseq (S n) t).
Proof.
  intros. inversion H.
  econstructor; eauto.
Qed.

Lemma get_each_n'_type :
  forall fuel l n t,
    Forall (fun x => has_type x t) l ->
    Nat.divide n (Datatypes.length l) ->
    n <> O ->
    (fuel >= Datatypes.length l)%nat ->
    has_type (eseq (map eseq (get_each_n' fuel n l))) (tseq (Nat.div (Datatypes.length l) n) (tseq n t)).
Proof.
  induction fuel; intros.
  destruct l; simpl in *; try omega.
  rewrite Nat.div_0_l by congruence.
  econstructor; eauto.
  assert (fuel >= Datatypes.length l \/ S fuel = Datatypes.length l)%nat by omega.
  destruct H3.
  erewrite get_each_n'_extra_fuel; try apply H3; try omega.
  eapply IHfuel; eauto.

  destruct l; destruct n; try solve [simpl in *; try congruence; try omega].
  unfold get_each_n'. fold (@get_each_n' ext_val).

  
Admitted.
  

(* This'll be a fun one *)
(* if too hard, it's fine to existentially quantify the Nat.div number *)
Lemma type_stream_of_bytes :
  forall n l t,
    Forall (fun x => has_type x t) l ->
    Nat.divide n (Datatypes.length l) ->
    has_type (eseq (map eseq (get_each_n n l))) (tseq (Nat.div (Datatypes.length l) n) (tseq n t)).
Proof.
  
  
Admitted.
