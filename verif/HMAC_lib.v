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
  
  ).

Lemma good_hash_eval :
  forall h GE T SE hf,
    good_hash h GE T SE hf ->
    exists id exp TE E,
      eager_eval_expr GE T SE h (sclose id exp TE E).
Proof.
  intros. unfold good_hash in *.
  do 5 destruct H.
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
  do 5 destruct H.
  do 4 eexists. split; eauto.
Qed.

Definition global_extends (ge GE : genv) : Prop :=
  forall id v,
    ge id = Some v ->
    GE id = Some v.

Lemma global_extends_eager_eval :
    forall expr v ge TE SE,
      eager_eval_expr ge TE SE expr v ->
      forall GE,
        global_extends ge GE ->
        eager_eval_expr GE TE SE expr v.
Proof.
  
Admitted. (* needs crazy induction *)
  

(* lowercase is concrete, uppercase is abstract *)
(* wf_env lets this proof be used over a variety of environments that meet the proper constraints *)
Definition wf_env (ge GE : genv) (TE : tenv) (SE : senv) : Prop :=
  forall id,
    ge id <> None -> (TE id = None /\ SE id = None /\ ge id = GE id).

Lemma wf_env_global :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      GE id = Some exp.
Proof.
  intros. unfold wf_env in *.
  destruct (H id); try congruence.
  destruct H2. congruence.
Qed.

Lemma wf_env_not_local :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      SE id = None.
Proof.
  intros. unfold wf_env in *.
  destruct (H id); try congruence.
  destruct H2. congruence.
Qed.

Lemma wf_env_not_type :
  forall ge GE TE SE,
    wf_env ge GE TE SE ->
    forall id exp,
      ge id = Some exp ->
      TE id = None.
Proof.
  intros. unfold wf_env in *.
  destruct (H id); try congruence.
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

Lemma length_cons :
  forall {A} (e : A) l,
    Datatypes.length (e :: l) = S (Datatypes.length l).
Proof.
  reflexivity.
Qed.

Lemma map_cons :
  forall {A B} (f : A -> B) (e : A) l,
    map f (e :: l) = (f e) :: (map f l).
Proof.
  reflexivity.
Qed.

Lemma succ_nat_pred :
  forall n,
    (Z.of_nat (S n)) - 1 = Z.of_nat n.
Proof.
  intros.
  repeat rewrite Nat2Z.inj_succ.
  omega.
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


Lemma Forall_app :
  forall {A} (l1 l2 : list A) P,
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; intros; split; intros; simpl; auto.
  destruct H. auto.
  simpl in H. inversion H. subst.
  rewrite IHl1 in H3.
  destruct H3. split.
  econstructor; eauto.
  eauto.
  destruct H. inversion H. econstructor; eauto.
  rewrite IHl1. split; eauto.
Qed.

Lemma Forall_map :
  forall {A} (l : list A) P f,
    Forall P l ->
    (forall x, P x -> P (f x)) ->
    Forall P (map f l).
Proof.
  induction 1; intros; simpl; auto.
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

Lemma firstn_map :
  forall {A B: Type} (f : A -> B)  n l,
    firstn n (map f l) = map f (firstn n l).
Proof.
  induction n; intros.
  simpl. reflexivity.
  simpl. destruct l; simpl. reflexivity.
  f_equal. eapply IHn.
Qed.


Lemma get_each_n_map_commutes :
  forall {A B : Type} (f : A -> B) n l,
    get_each_n n (map f l) = map (map f) (get_each_n n l).
Proof.
  (* This is true, fun one though *)
Admitted.

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


Lemma map_injective_function :
  forall {A B} (f : A -> B) (l : list A),
    Forall (fun a => (forall b, f a = f b -> a = b)) l ->
    forall l',
      map f l = map f l' ->
      l = l'.
Proof.
  induction l; intros; simpl in *.
  destruct l'; simpl in *; try congruence; auto.
  destruct l'; simpl in *; try congruence.
  inversion H0.
  inversion H. subst. eapply H5 in H2. subst.
  f_equal.
  eapply IHl; eauto.
Qed.      

Lemma to_sval_list_pair_equiv :
  forall f,
    to_sval_list_pair f = combine (map fst f) (map to_sval (map snd f)).
Proof.
  induction f; intros; simpl; auto.
  destruct a. simpl. f_equal. auto.
Qed.

Lemma combine_injective :
  forall {A B : Type} (l1 : list A) (l2 : list B),
  forall l3 l4,
    combine l1 l2 = combine l3 l4 ->
    (Datatypes.length l1 = Datatypes.length l2) ->
    (Datatypes.length l3 = Datatypes.length l4) ->
    l1 = l3 /\ l2 = l4.
Proof.
  induction l1; intros; simpl in *.
  destruct l2; destruct l3; destruct l4; simpl in *; try congruence.
  split; auto.
  destruct l2; destruct l3; destruct l4; simpl in *; try congruence.
  inversion H0. inversion H1. inversion H. subst. clear H H0 H1.
  eapply IHl1 in H7; eauto. destruct H7. subst. split; auto.
Qed.

Lemma list_pair_parts_eq :
  forall {A B : Type} (l1 l2 : list (A * B)),
    map fst l1 = map fst l2 ->
    map snd l1 = map snd l2 ->
    l1 = l2.
Proof.
  induction l1; intros;
    destruct l2; simpl in *; try congruence.
  inversion H. inversion H0.
  f_equal.
  destruct a; destruct p; simpl in *.
  congruence.
  subst.
  eapply IHl1; eauto.
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

