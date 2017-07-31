Require Import List.
Import ListNotations.

Require Import Bvector.
Require Import Program. (* dependent destruction *)
Require Import Coqlib.

Require Import Utils.
Require Import Bitstream.
Require Import Eager.

Require Import HMAC_spec.
Require Import HMAC_lib.



Fixpoint to_bvector (w : nat) (e : ext_val) : option (Bvector w) :=
  match e,w with
  | eseq (ebit b :: r),S n =>
    match to_bvector n (eseq r) with
    | Some bv => 
      Some (Vector.cons bool b n bv)
    | _ => None
    end
  | eseq nil, O => Some (Vector.nil bool)
  | _,_ => None
  end.

Lemma to_bvector_succeeds :
  forall l n,
    has_type (eseq l) (tseq n tbit) ->
    exists bv,
      to_bvector n (eseq l) = Some bv.
Proof.
  induction l; intros.

  * inversion H. subst. simpl.
    eauto.

  * inversion H. subst. inversion H2.
    subst.
    edestruct IHl. econstructor; eauto.
    inversion H3. subst.
    simpl. rewrite H0.
    eauto.
Qed.

(*
(* Haha lol *)
Lemma false_set :
  forall (A : Set),
    False ->
    A.
Proof.
  intros.
  inversion H.
Defined.

Definition to_bv {n : nat} (e : ext_val) (p : has_type e (tseq n tbit)) : Bvector n.
  assert (exists l, e = eseq l). inversion p. eauto.
  destruct e;
    try solve [eapply false_set; destruct H; congruence].
  destruct (to_bvector n (eseq l)) eqn:?. exact b.
  eapply false_set.
  eapply to_bvector_succeeds in p. destruct p. congruence.
Defined.
 *)

Lemma bytestream_type :
  forall l t,
    Forall (fun x => has_type x t) l ->
    has_type (eseq l) (tseq (length l) t).
Proof.
  induction l; intros.
  econstructor; eauto.
  inversion H. subst.
  econstructor; eauto.
Qed.

Fixpoint bv_to_extval' {w : nat} (bv : Bvector w) : list ext_val :=
  match bv with
  | Vector.nil => nil
  | Vector.cons b _ r => ebit b :: bv_to_extval' r
  end.
  
Definition bv_to_extval {w : nat} (bv : Bvector w) : ext_val :=
  let bits := bv_to_extval' bv in
  let bytes := get_each_n 8 bits in
  eseq (map eseq bytes).

(* Bottom out with nil, maybe not a great idea but it's ok *)
Fixpoint eappend (l : list ext_val) : ext_val :=
  match l with
  | nil => eseq nil
  | (eseq l0) :: r =>
    match eappend r with
    | eseq x => eseq (l0 ++ x)
    | _ => eseq nil
    end
  | _ => eseq nil
  end.


(* TODO *)
Definition correct_model_hash {c p : nat} (hf : ext_val -> ext_val) (h : list (Bvector (b c p)) -> Bvector c) : Prop := True. 

(* We need this to be true about the hash function *)  
Axiom correct_hash_commutes :
  forall {c p : nat} hf (HASH : list (Bvector (b c p)) -> Bvector c),
    correct_model_hash hf HASH ->
    forall l,
      bv_to_extval (HASH l) = hf (eappend (map bv_to_extval l)).


Lemma split_append :
  forall a (x : Bvector a) b (y : Bvector b),
    splitVector a b (Vector.append x y) = (x,y).
Proof.
  induction x; intros.
  simpl. reflexivity.
  simpl. rewrite IHx. reflexivity.
Qed.

Lemma get_each_n_head :
  forall {A : Type} (l l' : list A) n,
    n = length l ->
    n <> O ->
    get_each_n n (l ++ l') = [l] ++ get_each_n n l'.
Proof.
  (* This is morally true, might need to massage preconditions a tiny bit to make it actually true, *)
  (* and the induction to prove it is going to be very annoying *)
Admitted.


Lemma zero_width_is_nil :
  forall {A} (v : Vector.t A O),
    v = []%vector.
Proof.  
  intros.
  dependent destruction v.
  reflexivity.
Qed.

(* In order to prove these two parts, we're going to need a way to say that Bvectors have certain values *)
(* that match with the values given to xor_const. *)
(* we should probably abstract over the numbers in the future, but for now we could leave them as concrete *)

Definition same_bits {w : nat} (n : Z) (bv : Bvector w) : Prop := False.
  

Lemma same_bits_testbit :
  forall {w} n b7 b6 b5 b4 b3 b2 b1 b0 (bv : Bvector w),
    same_bits n (Vector.append [b7;b6;b5;b4;b3;b2;b1;b0]%vector bv) ->
    b7 = Z.testbit n 7 /\
    b6 = Z.testbit n 6 /\
    b5 = Z.testbit n 5 /\
    b4 = Z.testbit n 4 /\
    b3 = Z.testbit n 3 /\
    b2 = Z.testbit n 2 /\
    b1 = Z.testbit n 1 /\
    b0 = Z.testbit n 0 /\
    same_bits n bv.
Proof.
Admitted.

Lemma BVxor_cons :
  forall n b b' v v',
    BVxor (S n) (b :: v)%vector (b' :: v')%vector = ((xorb b b') :: (BVxor n v v'))%vector.
Proof.
  simpl. auto.
Qed.

Lemma hmac_first_part_equiv :
  forall keylen w ekey nkey opad n,
    has_type (eseq ekey) (bytestream keylen) ->
    bv_to_extval nkey = eseq ekey ->
    same_bits n opad ->
    map eseq (get_each_n 8 (bv_to_extval' (BVxor w nkey opad))) = map (xor_const n) ekey.
Proof.
  induction keylen; intros.
  * unfold bytestream in H.
    inversion H. subst. destruct ekey; simpl in H3; try congruence.
    simpl. destruct nkey; simpl in H0; try congruence.
    Focus 2. unfold bv_to_extval in H0. inversion H0.
    unfold bv_to_extval'.
    assert (BVxor 0 []%vector opad = []%vector) by (eapply zero_width_is_nil).
    rewrite H2. simpl. reflexivity.

  * inversion H.
    destruct ekey; simpl in H3; try congruence.
    destruct nkey.
    unfold bv_to_extval in H0.
    unfold bv_to_extval' in H0. simpl in H0. inversion H0.
    inversion H4.
    unfold bv_to_extval in H0.
    unfold bv_to_extval' in H0.
    fold (@bv_to_extval' n0) in H0.
    inversion H8. subst.
    do 9 (destruct l1; simpl in H10; try congruence).
    clear H10.
    repeat match goal with
           | [ H : Forall (fun x => has_type x tbit) _ |- _ ] => inversion H; clear H
           end;
      repeat match goal with
             | [ H : has_type _ tbit |- _ ] => inversion H; clear H
             end;
    subst.
    
    do 7 (destruct nkey; [ subst;
    unfold bv_to_extval in H0;
    unfold bv_to_extval' in H0; simpl in H0; inversion H0;
    inversion H4 | 
                     unfold bv_to_extval in H0;
                     unfold bv_to_extval' in H0;
                     fold (@bv_to_extval' n0) in H0 ]).
    remember (bv_to_extval' nkey) as extval_key.

    replace ((ebit h :: ebit h0 :: ebit h1 :: ebit h2 :: ebit h3 :: ebit h4 :: ebit h5 :: ebit h6 :: extval_key)) with
        ((ebit h :: ebit h0 :: ebit h1 :: ebit h2 :: ebit h3 :: ebit h4 :: ebit h5 :: ebit h6 :: nil) ++ extval_key) in H0 by reflexivity.
      
    erewrite get_each_n_head in H0 by (simpl; eauto).
    simpl in H0.
    inversion H0. subst.
    clear H0.
    inversion H3.
    unfold length.

    eapply is_seq in H9.
    replace (tseq (length (map eseq (get_each_n 8 (bv_to_extval' nkey)))) byte) with
        (bytestream (length (map eseq (get_each_n 8 (bv_to_extval' nkey))))) in H9 by reflexivity.

    rewrite H2 in H9.
    do 8 (dependent destruction opad).
    replace (h :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: opad)%vector with
        (Vector.append (h :: h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: [])%vector opad) in H1 by (simpl; auto).
    eapply same_bits_testbit in H1.
    repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           end.
    
    eapply IHkeylen in H9;
      [ idtac |
        unfold bv_to_extval; reflexivity
        | eassumption ].
    
    repeat rewrite BVxor_cons.
    unfold bv_to_extval'.
    fold (@bv_to_extval' n0).
    replace (ebit (xorb b6 h)
        :: ebit (xorb b5 h0)
           :: ebit (xorb b4 h1)
              :: ebit (xorb b3 h2)
                 :: ebit (xorb b2 h3)
                 :: ebit (xorb b1 h4) :: ebit (xorb b0 h5) :: ebit (xorb b h6) :: bv_to_extval' (BVxor n0 nkey opad)) with
        ((ebit (xorb b6 h)
        :: ebit (xorb b5 h0)
           :: ebit (xorb b4 h1)
              :: ebit (xorb b3 h2)
                 :: ebit (xorb b2 h3)
                 :: ebit (xorb b1 h4) :: ebit (xorb b0 h5) :: ebit (xorb b h6) :: nil) ++ bv_to_extval' (BVxor n0 nkey opad)) by (simpl; auto).
    
    erewrite get_each_n_head by (simpl; auto).
    unfold app.
    repeat rewrite map_cons.
    erewrite <- H9.
    f_equal.

    unfold xor_const.
    unfold xor_const_list.
    unfold length.
    f_equal.
    subst. reflexivity.
Qed.


Lemma hmac_second_part_equiv :
  forall c p hf HASH,
    correct_model_hash hf HASH ->
    forall ekey emsg l,
      hf (eseq (map (fun x : ext_val => xor_const 54 x) ekey ++ emsg)) = eseq l ->
      forall ipad,
        same_bits 54 ipad ->
      forall (fpad : Bvector c -> Bvector p) nkey msgl,
        bv_to_extval' (Vector.append (HASH (BVxor (b c p) nkey ipad :: msgl)) (fpad (HASH (BVxor (b c p) nkey ipad :: msgl)))) = l.
Proof.
Admitted.

(* I think this is the right theorem *)
Theorem HMAC_equiv (MSGT : Set) :
  forall keylen msglen key msg,
    has_type key (bytestream keylen) ->
    has_type msg (bytestream msglen) ->
    forall c p hf res HashBlock iv (splitAndPad : MSGT -> list (Bvector (b c p))) fpad,
      hmac_model hf key msg = Some res ->
      @correct_model_hash c p hf (h_star p HashBlock iv) ->
      forall nmsg nkey,
        eseq (map bv_to_extval (splitAndPad nmsg)) = msg ->
        bv_to_extval nkey = key ->
        forall opad ipad,
          same_bits 92 opad ->
          same_bits 54 ipad ->
        bv_to_extval (@HMAC c p HashBlock iv MSGT splitAndPad fpad opad ipad nkey nmsg) = res.
Proof.
  intros.
  unfold HMAC.
  unfold HMAC_2K.
  unfold GHMAC_2K.
  unfold hash_words.
  rewrite split_append.
  simpl. unfold app_fpad.
  unfold hmac_model in H1.
  destruct key; simpl in *; try congruence.
  destruct msg; simpl in *; try congruence.
  destruct (hf (eseq (map (fun x : ext_val => xor_const 54 x) l ++ l0))) eqn:?; try congruence.
  inversion H1.

  match goal with
  | [ |- bv_to_extval (HashBlock (HashBlock iv ?V1) ?V2) = _ ] =>
    replace (HashBlock (HashBlock iv V1) V2) with (h_star p HashBlock iv (V1 :: V2 :: nil))
  end.
  Focus 2. unfold h_star. simpl. reflexivity.
  match goal with
  | [ |- context[(h_star p HashBlock (HashBlock iv ?V1) ?V2)] ] =>
    replace (h_star p HashBlock (HashBlock iv V1) V2) with (h_star p HashBlock iv (V1 :: V2))
  end.
  Focus 2. simpl. reflexivity.
  remember (h_star p HashBlock iv) as HASH.

  rename l into ekey.
  rename l0 into emsg.
  erewrite correct_hash_commutes by eassumption.
  f_equal. simpl.
  f_equal. rewrite app_nil_r.
  f_equal.
  eapply hmac_first_part_equiv; eauto.

  f_equal. f_equal.

  remember (splitAndPad nmsg) as msgl.
  
  eapply hmac_second_part_equiv; eauto.
Qed.
