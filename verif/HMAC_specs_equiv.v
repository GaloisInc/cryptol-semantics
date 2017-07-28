Require Import List.
Import ListNotations.

Require Import Bvector.
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

(* TODO *)
Definition correct_model_hash {c p : nat} (hf : ext_val -> ext_val) (h : list (Bvector (b c p)) -> Bvector c) : Prop := True. 


(*Check HMAC.*)
(* HMAC args in order: c p : nat (bit widths) *)
(* Bv c -> Bv (c + p) -> Bv c: "compression function", i.e. the hash *)
(* iv : Bv c "initialization vector" *)
(* msgtype : Set *)
(* splitAndPad: turn message into bits *)
(* fpad : Bvector c -> Bvector (c + p) pads on 0s *)
(* opad ipad : more 0s *)
(* key : Bv (c + p) *)
(* msg : Message *)
(* result has type Bv c *)

Fixpoint bv_to_extval' {w : nat} (bv : Bvector w) : list ext_val :=
  match bv with
  | Vector.nil => nil
  | Vector.cons b _ r => ebit b :: bv_to_extval' r
  end.
  
Definition bv_to_extval {w : nat} (bv : Bvector w) : ext_val :=
  let bits := bv_to_extval' bv in
  let bytes := get_each_n 8 bits in
  eseq (map eseq bytes).
(*
Definition get_byte (e : ext_val) : option (list bool) :=
  match e with
  | eseq l =>
    match l with
    | (ebit b1 :: ebit b2 :: ebit b3 :: ebit b4 ::
            ebit b5 :: ebit b6 :: ebit b7 :: ebit b8 :: nil) => Some ([b1;b2;b3;b4;b5;b6;b7;b8])
    | _ => None
    end
  | _ => None
  end.

(* take a list of bytes as an ext_val, convert to flattened bits  *)
Definition extval_to_bv' (e : ext_val) : option (list bool) :=
  match e with
  | eseq l =>
    match collect (map get_byte l) with
    | Some bytes =>
      Some ((fold_left (@app bool) bytes nil))
    | _ => None
    end
  | _ => None
  end.
*)
Lemma split_append :
  forall a (x : Bvector a) b (y : Bvector b),
    splitVector a b (Vector.append x y) = (x,y).
Proof.
  induction x; intros.
  simpl. reflexivity.
  simpl. rewrite IHx. reflexivity.
Qed.


(*
Definition extval_to_bv {w : nat} (e : ext_val) :=
  match extval_to_bv' e with
  | Some l =>
    match Nat.eq_dec (length l) w with
    | left p => Some (Vector.of_list l)
    | _ => None
    end
  | None => None
  end.
*)


(* I think this is the right theorem *)
Theorem HMAC_equiv (MSGT : Set) :
  forall keylen msglen key msg,
    has_type key (bytestream keylen) ->
    has_type msg (bytestream msglen) ->
    forall c p hf res HashBlock iv (splitAndPad : MSGT -> list (Bvector (b c p))) fpad opad ipad,
      hmac_model hf key msg = Some res ->
      @correct_model_hash c p hf (h_star p HashBlock iv) ->
      forall nmsg nkey,
        eseq (map bv_to_extval (splitAndPad nmsg)) = msg ->
        bv_to_extval nkey = key ->
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

  
  
  (* TODO: What's the correct version of this? *)
Lemma correct_hash_commutes :
  forall {n m} h (hf : Bvector n -> Bvector (b n m) -> Bvector n) iv,
    correct_model_hash h hf iv ->
    forall x y,
      @bv_to_extval n (hf x y) = h (@bv_to_extval (b n m) y).
Proof.
Admitted.



  
  
Admitted.