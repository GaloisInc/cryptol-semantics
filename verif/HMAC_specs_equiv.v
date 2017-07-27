Require Import List.
Import ListNotations.
Require Import Bvector.

Require Import Coqlib.

Require Import HMAC_spec.
Require Import HMAC_lib.
Require Import Bitstream.
Require Import Eager.



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
Definition correct_model_hash {c p : nat} (hf : ext_val -> ext_val) (h : Bvector (b c p) -> Bvector c) : Prop := True.


Check HMAC.
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


Definition bv_to_extval {w : nat} (bv : Bvector w) : ext_val := eseq nil.
  

  
(* I think this is the right theorem *)
Theorem HMAC_equiv (MSGT : Set) :
  forall keylen msglen key msg,
    has_type key (bytestream keylen) ->
    has_type msg (bytestream msglen) ->
    forall c p hf res H iv (splitAndPad : MSGT -> list (Bvector (b c p))) fpad opad ipad,
      hmac_model hf key msg = Some res ->
      @correct_model_hash c p hf (H iv) ->
      forall nmsg nkey nres,
        eseq (map bv_to_extval (splitAndPad nmsg)) = msg ->
        bv_to_extval nkey = key ->
        bv_to_extval nres = res ->
        @HMAC c p H iv MSGT splitAndPad fpad opad ipad nkey nmsg = nres.
Proof.
Admitted.