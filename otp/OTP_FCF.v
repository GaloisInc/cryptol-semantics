Set Implicit Arguments.

(* Import the core FCF definitions and theory. *)
Require Import otp.FCF.

(* Matches our OTP definition in OTP_verif.v *)
Definition OTP_encrypt_FCF {SP : nat} (key msg : Bvector SP) : Bvector SP :=
  BVxor SP key msg.  

(* Indistinguishability security property *)
Definition rand_indist {SP : nat} (x : Comp (Bvector SP)) :=
  forall (n : Bvector SP),
    evalDist x n == evalDist ({0,1}^SP) n. 

Lemma allow_assumption :
  forall SP input (f : Bvector SP -> Bvector SP) n,
    rand_indist (ret input) ->
    evalDist (ret (f input)) n == evalDist (x <-$ {0,1}^SP; ret (f x)) n.
Proof.
  intros.
  unfold rand_indist in *.
  rewrite <- evalDist_left_ident_eq with (c2 := fun x => ret f x).
  eapply evalDist_seq_eq. intros. apply H.
  intros. reflexivity.
Qed.

Lemma OTP_encrypt_indist :
  forall SP (msg key : Bvector SP),
    rand_indist (ret key) ->
    rand_indist (ret (OTP_encrypt_FCF key msg)). 
Proof. 
  intros.
  unfold rand_indist.
  intros.
  unfold OTP_encrypt_FCF.
  unfold rand_indist in *.
  symmetry.
  rewrite <- evalDist_right_ident.
  symmetry.
  erewrite allow_assumption with (f := fun x => BVxor SP x msg).

  eapply evalDist_iso. 
  - intuition. 
  - instantiate (1:= BVxor SP msg). 
    instantiate (1:= BVxor SP msg). 
    intros. 
    rewrite <- BVxor_assoc. 
    rewrite BVxor_same_id. 
    rewrite BVxor_id_l. 
    reflexivity. 
  - intros. 
    rewrite <- BVxor_assoc. 
    rewrite BVxor_same_id. 
    rewrite BVxor_id_l. 
    reflexivity. 
  - intros. 
    simpl. 
    apply in_getAllBvectors. 
  - intros. 
    simpl. reflexivity. 
  - intros. 
    rewrite BVxor_comm.
    rewrite <- BVxor_assoc.
    rewrite BVxor_same_id. 
    rewrite BVxor_id_l. 
    reflexivity.
  - exact H.
Qed.  


Definition OTP {SP : nat} (msg : Bvector SP) : Comp (Bvector SP) :=
  key <-$ {0,1}^SP;
  ret (OTP_encrypt_FCF key msg). 

(* Assuming the key is drawn uniformly at random (assumption added by OTP), 
 OTP_encrypt is indistinguishable from random bits *)
Theorem OTP_indist : forall SP (msg : Bvector SP),
    rand_indist (OTP msg). 
Proof. 
  intros. 
  unfold rand_indist.
  intros.
  unfold OTP.
  unfold OTP_encrypt_FCF.

  symmetry.    
  rewrite <- evalDist_right_ident. 
  eapply evalDist_iso. 
  - intuition. 
  - instantiate (1:= BVxor SP msg). 
    instantiate (1:= BVxor SP msg). 
    intros. 
    rewrite <- BVxor_assoc. 
    rewrite BVxor_same_id. 
    rewrite BVxor_id_l. 
    reflexivity. 
  - intros. 
    rewrite <- BVxor_assoc. 
    rewrite BVxor_same_id. 
    rewrite BVxor_id_l. 
    reflexivity. 
  - intros. 
    simpl. 
    apply in_getAllBvectors. 
  - intros. 
    simpl. reflexivity. 
  - intros. 
    rewrite BVxor_comm. 
    reflexivity. 
Qed. 

