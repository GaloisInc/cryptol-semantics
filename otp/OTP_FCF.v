Set Implicit Arguments.

(* Import the core FCF definitions and theory. *)
Require Import otp.FCF.

Definition D := evalDist. 

(* Standard textbook OTP,
 but utilizes random selection from a distribution*)
Definition OTPEnc {SP : nat} (m : Bvector SP) : Comp (Bvector SP) := 
  k <-$ {0,1}^SP; 
  ret (BVxor SP k m).

(* Matches our OTP definition in OTP_verif.v *)
Definition OTP_encrypt {SP : nat} (key msg : Bvector SP) : Bvector SP :=
  BVxor SP key msg.  
                                                      
Definition OTP {SP : nat} (msg : Bvector SP) : Comp (Bvector SP) :=
  key <-$ {0,1}^SP;
  ret (OTP_encrypt key msg). 
 
(* Indistinguishability security property *)
Definition rand_indist {SP : nat} (x : Comp (Bvector SP)) {n : Bvector SP} :=
  D x n == D ({0,1}^SP) n. 

Lemma distro_irr_eq' :
  forall (A B : Set) (b : Comp B) (a : B -> Comp A) (y : A) (v : Rat),
    well_formed_comp b ->
    (forall x : B, In x (getSupport b) -> evalDist (a x) y == v) ->
    forall x,
      In x (getSupport b) ->
      evalDist (x <-$ b; a x) y == evalDist (a x) y.
Proof.
  intros.
  eapply distro_irr_eq in H.
  Focus 2.
  intros. eapply H0.
  eauto. rewrite H. rewrite H0; eauto.
  reflexivity.
Qed.

Lemma allow_assumption :
  forall SP input (f : Bvector SP -> Bvector SP) n,
    (forall x, @rand_indist SP (ret input) x) ->
    evalDist (ret (f input)) n == evalDist (x <-$ {0,1}^SP; ret (f x)) n.
Proof.
  intros.
  unfold rand_indist in *.
  unfold D in *.
  rewrite <- evalDist_left_ident_eq with (c2 := fun x => ret f x).
  eapply evalDist_seq_eq. intros. apply H.
  intros. reflexivity.
Qed.

Lemma OTP_encrypt_indist :
  forall SP (msg key : Bvector SP),
  (forall n,
      @rand_indist SP (ret key) n) ->
  forall n,
      @rand_indist SP (ret (OTP_encrypt key msg)) n. 
Proof. 
  intros.
  unfold rand_indist.
  unfold OTP_encrypt.
  unfold rand_indist in *.
  unfold D in *.
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

(* Assuming the key is drawn uniformly at random (assumption added by OTP), 
 OTP_encrypt is indistinguishable from random bits *)
Theorem OTP_indist : forall SP (msg n : Bvector SP),
    @rand_indist SP (OTP msg) n. 
Proof. 
  intros. 
  unfold rand_indist.
  unfold OTP.
  unfold OTP_encrypt.

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

(* 
evalDist_iso:
  forall (rel : Rat -> Rat -> Prop) (A B C D : Set)
    (f : C -> D) (f_inv : D -> C) (d : Comp D) 
    (c : Comp C) (f1 : D -> Comp B) (f2 : C -> Comp A)
    (a : A) (b : B),
  RatRel rel ->
  (forall x : D, In x (getSupport d) -> f (f_inv x) = x) ->
  (forall x : C, In x (getSupport c) -> f_inv (f x) = x) ->
  (forall x : D,
   In x (getSupport d) -> In (f_inv x) (getSupport c)) ->
  (forall x : C,
   In x (getSupport c) -> evalDist d (f x) == evalDist c x) ->
  (forall x : C,
   In x (getSupport c) ->
   rel (evalDist (f1 (f x)) b) (evalDist (f2 x) a)) ->
  rel (evalDist (x <-$ d; f1 x) b)
    (evalDist (x <-$ c; f2 x) a)
*)

 
(*   evalDist_right_ident:
       forall (A : Set) (eqd : EqDec A) (c : Comp A) (a : A),
       evalDist (x <-$ c; ret x) a == evalDist c a  
*)
