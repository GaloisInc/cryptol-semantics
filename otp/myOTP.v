Set Implicit Arguments.

(* Import the core FCF definitions and theory. *)
Require Import otp.FCF.
(* We will use a construction that produces a random group element.  
  This functionality is provided in the RndGrpElem module. *)
(* Require Import RndGrpElem.
(* Import the security definitions for public key encryption. *)
Require Import Encryption_PK.
(* Import the security definitions for Diffie-Hellman problems.  *)
Require Import DiffieHellman.
*)

Definition D := evalDist. 

Variable SP : nat. 
Definition OTPKeyGen (SP : nat) : Comp (Bvector SP) := 
  k <-$ {0,1}^SP;
  ret k.

(* Standard textbook OTP,
 but utilizes random selection from a distribution*)
Definition OTPEnc (m : Bvector SP) : Comp (Bvector SP) := 
  k <-$ {0,1}^SP; 
  ret (BVxor SP k m).

(* Matches our OTP definition 
 as seen in OTP.v and OTP_equiv.v *)
Definition OTP_encrypt (key msg : Bvector SP) : Bvector SP :=
  BVxor SP key msg.  
                                                      
(* bind : a -> (b -> Comp b) -> Comp a *) 
 
Definition rand_indist (x : Comp (Bvector SP)) {n : Bvector SP} :=
  D x n == D ({0,1}^SP) n. 

(*
(* Want to be able to rewrite like this somehow *)
Lemma rand_equiv : forall k x n,
    @rand_indist k n ->
    k = ret (x <-$ {0,1}^SP). 
*)

Theorem OTPEnc_indist : forall (m n : Bvector SP), 
   @rand_indist (OTPEnc m) n.   
Proof. 
  intros. 
  unfold rand_indist.
  unfold OTPEnc.
  symmetry.    
  rewrite <- evalDist_right_ident. 
  eapply (evalDist_iso (BVxor SP m) (BVxor SP m)); try intuition. 
   - rewrite <- BVxor_assoc. rewrite BVxor_same_id. rewrite BVxor_id_l. reflexivity. 
   - rewrite <- BVxor_assoc. rewrite BVxor_same_id. rewrite BVxor_id_l. reflexivity. 
   - simpl. apply in_getAllBvectors. 
   - simpl. reflexivity.
   - rewrite BVxor_comm. reflexivity. 
Qed.         


Theorem OTP_indist : forall (key msg n : Bvector SP),
    @rand_indist (ret key) n -> 
    @rand_indist (ret (OTP_encrypt key msg)) n. 
Proof. 
  intros. 
  inversion H.
  unfold OTP_encrypt.
  unfold rand_indist. 

  symmetry.    
  rewrite <- evalDist_right_ident. 
  Admitted. (* 
  eapply (evalDist_iso (BVxor SP key) (BVxor SP key)); try intuition. 

   - rewrite <- BVxor_assoc. rewrite BVxor_same_id. rewrite BVxor_id_l. reflexivity. 
   - rewrite <- BVxor_assoc. rewrite BVxor_same_id. rewrite BVxor_id_l. reflexivity. 
   - simpl. apply in_getAllBvectors. 
   - simpl. reflexivity.
   - rewrite BVxor_comm. reflexivity. 
Qed.         
      *) 

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
