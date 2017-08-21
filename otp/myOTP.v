Set Implicit Arguments.

(* Import the core FCF definitions and theory. *)
Require Import FCF.
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

Definition OTPEnc (m : Bvector SP) : Comp (Bvector SP) := 
  k <-$ {0,1}^SP; 
  ret (BVxor SP k m).

(* bind : a -> (b -> Comp b) -> Comp a *) 
 


Theorem OTP_rand : forall (m n : Bvector SP), 
   D (OTPEnc m) n == D ({0,1}^SP) n.
Proof. 
  intros. 
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
