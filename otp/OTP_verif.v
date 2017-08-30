Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Cryptol.Coqlib.
Require Import Cryptol.Bitvectors.

Require Import Cryptol.AST.
Require Import Cryptol.Semantics.
Require Import Cryptol.Utils.
Require Import Cryptol.Builtins.
Require Import Cryptol.BuiltinSem.
Require Import Cryptol.Values.        
Require Import Cryptol.Bitstream.

Require Import Cryptol.EvalTac.
Require Import Cryptol.Eager.
 
Import HaskellListNotations.
Open Scope string.
Require Import HMAC.HMAC_lib. 

Require Import otp.OTP_cryptol. 


Fixpoint xor_ext (l1 l2 : list ext_val) : option (list ext_val) := 
  match l1 with 
  | (ebit x :: xs) => match l2 with
       | (ebit y :: ys) => match (xor_ext xs ys) with 
             | Some bs => Some ((ebit (xorb x y)) :: bs)
             | _ => None
             end
       | [] => Some []
       | _ => None
       end
  | [] => Some []
  | _ => None
  end. 

Definition xor_ext' (x y : ext_val) : ext_val :=
  match x with 
  | eseq l1 => match y with 
    | eseq l2 => match xor_ext l1 l2 with
       | Some bs => eseq bs
       | _ => ebit false
       end
    | _ => ebit false
    end
  | _ => ebit false
  end.

Definition otp_encrypt (key msg : ext_val) : ext_val :=
  xor_ext' key msg.
  

Lemma length_cons : forall {A : Type} n x (xs : list A), 
  Datatypes.length xs = n <-> 
  Datatypes.length (x::xs) = S n.
Proof.
  split. 
  - destruct n; intros.
    + rewrite length_zero_iff_nil in H. subst. simpl. reflexivity.
    + inversion H. simpl. reflexivity.
  - intros. inversion H. reflexivity.  
Qed.

Lemma bool_destr : forall (b: bool),
    (if b then true else false) = b. 
  Proof. 
    destruct b; auto. 
  Qed.

  
Lemma otp_equiv' : forall key msg,
  has_type key byte -> 
  has_type msg byte ->
  exists l,  
    eager_eval_expr ge tempty sempty
                    (EApp (EApp (EVar encrypt) (EValue key)) (EValue msg)) (to_sval l)
    /\ otp_encrypt key msg = l.
Proof.
  intros. inversion H. do 9 (destruct l; simpl in H1; try omega).

  subst.
  repeat match goal with
         | [ H : Forall _ _ |- _ ] => inversion H; clear H
         end;
    repeat match goal with
           | [ H : has_type _ tbit |- _ ] => inversion H; clear H
           end;
    subst.
  inversion H0. clear H0. inversion H4. clear H4.
  symmetry in H0. rewrite <- length_zero_iff_nil in H0. omega.
  inversion H6. symmetry in H8. rewrite <- length_zero_iff_nil in H8.
  rewrite length_cons in H8. rewrite H7 in H8. omega.
  inversion H9. symmetry in H11. rewrite <- length_zero_iff_nil in H11.
  rewrite length_cons in H11. rewrite H10 in H11. subst.
  rewrite <- length_cons in H2. omega.
  subst.

  inversion H12. symmetry in H3. rewrite <- length_zero_iff_nil in H3.
  do 3 (rewrite <- length_cons in H2). omega. subst.
  
  inversion H5. symmetry in H7. rewrite <- length_zero_iff_nil in H7.
  do 4 (rewrite <- length_cons in H2). omega. subst. 
  
  inversion H10. symmetry in H13. rewrite <- length_zero_iff_nil in H13. 
  do 5 (rewrite <- length_cons in H2). omega. subst.
  
  inversion H14. symmetry in H15. rewrite <- length_zero_iff_nil in H15. 
  do 6 (rewrite <- length_cons in H2). omega. subst.
 
  inversion H16. symmetry in H17. rewrite <- length_zero_iff_nil in H17. 
  do 7 (rewrite <- length_cons in H2). omega. subst.

  inversion H18. subst. Focus 2. subst. simpl in H2. omega. 

  repeat match goal with
    | [H : has_type _ tbit |- _] => inversion H; clear H end. 

  eexists. 
  split. 

  e. e. g. e. e. e. e. e. e. e.
  g.
  e. e. lv. e. lv. e.
  lv. lv.
  simpl. f_equal.
  unfold to_sval. 
  instantiate (1:= eseq
                     (
                       (ebit (if b6 then if b14 then false else true else b14)) ::
                                                                                (ebit (if b5 then if b13 then false else true else b13)) ::
                                                                                (ebit (if b4 then if b12 then false else true else b12)) ::
                                                                                (ebit (if b3 then if b11 then false else true else b11)) ::
                                                                                (ebit (if b2 then if b10 then false else true else b10)) ::
                                                                                (ebit (if b1 then if b9 then false else true else b9)) ::
                                                                                (ebit (if b0 then if b8 then false else true else b8)) ::
                                                                                (ebit (if b then if b7 then false else true else b7)) :: nil )). 
  simpl. 
  reflexivity. 
  simpl. 
  unfold xorb.    
  repeat rewrite bool_destr. 
  reflexivity. 
Qed.

Theorem otp_equiv : forall key msg,
  has_type key byte -> 
  has_type msg byte ->
  eager_eval_expr ge tempty sempty
                  (EApp (EApp (EVar encrypt) (EValue key)) (EValue msg)) (to_sval (otp_encrypt key msg)).
Proof.
  intros.
  edestruct otp_equiv'. exact H. exact H0.
  destruct H1.
  subst x.
  assumption.
Qed.  
