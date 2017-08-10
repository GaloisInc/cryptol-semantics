(* Add LoadPath "~/Desktop/Galois/cryptol-semantics/verif".
Add LoadPath "~/Desktop/Galois/cryptol-semantics/src".   *)
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
Require Import Values.        
Require Import Bitstream.

Require Import EvalTac.
Require Import Eager.
 
Import HaskellListNotations.
Open Scope string.
Require Import HMAC_lib. 

Require Import OTP. 

(* Change these to Options *)
Fixpoint xor_ext (l1 l2 : list ext_val) : list ext_val :=
  match l1 with 
  | (ebit x :: xs) => match l2 with
     | (ebit y :: ys) => (ebit (xorb x y)) :: xor_ext xs ys
     | _ => []
     end
  | _ => []
  end.


Fixpoint xor1 (l1 l2 : list ext_val) : option (list ext_val) := 
  match l1 with 
  | (ebit x :: xs) => match l2 with
       | (ebit y :: ys) => match (xor1 xs ys) with 
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
    | eseq l2 => match xor1 l1 l2 with
       | Some bs => eseq bs
       | _ => ebit false
       end
    | _ => ebit false
    end
  | _ => ebit false
  end.

Definition otp_encrypt (key msg : ext_val) : ext_val :=
  xor_ext' key msg.
  
Definition k1 : ext_val := eseq (ebit false::ebit true::ebit false::nil).
Definition m1 : ext_val := eseq (ebit true::ebit true::ebit true::nil).
(* Eval compute in (xor_ext' k1 m1).  *)
(* Eval compute in (otp_encrypt k1 m1).  *)

(* Definition otp_encrypt'  (k m: list val) : list val :=
  match to_bitv k with
  | None => []
  | Some bvk => 
      match to_bitv m with
      | None => []
      | Some bvm => from_bitv (otp_encrypt bvk bvm)  
      end
  end.  *)

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

(* I think l needs to be existentially quantified *)
Theorem otp_equiv : forall key msg l,
  has_type key byte -> 
  has_type msg byte ->
    eager_eval_expr ge tempty sempty
                    (EApp (EApp (EVar encrypt) (EValue key)) (EValue msg)) (to_sval l) /\ otp_encrypt key msg = l.
Proof.
  intros; split.  inversion H. do 9 (destruct l0; simpl in H1; try omega).
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

  inversion H18. subst.

  repeat match goal with
    | [H : has_type _ tbit |- _] => inversion H; clear H end. 
  

  (* repeat match goal with 
   | [H : Forall _ _ |- _] => inversion H; clear H end;
   repeat match goal with
     | [H : [] = _ |- _] => rewrite length_cons in H end. *)

  e. e. g. e. e. e. e. e. e. e.
  g.
  e. e. e. e. e. e.
  e. e. e. e. e. e. e.
(*  
  e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. e. e. e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. e. e. e. e. e. e. e. g. e. e. e.
  e. e. e. e. e. e. e. e. e. e. 
  simpl. f_equal. destruct (to_sval l) eqn:?.      

*)  
  Admitted.  
    
(* Lemma something : forall k ge te e, 
  exists k', 
  Forall2 (eager_eval_expr ge te e) (map EValue k) k'. 
Proof.
  induction k; intros.
  - eexists. econstructor.
  - edestruct IHk. destruct a;
    eexists;
    econstructor; eauto.    
    econstructor. instantiate (1:= sbit b). econstructor.
    econstructor. (* Can't use 'e', needs to be the same environment as E but strict *)instantiate (1:= sclose id e0 TE e). econstructor. admit. 
    econstructor.  (* Same as above *) admit.
    econstructor.   


    inversion H. subst.      

Admitted.     *)
(*
Lemma otp_equiv : forall k msg l, 
  n_bits 8 k -> 
  n_bits 8 msg -> 
    strict_eval_val ge (thunk_list (otp_encrypt' k msg)) l ->
    eager_eval_expr ge tempty sempty (EApp (EApp (EVar encrypt) (EList (map EValue k))) (EList (map EValue msg))) l. 
Proof. 
  intros. eapply n_bits_eval in H. destruct H. eapply n_bits_eval in H0. destruct H0.    
  inversion H0. clear H0. inversion H. clear H. 
  econstructor. econstructor. eapply eager_eval_global_var. 
  unfold sempty. reflexivity.
  unfold ge. econstructor. 
  econstructor. eassumption.
  econstructor. eassumption.

  econstructor. econstructor.
  econstructor. eapply eager_eval_global_var. unfold extend. simpl. unfold sempty. reflexivity.
  unfold ge. econstructor. (* This takes like 10 seconds but solves the first goal *)
  econstructor. econstructor. econstructor. econstructor. econstructor.  
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor.
  
  simpl. 
  (* Since x0 and x have length 8, they must be svcons *) 
  unfold strict_list. 
  unfold xor_sem.  
         

  
     
      

Admitted.





*)