(*Add LoadPath "~/Desktop/Galois/cryptol-semantics/verif".
Add LoadPath "~/Desktop/Galois/cryptol-semantics/src".*)
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

Require Import OTP. 



Definition otp_encrypt (k msg : BitV 8) : BitV 8 :=
  xor k msg.
  
Definition otp_encrypt'  (k m: list val) : list val :=
  match to_bitv k with
  | None => []
  | Some bvk => 
      match to_bitv m with
      | None => []
      | Some bvm => from_bitv (otp_encrypt bvk bvm)  
      end
  end. 

Definition sempty : senv := fun _ => None.  

Lemma something : forall k ge te e, 
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

Admitted.    
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