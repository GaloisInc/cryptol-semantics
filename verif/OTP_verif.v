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

(*Lemma something : forall k ge e, 
  exists k', 
  Forall2 (eager_eval_expr ge e) (map EValue k) k'. 
Proof.
  induction k; intros.
  - eexists. econstructor.
  - edestruct IHk; eauto.
    eexists. econstructor; eauto.
    econstructor.    
 *) 

Lemma otp_equiv : forall k msg l, 
n_bits 8 k -> 
n_bits 8 msg -> 
  strict_eval_val ge (thunk_list (otp_encrypt' k msg)) l ->
  eager_eval_expr ge tempty sempty (EApp (EApp (EVar encrypt) (EList (map EValue k))) (EList (map EValue msg))) l. 
Proof. 
  intros. eapply n_bits_eval in H. destruct H. eapply n_bits_eval in H0. destruct H0.    
  econstructor. econstructor. eapply eager_eval_global_var. 
  unfold sempty. reflexivity.
  unfold ge. econstructor. econstructor.
  admit. (*eassumption.   *)
  econstructor. (*eassumption. *)
  admit.

  econstructor.
  econstructor. econstructor. eapply eager_eval_global_var. unfold extend. simpl. unfold sempty. reflexivity.
  unfold ge. econstructor.
  econstructor. econstructor. econstructor. eauto.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. eapply eager_eval_local_var. unfold extend. simpl. eauto.
  econstructor.
  econstructor. econstructor. unfold extend. simpl. eauto.
  econstructor.
  
  econstructor. unfold extend. simpl. auto.
  econstructor. econstructor. unfold extend. simpl. auto.
  econstructor.
  
  simpl. 
  inversion H. subst. clear H.  
  inversion H0. subst. clear H0.
         

  
     
      

Admitted.





