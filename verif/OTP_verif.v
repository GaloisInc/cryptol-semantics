(* Add LoadPath "~/Desktop/Galois/cryptol-semantics/verif".
Add LoadPath "~/Desktop/Galois/cryptol-semantics/src".  *)
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

(* Need to convert an ext_val which is an eseq into a list val
   Morally want "(map EValue (map to_val key))" 
   Do I need to put xor_ext into the GE to use it in otp_encrypt? *)
Theorem otp_equiv : forall key msg l, 
  has_type key byte -> 
  has_type msg byte -> 
      eager_eval_expr ge tempty sempty 
        (EApp (EApp (EVar encrypt) (EValue (to_val key))) (EValue (to_val msg))) (to_sval l) /\ otp_encrypt key msg = l.
Proof.
  intros; split.  inversion H. do 9 (destruct l0; simpl in H1; try omega).
  inversion H3.    
  e. e. g. e. e. simpl. repeat econstructor. 
   destruct (to_val e6) eqn:?. 
    (* instantiate (01:=(sbit b)).   why not? *)
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