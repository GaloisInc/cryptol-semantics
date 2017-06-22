
(* DONE        Change .cry so it uses + and (-) 
   DONE (?)    Figure out numbers for Plus, Eq, Neg
   PARTIAL     Use tactics to finish proofs
               Write Fib in coq (using 32 bit nats from compcert library)
               Prove equivalence of Fib implementations
*)




Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.   
        
Require Import Tactics. 

(* right side of this generated from cryptol implementation *)

Import HaskellListNotations.

(* right side of this generated from cryptol implementation *)

(* 
Definition fib_cry : DeclGroup := (Recursive [(Decl 484 (DExpr (EAbs 485 (EIf (EApp (EApp (ETApp (EVar 259) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 0)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])) (EIf (EApp (EApp (ETApp (EVar 259) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) []))) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])) (EApp (EApp (ETApp (EVar 243) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EApp (EVar 484) (EApp (EApp (ETApp (EVar 243) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (EApp (ETApp (EVar 253) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 1)) [])) (TCon (TC (TCNum 32)) [])))))) (EApp (EVar 484) (EApp (EApp (ETApp (EVar 243) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (EVar 485)) (EApp (ETApp (EVar 253) (TCon (TC TCSeq) [TCon (TC (TCNum 32)) [],TCon (TC TCBit) []])) (ETApp (ETApp (EVar 242) (TCon (TC (TCNum 2)) [])) (TCon (TC (TCNum 32)) [])))))))))))]).

Definition width : nat := 32. 
Definition fibnum : ident := 484. 
Definition fibvar : ident := 12. 

(* A non-zero width *)
Lemma nz : width <> O.
Proof. 
  unfold width. congruence. 
Qed.

(* 17 -> eq *)
(* 1 -> plus *)
(* 11 -> neg *)
Definition plus_decl := builtin_binop 242 Plus.
Definition eq_decl := builtin_binop 259 Eq.
Definition neg_decl := builtin_unop 243 Neg.


(* Global environment *)
Definition fib_ge := bind_decl_group fib_cry
                                    (bind_decl_group neg_decl
                                    (bind_decl_group eq_decl
                                    (bind_decl_group plus_decl
                                                     gempty))). 

(* Local environment *)
Definition Env (n:Z) := extend empty fibvar (bits (@repr width nz n)). 

(*

Function fib (n : nat) : nat := 
  match n with 
   | O => 1
   | S n' => match n' with
        | O => 1
        | S n'' => fib n' + fib n''
   end 
end.



Theorem fib_equiv : forall n m, m = fib (Z2N n) ->  
   eval_expr fib_ge (Env n) (EApp (EVar fibnum) (EVar fibvar)) 
   (bits (@repr width nz m)). 

*)






Definition E := Env 0. 


(* Fib 0 = 1 *)
Lemma eval_fib0 : eval_expr fib_ge E (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 1)). 
Proof.
  e. 
  - global. e. 
  - local. 
  - eapply eval_if_t. 
    + e. e. e. global. e. local.  
      * unfold extend. e. 
      * e. 
      * e. 
        -- local. 
        -- local.   
        -- constructor; exact nz.  
    + e. 
  Unshelve. exact nz. 
Qed.   
     

Definition E1 := Env 1.  

(* Fib 1 = 1 *)
Lemma eval_fib1 : eval_expr fib_ge E1 (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 1)).  
Proof. 
  e. 
  - global. e. 
  - local. 
  - eapply eval_if_f. 
    + e. e. e. global. e. local.  
      * unfold extend. e. 
      * e. 
      * e. 
        -- local. 
        -- local.   
        -- constructor; exact nz.  
    + eapply eval_if_t. 
      * e. e. e. global. e. local.  
        -- unfold extend. e. 
        -- e. 
        -- e. 
           ++ local. 
           ++ local.   
           ++ constructor; exact nz.
      * e.  
  Unshelve. exact nz. exact nz. 
Qed.    
  

Definition E2 := Env 2. 

(* Fib 2 = 2 *)
Lemma eval_fib2 : eval_expr fib_ge E2 (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 2)).
Proof. 
  e. 
  - global. e. 
  - local. 
  - eapply eval_if_f. 
    + e. e. e. global. e. local.  
      * unfold extend. e. 
      * e. 
      * e. 
        -- local. 
        -- local.   
        -- constructor; exact nz. 
    + eapply eval_if_f. 
      * e. e. e. global. e. local.  
        -- unfold extend. e. 
        -- e. 
        -- e. 
          ++ local. 
          ++ local.   
          ++ constructor; exact nz.
      * econstructor. 
      (* Something is going wrong in the next line *)
      e. e. e. global. e. e. global. e. e. e. e. global. e. local. e. local. 
        -- (* This isn't true - eapply eval_neg.*) 
Admitted. 

(* Fib 3 = 3 *)
Lemma eval_fib3 : eval_expr fib_ge E3 (EApp (EVar fibnum) (EVar fibvar)) (bits (@repr width nz 3)).
Proof. 
  econstructor. 
  - unfold fib_ge. simpl. eapply eval_global_var.
    + unfold E. unfold extend. simpl. unfold empty. reflexivity. 
    + simpl. reflexivity. 
    + econstructor. 
  - econstructor. unfold E. unfold extend. simpl. reflexivity. 
  - 


 (* #3 *)unfold fib_ge. simpl. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    econstructor. 
    + unfold extend. simpl. 


 (* #3 *)eapply eval_if_t. 
    + econstructor. 
      econstructor. 
      econstructor. 
      econstructor. unfold extend. simpl. unfold E. unfold extend. simpl. unfold empty. 


 (* #3 *)unfold fib_ge. simpl. econstructor. econstructor. econstructor. econstructor. eapply eval_global_var.
    unfold extend. simpl. unfold E. unfold extend. simpl. unfold empty. reflexivity.


 (* #3 *) econstructor.      
    + econstructor.
      econstructor. 
      econstructor. 
      * econstructor. unfold extend. simpl. unfold E. 
        unfold extend. simpl. unfold empty. (* This isn't true. So E doesn't have everything we need (?) *)  






*)