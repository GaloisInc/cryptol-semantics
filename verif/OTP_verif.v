Add LoadPath "~/Desktop/Galois/cryptol-semantics/verif".
Add LoadPath "~/Desktop/Galois/cryptol-semantics/src".
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



Definition otp_encrypt (k : BitV 8) (msg : BitV 8) : BitV 8 :=
  xor k msg.
  
Definition otp_encrypt'  (k : list val) (m : list val) : list val :=
  match to_bitv k with
  | None => []
  | Some bvk => 
      match to_bitv m with
      | None => []
      | Some bvm => from_bitv (otp_encrypt bvk bvm)  
      end
  end. 

Definition sempty : senv := fun _ => None.  





Lemma otp_equiv : forall k msg l, 
  strict_eval_val ge (thunk_list (otp_encrypt' k msg)) l ->
  eager_eval_expr ge sempty (EApp (EApp (EVar encrypt) (EList (map EValue k))) (EList (map EValue msg))) l. 
Proof.
Admitted. 







