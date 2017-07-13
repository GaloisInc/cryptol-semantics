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



Function otp_encrypt (k : BitV 8) (msg : BitV 8) : BitV 8 :=
  xor k msg.

(* Eval compute in (otp_encrypt (@repr 8 8) (@repr 8 5)). 
Eval compute in (otp_encrypt (@repr 8 8) (@repr 8 13)). 
*)


(*Lemma otp_equiv : forall k msg bvk bvm, 
  to_bitv k = Some bvk -> 
  to_bitv msg = Some bvm -> 
  strict_eval_expr ge empty (EApp (EApp (EVar encrypt) (EList (map EValue k))) (EList (map EValue msg))) (otp_encrypt bvk bvm). 
*)

