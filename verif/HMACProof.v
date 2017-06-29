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

Require Import EvalTac.

Require Import HMAC.
Require Import HMACSpec.

(* TODO: here will be a proof about HMAC *)
(* relating the cryptol implementation to the spec *)

Definition lzero := EList ((ETApp (ETApp (EVar (0,"demote")) (TCon (TC (TCNum 0)) nil)) (TCon (TC (TCNum 8)) nil)) :: nil).

Definition t := TCon (TC (TCNum 1)) nil.

Definition call_hmac_on_zero := EApp (EApp (ETApp (ETApp (EVar hmacSHA256) t) t) lzero) lzero.

Lemma eval_hmac_sha256 :
  exists v,
    eval_expr ge empty call_hmac_on_zero v.
Proof.
  
  eexists.
  e. e. e. e.
  g.
  e. e. e. e.
  e. e. e. e. e. e.
  e. e. e. e. e.
  e. e. e.
  e. do 10 e.
  e. e. e.
  e. e. e. e. e.
  e. e. e. e. e. e. g.
  e. e. e. e. e. e. e. e. e. e.
  repeat e. repeat e.
  
Admitted.