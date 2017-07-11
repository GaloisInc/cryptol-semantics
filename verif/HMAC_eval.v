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
Require Import HexConvert.

Import HaskellListNotations.
Open Scope string.

Require Import HMAC.



Definition z : Expr := EList (EValue (thunk_list (repeat (bit false) 8)) :: nil).

Definition t : Expr := ETyp (TCon (TC (TCNum 1)) nil).

Definition result_hex := "0x6620b31f2924b8c01547745f41825d322336f83ebb13d723678789d554d8a3ef".

Definition result : list val := val_of_hex_lit result_hex.

Lemma eval_at_zero :
  exists v,
    eval_expr ge empty (EApp (EApp (ETApp (ETApp (EVar hmacSHA256) t) t) z) z) v /\ (force_list ge empty v result).
Proof.
  init_globals ge.
  eexists; split.
  e.
  e. e. e. g.
  e. e. e. e. e. e.
  e. e. e. e. e. e.
  e. g.
  e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. g.
  e. e. e. e. e. e.
  e. e. g.
  e. e. e. e.
  e. e. g.
  e. e. e. e. e. e.
  e. e. e. e. e. e. e.
  e. e. e.
  e. e. e. e. e.
  e. g. e. e. e.
  e. e. e. e. e.
  e. e. e. e. e.
  g. e. e. e. e. e.
  g. e. e. e. e. e. g.
  e. e. e. e.
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  e. e. e. e. g.
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).  
  
  
  

  
Admitted.
  