
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
Require Import Cryptol.BuiltinSyntax.
Require Import Cryptol.Values.        

Require Import Cryptol.EvalTac.

Import HaskellListNotations.
Open Scope string.

Require Import CryptolVerif.Zero.

Lemma t1_zero :
  exists v,
    eval_expr ge tempty empty (EVar t1) v /\ force_list ge tempty empty v (repeat (bit false) 16).
Proof.
Admitted.
(*  assert (Hplus : ge (1,"+") = Some (mb 1 2 Plus)) by reflexivity.
  assert (Htrue : ge (9, "True") = Some (mb 0 0 true_builtin)) by reflexivity.  
  assert (Hfalse : ge (10, "False") = Some (mb 0 0 false_builtin)) by reflexivity.  
  assert (Hdemote : ge (0, "demote") = Some (mb 2 0 Demote)) by reflexivity.
  assert (Hzero : ge (29, "zero") = Some (mb 1 0 Zero)) by reflexivity.
  
  eexists; split;
    try g. e. e. g.
  all: repeat e.
Qed.
*)