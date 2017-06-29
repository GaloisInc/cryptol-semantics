Require Import Coqlib.
Require Import EvalTac.
Require Import Semantics.
Require Import Values.
Require Import AST.
Require Import BuiltinTest.

Lemma eval_t :
  eval_expr ge empty (EVar (242,"t")) (bits (v 5)).
Proof.
  repeat e.
Qed.

Lemma eval_f :
  eval_expr ge empty (EVar (243,"f")) (bits (v 5)).
Proof.
  repeat e.
Qed.
