Require Import Semantics.
Require Import BuiltinSem.
Require Import AST.

Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac g := eapply eval_global_var; try reflexivity; try (unfold mb; simpl).

Ltac e :=
  match goal with
  | [ |- eval_expr _ ?E (EVar ?id) _ ] =>
    try solve [ec]; g
  | [ |- _ ] => ec
  end.

