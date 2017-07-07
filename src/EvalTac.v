Require Import Semantics.
Require Import BuiltinSem.
Require Import AST.

Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac fg := eapply eval_global_var; [ reflexivity | eassumption | idtac].
Ltac g := eapply eval_global_var; try eassumption; try reflexivity.

Ltac e :=
  match goal with
  | [ |- eval_expr _ ?E (EVar ?id) _ ] =>
    try fg; try reflexivity;
    try solve [eapply eval_local_var; reflexivity]
  | [ |- _ ] => ec
  end.

