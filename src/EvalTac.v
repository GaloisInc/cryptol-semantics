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

Close Scope nat.
Require Import Coqlib.
Require Import Builtins.

Ltac init_globals global_env :=
  assert (Hdemote : global_env (0, "demote") = Some (mb 2 0 Demote)) by reflexivity;
  assert (Hplus : global_env (1,"+") = Some (mb 1 2 Plus)) by reflexivity;
  assert (Htrue : global_env (9, "True") = Some (mb 0 0 true_builtin)) by reflexivity;
  assert (Hfalse : global_env (10, "False") = Some (mb 0 0 false_builtin)) by reflexivity;
  assert (Hgt : global_env (14,">") = Some (mb 1 2 Gt)) by reflexivity;
  assert (Hat : global_env (40, "@") = Some (mb 3 2 At)) by reflexivity;
  assert (Hsplit : global_env (37,"split") = Some (mb 3 1 split)) by reflexivity;
  assert (HsplitAt : global_env (35,"splitAt") = Some (mb 3 1 splitAt)) by reflexivity;
  assert (HAppend : global_env (34,"#") = Some (mb 3 2 Append)) by reflexivity.
  
  


