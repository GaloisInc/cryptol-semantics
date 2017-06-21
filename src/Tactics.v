Require Import Semantics.
Require Import AST.

Ltac e := match goal with
                 | [ |- eval_expr _ _ (EVar _) _] => idtac
                 | [ |- eval_expr _ _ (EIf _ _ _) _] => idtac
                 | [ |- eval_expr _ _ _ _ ] => econstructor; eauto; try solve [try unfold extend; simpl; reflexivity]
                 end.

Ltac global := eapply eval_global_var; [ unfold extend; simpl; unfold empty; auto | simpl; reflexivity | idtac].

Ltac local := econstructor; simpl; reflexivity.
