Require Import Semantics.
Require Import BuiltinSyntax.

Require Import AST.

Require Import Coqlib.
Require Import Builtins.
Require Import Eager.
Require Import GlobalExtends.

Ltac ec := econstructor; try unfold mb; try reflexivity.
Ltac fg := eapply eager_eval_global_var; [ reflexivity | eassumption | idtac].
Ltac g := eapply eager_eval_global_var; try eassumption; try reflexivity.

Ltac et :=
  match goal with
  | [ |- eager_eval_type _ _ _ _ ] => solve [repeat econstructor; eauto]
  | [ |- Forall2 (eager_eval_type _ _) _ _ ] => econstructor; try et
  end.


Ltac f2 :=
  repeat progress match goal with
                  | [ |- Forall2 _ _ _ ] => econstructor
                  | [ |- Forall _ _ ] => econstructor
                  | [ |- _ ] => idtac
                  end.

(*Ltac ag := eapply eager_eval_global_var;
           [simpl; unfold extend; simpl; eapply wf_env_not_local; eauto; reflexivity |
            simpl; unfold extend; simpl; eapply wf_env_global; eauto; simpl; reflexivity |
            idtac].*)

(* solve completely, or leave only 1 subgoal *)
(* fail if running T generates too many subgoals *)
Ltac solve_1 T :=
  first [ ( T; [ idtac ]) ||
          solve [T]].


Ltac ag :=
  let ag' := 
      eapply eager_eval_global_var; [simpl; unfold extend; simpl; eapply wf_env_not_local; try eassumption; try reflexivity |
                                     try eassumption; simpl; unfold extend; simpl; eapply wf_env_global; simpl; try reflexivity |
                                     idtac]
  in
  ag'; try eassumption; try reflexivity.

Ltac lv := eapply eager_eval_local_var; try reflexivity.

(*            | [ |- eager_eval_expr ?GE _ ?E (EVar ?id) _ ] => solve_1 ag
            | [ |- eager_eval_expr ?GE _ ?E (EVar ?id) _ ] => solve_1 fg
            | [ |- eager_eval_expr ?GE _ ?E (EVar ?id) _ ] => solve_1 lv*)

Ltac e :=
  progress (match goal with
            | [ |- eager_eval_expr _ _ _ ?EXPR _ ] =>
              match EXPR with
              | EVar _ => fail 3 "can't handle variables"
              | _ => ec
              end
            end; try eassumption; try et; f2).


Ltac abstract_globals ge :=
  repeat match goal with
         | [ H : ge _ = _ |- _ ] => eapply wf_env_global in H; eauto
         end.

Ltac init_globals global_env :=
  assert (Hdemote : global_env (0, "demote") = Some (mb 2 0 Demote)) by reflexivity;
  assert (Hplus : global_env (1,"+") = Some (mb 1 2 Plus)) by reflexivity;
  assert (Htrue : global_env (9, "True") = Some (mb 0 0 true_builtin)) by reflexivity;
  assert (Hfalse : global_env (10, "False") = Some (mb 0 0 false_builtin)) by reflexivity;
  assert (Hgt : global_env (14,">") = Some (mb 1 2 Gt)) by reflexivity;
  assert (Hxor : global_env (28,"^") = Some (mb 1 2 Xor)) by reflexivity;
  assert (Hat : global_env (40, "@") = Some (mb 3 2 At)) by reflexivity;
  assert (Hsplit : global_env (37,"split") = Some (mb 3 1 split)) by reflexivity;
  assert (HsplitAt : global_env (35,"splitAt") = Some (mb 3 1 splitAt)) by reflexivity;
  assert (Hzero : global_env (29,"zero") = Some (mb 1 0 Zero)) by reflexivity;
  assert (HAppend : global_env (34,"#") = Some (mb 3 2 Append)) by reflexivity.


Ltac e' := e; match goal with
              | [ |- context[eager_eval_type] ] => repeat et
              | [ |- _ ] => idtac
              end.

Ltac break_exists :=
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  end.

Ltac break_and :=
  match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end.

Ltac break :=
  progress (try break_exists; try break_and).

(* TODO *)  
  


