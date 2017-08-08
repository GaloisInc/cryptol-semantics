Require Import Eager.
Require Import AST.
Require Import List.
Require Import Semantics.
Require Import String.
Require Import Builtins.

Print eager_eval_expr_ind.

Print eager_eval_expr.
(*
Definition eager_eval_expr_ind_total 
  (P : genv -> tenv -> senv -> Expr -> strictval -> Prop)
  (Pl : genv -> tenv -> senv -> list Expr -> list strictval -> Prop)
  (Hglobal_var : forall (ge : ident -> option Expr) (id : ident) 
                        (E : ident -> option val) (v : val) (e : Expr),
      ge id = Some e ->
      E id = None -> eager_eval_expr ge E e v -> P ge E e v -> P ge E (EVar id) v)
  (Hlist : forall (ge : genv) (l : list Expr) (vs : list val) (E : env),
      Forall2 (eager_eval_expr ge E) l vs ->
      Pl ge E l vs ->
      P ge E (EList l) (listval vs))
  (Hlocal_var : forall (ge : genv) (id : ident) (E : ident -> option val) (v : val),
      E id = Some v -> P ge E (EVar id) v)
  (Hconst : forall (ge : genv) (z : Z) (E : env), P ge E (EConst z) (num z))
  (HPlnil : forall ge E, Pl ge E nil nil)
  (HPlcons : forall ge E e v es vs,
      P ge E e v ->
      Pl ge E es vs ->
      Pl ge E (e :: es) (v :: vs))
  (ge : genv)
  (E : env)
  (expr : Expr)
  (v : val)
  (eval : eager_eval_expr ge E expr v) : P ge E expr v :=
  let fix go ge E exp v eval : P ge E exp v :=
      let fix go_list ge E es vs f2eval : Pl ge E es vs :=
          match f2eval in (Forall2 _ es0 vs0) return (Pl ge E es0 vs0) with
          | Forall2_nil => HPlnil ge E
          | Forall2_cons e' v' es' vs' eval_fst forall_eval_rest =>
            HPlcons ge E e' v' es' vs' (go ge E e' v' eval_fst) (go_list ge E es' vs' forall_eval_rest)
          end
          in
      match eval in (eager_eval_expr ge0 E0 exp0 v0) return (P ge0 E0 exp0 v0) with
      | eval_global_var ge id E v P2 P3 P4 P5 =>
        Hglobal_var ge id E v P2 P3 P4 P5 (go ge E P2 v P5)
      | eval_list ge l vs E P3 =>
        Hlist ge l vs E P3 (go_list ge E l vs P3)
      | eval_local_var ge id E v P2 => Hlocal_var ge id E v P2
      | eval_const ge z E => Hconst ge z E
      end in
          go ge E expr v eval.
  *)