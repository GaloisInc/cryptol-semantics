
Require Import Coqlib.
Require Import String.

Definition ident : Type := Z * string.

Definition ident_eq :
  forall (x y : ident),
    { fst x = fst y } + { fst x <> fst y }.
Proof.
  decide equality;
  eapply Pos.eq_dec. 
Defined.

Definition extend { vtype : Type } (E : ident -> option vtype) (id : ident) (v : vtype) :=
  fun x => if ident_eq x id then Some v else E x.

Inductive Expr :=
| EVar (id : ident)
| EConst (z : Z)
| EList (l : list Expr)
.

Inductive val :=
| num (z : Z)
| listval (l : list val)
.

Definition genv : Type := ident -> option Expr.
Definition gempty : genv := fun _ => None.
Definition env : Type := ident -> option val.

Inductive eval_expr (ge : genv) : env -> Expr -> val -> Prop :=
| eval_global_var :
    forall id E v e,
      ge id = Some e ->
      E id = None ->
      eval_expr ge E e v -> (* This line is the killer *)
      eval_expr ge E (EVar id) v
| eval_list :
    forall l vs E,
      Forall2 (eval_expr ge E) l vs ->
      eval_expr ge E (EList l) (listval vs)
| eval_local_var :
    forall id E v,
      E id = Some v ->
      eval_expr ge E (EVar id) v
| eval_const :
    forall z E,
      eval_expr ge E (EConst z) (num z)
.

Fixpoint lookup (id : ident) (l : list (ident * Expr)) : option Expr :=
  match l with
  | nil => None
  | (id',e) :: r =>
    if ident_eq id id' then Some e else lookup id r
  end.

Inductive eval_expr_listenv : list (ident * Expr) -> env -> Expr -> val -> Prop :=
| eval_global_var_listenv :
    forall ge id E v e,
      E id = None ->
      lookup id ge = Some e ->
      eval_expr_listenv ge E e v -> (* This line is the killer *)
      eval_expr_listenv ge E (EVar id) v
| eval_list_listenv :
    forall ge l vs E,
      Forall2 (eval_expr_listenv ge E) l vs ->
      eval_expr_listenv ge E (EList l) (listval vs)
| eval_local_var_listenv :
    forall ge id E v,
      E id = Some v ->
      eval_expr_listenv ge E (EVar id) v
| eval_const_listenv :
    forall ge z E,
      eval_expr_listenv ge E (EConst z) (num z)
.

(*
Lemma eval_expr_listenv_swap :
  forall ge E expr v,
    eval_expr_listenv ge E expr v ->
    forall ge',
      (forall id exp,
          lookup id ge = Some exp ->
          lookup id ge' = Some exp) ->
      eval_expr_listenv ge' E expr v.
Proof.
 *)

(*
Fixpoint make_ge (l : list (ident * Expr)) (ge : genv) : genv :=
  match l with
  | nil => ge
  | (id,exp) :: l' =>
    let ge' := make_ge l' ge in
    extend ge' id exp
  end.

Definition finite' (ge : genv) (l : list (ident * Expr)) : Prop :=
  forall id,
    ge id = make_ge l gempty id.
*)

Lemma eval_expr_swap_ge :
  forall ge E expr v,
    eval_expr ge E expr v ->
    forall ge',
      (forall id exp,
          ge id = Some exp ->
          ge' id = Some exp) ->
      eval_expr ge' E expr v.
Proof.
  (* Proving this is the goal *)
  (* If I can do it here, I can do it higher up *)
Admitted.
                