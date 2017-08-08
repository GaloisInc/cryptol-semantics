
Require Import Coqlib.
Require Import String.
Require Import Lib.
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

Definition Expr_ind_full
           (P : Expr -> Prop)
           (Pl : list Expr -> Prop)
           (PVar : forall id, P (EVar id))
           (PConst : forall z, P (EConst z))
           (PList : forall l, Pl l -> P (EList l))
           (Hnil : Pl nil)
           (Hcons : forall f r, P f -> Pl r -> Pl (f :: r))
           (e : Expr)
  : P e :=
  let fix go e :=
  let fix go_list l :=
      match l as _l return Pl _l with
      | nil => Hnil
      | f :: r => Hcons f r (go f) (go_list r)
      end in
  match e with
  | EVar id => PVar id
  | EConst z => PConst z
  | EList l => PList l (go_list l)
  end in
  go e.

Definition Expr_ind_useful
           (P : Expr -> Prop)
           (PVar : forall id, P (EVar id))
           (PConst : forall z, P (EConst z))
           (PList : forall l, Forall P l -> P (EList l))
           (e : Expr)
  : P e.
  eapply Expr_ind_full. eauto. eauto.
  eapply PList. econstructor.
  intros. econstructor; eauto.
Defined.

Inductive val :=
| num (z : Z)
| listval (l : list val)
.

Definition genv : Type := ident -> option Expr.
Definition gempty : genv := fun _ => None.
Definition env : Type := ident -> option val.

Inductive eval_expr : genv -> env -> Expr -> val -> Prop :=
| eval_global_var :
    forall ge id E v e,
      ge id = Some e ->
      E id = None ->
      eval_expr ge E e v -> (* This line is the killer *)
      eval_expr ge E (EVar id) v
| eval_list :
    forall ge l vs E,
      Forall2 (eval_expr ge E) l vs ->
      eval_expr ge E (EList l) (listval vs)
| eval_local_var :
    forall ge id E v,
      E id = Some v ->
      eval_expr ge E (EVar id) v
| eval_const :
    forall ge z E,
      eval_expr ge E (EConst z) (num z)
.


Definition widens (ge : genv) (e : Expr) : Prop :=
  forall E v,
    eval_expr ge E e v ->
    forall id exp,
      ge id = None ->
      eval_expr (extend ge id exp) E e v.


Lemma widens_ge :
  forall e (ge : genv),
    (forall id e, ge id = Some e -> widens ge e) ->
    widens ge e.
Proof.
  induction e; intros.
  unfold widens. intros. inversion H0. subst. econstructor; eauto.
  unfold extend. destruct (ident_eq id id0). admit.
  eassumption.
  eapply H in H3. eapply H3. eauto. eauto.
  eapply eval_local_var. eauto.
  unfold widens. intros.
  inversion H0.
  econstructor; eauto.
  unfold widens.
  intros.
  inversion H0. subst.
  econstructor.
  eapply Forall_Forall2_implies; try eassumption.
Admitted. (* we can prove this *)  
  
Lemma ge_widens_empty :
  forall ge e,
    (forall id, ge id = None) ->
    widens ge e.
Proof.
  unfold widens.
  intros.
  eapply widens_ge; eauto.
  intros.
  rewrite H in H2. congruence.
Qed.

Lemma widens_out :
  forall (ge : genv),
    (forall id e, ge id = Some e -> widens ge e) ->
    forall idNew eNew,
      forall id e, (extend ge idNew eNew) id = Some e -> widens (extend ge idNew eNew) e.
Proof.
  (* If we can prove this, we're set? *)
Admitted.

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

Lemma all_widens :
  forall l ge,
    finite' ge l ->
    forall e,
      widens ge e.
Proof.
  induction l; intros.
  unfold finite' in *.
  eapply ge_widens_empty.
  intros. rewrite H. simpl. unfold gempty. reflexivity.

  (* How do I prove this? *)
Admitted.

(* we can prove that any expression widens, given that everything in the environment widens *)
(* what is hard is proving that everything in the environment widens *)


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


(* There isn't a counterexample here *)
(* rather the problem is that the Inductive hypothesis is not strong enough *)

(* We need to be able to simultaneously add something to the global
environment, while showing that all previous expressions still
evaluate to the same thing under this new global environment *)

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
                