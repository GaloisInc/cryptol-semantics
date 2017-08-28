Require Import Cryptol.Coqlib.
Require Import String.
Require Import Cryptol.Lib.
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

Definition eval_expr_ind_total 
  (P : genv -> env -> Expr -> val -> Prop)
  (Pl : genv -> env -> list Expr -> list val -> Prop)         
  (Hglobal_var : forall (ge : ident -> option Expr) (id : ident) 
                        (E : ident -> option val) (v : val) (e : Expr),
      ge id = Some e ->
      E id = None -> eval_expr ge E e v -> P ge E e v -> P ge E (EVar id) v)
  (Hlist : forall (ge : genv) (l : list Expr) (vs : list val) (E : env),
      Forall2 (eval_expr ge E) l vs ->
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
  (eval : eval_expr ge E expr v) : P ge E expr v :=
  let fix go ge E exp v eval : P ge E exp v :=
      let fix go_list ge E es vs f2eval : Pl ge E es vs :=
          match f2eval in (Forall2 _ es0 vs0) return (Pl ge E es0 vs0) with
          | Forall2_nil => HPlnil ge E
          | Forall2_cons e' v' es' vs' eval_fst forall_eval_rest =>
            HPlcons ge E e' v' es' vs' (go ge E e' v' eval_fst) (go_list ge E es' vs' forall_eval_rest)
          end
          in
      match eval in (eval_expr ge0 E0 exp0 v0) return (P ge0 E0 exp0 v0) with
      | eval_global_var ge id E v P2 P3 P4 P5 =>
        Hglobal_var ge id E v P2 P3 P4 P5 (go ge E P2 v P5)
      | eval_list ge l vs E P3 =>
        Hlist ge l vs E P3 (go_list ge E l vs P3)
      | eval_local_var ge id E v P2 => Hlocal_var ge id E v P2
      | eval_const ge z E => Hconst ge z E
      end in
          go ge E expr v eval.

Definition eval_expr_ind_useful 
  (P : genv -> env -> Expr -> val -> Prop)
  (Hglobal_var : forall (ge : ident -> option Expr) (id : ident) 
                        (E : ident -> option val) (v : val) (e : Expr),
      ge id = Some e ->
      E id = None -> eval_expr ge E e v -> P ge E e v -> P ge E (EVar id) v)
  (Hlist : forall (ge : genv) (l : list Expr) (vs : list val) (E : env),
      Forall2 (eval_expr ge E) l vs ->
      Forall2 (P ge E) l vs ->
      P ge E (EList l) (listval vs))
  (Hlocal_var : forall (ge : genv) (id : ident) (E : ident -> option val) (v : val),
      E id = Some v -> P ge E (EVar id) v)
  (Hconst : forall (ge : genv) (z : Z) (E : env), P ge E (EConst z) (num z))
  (ge : genv)
  (E : env)
  (expr : Expr)
  (v : val)
  (eval : eval_expr ge E expr v) : P ge E expr v .
  eapply eval_expr_ind_total; intros; try solve [eauto].
  eapply Hlist. eassumption.
  eapply H0.
  simpl. econstructor.
  simpl in *. econstructor; eauto.
Defined.
           

Lemma eval_expr_swap_ge :
  forall ge E expr v,
    eval_expr ge E expr v ->
    forall ge',
      (forall id exp,
          ge id = Some exp ->
          ge' id = Some exp) ->
      eval_expr ge' E expr v.
Proof.
  intros.
  induction H using eval_expr_ind_useful; intros.
  - apply eval_global_var with e; auto. 
  - econstructor.

    induction H1; eauto.
    inversion H. subst.
    econstructor; eauto.
    
  - apply eval_local_var. auto. 
  - constructor; auto.  
Qed.
