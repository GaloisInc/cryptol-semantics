Require Import Eager.
Require Import AST.
Require Import List.
Require Import Semantics.
Require Import String.
Require Import Builtins.

Print eager_eval_expr_ind.

Print eager_eval_expr.

Definition eager_eval_expr_ind_total 
  (P : genv -> tenv -> senv -> Expr -> strictval -> Prop)
  (Pl : genv -> tenv -> senv -> list Expr -> list strictval -> Prop)
  (HTuple : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
                   (vs : list strictval),
      Forall2 (eager_eval_expr ge TE E) l vs -> P ge TE E (ETuple l) (stuple vs))
  (HTupleSel : forall (ge : genv) (TE : tenv) (E : senv) (e : Expr) 
                      (l : list strictval) (n : nat) (v : strictval),
      eager_eval_expr ge TE E e (stuple l) ->
      P ge TE E e (stuple l) ->
      nth_error l n = Some v -> P ge TE E (ESel e (TupleSel n)) v)
  (HRec : forall (ge : genv) (TE : tenv) (E : senv) (l : list (string * Expr))
                 (vs : list strictval),
      Forall2 (eager_eval_expr ge TE E) (map snd l) vs ->
      Pl ge TE E (map snd l) vs ->
      P ge TE E (ERec l) (srec (combine (map fst l) vs)))
  (HRecordSel : forall (ge : genv) (TE : tenv) (E : senv) (l : list (string * strictval))
                       (str : string) (v : strictval) (e : Expr),
      eager_eval_expr ge TE E e (srec l) ->
      P ge TE E e (srec l) ->
      lookup str l = Some v -> P ge TE E (ESel e (RecordSel str)) v)
  (HWhere : forall (ge : genv) (TE : tenv) (E : ident -> option strictval)
                   (expr : Expr) (decls : list DeclGroup) (v : strictval),
      eager_eval_expr (bind_decl_groups decls ge) TE 
                      (erase_decl_groups decls E) expr v ->
      P (bind_decl_groups decls ge) TE (erase_decl_groups decls E) expr v ->
      P ge TE E (EWhere expr decls) v)
  (HIf : forall (ge : genv) (TE : tenv) (E : senv) (c t f4 : Expr) 
                (v : strictval) (b : bool),
      eager_eval_expr ge TE E c (sbit b) ->
      P ge TE E c (sbit b) ->
      eager_eval_expr ge TE E (if b then t else f4) v ->
      P ge TE E (if b then t else f4) v -> P ge TE E (EIf c t f4) v)
  (HLocalVar : forall (ge : genv) (TE : tenv) (E : ident -> option strictval) 
                      (id : ident) (v : strictval), E id = Some v -> P ge TE E (EVar id) v)
  (HGlobalVar : forall (ge : genv) (TE : tenv) (E : ident -> option strictval) 
                       (id : ident) (v : strictval) (exp : Expr),
      E id = None ->
      ge id = Some exp ->
      eager_eval_expr ge TE E exp v -> P ge TE E exp v -> P ge TE E (EVar id) v)
  (HAbs : forall (ge : genv) (TE : tenv) (E : senv) (id : ident) (exp : Expr),
        P ge TE E (EAbs id exp) (sclose id exp TE E))
  (HTAbs : forall (ge : genv) (TE : tenv) (E : senv) (e : Expr) (id : ident),
        P ge TE E (ETAbs id e) (stclose id e TE E))
  (HApp : forall (ge : genv) (TE : tenv) (E : senv) (f9 : Expr) 
          (id : ident) (exp : Expr) (E' : ident -> option strictval)
          (TE' : ident -> option Tval) (a : Expr) (av v : strictval),
        eager_eval_expr ge TE E f9 (sclose id exp TE' E') ->
        P ge TE E f9 (sclose id exp TE' E') ->
        eager_eval_expr ge TE E a av ->
        P ge TE E a av ->
        eager_eval_expr ge TE' (extend E' id av) exp v ->
        P ge TE' (extend E' id av) exp v -> P ge TE E (EApp f9 a) v)
  (HTApp : forall (ge : genv) (TE : tenv) (TE' : ident -> option Tval) 
           (E : senv) (e : Expr) (id : ident) (e' : Expr)
           (E' : ident -> option strictval) (v : strictval) 
           (t : Tval) (te : Typ),
         eager_eval_expr ge TE E e (stclose id e' TE' E') ->
         P ge TE E e (stclose id e' TE' E') ->
         eager_eval_type ge TE te t ->
         eager_eval_expr ge (extend TE' id t) E e' v ->
         P ge (extend TE' id t) E e' v -> P ge TE E (ETApp e (ETyp te)) v)
  (HValue : forall (ge : genv) (v : val) (sv : strictval) (TE : tenv) (E : senv),
         strict_eval_val ge v sv -> P ge TE E (EValue v) sv)
  (HList : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
           (vs : list strictval) (v : strictval),
      Forall2 (eager_eval_expr ge TE E) l vs ->
      Pl ge TE E l vs ->
      v = strict_list vs -> P ge TE E (EList l) v)
  (HComp : forall (ge : genv) (TE : tenv) (E : senv) (llm : list (list Match))
                  (llidv : list (list (ident * strictval))) (vs : list strictval)
                  (v : strictval) (e : Expr),
      eager_par_match ge TE E llm llidv ->
      Forall2 (fun senv : senv => eager_eval_expr ge TE senv e)
              (bind_senvs E llidv) vs ->
      v = strict_list vs -> P ge TE E (EComp e llm) v)
  (HBuiltin : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
           (targs : list Tval) (args : list strictval) 
           (bi : builtin) (v : strictval),
      Forall2 (eager_eval_type ge TE) (get_types l) targs ->
      Forall2 (eager_eval_expr ge TE E) (not_types l) args ->
      Pl ge TE E (not_types l) args ->
      strict_builtin_sem bi targs args = Some v -> P ge TE E (EBuiltin bi l) v)
  (HPlnil : forall ge TE E, Pl ge TE E nil nil)
  (HPlcons : forall ge TE E e v es vs,
      P ge TE E e v ->
      Pl ge TE E es vs ->
      Pl ge TE E (e :: es) (v :: vs))
  (ge : genv)
  (TE : tenv)
  (E : senv)
  (expr : Expr)
  (v : strictval)
  (eval : eager_eval_expr ge TE E expr v) : P ge TE E expr v .
Admitted.
(*  let fix go ge E exp v eval : P ge E exp v :=
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