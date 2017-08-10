Require Import AST.
Require Import List.
Require Import Semantics.
Require Import String.
Require Import Builtins.
Require Import Eager.


Definition eager_eval_expr_ind_total 
  (P : genv -> tenv -> senv -> Expr -> strictval -> Prop)
  (Pl : genv -> tenv -> senv -> list Expr -> list strictval -> Prop)
  (Ppm : genv -> tenv -> senv -> list (list Match) -> list (list (ident * strictval)) -> Prop)
  (Pm : genv -> tenv -> senv -> list Match -> list (list (ident * strictval)) -> Prop)
  (Plse : genv -> tenv -> Expr -> list senv -> list strictval -> Prop)
  (HTuple : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
                   (vs : list strictval),
      Forall2 (eager_eval_expr ge TE E) l vs ->
      Pl ge TE E l vs ->
      P ge TE E (ETuple l) (stuple vs))
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
  (HIf : forall (ge : genv) (TE : tenv) (E : senv) (c t f : Expr) 
                (v : strictval) (b : bool),
      eager_eval_expr ge TE E c (sbit b) ->
      P ge TE E c (sbit b) ->
      eager_eval_expr ge TE E (if b then t else f) v ->
      P ge TE E (if b then t else f) v -> P ge TE E (EIf c t f) v)
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
  (HApp : forall (ge : genv) (TE : tenv) (E : senv) (f : Expr) 
          (id : ident) (exp : Expr) (E' : ident -> option strictval)
          (TE' : ident -> option Tval) (a : Expr) (av v : strictval),
        eager_eval_expr ge TE E f (sclose id exp TE' E') ->
        P ge TE E f (sclose id exp TE' E') ->
        eager_eval_expr ge TE E a av ->
        P ge TE E a av ->
        eager_eval_expr ge TE' (extend E' id av) exp v ->
        P ge TE' (extend E' id av) exp v -> P ge TE E (EApp f a) v)
  (HTApp : forall (ge : genv) (TE : tenv) (TE' : ident -> option Tval) 
           (E : senv) (e : Expr) (id : ident) (e' : Expr)
           (E' : ident -> option strictval) (v : strictval) 
           (t : Tval) (te : Typ),
         eager_eval_expr ge TE E e (stclose id e' TE' E') ->
         P ge TE E e (stclose id e' TE' E') ->
         eager_eval_type ge TE te t ->
         eager_eval_expr ge (extend TE' id t) E e' v ->
         P ge (extend TE' id t) E e' v -> P ge TE E (ETApp e (ETyp te)) v)
  (HValue : forall (ge : genv) (v : ext_val) (sv : strictval) (TE : tenv) (E : senv),
      sv = to_sval v ->
      P ge TE E (EValue v) sv)
  (HList : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
           (vs : list strictval) (v : strictval),
      Forall2 (eager_eval_expr ge TE E) l vs ->
      Pl ge TE E l vs ->
      v = strict_list vs -> P ge TE E (EList l) v)
  (HComp : forall (ge : genv) (TE : tenv) (E : senv) (llm : list (list Match))
                  (llidv : list (list (ident * strictval))) (vs : list strictval)
                  (v : strictval) (e : Expr),
      eager_par_match ge TE E llm llidv ->
      Ppm ge TE E llm llidv ->
      Forall2 (fun senv : senv => eager_eval_expr ge TE senv e)
              (bind_senvs E llidv) vs ->
      Plse ge TE e (bind_senvs E llidv) vs ->
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
  (HParOne : forall ge TE E lm llidv,
      eager_index_match ge TE E lm llidv ->
      Pm ge TE E lm llidv ->
      Ppm ge TE E (lm :: nil) llidv)
  (HParMore : forall ge TE E lm llidv lr llidv',
      lr <> nil ->
      eager_index_match ge TE E lm llidv ->
      Pm ge TE E lm llidv ->
      eager_par_match ge TE E lr llidv' ->
      Ppm ge TE E lr llidv' ->
      Ppm ge TE E (lm :: lr) (zipwith (fun x y => x ++ y) llidv llidv'))
  (HIndexLast : forall ge TE E e vs lv id,
      eager_eval_expr ge TE E e vs ->
      P ge TE E e vs ->
      list_of_strictval vs = Some lv ->
      Pm ge TE E (From id e :: nil) (map (fun sv => (id,sv) :: nil) lv))
  (HIndexMid : forall ge TE E e vs lv llidv id r,
      r <> nil ->
      eager_eval_expr ge TE E e vs ->
      P ge TE E e vs ->
      list_of_strictval vs = Some lv ->
      eager_index_match ge TE E r llidv ->
      Pm ge TE E r llidv ->
      Pm ge TE E (From id e :: r) (product (map (fun sv => (id,sv)) lv) llidv))
  (HPlsenil : forall ge TE e, Plse ge TE e nil nil)
  (HPlsecons : forall ge TE e env v envs vs,
      P ge TE env e v ->
      Plse ge TE e envs vs ->
      Plse ge TE e (env :: envs) (v :: vs))
  (ge : genv)
  (TE : tenv)
  (E : senv)
  (expr : Expr)
  (v : strictval)
  (eval : eager_eval_expr ge TE E expr v) : P ge TE E expr v  :=
  let fix go ge TE E exp v eval : P ge TE E exp v :=
      let fix go_index ge TE E lm llidv EIM :=
          match EIM in (eager_index_match _ TE0 E0 LM0 LLIDV0) return (Pm ge TE0 E0 LM0 LLIDV0) with
          | eager_idx_last TE E e vs lv id eval_e lst =>
            HIndexLast ge TE E e vs lv id eval_e (go ge TE E e vs eval_e) lst
          | eager_idx_mid TE E e vs lv llidv id r nnil eval_e lst EIM' =>
            HIndexMid ge TE E e vs lv llidv id r nnil eval_e (go ge TE E e vs eval_e) lst
                      EIM' (go_index ge TE E r llidv EIM')
          end
      in
        let fix go_par ge TE E llm llidv EPM :=
            match EPM in (eager_par_match _ TE0 E0 LLM0 LLIDV0) return (Ppm ge TE0 E0 LLM0 LLIDV0) with
            | eager_par_one TE E lm llidv EIM =>
              HParOne ge TE E lm llidv EIM (go_index ge TE E lm llidv EIM)
            | eager_par_more TE E lm llidv lr llidv' nnil EIM EPM =>
              HParMore ge TE E lm llidv lr llidv' nnil EIM (go_index ge TE E lm llidv EIM)
                       EPM (go_par ge TE E lr llidv' EPM)
            end in
      let fix go_list ge TE E es vs f2eval : Pl ge TE E es vs :=
          match f2eval in (Forall2 _ es0 vs0) return (Pl ge TE E es0 vs0) with
          | Forall2_nil => HPlnil ge TE E
          | Forall2_cons e' v' es' vs' eval_fst forall_eval_rest =>
            HPlcons ge TE E e' v' es' vs' (go ge TE E e' v' eval_fst) (go_list ge TE E es' vs' forall_eval_rest)
          end
      in
      let fix go_list_senv ge TE e envs vs f2eval : Plse ge TE e envs vs :=
          match f2eval in (Forall2 _ envs0 vs0) return (Plse ge TE e envs0 vs0) with
          | Forall2_nil => HPlsenil ge TE e
          | Forall2_cons env' v' envs' vs' eval_fst forall_eval_rest =>
            HPlsecons ge TE e env' v' envs' vs' (go ge TE env' e v' eval_fst) (go_list_senv ge TE e envs' vs' forall_eval_rest)
          end
      in
        match eval in (eager_eval_expr _ TE0 E0 exp0 v0) return (P _ TE0 E0 exp0 v0) with
        | eager_eval_tuple TE E l vs F2 =>
          HTuple ge TE E l vs F2 (go_list ge TE E l vs F2)
        | eval_tuple_sel TE E e l n v eval_e nth =>
          HTupleSel ge TE E e l n v eval_e (go ge TE E e (stuple l) eval_e) nth
        | eval_record TE E lp vs F2' =>
          HRec ge TE E lp vs F2' (go_list ge TE E (map snd lp) vs F2')
        | eval_record_sel TE E lp str v e eval_e lkup =>
          HRecordSel ge TE E lp str v e eval_e (go ge TE E e (srec lp) eval_e) lkup
        | eager_eval_where TE E exp decls v eval_exp =>
          HWhere ge TE E exp decls v eval_exp (go (bind_decl_groups decls ge) TE (erase_decl_groups decls E) exp v eval_exp)
        | eager_eval_if TE E c t f v b eval_cond eval_branch =>
          HIf ge TE E c t f v b eval_cond (go ge TE E c (sbit b) eval_cond) eval_branch (go ge TE E (if b then t else f) v eval_branch)
        | eager_eval_local_var TE E id v lkupE =>
          HLocalVar ge TE E id v lkupE
        | eager_eval_global_var TE E id v exp lkupE lkupge eval_exp =>
          HGlobalVar ge TE E id v exp lkupE lkupge eval_exp (go ge TE E exp v eval_exp)
        | eager_eval_abs TE E id exp =>
          HAbs ge TE E id exp 
        | eager_eval_tabs TE E e id =>
          HTAbs ge TE E e id
        | eager_eval_app TE E f id exp E' TE' a av v eval_clos eval_arg eval_body =>
          HApp ge TE E f id exp E' TE' a av v eval_clos (go ge TE E f (sclose id exp TE' E') eval_clos)
               eval_arg (go ge TE E a av eval_arg) eval_body (go ge TE' (extend E' id av) exp v eval_body)
        | eager_eval_tapp TE TE' E e id e' E' v t te eval_clos eval_targ eval_body =>
          HTApp ge TE TE' E e id e' E' v t te eval_clos (go ge TE E e (stclose id e' TE' E') eval_clos)
                eval_targ eval_body (go ge (extend TE' id t) E e' v eval_body)
        | eager_eval_lazyval v sv TE E seval =>
          HValue ge v sv TE E seval
        | eager_eval_list TE E l vs v F2 eqv =>
          HList ge TE E l vs v F2 (go_list ge TE E l vs F2) eqv
        | eager_eval_comp TE E llm llidv vs v e epm F2 eqv =>
          HComp ge TE E llm llidv vs v e epm (go_par ge TE E llm llidv epm) F2
                (go_list_senv ge TE e (bind_senvs E llidv) vs F2) 
                eqv
        | eager_eval_builtin TE E l targs args bi v F2types F2not_types bi_sem =>
          HBuiltin ge TE E l targs args bi v F2types F2not_types (go_list ge TE E (not_types l) args F2not_types) bi_sem
        end in
        go ge TE E expr v eval.

Definition eager_eval_expr_ind_useful
  (P : genv -> tenv -> senv -> Expr -> strictval -> Prop)
  (Ppm : genv -> tenv -> senv -> list (list Match) -> list (list (ident * strictval)) -> Prop)
  (Pm : genv -> tenv -> senv -> list Match -> list (list (ident * strictval)) -> Prop)
  (HTuple : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
                   (vs : list strictval),
      Forall2 (eager_eval_expr ge TE E) l vs ->
      Forall2 (P ge TE E) l vs ->
      P ge TE E (ETuple l) (stuple vs))
  (HTupleSel : forall (ge : genv) (TE : tenv) (E : senv) (e : Expr) 
                      (l : list strictval) (n : nat) (v : strictval),
      eager_eval_expr ge TE E e (stuple l) ->
      P ge TE E e (stuple l) ->
      nth_error l n = Some v -> P ge TE E (ESel e (TupleSel n)) v)
  (HRec : forall (ge : genv) (TE : tenv) (E : senv) (l : list (string * Expr))
                 (vs : list strictval),
      Forall2 (eager_eval_expr ge TE E) (map snd l) vs ->
      Forall2 (P ge TE E) (map snd l) vs ->
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
  (HIf : forall (ge : genv) (TE : tenv) (E : senv) (c t f : Expr) 
                (v : strictval) (b : bool),
      eager_eval_expr ge TE E c (sbit b) ->
      P ge TE E c (sbit b) ->
      eager_eval_expr ge TE E (if b then t else f) v ->
      P ge TE E (if b then t else f) v -> P ge TE E (EIf c t f) v)
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
  (HApp : forall (ge : genv) (TE : tenv) (E : senv) (f : Expr) 
          (id : ident) (exp : Expr) (E' : ident -> option strictval)
          (TE' : ident -> option Tval) (a : Expr) (av v : strictval),
        eager_eval_expr ge TE E f (sclose id exp TE' E') ->
        P ge TE E f (sclose id exp TE' E') ->
        eager_eval_expr ge TE E a av ->
        P ge TE E a av ->
        eager_eval_expr ge TE' (extend E' id av) exp v ->
        P ge TE' (extend E' id av) exp v -> P ge TE E (EApp f a) v)
  (HTApp : forall (ge : genv) (TE : tenv) (TE' : ident -> option Tval) 
           (E : senv) (e : Expr) (id : ident) (e' : Expr)
           (E' : ident -> option strictval) (v : strictval) 
           (t : Tval) (te : Typ),
         eager_eval_expr ge TE E e (stclose id e' TE' E') ->
         P ge TE E e (stclose id e' TE' E') ->
         eager_eval_type ge TE te t ->
         eager_eval_expr ge (extend TE' id t) E e' v ->
         P ge (extend TE' id t) E e' v -> P ge TE E (ETApp e (ETyp te)) v)
  (HValue : forall (ge : genv) (v : ext_val) (sv : strictval) (TE : tenv) (E : senv),
      sv = to_sval v ->
      P ge TE E (EValue v) sv)
  (HList : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
           (vs : list strictval) (v : strictval),
      Forall2 (eager_eval_expr ge TE E) l vs ->
      Forall2 (P ge TE E) l vs ->
      v = strict_list vs -> P ge TE E (EList l) v)
  (HComp : forall (ge : genv) (TE : tenv) (E : senv) (llm : list (list Match))
                  (llidv : list (list (ident * strictval))) (vs : list strictval)
                  (v : strictval) (e : Expr),
      eager_par_match ge TE E llm llidv ->
      Ppm ge TE E llm llidv ->
      Forall2 (fun senv : senv => eager_eval_expr ge TE senv e)
              (bind_senvs E llidv) vs ->
      Forall2 (fun senv : senv => P ge TE senv e) (bind_senvs E llidv) vs ->
      v = strict_list vs -> P ge TE E (EComp e llm) v)
  (HBuiltin : forall (ge : genv) (TE : tenv) (E : senv) (l : list Expr)
           (targs : list Tval) (args : list strictval) 
           (bi : builtin) (v : strictval),
      Forall2 (eager_eval_type ge TE) (get_types l) targs ->
      Forall2 (eager_eval_expr ge TE E) (not_types l) args ->
      Forall2 (P ge TE E) (not_types l) args ->
      strict_builtin_sem bi targs args = Some v -> P ge TE E (EBuiltin bi l) v)
  (HParOne : forall ge TE E lm llidv,
      eager_index_match ge TE E lm llidv ->
      Pm ge TE E lm llidv ->
      Ppm ge TE E (lm :: nil) llidv)
  (HParMore : forall ge TE E lm llidv lr llidv',
      lr <> nil ->
      eager_index_match ge TE E lm llidv ->
      Pm ge TE E lm llidv ->
      eager_par_match ge TE E lr llidv' ->
      Ppm ge TE E lr llidv' ->
      Ppm ge TE E (lm :: lr) (zipwith (fun x y => x ++ y) llidv llidv'))
  (HIndexLast : forall ge TE E e vs lv id,
      eager_eval_expr ge TE E e vs ->
      P ge TE E e vs ->
      list_of_strictval vs = Some lv ->
      Pm ge TE E (From id e :: nil) (map (fun sv => (id,sv) :: nil) lv))
  (HIndexMid : forall ge TE E e vs lv llidv id r,
      r <> nil ->
      eager_eval_expr ge TE E e vs ->
      P ge TE E e vs ->
      list_of_strictval vs = Some lv ->
      eager_index_match ge TE E r llidv ->
      Pm ge TE E r llidv ->
      Pm ge TE E (From id e :: r) (product (map (fun sv => (id,sv)) lv) llidv))
  (ge : genv)
  (TE : tenv)
  (E : senv)
  (expr : Expr)
  (v : strictval)
  (eval : eager_eval_expr ge TE E expr v) : P ge TE E expr v .
Proof.
  eapply eager_eval_expr_ind_total with (Pl := fun ge TE E => Forall2 (P ge TE E)); try eassumption;
    intros; try solve [repeat econstructor; eauto].
  eapply HComp; try eassumption.
  instantiate (1 := fun ge TE e => Forall2 (fun senv => P ge TE senv e)) in H2.
  simpl in H2. eassumption.
  simpl. econstructor.
  simpl in *. econstructor; eauto.
Defined.
