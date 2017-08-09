Require Import String.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* Borrow from CompCert *)
Require Import Coqlib.

(*Require Import Integers.*)
Require Import Bitvectors.
Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import BuiltinSem.
Require Import Semantics.
Require Import GetEachN.

Open Scope list_scope.

Definition match_env (ge : genv) (E : env) (SE : senv) : Prop :=
  forall id,
    option_rel (strict_eval_val ge) (E id) (SE id).

Inductive eager_eval_type (ge : genv) : tenv -> Typ -> Tval -> Prop :=
| eager_eval_tvar_bound :
    forall E uid t k,
      E (uid,""%string) = Some t -> (* this lookup can be done with any string, as ident_eq only uses uid *)
      eager_eval_type ge E (TVar (TVBound uid k)) t
(* | eager_eval_tvar_free : *)
(* TODO: not sure what to do with free type variables...*)
| eager_eval_trec :
    forall E l lv,
      Forall2 (eager_eval_type ge E) (map snd l) (map snd lv) ->
      map fst l = map fst lv ->
      eager_eval_type ge E (TRec l) (trec lv)
| eager_eval_ttup :
    forall E l lv n,
      Forall2 (eager_eval_type ge E) l lv ->
      n = length l ->
      eager_eval_type ge E (TCon (TC (TCTuple n)) l) (ttup lv)
| eager_eval_tseq :
    forall E l len lenv elem elemv,
      l = len :: elem :: nil ->
      eager_eval_type ge E len lenv ->
      eager_eval_type ge E elem elemv ->
      eager_eval_type ge E (TCon (TC TCSeq) l) (tseq lenv elemv)
| eager_eval_tnum :
    forall E n,
      eager_eval_type ge E (TCon (TC (TCNum n)) nil) (tnum n)
| eager_eval_tbit :
    forall E,
      eager_eval_type ge E (TCon (TC TCBit) nil) tbit
| eager_eval_tinf :
    forall E,
      eager_eval_type ge E (TCon (TC TCInf) nil) tinf
| eager_eval_tfunction_type_base :
    forall E a arg r res,
      eager_eval_type ge E a arg ->
      eager_eval_type ge E r res ->
      eager_eval_type ge E (TCon (TC TCFun) (a :: r :: nil)) (tfun arg res)
| eager_eval_tfunction_type_rec :
    forall E a r arg res,
      eager_eval_type ge E a arg ->
      eager_eval_type ge E (TCon (TC TCFun) r) res ->
      eager_eval_type ge E (TCon (TC TCFun) (a :: r)) (tfun arg res)
| eager_eval_type_add :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      n = a + b ->
      eager_eval_type ge E (TCon (TF TCAdd) (l :: r :: nil)) (tnum n)
| eager_eval_type_sub :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      n = a - b ->
      eager_eval_type ge E (TCon (TF TCSub) (l :: r :: nil)) (tnum n)
| eager_eval_type_mul :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      n = a * b ->
      eager_eval_type ge E (TCon (TF TCMul) (l :: r :: nil)) (tnum n)
| eager_eval_type_div :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      b <> 0 ->
      n = a / b ->
      eager_eval_type ge E (TCon (TF TCDiv) (l :: r :: nil)) (tnum n)
| eager_eval_type_mod :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      b <> 0 ->
      n = a mod b ->
      eager_eval_type ge E (TCon (TF TCMod) (l :: r :: nil)) (tnum n)
| eager_eval_type_exp :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      n = Z.pow a b ->
      eager_eval_type ge E (TCon (TF TCExp) (l :: r :: nil)) (tnum n)
| eager_eval_type_min :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      n = Z.min a b ->
      eager_eval_type ge E (TCon (TF TCMin) (l :: r :: nil)) (tnum n)
| eager_eval_type_max :
    forall E l r a b n,
      eager_eval_type ge E l (tnum a) ->
      eager_eval_type ge E r (tnum b) ->
      n = Z.max a b ->
      eager_eval_type ge E (TCon (TF TCMax) (l :: r :: nil)) (tnum n)
| eager_eval_type_width :
    forall E e n,
      eager_eval_type ge E e (tnum n) ->
      eager_eval_type ge E (TCon (TF TCWidth) (e :: nil)) (tnum (calc_width n))
(* | eager_eval_type_len_from_then_to : *)
(* | eager_eval_type_len_from_then : *)
.


Fixpoint zipwith {A B C : Type} (f : A -> B -> C) (lA : list A) (lB : list B) : list C :=
  match lA,lB with
  | a :: aa, b :: bb => (f a b) :: zipwith f aa bb
  | _,_ => nil
  end.

Fixpoint foreach {A B C : Type} (f : A -> B -> C) (a : A) (lB : list B) : list C :=
  map (f a) lB.

(* for each element in lA, make a copy of lB and append that element to the front *)
(* cartesian product, in a sense *)
Fixpoint product {A : Type} (lA : list A) (lB : list (list A)) : list (list A) :=
  match lA with
  | nil => nil
  | f :: nil => map (fun x => f :: x) lB
  | f :: r =>
    (map (fun x => f :: x) lB) ++ (product r lB)
  end.

Definition bind_senvs (E : senv) : list (list (ident * strictval)) -> list senv :=
  map (fun lidv => fold_left (fun senv => fun idv => extend senv (fst idv) (snd idv)) lidv E).

Fixpoint eq_sem (a b : strictval) : option strictval :=
  match a,b with
  | (sbit a),(sbit b) => Some (sbit (if a then (if b then true else false) else (if b then false else true)))
  | svnil, svnil => Some (sbit true)
  | svcons fa ra, svcons fb rb =>
    match eq_sem fa fb, eq_sem ra rb with
    | Some (sbit rf), Some (sbit rr) => Some (sbit (if rf then rr else false))
    | _,_ => None
    end
  | _,_ => None
  end.

Fixpoint xor_sem (a b : strictval) : option strictval :=
  match a,b with
  | (sbit a),(sbit b) => Some (sbit (if a then (if b then false else true) else b))
  | (svcons fa ra), (svcons fb rb) =>
    match xor_sem fa fb, xor_sem ra rb with
    | Some sa, Some sr => Some (svcons sa sr)
    | _,_ => None
    end
  | svnil,svnil => Some svnil
  | _,_ => None
  end.

Fixpoint lt_sem (a b : strictval) : option strictval :=
  match a,b with
  | (sbit a),(sbit b) => Some (sbit (if b then (if a then false else true) else false))
  | (svcons fa ra), (svcons fb rb) =>
    match eq_sem fa fb, lt_sem fa fb, lt_sem ra rb with
    | Some (sbit false), Some (sbit b), Some _ => Some (sbit b)
    | Some (sbit true), Some _, Some (sbit b) => Some (sbit b)
    | _,_,_ => None
    end
  | svnil,svnil => Some (sbit false)
  | _,_ => None
  end.

Fixpoint gt_sem (a b : strictval) : option strictval :=
  match lt_sem a b, eq_sem a b with
  | Some (sbit x), Some (sbit y) => Some (sbit (if x then false else if y then false else true))
  | _,_ => None
  end.
  
Fixpoint strictval_from_bitv' (ws n : nat) (bv : BitV ws) : list strictval :=
  match n with
  | O => nil
  | S n' => sbit (testbit bv (Z.of_nat n')) :: strictval_from_bitv' ws n' bv
  end.

Definition strictval_from_bitv {ws : nat} (bv : BitV ws) : list strictval := strictval_from_bitv' ws ws bv.

Definition strictnum (value width : Z) : strictval :=
  let bv := @repr (Z.to_nat width) value in
  strict_list (strictval_from_bitv bv).

Fixpoint demote_sem (tv twidth : Tval) : option strictval :=
  match tv,twidth with
  | tnum v, tnum w => Some (strictnum v w)
  | _,_ => None
  end.

Fixpoint zero_sem (t : Tval) : option strictval :=
  match t with
  | trec lst => None
  (*srec (combine (map fst lst) (map zero_sem (map snd lst)))*)
  | ttup l => None
  (*stuple (map zero_sem l)*)
  | tseq (tnum n) t' =>
    match zero_sem t' with
    | Some sv => Some (strict_list (repeat sv (Z.to_nat n)))
    | None => None
    end
  | tseq _ _ => None
  | tfun _ _ => None
  | tnum _ => None
  | tbit => Some (sbit false)
  | tinf => None
  end.

Fixpoint append_sem (l1 l2 : strictval) : option strictval :=
  match l1 with
  | svnil => Some l2
  | svcons f r =>
    match append_sem r l2 with
    | Some sv => Some (svcons f sv)
    | None => None
    end
  | _ => None
  end.

Fixpoint splitAt_sem (t1 : Tval) (l : strictval) : option strictval :=
  match t1,l with
  | tnum 0, _ => Some (stuple (svnil :: l :: nil))
  | tnum n, svcons f r =>
    match splitAt_sem (tnum (n-1)) r with
    | Some (stuple (l1 :: l2 :: nil)) =>
      Some (stuple ((svcons f l1) :: l2 :: nil))
    | _ => None
    end
  | _,_ => None
  end.

Definition splitSem (t : Tval) (l : strictval) : option strictval :=
  match t,list_of_strictval l with
  | tnum n,Some l' => Some (strict_list (map strict_list (get_each_n (Z.to_nat n) l')))
  | _,_ => None
  end.

Definition strict_builtin_sem (bi : builtin) (t : list Tval) (l : list strictval) : option strictval :=
  match bi,t,l with
  | Xor,t::nil,(a :: b :: nil) => xor_sem a b
  | Lt,t::nil,(a :: b :: nil) => lt_sem a b
  | Gt,t::nil,(a :: b :: nil) => gt_sem a b
  | Eq,t::nil,(a :: b :: nil) => eq_sem a b
  | Demote,(tv :: twidth :: nil),nil => demote_sem tv twidth
  | Zero,(t :: nil),nil => zero_sem t
  | Append,(t1 :: t2 :: t3 ::nil), (l1 :: l2 :: nil) => append_sem l1 l2
  | splitAt,(t1 :: t2 :: t3 :: nil), (l :: nil) => splitAt_sem t1 l
  | split,(t1 :: t2 :: t3 :: nil),(l :: nil) => splitSem t2 l
  | _,_,_ => None
  end.


Lemma splitAt_zero :
  forall x,
    splitAt_sem (tnum 0) x = Some (stuple (svnil :: x :: nil)).
Proof.
  destruct x; simpl; auto.
Qed.

Lemma splitAt_cons :
  forall r x f,
    splitAt_sem (tnum (Z.of_nat (Datatypes.length r))) (strict_list (r ++ x)) = Some (stuple (strict_list r :: strict_list x :: nil)) ->
    splitAt_sem (tnum (Z.of_nat (Datatypes.length (f :: r)))) (strict_list ((f :: r) ++ x)) = Some (stuple (svcons f (strict_list r) :: strict_list x :: nil)).
Proof.
  intros. destruct r. simpl.
  rewrite splitAt_zero. reflexivity.
  (* This is true *)
Admitted.

Lemma splitAt_len :
  forall l1 t t' (l2 : list strictval),
    strict_builtin_sem splitAt (tnum (Z.of_nat (Datatypes.length l1)) :: t :: t' :: nil) (strict_list (l1 ++ l2) :: nil) = Some (stuple (strict_list l1 :: strict_list l2 :: nil)).
Proof.
  induction l1; intros.
  simpl. unfold splitAt_sem. fold splitAt_sem.
  rewrite splitAt_zero. reflexivity.
  unfold strict_builtin_sem.
  unfold strict_list. fold strict_list.
  simpl in IHl1.
  eapply splitAt_cons. eauto.
Qed.


(* Helper functions for evaluation of Builtins *)
(* While evaluation of types and values is necessarily separate, as *)
(* *)
Fixpoint get_types (l : list Expr) : list Typ :=
  match l with
  | ETyp t :: r => t :: get_types r
  | f :: r => nil
  | nil => nil
  end.

Fixpoint not_types (l : list Expr) : list Expr :=
  match l with
  | ETyp t :: r => not_types r
  | f :: r => f :: not_types r
  | nil => nil
  end.


Inductive eager_eval_expr (ge : genv) : tenv -> senv -> Expr -> strictval -> Prop :=

(* Definitely needed: *)
(* ListSel *)
(* ELiftUnary *)
(* ELiftBinary *)

  
(* Maybe needed? *)
(* Append *)
(* Head *)
(* Drop *)
(* Take *)

| eager_eval_tuple :
    forall TE E l vs,
      Forall2 (eager_eval_expr ge TE E) l vs ->
      eager_eval_expr ge TE E (ETuple l) (stuple vs)
| eval_tuple_sel :
    forall TE E e l n v,
      eager_eval_expr ge TE E e (stuple l) ->
      nth_error l n = Some v ->
      eager_eval_expr ge TE E (ESel e (TupleSel n)) v
| eval_record :
    forall TE E l vs,
      Forall2 (eager_eval_expr ge TE E) (map snd l) vs ->
      eager_eval_expr ge TE E (ERec l) (srec (combine (map fst l) vs))
| eval_record_sel :
    forall TE E l str v e,
      eager_eval_expr ge TE E e (srec l) ->
      lookup str l = Some v ->
      eager_eval_expr ge TE E (ESel e (RecordSel str)) v
| eager_eval_where :
    forall TE E expr decls v,
      eager_eval_expr (bind_decl_groups decls ge) TE (erase_decl_groups decls E) expr v ->
      eager_eval_expr ge TE E (EWhere expr decls) v
| eager_eval_if :
    forall TE E c t f v b,
      eager_eval_expr ge TE E c (sbit b) ->
      eager_eval_expr ge TE E (if b then t else f) v ->
      eager_eval_expr ge TE E (EIf c t f) v
| eager_eval_local_var :
    forall TE E id v,
      E id = Some v ->
      eager_eval_expr ge TE E (EVar id) v
| eager_eval_global_var :
    forall TE E id v exp,
      E id = None ->
      ge id = Some exp ->
      eager_eval_expr ge TE E exp v ->
      eager_eval_expr ge TE E (EVar id) v
| eager_eval_abs :
    forall TE E id exp,
      eager_eval_expr ge TE E (EAbs id exp) (sclose id exp TE E)
| eager_eval_tabs :
    forall TE E e id,
      eager_eval_expr ge TE E (ETAbs id e) (stclose id e TE E)
| eager_eval_app :
    forall TE E f id exp E' TE' a av v,
      eager_eval_expr ge TE E f (sclose id exp TE' E') ->
      eager_eval_expr ge TE E a av ->
      eager_eval_expr ge TE' (extend E' id av) exp v ->
      eager_eval_expr ge TE E (EApp f a) v
| eager_eval_tapp :
    forall TE TE' E e id e' E' v t te,
      eager_eval_expr ge TE E e (stclose id e' TE' E') ->
      eager_eval_type ge TE te t -> 
      eager_eval_expr ge (extend TE' id t) E e' v ->
      eager_eval_expr ge TE E (ETApp e (ETyp te)) v
| eager_eval_lazyval :
    forall v sv TE E,      
      strict_eval_val ge v sv ->
      eager_eval_expr ge TE E (EValue v) sv
| eager_eval_list :
    forall TE E l vs v,
      Forall2 (eager_eval_expr ge TE E) l vs ->
      v = strict_list vs ->
      eager_eval_expr ge TE E (EList l) v
| eager_eval_comp :
    forall TE E llm llidv vs v e,
      eager_par_match ge TE E llm llidv ->
      Forall2 (fun senv => eager_eval_expr ge TE senv e) (bind_senvs E llidv) vs ->
      v = strict_list vs ->
      eager_eval_expr ge TE E (EComp e llm) v
| eager_eval_builtin :
    forall TE E l targs args bi v,
      Forall2 (eager_eval_type ge TE) (get_types l) targs ->
      Forall2 (eager_eval_expr ge TE E) (not_types l) args ->
      strict_builtin_sem bi targs args = Some v ->
      eager_eval_expr ge TE E (EBuiltin bi l) v
with eager_par_match (ge : genv) : tenv -> senv -> list (list Match) -> list (list (ident * strictval)) -> Prop :=
     | eager_par_one :
         forall TE E lm lidv,
           eager_index_match ge TE E lm lidv ->
           eager_par_match ge TE E (lm :: nil) lidv
     | eager_par_more :
         forall TE E lm lidv lr llidv,
           lr <> nil ->
           eager_index_match ge TE E lm lidv ->
           eager_par_match ge TE E lr llidv ->
           eager_par_match ge TE E (lm :: lr) (zipwith (fun x => fun y => x ++ y) lidv llidv)

(* provide the bound environments for one part of a list comprehension *)
with eager_index_match (ge : genv) : tenv -> senv -> list Match -> list (list (ident * strictval)) -> Prop :=
     | eager_idx_last :
         forall TE E e vs lv id,
           eager_eval_expr ge TE E e vs ->
           list_of_strictval vs = Some lv ->
           eager_index_match ge TE E ((From id e) :: nil) (map (fun sv => (id,sv) :: nil) lv)
     | eager_idx_mid :
         forall TE E e vs lv llidv id r,
           r <> nil ->
           eager_eval_expr ge TE E e vs ->
           list_of_strictval vs = Some lv ->
           eager_index_match ge TE E r llidv ->
           eager_index_match ge TE E ((From id e) :: r) (product (map (fun sv => (id,sv)) lv) llidv)
.  

Lemma match_env_none :
  forall ge E SE id,
    match_env ge E SE ->
    (E id = None <-> SE id = None).
Proof.
  split; intros;
    unfold match_env in *;
    specialize (H id);
    rewrite H0 in *; inversion H; auto.
Qed.

Lemma eager_to_strict_lazy_type :
  forall t tv ge TE,
    eager_eval_type ge TE t tv ->
    eval_type ge TE t tv.
Proof.
  induction t using Typ_ind_useful; intros.

Admitted.

Lemma eager_to_strict_lazy :
  forall exp ge TE SE sv,
    eager_eval_expr ge TE SE exp sv ->
    forall E,
      match_env ge E SE ->
      strict_eval_expr ge TE E exp sv.
Proof.
  intro.
  eapply Expr_ind_useful with (e := exp); intros.
Admitted.
(*
  - inversion H0. subst.
    unfold Pl in H.
    eapply Lib.Forall_Forall2_implies in H4.
    Focus 3.
    intros. eapply eager_to_strict_lazy_type; eauto.
    Focus 2. instantiate (1 := fun x => True).
    admit.
    eapply Lib.Forall_Forall2_implies in H7.
    Focus 3.
    intros. eapply H; eauto.
    econstructor; eauto.

    econstructor; eauto.
    Search Forall2.
  
  induction 
  induction 1; intros.
  - admit. (* needs Forall2 induction *)
  - admit.
  - admit.
  - admit.
  - admit.
  - specialize (IHeager_eval_expr1 _ H1).
    specialize (IHeager_eval_expr2 _ H1).
    inversion IHeager_eval_expr1.
    inversion IHeager_eval_expr2.
    subst.
    inversion H3. subst.
    econstructor. econstructor. eassumption.
    eassumption. eassumption.
  - unfold match_env in *.
    specialize (H0 id). rewrite H in H0. inv H0.
    econstructor.
    econstructor; eauto.
    eauto.
  - erewrite <- match_env_none in H by eauto.
    eapply IHeager_eval_expr in H2. inversion H2. subst.
    econstructor. eapply eval_global_var; eauto.
    eassumption.
  - econstructor; eauto. econstructor. econstructor.
    eassumption.
  - econstructor; eauto. econstructor. econstructor.
    eassumption.
  - specialize (IHeager_eval_expr1 E0 H2).
    specialize (IHeager_eval_expr2 E0 H2).
    inversion IHeager_eval_expr1. subst. inversion H4. subst.
    assert (match_env ge E1 E'). unfold match_env. intros. apply H7.
    inversion IHeager_eval_expr2. subst.
    assert (match_env ge (extend E1 id v0) (extend E' id av)). {
      unfold extend. unfold match_env. intros.
      destruct (ident_eq id0 id). econstructor. assumption.
      eapply H5.
    } idtac.
    eapply IHeager_eval_expr3 in H9.
    inversion H9. subst.
    repeat (econstructor; eauto).
  - remember IHeager_eval_expr1 as He1. clear HeqHe1.
    remember IHeager_eval_expr2 as He2. clear HeqHe2.
    specialize (IHeager_eval_expr1 E0 H2).
    specialize (IHeager_eval_expr2 E0 H2).
    eapply eager_to_strict_lazy_type in H0.
    inversion IHeager_eval_expr1. subst. inversion H4. subst.
    inversion IHeager_eval_expr2. subst.
    assert (match_env ge E1 E'). {
      unfold match_env. intros. eapply H7.
    } idtac.

    admit. (* idk *)
  - econstructor; eauto.
    econstructor; eauto.
  - admit. (* weird forall2 induction needed *)
  - admit. (* weird forall2 induction needed *)
  - admit.
    all: fail. (* make sure we have enough bullets *)
*)
Lemma eager_eval_other_envs :
  forall ge TE Es vs exp,
    Forall2 (fun s => eager_eval_expr ge TE s exp) Es vs ->
    forall Es',
      Forall2 (fun E => fun E' => (forall v, eager_eval_expr ge TE E exp v <-> eager_eval_expr ge TE E' exp v)) Es Es' ->
      Forall2 (fun s => eager_eval_expr ge TE s exp) Es' vs.
Proof.
  induction 1; intros. inversion H. subst. econstructor.
  inversion H1. subst. econstructor; eauto.
  eapply H4; eauto.
Qed.        

Fixpoint apply (e : Expr) (l : list Expr) : Expr :=
  match l with
  | nil => e
  | f :: r => apply (EApp e f) r
  end.

Fixpoint tapply (e : Expr) (l : list Expr) : Expr :=
  match l with
  | nil => e
  | f :: r => tapply (ETApp e f) r
  end.


Lemma append_strict_list :
  forall t1 t2 t3 a b,
    strict_builtin_sem Append (t1 :: t2 :: t3 :: nil) ((strict_list a) :: (strict_list b) :: nil) = Some (strict_list (a ++ b)).
Proof.
  induction a; intros; simpl; auto.
  specialize (IHa b). simpl in IHa. rewrite IHa.
  reflexivity.
Qed.
