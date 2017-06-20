Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Definition ident := Z.


Definition BitV (n : nat) : Type := (@Integers.Int n).


(* (* Do we need anything with this? *) *)
(* Inductive NumInfo := *)
(* (*| BinLit (n : nat) *)
(* | OctLit (n : nat) *) *)
(* | DecLit *)
(* (*| HexLit (n : nat) *)
(* | CharLit *)
(* | PolyLit (n : nat)*) *)
(* . *)

(* Inductive Literal := *)
(* | ECNum (n : nat) (inf : NumInfo) *)
(* (* | ECString (s : string)*) *)
(* . *)


Inductive Selector :=
| TupleSel (n : nat) (o : option nat)
| ListSel (n : nat) (o : option nat)
.

(* Internally defined somehow *)
Inductive binop :=
| Plus
| Eq
.

Inductive Expr :=
(* literal bits *)
| ELit {w : nat} (bv : BitV w)
(* binary operation *)
| EBinop (op : binop) (l r : Expr) 
(* Literal finite list, e.g. [1,2,3] *)
| EList (l : list Expr)
(* Tuples, e.g. (1,2,3) *)
| ETuple (l : list Expr)
(* MISSING: ERec *)
(* select: pull one datum out of a record/tuple/list *)
| ESel (e : Expr) (s : Selector)
(* If/then/else, e.g. if cond then t else f *)
| EIf (cond t f : Expr)
(* List Comprehension, e.g. [ p + q | p <- xs | q <- ys ] *)
| EComp (e : Expr) (l : list (list Match))
(* Variable, e.g. 'x' *)
| EVar (id : ident)
(* MISSING: ETAbs *)
(* MISSING: ETApp *)       
(* Function application, e.g. f v *)
| EApp (f v : Expr)
(* Anonymous function, e.g. \\x -> x *)
| EAbs (id : ident) (e : Expr)
(* MISSING: EProofAbs *)
(* MISSING: EProofApp *)
(* Where, e.g. 1 + x where { x = 2 } *)
| EWhere (e : Expr) (l : list DeclGroup)
with Match :=
     | From (id : ident) (e : Expr)
with DeclDef :=
     | DExpr (e : Expr)
with Declaration := 
     | Decl (id : ident) (d : DeclDef)
with DeclGroup :=
     | Recursive (l : list Declaration)
     | NonRecursive (d : Declaration)
.

(* TODO: make sure we can shadow variables 5 and 6 here, or change up *)
Definition builtin_binop (id : ident) (op : binop) : DeclGroup :=
  NonRecursive (Decl id (DExpr (EAbs 5 (EAbs 6 (EBinop op (EVar 5) (EVar 6)))))).

(* Operational Semantics *)

Definition genv := ident -> option Expr.
Definition gempty : genv := fun _ => None.

Fixpoint declare (l : list Declaration) (ge : genv) :=
  match l with
  | nil => ge
  | (Decl id (DExpr e)) :: r =>
    let ge' := fun x => if Z.eq_dec x id then Some e else ge x in
    declare r ge'
  end.

Definition bind_decl_group (g : DeclGroup) (ge : genv) : genv :=
  match g with
  | Recursive l => declare l ge
  | NonRecursive d => declare (d :: nil) ge
  end.

Fixpoint bind_decl_groups (lg : list DeclGroup) (ge : genv) : genv :=
  match lg with
  | nil => ge
  | g :: gs =>
    bind_decl_groups gs (bind_decl_group g ge)
  end.

Inductive val :=
| bit (b : bool) (* Can we ever get this now? *)
| bits {n} (b : BitV n) (* bitvector *)
| close (id : ident) (e : Expr) (E : ident -> option val)  (* closure *)
| vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
| vnil (* empty list *)
| tuple (l : list val) (* heterogeneous tuples *)
.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.

Definition extend (E : env) (id : ident) (v : val) : env :=
  fun x => if Z.eq_dec x id then Some v else E x.

Definition extend_list (E : env) (id : ident) (vs : list val) : list env :=
  map (fun x => extend E id x) vs.


(* All of our list values are lazy, but here we have a fully computed
list, so we remember that by very simply thunking the result *)
Fixpoint thunk_list (l : list val) : val :=
  match l with
  | nil => vnil
  | f :: r =>
    vcons f (EVar 0) (extend empty 0 (thunk_list r))
  end.


Fixpoint fold_extend (E : env) (l : list (ident * val)) : env :=
  match l with
  | nil => E
  | (id,v) :: r => extend (fold_extend E r) id v
  end.


Fixpoint decl_exprs (l : list Declaration) : list Expr :=
  match l with
  | nil => nil
  | (Decl id (DExpr e)) :: r => e :: decl_exprs r
  end.

Fixpoint decl_ids (l : list Declaration) : list ident :=
  match l with
  | nil => nil
  | (Decl id _) :: r => id :: decl_ids r
  end.


Inductive eval_binop : binop -> val -> val -> val -> Prop :=
| eval_plus :
    forall {w : nat} {nz : w <> O} (n m : BitV w) {p : w <> O},
      eval_binop Plus (bits n) (bits m) (bits (@add w nz n m))
| eval_eq :
    forall {w : nat} {nz : w <> O} (n m : BitV w) {p : w <> O},
      eval_binop Eq (bits n) (bits m) (bit (@eq w n m)).


Inductive eval_expr (ge : genv) : env -> Expr -> val -> Prop :=
| eval_lit :
    forall {w} E (bv : BitV w),
      eval_expr ge E (ELit bv) (bits bv)
| eval_bin_op :
    forall E le lv re rv op v,
      eval_expr ge E le lv ->
      eval_expr ge E re rv ->
      eval_binop op lv rv v ->
      eval_expr ge E (EBinop op le re) v
| eval_list :
    forall E l vs,
      Forall2 (eval_expr ge E) l vs ->
      eval_expr ge E (EList l) (thunk_list vs)
| eval_tuple :
    forall E l vs,
      Forall2 (eval_expr ge E) l vs ->
      eval_expr ge E (ETuple l) (tuple vs)
| eval_tuple_sel :
    forall E e l n v o,
      eval_expr ge E e (tuple l) ->
      nth_error l n = Some v ->
      eval_expr ge E (ESel e (TupleSel n o)) v
(* TODO: eval_list_sel *)                
| eval_if_t : (* TODO: currently we have no expressions to produce a single bit...operators might fix *)
    forall E c t f v,
      eval_expr ge E c (bit true) ->
      eval_expr ge E t v ->
      eval_expr ge E (EIf c t f) v
| eval_if_f :
    forall E c t f v,
      eval_expr ge E c (bit false) ->
      eval_expr ge E f v ->
      eval_expr ge E (EIf c t f) v
(* TODO: eval_comp *)
| eval_local_var :
    forall E id v,
      E id = Some v ->
      eval_expr ge E (EVar id) v
| eval_global_var :
    forall E id v exp,
      E id = None ->
      ge id = Some exp ->
      eval_expr ge E exp v ->
      eval_expr ge E (EVar id) v
| eval_abs :
    forall E id exp,
      eval_expr ge E (EAbs id exp) (close id exp E)
| eval_app :
    forall E f id exp E' a av v,
      eval_expr ge E f (close id exp E') ->
      eval_expr ge E a av ->
      eval_expr ge (extend E' id av) exp v ->
      eval_expr ge E (EApp f a) v
| eval_where :
    forall E exp decls v,
      eval_expr (bind_decl_groups decls ge) E exp v ->
      eval_expr ge E (EWhere exp decls) v
.


(* List comprehension is weird *)
(* [ head | x <- e1, y <- e2 | z <- e3, w <- e4 ] *)
(* | eval_comp : (* Doesn't yet tie the knot, no self reference yet *) *)
(*     forall l head vs E lvs' lvs, *)
(*       Forall2 (eval_expr ge E) (map snd l) lvs' -> *)
(*       lvs' = map seq lvs -> *)
(*       Forall2 (fun e' v => eval_expr ge e' head v) (comp_envs E (combine (map fst l) lvs)) vs -> *)
(*       eval_expr ge E (EComp head l) (seq vs) *)

(*| eval_list_sel_fin :
    forall {n} E lst lv idx (bs : BitV n) v,
      eval_expr E lst (seq lv) ->
      eval_expr E idx (bits bs) ->
      nth_error lv (nat_of_bits bs) = Some v ->
      eval_expr E (EListSel lst idx) v
| eval_list_sel_inf :
    forall {n} E lst g E' idx (bs : BitV n) v,
      eval_expr E lst (infseq g E') ->
      eval_expr E idx (bits bs) ->
      eval_expr E' (g (nat_of_bits bs)) v ->
      eval_expr E (EListSel lst idx) v*)


(* Haskell Tests *)

(* Verbatim ASTs from cryptol: *)
(* First we need some list notation to match Haskell *)
Open Scope list_scope.
Module HaskellListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Definition  Nothing {A : Type} : option A := None.
End HaskellListNotations.

Import HaskellListNotations.

(* right side of this generated from cryptol implementation *)

Definition id_cry : DeclGroup := (NonRecursive (Decl 242 (DExpr (EAbs 243 (EWhere (EApp (EVar 244) (EVar 243)) [(Recursive [(Decl 244 (DExpr (EAbs 245 (EIf (EApp (EApp (EVar 17) (EVar 245)) (EVar 0)) (EVar 0) (EApp (EApp (EVar 1) (EVar 0)) (EApp (EVar 244) (EApp (EApp (EVar 1) (EVar 245)) (EApp (EVar 11) (EVar 0)))))))))])]))))).

Definition width : nat := 32.

Lemma nz :
  width <> O.
Proof.
  unfold width. congruence.
Qed.

Definition lit (z : Z) : Expr :=
  ELit (@repr width nz z).

(* 17 -> eq *)
(* 1 -> plus *)
Definition id_cry_hand_mod : DeclGroup := (NonRecursive (Decl 242 (DExpr (EAbs 243 (EWhere (EApp (EVar 244) (EVar 243)) [(Recursive [(Decl 244 (DExpr (EAbs 245 (EIf (EApp (EApp (EVar 17) (EVar 245)) (lit 0)) (lit 0) (EApp (EApp (EVar 1) (lit 1)) (EApp (EVar 244) (EApp (EApp (EVar 1) (EVar 245)) (lit (-1)))))))))])]))))).

Definition eq_decl := builtin_binop 17 Eq.
Definition plus_decl := builtin_binop 1 Plus.

Definition id_ge := bind_decl_group id_cry_hand_mod
                                    (bind_decl_group eq_decl
                                                     (bind_decl_group plus_decl gempty)).
Definition E := extend empty 12 (bits (@repr width nz 2)).

Lemma eval_id :
  eval_expr id_ge E (EApp (EVar 242) (EVar 12)) (bits (@repr width nz 2)).
Proof.
  econstructor. unfold id_ge.
  simpl. eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. auto.
  simpl. reflexivity.
  econstructor. econstructor. unfold E. unfold extend. simpl. reflexivity.
  econstructor.
  simpl. econstructor.
  eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. auto.
  simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  eapply eval_if_f.
  econstructor. econstructor.
  eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. auto.
  simpl. unfold id_ge. unfold bind_decl_group. simpl. reflexivity.
  econstructor; eauto.
  econstructor; eauto. unfold extend. simpl. reflexivity.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto. unfold extend. simpl. reflexivity.
  econstructor; eauto. unfold extend. simpl. reflexivity.
  econstructor; eauto; exact nz.

  econstructor. econstructor. eapply eval_global_var. unfold E. unfold extend. simpl. unfold empty. reflexivity.
  simpl. unfold id_ge. simpl. reflexivity.

  econstructor. econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply eval_global_var; eauto. simpl. reflexivity.
  econstructor; eauto.
  econstructor. econstructor.
  eapply eval_global_var; eauto. simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor.
  unfold extend. simpl. reflexivity.
  econstructor. econstructor. econstructor. econstructor.
  unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.

  eapply eval_if_f. econstructor.
  econstructor. eapply eval_global_var; eauto. simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor. unfold E. unfold extend. simpl. reflexivity.

  econstructor. econstructor.
  econstructor;
    try econstructor; try unfold extend; simpl; eauto.
  econstructor; exact nz.
  
  econstructor.
  econstructor. eapply eval_global_var; eauto. simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor.
  econstructor. econstructor.
  eapply eval_global_var. simpl. unfold id_ge. simpl. reflexivity. simpl. reflexivity.
  econstructor. econstructor. econstructor. eapply eval_global_var.
  simpl. unfold id_ge. simpl. reflexivity. simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. econstructor.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
  eapply eval_if_t. econstructor. econstructor.
  eapply eval_global_var. unfold extend. simpl. unfold E. unfold extend. simpl. unfold empty.
  reflexivity.
  simpl. unfold id_ge. simpl. reflexivity.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. econstructor. econstructor; try unfold extend; try econstructor; simpl; eauto.
  econstructor; eauto; exact nz.
  econstructor.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
  econstructor. econstructor. unfold extend. simpl. reflexivity.
  econstructor. unfold extend. simpl. reflexivity.
  econstructor. exact nz.
  Unshelve.
  all: exact nz.
Qed.
  


