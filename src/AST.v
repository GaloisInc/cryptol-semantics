Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.


Definition ident := nat.

Inductive BitV : nat -> Set :=
| bitNil : BitV O
| bitCons (b : bool) :
    forall {n} (bs : BitV n),
      BitV (S n).

Fixpoint bitlist {n} (b : BitV n) : list bool :=
  match b with
  | bitNil => nil
  | bitCons b bs => b :: bitlist bs
  end.

Lemma length_correct :
  forall n (bs : BitV n),
    length (bitlist bs) = n.
Proof.
  induction bs; intros; simpl; auto.
Qed.

Fixpoint nat_of_bits {n} (b : BitV n) : nat :=
  match b with
  | bitNil => O
  | bitCons b bs =>
    let n' := nat_of_bits bs in
    (n'*2) + (if b then 1 else 0)
  end.


(* Do we need anything with this? *)
Inductive NumInfo :=
(*| BinLit (n : nat)
| OctLit (n : nat) *)
| DecLit
(*| HexLit (n : nat)
| CharLit
| PolyLit (n : nat)*)
.

Inductive Literal :=
| ECNum (n : nat) (inf : NumInfo)
(* | ECString (s : string)*)
.


Inductive Selector :=
| TupleSel (n : nat) (o : option nat)
| ListSel (n : nat) (o : option nat)
.


Inductive Expr :=
(* Literal finite list, e.g. [1,2,3] *)
| EList : list Expr -> Expr
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

(* Operational Semantics *)

Definition genv := ident -> option Expr.
Definition gempty : genv := fun _ => None.

Fixpoint declare (l : list Declaration) (ge : genv) :=
  match l with
  | nil => ge
  | (Decl id (DExpr e)) :: r =>
    let ge' := fun x => if Nat.eq_dec x id then Some e else ge x in
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
  fun x => if Nat.eq_dec x id then Some v else E x.

Definition extend_list (E : env) (id : ident) (vs : list val) : list env :=
  map (fun x => extend E id x) vs.


(* All of our list values are lazy, but here we have a fully computed
list, so we remember that by very simply thunking the result *)
Fixpoint thunk_list (l : list val) : val :=
  match l with
  | nil => vnil
  | f :: r =>
    vcons f (EVar O) (extend empty O (thunk_list r))
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


Inductive eval_expr (ge : genv) : env -> Expr -> val -> Prop :=
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

Definition one : BitV (S (S O)).
  eapply bitCons. exact true.
  eapply bitCons. exact false.
  eapply bitNil.
Defined.

Definition two : BitV (S (S O)).
  eapply bitCons. exact false.
  eapply bitCons. exact true.
  eapply bitNil.
Defined.

Definition three : BitV (S (S O)).
  eapply bitCons. exact true.
  eapply bitCons. exact true.
  eapply bitNil.
Defined.

(* right side of this generated from cryptol implementation *)

Definition id_cry : DeclGroup := (NonRecursive (Decl 242 (DExpr (EAbs 243 (EWhere (EApp (EVar 244) (EVar 243)) [(Recursive [(Decl 244 (DExpr (EAbs 245 (EIf (EApp (EApp (EVar 17) (EVar 245)) (EVar 0)) (EVar 0) (EApp (EApp (EVar 1) (EVar 0)) (EApp (EVar 244) (EApp (EApp (EVar 2) (EVar 245)) (EVar 0))))))))])]))))).

Definition id_ge := bind_decl_group id_cry gempty.
Definition E := extend empty 12 (bits three).

Lemma eval_id :
  eval_expr id_ge E (EApp (EVar 242) (EVar 12)) (bits three).
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

Admitted.
  

