Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.
Require Import AST.

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
| tuple (l : list val) (* heterogeneous tuples *)
| rec (l : list (string * val))
| vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
| vnil (* empty list *)
| vcomp (e : Expr) (E : ident -> option val) (l : list (list Match)) (* lazy list comprehension *)
.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.

Definition extend (E : env) (id : ident) (v : val) : env :=
  fun x => if Z.eq_dec x id then Some v else E x.


(* Conversion from fully computed finite list to lazy list via trivial thunking *)
Fixpoint thunk_list (l : list val) : val :=
  match l with
  | nil => vnil
  | f :: r =>
    vcons f (EVar 0) (extend empty 0 (thunk_list r))
  end.

(* TODO: move this to Op.v *)
Inductive eval_binop : binop -> val -> val -> val -> Prop :=
| eval_plus :
    forall {w : nat} {nz : w <> O} (n m : BitV w) {p : w <> O},
      eval_binop Plus (bits n) (bits m) (bits (@add w nz n m))
| eval_eq :
    forall {w : nat} {nz : w <> O} (n m : BitV w) {p : w <> O},
      eval_binop Eq (bits n) (bits m) (bit (@eq w n m))
.

(* TODO: move this to Op.v *)
Inductive eval_unop : unop -> val -> val -> Prop :=
| eval_neg :
    forall {w : nat} {nz : w <> O} (n : BitV w) {p : w <> O},
      eval_unop Neg (bits n) (bits (@neg w nz n))
.

(* TODO: is this used? *)
Lemma nat_nz :
  forall z (nz : z > 0),
    Z.to_nat z <> O.
Proof.
  intros.
  unfold Z.gt in *. unfold Z.compare in *. 
  destruct z; simpl in nz; try congruence.
  unfold Z.to_nat.
  remember (Pos2Nat.is_pos p). omega.
Qed.  

Fixpoint lookup (str : string) (l : list (string * val)) : option val :=
  match l with
  | nil => None
  | (s,v) :: r =>
    if string_dec str s then Some v else lookup str r
  end.

Inductive eval_expr (ge : genv) : env -> Expr -> val -> Prop :=
| eval_un_op :
    forall E ae av op v,
      eval_expr ge E ae av ->
      eval_unop op av v ->
      eval_expr ge E (EUnop op ae) v
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
    forall E e l n v,
      eval_expr ge E e (tuple l) ->
      nth_error l n = Some v ->
      eval_expr ge E (ESel e (TupleSel n)) v
| eval_record :
    forall E l vs,
      Forall2 (eval_expr ge E) (map snd l) vs ->
      eval_expr ge E (ERec l) (rec (combine (map fst l) vs))
| eval_record_sel :
    forall E l str v e,
      eval_expr ge E e (rec l) ->
      lookup str l = Some v ->
      eval_expr ge E (ESel e (RecordSel str)) v
(* TODO: eval_list_sel *)                
| eval_if_t : 
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


(* Special case of a numeric program literal, e is always EVar 0 so that might be some builtin we could define *)
| eval_tapp_const :
    forall E e n (w : Z) (nz : w > 0) wn (nz' : wn <> O),
      wn = Z.to_nat w ->
      eval_expr ge E (ETApp (ETApp e (TCon (TC (TCNum n)) nil)) (TCon (TC (TCNum w)) nil)) (bits (@repr wn nz' n))
(* TODO: we should probably make rules for TAbs and TApp that do something *)
| eval_tapp :
    forall E e t v,
      eval_expr ge E e v ->
      eval_expr ge E (ETApp e t) v
| eval_tabs :
    forall E e a v,
      eval_expr ge E e v ->
      eval_expr ge E (ETAbs a e) v

.




(* List comprehension is weird *)

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

(* Definition extend_list (E : env) (id : ident) (vs : list val) : list env := *)
(*   map (fun x => extend E id x) vs. *)

(* Fixpoint decl_exprs (l : list Declaration) : list Expr := *)
(*   match l with *)
(*   | nil => nil *)
(*   | (Decl id (DExpr e)) :: r => e :: decl_exprs r *)
(*   end. *)

(* Fixpoint decl_ids (l : list Declaration) : list ident := *)
(*   match l with *)
(*   | nil => nil *)
(*   | (Decl id _) :: r => id :: decl_ids r *)
(*   end. *)
(* Definition zrepr {w : Z} {nz : w > 0} (n : Z) : BitV (Z.to_nat w). *)
(*   refine (@repr (Z.to_nat w) _ n). *)
(*   unfold Z.gt in *. unfold Z.compare in *. *)
(*   destruct w; simpl in nz; try congruence. *)
(*   unfold Z.to_nat. *)
(*   remember (Pos2Nat.is_pos p). omega. *)
(* Defined. *)

(* Fixpoint fold_extend (E : env) (l : list (ident * val)) : env := *)
(*   match l with *)
(*   | nil => E *)
(*   | (id,v) :: r => extend (fold_extend E r) id v *)
(*   end. *)



