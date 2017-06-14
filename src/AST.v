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

(*
Inductive CType := (*TFun (CType n) (CType n)  -- ^ @[8] -> [8]@
            | TSeq (CType n) (CType n)  -- ^ @[8] a@ *)
| TSeq (len : CType) (T : CType) (* Tnum for finite, Tinf for inf, T for type *)
| TBitv (n : nat)                    (* ^ @Bit@*)
| TNum (n : nat)            (* ^ @10@*)
| TInf
(*          | TChar Char              -- ^ @'a'@
            | TInf                    -- ^ @inf@
            | TUser n [CType n]        -- ^ A type variable or synonym
            | TApp TFun [CType n]      -- ^ @2 + x@
            | TRecord [Named (CType n)]-- ^ @{ x : [8], y : [32] }@
            | TTuple [CType n]         -- ^ @([8], [32])@
            | TWild                   -- ^ @_@, just some type.
            | TLocated (CType n) Range -- ^ Location information
            | TParens (CType n)        -- ^ @ (ty) @
            | TInfix (CType n) (Located n) Fixity (CType n) -- ^ @ ty + ty @
              deriving (Eq, Show, Generic, NFData)*)
.
 *)

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

Inductive Pattern :=
| PVar (id : ident)
.

Inductive Selector :=
| TupleSel (n : nat) (o : option nat)
| ListSel (n : nat) (o : option nat)
.

Inductive Expr :=
(* boolean literal, e.g. True *)
| EBool (b : bool)
(* Variable, e.g. 'x' *)
| EVar (id : ident)
(* Literal, e.g. 0x1200 *)
(*| ELit {n} : BitV n -> Expr*)
| ELit (l : Literal)
(* Literal finite list, e.g. [1,2,3] *)
| EList : list Expr -> Expr
(* Function application, e.g. f v *)
| EApp (f v : Expr)
(* If/then/else, e.g. if cond then t else f *)
| EIf (cond t f : Expr)
(* Where, e.g. 1 + x where { x = 2 } *)
| EWhere : Expr -> ident -> Expr -> Expr
(* Anonymous function, e.g. \\x -> x *)
| EFun (l : list Pattern) (e : Expr)
(* List Comprehension, e.g. [ p + q | p <- xs | q <- ys ] *)
| EComp (e : Expr) (l : list (ident * Expr))
(* infinite sequence, e.g. [1,2,...] *)
| EInfFrom (f : nat -> Expr)
(* Tuples, e.g. (1,2,3) *)
| ETuple (l : list Expr)
(* select: pull one datum out of a record/tuple/list *)
| ESel (e : Expr) (s : Selector)
(* Parentheses (does nothing) *)
| EParens (e : Expr)                (* ^ @ (e)   @ (Removed by Fixity) *)
(*
| ERecord [Named (Expr n)]        (* ^ @ { x = 1, y = 2 } @ *) 
| EFromTo (Type n) (Maybe (Type n)) (Maybe (Type n)) (* ^ @[1, 5 ..  117 ] @ *)
| EComp (Expr n) [[Match n]]      (* ^ @ [ 1 | x <- xs ] @ *) 
| EAppT (Expr n) [(TypeInst n)]   (* ^ @ f `{x = 8}, f`{8} @ *)
| ETyped (Expr n) (Type n)        (* ^ @ 1 : [8] @ *)
| ETypeVal (Type n)               (* ^ @ `(x + 1)@, @x@ is a type *) 
| ELocated (Expr n) Range         (* ^ position annotation *) 
| EInfix (Expr n) (Located n) Fixity (Expr n) (* ^ @ a + b @ (Removed by Fixity) *) *)
.

(* Operational Semantics *)

Inductive val :=
| bit (b : bool)
| bits {n} (b : BitV n)
| seq (l : list val) (* homogenous finite list *)
| close (l : list Pattern) (e : Expr) (E : ident -> option val)
| infseq (g : nat -> Expr) (E : ident -> option val) (* given an index, return the element *)
| tuple (l : list val) (* heterogeneous tuples *)
.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.

Definition extend (E : env) (id : ident) (v : val) : env :=
  fun x => if Nat.eq_dec x id then Some v else E x.

Definition extend_list (E : env) (id : ident) (vs : list val) : list env :=
  map (fun x => extend E id x) vs.

Fixpoint comp_envs (E : env) (l : list (ident * list val)) : list env :=
  match l with
  | nil => nil
  | (id,vs) :: nil =>
    extend_list E id vs
  | (id,vs) :: r =>
    let Es := comp_envs E r in
    flat_map (fun x => extend_list x id vs) Es
  end.

Definition bind_pat (p : Pattern) (v : val) (E : env) : env :=
  match p with
  | PVar id => extend E id v
  end.


Inductive eval_expr : env -> Expr -> val -> Prop :=
| eval_parens :
    forall E exp v,
      eval_expr E exp v ->
      eval_expr E (EParens exp) v
| eval_var :
    forall E id v,
      E id = Some v ->
      eval_expr E (EVar id) v
| eval_lit :
    forall {w} E n (b : BitV w) t,
      nat_of_bits b = n ->
      eval_expr E (ELit (ECNum n t)) (bits b)
| eval_bool :
    forall E b,
      eval_expr E (EBool b) (bit b)
| eval_list :
    forall E l vs,
      Forall2 (eval_expr E) l vs ->
      eval_expr E (EList l) (seq vs)
| eval_where :
    forall E exp id bexp bv v,
      eval_expr E bexp bv ->
      eval_expr (extend E id bv) exp v ->
      eval_expr E (EWhere exp id bexp) v
| eval_if_t :
    forall E c t f v,
      eval_expr E c (bit true) ->
      eval_expr E t v ->
      eval_expr E (EIf c t f) v
| eval_if_f :
    forall E c t f v,
      eval_expr E c (bit false) ->
      eval_expr E f v ->
      eval_expr E (EIf c t f) v
| eval_lambda :
    forall E l exp,
      eval_expr E (EFun l exp) (close l exp E)
| eval_app :
    forall E f a v pf pr exp E',
      eval_expr E f (close (pf :: pr) exp E') ->
      eval_expr E a v ->
      pr <> nil ->
      eval_expr E (EApp f a) (close pr exp (bind_pat pf v E'))
| eval_app_final :
    forall E f exp E' a p v v',
      eval_expr E f (close (p :: nil) exp E') ->
      eval_expr E a v ->
      eval_expr (bind_pat p v E') exp v' ->
      eval_expr E (EApp f a) v'
| eval_comp : (* Doesn't yet tie the knot, no self reference yet *)
    forall l head vs E lvs' lvs,
      Forall2 (eval_expr E) (map snd l) lvs' ->
      lvs' = map seq lvs ->
      Forall2 (fun e' v => eval_expr e' head v) (comp_envs E (combine (map fst l) lvs)) vs ->
      eval_expr E (EComp head l) (seq vs)
| eval_inf_from :
    forall E g,
      eval_expr E (EInfFrom g) (infseq g E)
| eval_tuple :
    forall E l vs,
      Forall2 (eval_expr E) l vs ->
      eval_expr E (ETuple l) (tuple vs)
| eval_tuple_sel :
    forall E e l n v o,
      eval_expr E e (tuple l) ->
      nth_error l n = Some v ->
      eval_expr E (ESel e (TupleSel n o)) v
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
.                

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
Definition one_ast := ELit (ECNum 1 DecLit).
Definition l_ast := EList [ELit (ECNum 1 DecLit),ELit (ECNum 2 DecLit)].

Lemma eval_one_ast :
  exists n v,
    eval_expr empty one_ast (bits v) /\ @nat_of_bits n v = 1.
Proof.
  exists 1.
  exists (bitCons true (bitNil)). split. econstructor.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma eval_l_ast :
  eval_expr empty l_ast (seq ((bits one) :: (bits two) :: nil)).
Proof.
  repeat econstructor; eauto.
Qed.

Definition id_app := EApp (EParens (EFun [PVar 454] (EVar 454))) (ELit (ECNum 1 DecLit)).

Lemma id_app_eval :
  eval_expr empty id_app (bits one).
Proof.
  repeat econstructor; eauto.
Qed.

Definition two_arg_app := EApp (EApp (EParens (EFun [PVar 456,PVar 457] (EVar 456))) (ELit (ECNum 1 DecLit))) (ELit (ECNum 2 DecLit)).

Lemma two_arg_app_eval :
  eval_expr empty two_arg_app (bits one).
Proof.
  repeat econstructor; eauto; try congruence.
  instantiate (1 := two). reflexivity.
Qed.

Definition tupsel_test := ESel (ETuple [ELit (ECNum 1 DecLit),ELit (ECNum 2 DecLit)]) (TupleSel 1 Nothing).

Lemma tupsel_test_eval :
  eval_expr empty tupsel_test (bits two).
Proof.
  repeat (econstructor; eauto).
  instantiate (1 := one). reflexivity. reflexivity.
Qed.



(*

Definition simple_app := EApp (EFun (O) (EVar O)) (EBool true).

Lemma eval_app_test :
  eval_expr empty simple_app (bit true).
Proof.
  repeat econstructor.
Qed.

(* Tests *)


Definition l := EList ((ELit one) :: (ELit one) :: nil).

Lemma eval_list_test :
  eval_expr empty l (seq ((bits one) :: (bits one) :: nil)).
Proof.
  repeat econstructor.
Qed.


Definition btest := EIf (EBool true) (EBool false) (EVar O).

Lemma btest_eval :
  eval_expr empty btest (bit false).
Proof.
  repeat econstructor.
Qed.

Definition wtest := EWhere (EVar O) O (ELit one).

Lemma wtest_eval :
  eval_expr empty wtest (bits one).
Proof.
  repeat econstructor.
Qed.

Definition ctest := EComp (EVar O) ((O, EList ((ELit one) :: nil)):: nil).

Lemma ctest_eval :
  eval_expr empty ctest (seq ((bits one) :: nil)).
Proof.
  repeat econstructor.
  instantiate (1 := ((bits one :: nil) :: nil)).
  reflexivity.
  repeat econstructor.
Qed.

Definition tupsel_test := ETupSel (ETuple ((EBool true) :: (ELit one) :: nil)) (1).

Lemma tupsel_eval :
    eval_expr empty tupsel_test (bits one).
Proof.
  repeat econstructor.
Qed.

Definition listsel_fin_test := EListSel (EList ((EBool true) :: (ELit one) :: nil)) (ELit one).

Lemma listsel_fin_eval :
  eval_expr empty listsel_fin_test (bits one).
Proof.
  repeat econstructor.
Qed.
  
Definition listsel_inf_test := EListSel (EInfFrom (fun x => EBool true)) (ELit three).

Lemma listsel_inf_eval :
  eval_expr empty listsel_inf_test (bit true).
Proof.
  eapply eval_list_sel_inf;
    repeat econstructor.
Qed.


*)
