Require Import List. 
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

(* TODO *)
(* *)

Inductive Expr :=
(* boolean literal, e.g. True *)
| EBool (b : bool)
(* Variable, e.g. 'x' *)
| EVar : ident -> Expr
(* Literal, e.g. 0x1200 *)
| ELit {n} : BitV n -> Expr
(* Literal finite list, e.g. [1,2,3] *)
| EList : list Expr -> Expr
(* Function application, e.g. f v *)
| EApp (f v : Expr)
(* If/then/else, e.g. if cond then t else f *)
| EIf (cond t f : Expr)
(* Where, e.g. 1 + x where { x = 2 } *)
| EWhere : Expr -> ident -> Expr -> Expr
(* Anonymous function, e.g. \\x -> x *)
| EFun (id : ident) (e : Expr)
(* List Comprehension, e.g. [ p + q | p <- xs | q <- ys ] *)
| EComp (e : Expr) (l : list (ident * Expr))
(* infinite sequence, e.g. [1,2,...] *)
| EInfFrom (f : nat -> Expr)
(* Tuples, e.g. (1,2,3) *)
| ETuple (l : list Expr)
(* Tuple select: pull one datum out of a tuple *)
| ETupSel (e : Expr) (n : nat)
(* List Select: index into a list *)
| EListSel (lst : Expr) (idx : Expr)
         
(*| ETuple [Expr n]                 (* ^ @ (1,2,3) @ *)
| ERecord [Named (Expr n)]        (* ^ @ { x = 1, y = 2 } @ *) 
| ESel (Expr n) Selector          (* ^ @ e.l @ *) *)
(*| EFromTo (Type n) (Maybe (Type n)) (Maybe (Type n)) (* ^ @[1, 5 ..  117 ] @ *)
| EInfFrom (Expr n) (Maybe (Expr n))(* ^ @ [1, 3 ...] @ *)
| EComp (Expr n) [[Match n]]      (* ^ @ [ 1 | x <- xs ] @ *) *)
(*| EAppT (Expr n) [(TypeInst n)]   (* ^ @ f `{x = 8}, f`{8} @ *)*)
(*| ETyped (Expr n) (Type n)        (* ^ @ 1 : [8] @ *)
| ETypeVal (Type n)               (* ^ @ `(x + 1)@, @x@ is a type *) *)
(*| ELocated (Expr n) Range         (* ^ position annotation *) 
| EParens (Expr n)                (* ^ @ (e)   @ (Removed by Fixity) *)
| EInfix (Expr n) (Located n) Fixity (Expr n) (* ^ @ a + b @ (Removed by Fixity) *) *)
.

(* Operational Semantics *)

Inductive val :=
| bit (b : bool)
| bits {n} (b : BitV n)
| seq (l : list val) (* homogenous finite list *)
| close (x : ident) (e : Expr) (E : ident -> option val)
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

Inductive eval_expr : env -> Expr -> val -> Prop :=
| eval_var :
    forall E id v,
      E id = Some v ->
      eval_expr E (EVar id) v
| eval_lit :
    forall E n b,
      eval_expr E (ELit b) (@bits n b)
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
    forall E id exp,
      eval_expr E (EFun id exp) (close id exp E)
| eval_app :
    forall E f id exp E' a v v',
      eval_expr E f (close id exp E') ->
      eval_expr E a v ->
      eval_expr (extend E' id v) exp v' ->
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
    forall E e l n v,
      eval_expr E e (tuple l) ->
      nth_error l n = Some v ->
      eval_expr E (ETupSel e n) v
| eval_list_sel_fin :
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
      eval_expr E (EListSel lst idx) v
.                

(* Tests *)

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

Definition l := EList ((ELit one) :: (ELit one) :: nil).

Lemma eval_list_test :
  eval_expr empty l (seq ((bits one) :: (bits one) :: nil)).
Proof.
  repeat econstructor.
Qed.

Definition simple_app := EApp (EFun (O) (EVar O)) (EBool true).

Lemma eval_app_test :
  eval_expr empty simple_app (bit true).
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
  econstructor.
  econstructor.
  econstructor. econstructor.
  econstructor.
  econstructor.
  econstructor.
  
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

