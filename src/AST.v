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


Inductive CType := (*TFun (CType n) (CType n)  -- ^ @[8] -> [8]@
            | TSeq (CType n) (CType n)  -- ^ @[8] a@ *)
| TSeq (len : CType) (T : CType) (* Tnum for finite, Tinf for inf, T for type *)
| TBitv (n : nat)                    (* ^ @Bit@*)
| TNum (n : nat)            (* ^ @10@*)
| TInf
(*            | TChar Char              -- ^ @'a'@
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
(* Add comprehensions *)
(* Add tests for each Expr *)

Inductive Expr :=
| EBool (b : bool)
(* boolean literal, e.g. True *)
| EVar : ident -> Expr
(* Variable, e.g. 'x' *)
| ELit {n} : BitV n -> Expr
(* Literal, e.g. 0x1200 *)
| EList : list Expr -> Expr
(* Literal finite list, e.g. [1,2,3] *)
| EApp (f v : Expr)
(* Function application, e.g. f v *)
| EIf (cond t f : Expr)
(* If/then/else, e.g. if cond then t else f *)
| EWhere : Expr -> ident -> Expr -> Expr
(* Where, e.g. 1 + x where { x = 2 } *)
| EFun (id : ident) (e : Expr)
(* Anonymous function, e.g. \\x -> x *)

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
| seq (l : list val)
| close (x : ident) (e : Expr) (E : ident -> option val)
.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.

Definition extend (E : env) (id : ident) (v : val) : env :=
  fun x => if Nat.eq_dec x id then Some v else E x.

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
      eval_expr E (EApp f a) v'.


(* Tests *)

Definition one : BitV (S (S O)).
  eapply bitCons. exact false.
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
