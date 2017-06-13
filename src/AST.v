Require Import List. 
Require Import Coq.Arith.PeanoNat.

Definition ident := nat.


Inductive CType := (*TFun (CType n) (CType n)  -- ^ @[8] -> [8]@
            | TSeq (CType n) (CType n)  -- ^ @[8] a@ *)
| TBit                    (* ^ @Bit@*)
| TNum (n : nat)            (* ^ @10@*)
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

(* Note: just make a recursive eval_expr relation *)


Inductive Expr := 
| EVar : ident -> Expr                          (* ^ @ x @ *) 
| ELit : bool -> Expr                    (* ^ @ 0x10 @ *)
(*| ETuple [Expr n]                 (* ^ @ (1,2,3) @ *)
| ERecord [Named (Expr n)]        (* ^ @ { x = 1, y = 2 } @ *)
| ESel (Expr n) Selector          (* ^ @ e.l @ *)
| EList [Expr n]                  (* ^ @ [1,2,3] @ *)
| EFromTo (Type n) (Maybe (Type n)) (Maybe (Type n)) (* ^ @[1, 5 ..  117 ] @ *)
| EInfFrom (Expr n) (Maybe (Expr n))(* ^ @ [1, 3 ...] @ *)
| EComp (Expr n) [[Match n]]      (* ^ @ [ 1 | x <- xs ] @ *) *)
| EApp (f v : Expr)          (* ^ @ f x @ *)
(*| EAppT (Expr n) [(TypeInst n)]   (* ^ @ f `{x = 8}, f`{8} @ *)*)
| EIf (cond t f : Expr)   (* ^ @ if ok then e1 else e2 @ *) 
| EWhere : Expr -> ident -> Expr -> Expr        (* ^ @ 1 + x where { x = 2 } @ *)
(*| ETyped (Expr n) (Type n)        (* ^ @ 1 : [8] @ *)
| ETypeVal (Type n)               (* ^ @ `(x + 1)@, @x@ is a type *) *)
| EFun (id : ident) (e : Expr)       (* ^ @ \\x y -> x @ *)
(*| ELocated (Expr n) Range         (* ^ position annotation *) 

| EParens (Expr n)                (* ^ @ (e)   @ (Removed by Fixity) *)
| EInfix (Expr n) (Located n) Fixity (Expr n) (* ^ @ a + b @ (Removed by Fixity) *) *)
.

Inductive val :=
| bit (b : bool)
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
    forall E b,
      eval_expr E (ELit b) (bit b)
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

      

(*                

Inductive state :=
| Run (st : list env) (E : env) (e : Expr)
| Stop (v : val).





Inductive step : state -> state -> Prop :=
| st_var : (* evaluate a variable in an environment *)
    forall st E id v,
      E id = Some v ->
      step (Run st E (EVar id)) (Stop v)
| st_lit : (* evaluate a literal *)
    forall st E b,
      step (Run st E (ELit b)) (Stop (bit b))
| st_if_cond : (* step the condition *)
    forall st E c t f c' st' E',
      step (Run st E c) (Run st' E' c') ->
      step (Run st E (EIf c t f)) (Run st' E' (EIf c' t f)).
| st_if_t :
    forall st E c t f,
      step (Run (x :: st) E c) (Stop (bit true)) ->
      step (Run (x :: st) E (EIf c t f)) (Run st x t)
| st_if_f :
    forall st E c t f,
      step (Run st E c) (Stop (bit false)) ->
      step (Run st E (EIf c t f)) (Run st E f)
| st_where_r :
    forall st E id_expr id_expr' expr id,
      step (Run st E id_expr) (Run st E id_expr') ->
      step (Run st E (EWhere expr id id_expr)) (Run st E (EWhere expr id id_expr'))
| st_where_v :
    forall st e id_expr expr id,
      step (Run st e id_expr) (Stop v) ->
      step (Run st e (EWhere expr id id_expr)) (Run (e :: st) (extend e id v) (EPop expr))
| st_pop :
    

(* 

if (x where x = false) then 1 else 0


*)
    



Definition step (st : state) : option state :=
  match st with
  | Run s E e =>
    match e with
    | ELit m => Some (Stop (bit m))
    | EVar id =>
      match E id with
      | Some v => Some (Stop v)
      | None => None
      end
    | EWhere exp id rhs =>
      
      match eval E rhs with
      | Some rhv =>
        eval (extend E id rhv) exp
      | None => None
      end
    | EIf cond t f =>
      match eval E cond with
      | Some (bit true) => eval E t
      | Some (bit false) => eval E f
      | _ => None
      end
        
  

Fixpoint eval (E : env) (e : Expr) : option val :=
  match e with
  | ELit m => Some (bit m)
  | EVar id => E id
  | EWhere exp id rhs =>
    match eval E rhs with
    | Some rhv =>
      eval (extend E id rhv) exp
    | None => None
    end
  | EIf cond t f =>
    match eval E cond with
    | Some (bit true) => eval E t
    | Some (bit false) => eval E f
    | _ => None
    end
  | EFun id e =>
    Some (close id e E)
  | EApp f v =>
    match eval E f with
    | Some (close id e E') =>
      match eval E v with
      | Some v' =>
        eval (extend E' id v') e
      | None => None
      end
    | _ => None
    end
  end.

*)