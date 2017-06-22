Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.
Require Import Builtins.

Definition ident : Type := Z * string.

Definition ident_eq :
  forall (x y : ident),
    { x = y } + { x <> y }.
Proof.
  decide equality.
  eapply string_dec.
  eapply Z.eq_dec.
Defined.

Definition BitV (n : nat) : Type := (@Integers.Int n).



Inductive Kind :=
| KType
| KNum
| KProp
(* | Kind :-> Kind *)
.

Inductive userType :=
| UserTC (id : ident) (k : Kind)
.

Inductive TypeConstr :=
| TCNum (n : Z)
| TCInf
| TCBit
| TCSeq
| TCFun
| TCTuple (n : Z)
| TCNewtype (u : userType)
.

Inductive TFun :=
| TCWidth
| TCAdd
| TCSub
| TCMul
| TCDiv
| TCMod
| TCExp
| TCMin
| TCMax
| TCLenFromThen
| TCLenFromThenTo
.

Inductive TConstr :=
| TC (t : TypeConstr)
| TF (tf : TFun)
.     

Inductive TV_t :=
| TVFree (n : nat) (k : Kind) (l : list TV_t)
| TVBound (n : nat) (k : Kind)
.

Inductive Typ :=
| TCon (tc : TConstr) (l : list Typ)
| TVar (tv : TV_t)
| TUser (id : ident) (l : list Typ) (t : Typ)
| TRec (l : list (ident * Typ))
.

Inductive Expr :=
(* builtin *)
| EBuiltin (b : builtin) (l : list Expr)
(* Literal finite list, e.g. [1,2,3] *)
| EList (l : list Expr)
(* Tuples, e.g. (1,2,3) *)
| ETuple (l : list Expr)
(* Records *)
| ERec (l : list (string * Expr))
(* select: pull one datum out of a record/tuple/list *)
| ESel (e : Expr) (s : Selector)
(* If/then/else, e.g. if cond then t else f *)
| EIf (cond t f : Expr)
(* List Comprehension, e.g. [ p + q | p <- xs | q <- ys ] *)
| EComp (e : Expr) (l : list (list Match))
(* Variable, e.g. 'x' *)
| EVar (id : ident)
(* Type abstraction *)
| ETAbs (id : ident) (e : Expr)
(* Type application *)
| ETApp (e : Expr) (t : Typ)
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
     | DPrim
with Declaration := 
     | Decl (id : ident) (d : DeclDef)
with DeclGroup :=
     | Recursive (l : list Declaration)
     | NonRecursive (d : Declaration)
with Selector :=
     | TupleSel (n : nat)
     | ListSel (e : Expr)
     | RecordSel (s : string)
.




