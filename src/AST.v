Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.
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

Definition BitV (n : nat) : Type := (@Bitvectors.Int n).



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
| TVFree (n : Z) (k : Kind) (l : list TV_t)
| TVBound (n : Z) (k : Kind)
.

Inductive Typ :=
| TCon (tc : TConstr) (l : list Typ)
| TVar (tv : TV_t)
| TUser (id : ident) (l : list Typ) (t : Typ)
| TRec (l : list (string * Typ))
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
| ETApp (e : Expr) (t : Expr)
(* Type *)
| ETyp (t : Typ)
(* Function application, e.g. f v *)
| EApp (f v : Expr)
(* Anonymous function, e.g. \\x -> x *)
| EAbs (id : ident) (e : Expr)
(* MISSING: EProofAbs *)
(* MISSING: EProofApp *)
(* Where, e.g. 1 + x where { x = 2 } *)
| EWhere (e : Expr) (l : list DeclGroup)

(* The following expressions are not in the source langugage, but are *)
(* necessary for evaluation *)
(* list append *)
| EAppend (e1 e2 : Expr)
(* head of list *)
| EHead (e : Expr)
(* tail of list (n times) *)
| ETail (n : nat) (e : Expr)
(* Expression that is a value *)
| EValue (v : val)
with Match :=
     | From (id : ident) (e : Expr)
     | MLet (d : Declaration)
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
with val :=
     | bit (b : bool) (* Can we ever get this now? *)
     (*| bits {n} (b : BitV n) (* bitvector *)*)
     | close (id : ident) (e : Expr) (E : ident -> option val)  (* closure *)
     | tclose (id : ident) (e : Expr) (E : ident -> option val) (* type closure *)
     | tuple (l : list val) (* heterogeneous tuples *)
     | rec (l : list (string * val)) (* records *)
     | typ (t : Typ) (* type value, used to fill in type variables *)
     | vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
     | vnil (* empty list *)
.

Definition extend { vtype : Type } (E : ident -> option vtype) (id : ident) (v : vtype) :=
  fun x => if ident_eq x id then Some v else E x.

Definition genv := ident -> option Expr.
Definition gempty : genv := fun _ => None.



