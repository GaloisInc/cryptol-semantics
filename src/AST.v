Require Import String.
Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.
Require Import Builtins.

(* An identifier is both a unique identifier and a name, but the name is meaningless *)
Definition ident : Type := Z * string.

(* This definition is what makes the name meaningless *)
(* We leave the name in since it helps with reading ASTs *)
Definition ident_eq :
  forall (x y : ident),
    { fst x = fst y } + { fst x <> fst y }.
Proof.
  decide equality;
  eapply Pos.eq_dec. 
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
| TCNum (z : Z)
| TCInf
| TCBit
| TCSeq
| TCFun
| TCTuple (n : nat)
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
| TVFree (uid : Z) (k : Kind) (l : list TV_t)
| TVBound (uid : Z) (k : Kind)
.

Inductive Typ :=
| TCon (tc : TConstr) (l : list Typ)
| TVar (tv : TV_t)
| TUser (id : ident) (l : list Typ) (t : Typ)
| TRec (l : list (string * Typ))
.

(* Type level values *)
Inductive Tval :=
| trec (l : list (string * Tval)) (* record *)
| ttup (l : list Tval) (* tuple *)
| tseq (len : Tval) (elem : Tval)
| tfun (argt : Tval) (res : Tval)
| tnum (z : Z)
| tbit
| tinf (* length of infinite streams *)
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
(* first element of list *)
| EHead (e : Expr)
(* drop first n elements of list, leave the rest *)
| EDrop (n : nat) (e : Expr)
(* take first n elements of a list, throw out rest *)
| ETake (n : nat) (e : Expr)
(* Expression that is a value *)
| EValue (v : val)
(* Lifted evaluation of unary builtin *)
| ELiftUnary (b : builtin) (targs : list Expr) (e : Expr)
(* Lifted evaluation of binary builtin *)             
| ELiftBinary (b : builtin) (targs : list Expr) (e1 e2 : Expr) (env1 env2 : ident -> option val)
(* List Comprehension Implementation: keep track of where you are with a nat *)
| ECompImp (e : Expr) (n : nat) (llm : list (list Match))
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
     | close (id : ident) (e : Expr) (E : ident -> option val)  (* closure *)
     | tclose (id : ident) (e : Expr) (E : ident -> option val) (* type closure *)
     | tuple (l : list val) (* heterogeneous tuples *)
     | rec (l : list (string * val)) (* records *)
     | typ (t : Tval) (* type value, used to fill in type variables *)
     | vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
     | vnil (* empty list *)
with strictval :=
     | sbit (b : bool)
     | stuple (l : list strictval) (* heterogeneous tuples *)
     | srec (l : list (string * strictval)) (* records *)
     | styp (t : Tval) (* type value, used to fill in type variables *)
     | sclose (id : ident) (e : Expr) (E : ident -> option strictval)
     | stclose (id : ident) (e : Expr) (E : ident -> option strictval)
     | svcons (f r : strictval) 
     | svnil (* empty list *)
.

Fixpoint strict_list (lv : list strictval) : strictval :=
  match lv with
  | nil => svnil
  | f :: r => svcons f (strict_list r)
  end.


Definition extend { vtype : Type } (E : ident -> option vtype) (id : ident) (v : vtype) :=
  fun x => if ident_eq x id then Some v else E x.

Definition genv := ident -> option Expr.
Definition gempty : genv := fun _ => None.


Definition env := ident -> option val.
Definition empty : env := fun _ => None.


