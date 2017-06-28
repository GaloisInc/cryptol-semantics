Require Import AST.
Require Import String.
Require Import Coqlib.

Inductive val :=
| bit (b : bool) (* Can we ever get this now? *)
| bits {n} (b : BitV n) (* bitvector *)
| close (id : ident) (e : Expr) (E : ident -> option val)  (* closure *)
| tuple (l : list val) (* heterogeneous tuples *)
| rec (l : list (string * val)) (* records *)
| typ (t : Typ) (* type value, used to fill in type variables *)
| tclose (id : ident) (e : Expr) (E : ident -> option val) (* type closure *)
| vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
| vnil (* empty list *)
| vcomp (e : Expr) (E : ident -> option val) (l : list (list Match)) (* lazy list comprehension *)
| vapp (l1 l2 : Expr) (E : ident -> option val)
| vsplit (n m : Z) (l : Expr) (E : ident -> option val)
(*| vsplitAt (t1 t2 t3 : Typ) (l : Expr) (E : ident -> option val)*)
(* a slice of an underlying list *)
(* NOTE: indexing into slices can be a bit wonky *)
(* you can slice l from 3 to 6 *)
(* then, access 1 would actually go to element 4 of l *)
(* only then would you do any computation on the lazy list *)
| vslice (l h : nat) (e : Expr) (E : ident -> option val)
.

Definition env := ident -> option val.
Definition empty : env := fun _ => None.
