Require Import AST.
Require Import String.

Inductive val :=
| bit (b : bool) (* Can we ever get this now? *)
| bits {n} (b : BitV n) (* bitvector *)
| close (id : ident) (e : Expr) (E : ident -> option val)  (* closure *)
| tuple (l : list val) (* heterogeneous tuples *)
| rec (l : list (string * val))
| vcons (v : val) (e : Expr) (E : ident -> option val) (* lazy list: first val computed, rest is thunked *)
| vnil (* empty list *)
| vcomp (e : Expr) (E : ident -> option val) (l : list (list Match)) (* lazy list comprehension *)
| typ (t : Typ) (* type value, used to fill in type variables *)
| tclose (id : ident) (e : Expr) (E : ident -> option val) (* type closure *)
.
