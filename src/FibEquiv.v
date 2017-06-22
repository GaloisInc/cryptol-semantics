Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
        

Import HaskellListNotations.

Require Import Fib. 


Definition nz32 (n:Z) := @repr 32 nz n.
Definition add32 (x y : Int) := @add 32 nz x y. 
Definition sub32 (x y : Int) := @sub 32 nz x y. 

(*
Fixpoint fib (n : @Int 32) : (@Int 32) := 
  if (eq n (nz32 0)) then (nz32 1)
  else if (eq n (nz32 1)) then (nz32 1)
  else add32 (fib (sub32 n (nz32 2))) (fib (sub32 n (nz32 1))). 



Theorem fib_equiv : forall n,
   eval_expr fib_ge (Env n) (EApp (EVar fibnum) (EVar fibvar)) 
   (bits (@repr width nz (fib n)). 

*)


