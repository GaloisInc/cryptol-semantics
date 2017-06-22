Require Import List.
Import ListNotations.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Integers.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import Tactics.  
        
Require Import ZArith.Znat.  

Import HaskellListNotations.

Require Import Fib. 


Definition nz32 (n:Z) := @repr 32 nz n.
Definition add32 (x y : Int) := @add 32 nz x y. 
Definition sub32 (x y : Int) := @sub 32 nz x y. 


(*
Writing a Fib function over 32bit Ints doesn't appear to be fruitful since Coq doesn't believe that it terminates (since it doesn't for any negative argument). 

Fixpoint fib (n : @Int 32) : (@Int 32) := 
  if (eq n (nz32 0)) then (nz32 1)
  else if (eq n (nz32 1)) then (nz32 1)
  else add32 (fib (add32 n (nz32 (-1)))) (fib (add32 n (nz32(-2)))). 

Instead we will just define Fib over nats and then convert the result to a 32bit Int. Our equivalence theorem will have to have a restriction on the size of the input to take overflow into account
*)

Fixpoint fib (n : nat) : nat :=
  match n with
  | O  => S O 
  | S n' => match n' with 
         | O => S O
         | S n'' => fib n' + fib n''
  end
end.

(* Example of converting a fib result to 32bit Int *)
Eval compute in (nz32 (Z.of_nat (fib 5))).   

(* For the condition of the equiv theorem *)
Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

(* Just get the intval field in the Int record *)
Definition Int32_to_Z (n : Int) : Z := @intval 32 n. 

(* Lots of type conversion to say "Fib.cry n = fib n" *)
Theorem fib_equiv : forall n, Is_true (ltu n (nz32 (@max_unsigned 32))) -> 
   eval_expr fib_ge (Env (Int32_to_Z n)) (EApp (EVar fibnum) (EVar fibvar)) 
   (bits (nz32 (Z.of_nat (fib (Z.to_nat (Int32_to_Z n)))))). 
Proof. 
  intros.  
  e.
  - global. e.
  - local. 
  - induction (Z.to_nat (Int32_to_Z n)). (* induction on n as a nat *)
    + eapply eval_if_t. 
    e. e. e. global. e. local. e. e. e. local. local.
      * constructor; exact nz.
      * e. 
    + econstructor. e. e. e. global. e. local. e. e. e. local. local.
      * destruct p. (* these aren't all true. Probably chose a constructor too early (eval_if_t) *)







