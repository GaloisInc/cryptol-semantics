(*
1. eval function : genv -> env -> Expr -> option val
2. proof that eval gen en e = some j -> eval_expr gen en e j

ex: eval (if 0 then 1 else 0) = 0
*)


Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.

(*Require Import Integers.*)
Require Import Bitvectors.
Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import BuiltinSem.


Fixpoint eval (gen : genv) (en : env) (e : Expr) : option val := 
  let eval' := eval gen en in 
  match e with 
  | EBuiltin e' args => 
     match e' with 
     | true_builtin  => Some (bit true)
     | false_builtin => Some (bit false) 
     | _             => None
     end
  | EVar v => en v 
  | EIf cond t f => 
     match (eval' cond) with 
     | Some (bit true) => eval' t
     | _               => eval' f
     end
  | _ => None
end.

Definition sample_env : env := extend (extend empty (0, "zero") (bit true))
                                   (1, "one") (bit false). 


Eval compute in (eval gempty sample_env (EIf (EBuiltin false_builtin nil) (EVar (0, "zero")) (EVar (1, "one")))).   


