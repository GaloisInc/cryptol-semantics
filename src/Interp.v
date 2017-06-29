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

Require Import Semantics. 
Require Import EvalTac.  

Fixpoint eval (gen : genv) (en : env) (e : Expr) : option val := 
 let eval' := eval gen en in 
  match e with 

  | EBuiltin e' args => 
     match (e', args) with  
    (* Only have cases for cond of if-statement *)
     | (true_builtin, nil)  => Some (bit true)
     | (false_builtin, nil) => Some (bit false) (* don't actually need this case *)
     | _             => None
     end

 (* Lookup var in local env *)
  | EVar v => en v 

  | EIf cond t f => 
    (* evaluate cond, take appropriate branch *)
     match (eval' cond) with 
     | Some (bit true) => eval' t
     | _               => eval' f
     end

  | EWhere e' ds => 
     match ds with 
     (* Trivial "where" *)
     | nil => eval' e'
     | cons d ds' => 
       match d with 
       (* Not yet handled *)
       | Recursive _ => None 
       | NonRecursive (Decl id d') => 
         match d' with 
        (* Ignore the "where" *)
         | DPrim     => eval' e' 
         | DExpr e'' => 
           match eval' e'' with
          (* Evaluate in extended local env *)
           | Some v => eval gen (extend en id v) e'
           | None   => None
           end
         end
       end
     end  
  | _ => None
end.




(************ Examples ************)

Definition sample_env : env := extend (extend empty (0, "zero") (bit true))
                                   (1, "one") (bit false). 


(* eval' (if 0 then 1 else 0) = 0 *)
Eval compute in (eval gempty sample_env (EIf (EBuiltin false_builtin nil) (EVar (0, "zero")) (EVar (1, "one")))).   

(* eval' (if 1 then 1 else 0) = 1 *)
Eval compute in (eval gempty sample_env (EIf (EBuiltin true_builtin nil) (EVar (0, "zero")) (EVar (1, "one")))).

(* eval' a var not in the local env (should get "None") *)
Eval compute in (eval gempty sample_env (EVar (2, "hello"))).


(* eval' (if x where x = false then 1 else 0 *)
Eval compute in (eval gempty sample_env 
   (EWhere (EIf (EVar (2, "x")) (EVar (0, "zero")) (EVar (1, "one"))) 
    [NonRecursive (Decl (2, "x") (DExpr (EBuiltin false_builtin nil)))])). 

(* eval' (if x where x = true then 1 else 0 *)
Eval compute in (eval gempty sample_env 
   (EWhere (EIf (EVar (2, "x")) (EVar (0, "zero")) (EVar (1, "one"))) 
    [NonRecursive (Decl (2, "x") (DExpr (EBuiltin true_builtin nil)))])).



(************ Theorem ************)

(* Interesting cases are currently admitted *)
Theorem eval_expr_if_eval : forall gen en e v, 
   eval gen en e = Some v -> eval_expr gen en e v.
Proof. 
  intros. induction e. inversion H. destruct b in H1; try inversion H1; subst.
  (* EBuiltin true *)
  - econstructor.
    destruct l. inv H1. destruct b; simpl in H; inv H.
    econstructor; eauto. congruence.
 (* EBuiltin false *)
  - econstructor.
    destruct l. inv H1. destruct b; simpl in H; inv H.
    econstructor; eauto. congruence.
 (* EList *)  
  - inversion H.  
 (* ETuple *)
  - inversion H.
 (* ERec *) 
  - inversion H.  
 (* ESel *)   
  - inversion H.  
 (* EIf *)
  - admit.    
 (* EComp *)
  - inversion H. 
 (* EVar *)
  - inversion H. econstructor. assumption. 
 (* ETAbs *)
  - inversion H. 
 (* ETApp *)
  - inversion H.
 (* EAbs *)
  - inversion H.
 (* EApp *) 
  - inversion H. 
 (* EWhere *)
  - inversion H.
Admitted.   
