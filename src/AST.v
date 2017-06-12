Require Import List. 

Inductive Expr (n : nat) := 
(* | EVar n                          (* ^ @ x @ *) *)
| ELit : nat -> Expr n                    (* ^ @ 0x10 @ *)
(*| ETuple [Expr n]                 (* ^ @ (1,2,3) @ *)
| ERecord [Named (Expr n)]        (* ^ @ { x = 1, y = 2 } @ *)
| ESel (Expr n) Selector          (* ^ @ e.l @ *)
| EList [Expr n]                  (* ^ @ [1,2,3] @ *)
| EFromTo (Type n) (Maybe (Type n)) (Maybe (Type n)) (* ^ @[1, 5 ..  117 ] @ *)
| EInfFrom (Expr n) (Maybe (Expr n))(* ^ @ [1, 3 ...] @ *)
| EComp (Expr n) [[Match n]]      (* ^ @ [ 1 | x <- xs ] @ *)
| EApp (Expr n) (Expr n)          (* ^ @ f x @ *)
| EAppT (Expr n) [(TypeInst n)]   (* ^ @ f `{x = 8}, f`{8} @ *)
| EIf (Expr n) (Expr n) (Expr n)  (* ^ @ if ok then e1 else e2 @ *)
| EWhere (Expr n) [Decl n]        (* ^ @ 1 + x where { x = 2 } @ *)
| ETyped (Expr n) (Type n)        (* ^ @ 1 : [8] @ *)
| ETypeVal (Type n)               (* ^ @ `(x + 1)@, @x@ is a type *)
| EFun [Pattern n] (Expr n)       (* ^ @ \\x y -> x @ *)
| ELocated (Expr n) Range         (* ^ position annotation *) 

| EParens (Expr n)                (* ^ @ (e)   @ (Removed by Fixity) *)
| EInfix (Expr n) (Located n) Fixity (Expr n) (* ^ @ a + b @ (Removed by Fixity) *) *)
.