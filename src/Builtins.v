Require Import AST.

(* Borrow from CompCert *)
Require Import Coqlib.

(* TODO: make sure we can shadow variables 5 and 6 here, or change up *)
(* Pretty sure this just works, due to eager evaluation order *)
Definition builtin_binop (id : ident) (op : binop) : DeclGroup :=
  NonRecursive (Decl id (DExpr (EAbs 5 (EAbs 6 (EBinop op (EVar 5) (EVar 6)))))).

Definition builtin_unop (id : ident) (op : unop) : DeclGroup :=
  NonRecursive (Decl id (DExpr (EAbs 5 (EUnop op (EVar 5))))).

(* 17 -> eq *)
(* 1 -> plus *)
(* 11 -> neg *)
(* 40 -> @ *)
Definition plus_decl := builtin_binop 1 Plus.
Definition eq_decl := builtin_binop 17 Eq.
Definition neg_decl := builtin_unop 11 Neg.
(*Definition list_sel_decl := NonRecursive (Decl 40 (DExpr (EAbs 5 (EAbs 6 (EListSel*)
