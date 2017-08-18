Require Import List.
Require Import String.

Require Import Coqlib.

Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import Bitvectors.

Open Scope string.


Fixpoint make_type_arg_list (nt : nat) : list Typ :=
  match nt with
  | O => nil
  | S n' => (TVar (TVBound (Z.of_nat nt) KNum)) :: make_type_arg_list n'
  end.

Fixpoint make_val_arg_list (n : nat) : list Expr :=
  match n with
  | O => nil
  | S n' => (EVar (Z.of_nat n, "")) :: make_val_arg_list n'
  end.

Fixpoint iter {A : Type} (n : nat) (f : nat -> A -> A) (b : A) : A :=
  match n with
  | O => b
  | S n' => f n (iter n' f b)
  end.

Definition mb (num_type_args : nat) (num_args : nat) (b : builtin) : Expr :=
  let l := make_val_arg_list num_args in
  let t := map ETyp (make_type_arg_list num_type_args) in
  let raw_e := iter num_args (fun n => fun x => EAbs (Z.of_nat n, "") x) (EBuiltin b (t++l)) in
  let t_e := iter num_type_args (fun n => fun x => ETAbs ((Z.of_nat n), "") x) raw_e in
  t_e.


(* table of builtins, along with their arity *)
(* mb 9 9 _ indicates hasn't been implemented, will break when tested *)
Definition table : list (string * Expr) :=
  ("demote", mb 2 0 Demote) :: 
  ("+", mb 1 2 Plus) :: (* TESTED *)
  ("-", mb 1 2 Minus) :: 
  ("*", mb 1 2 Times) :: 
  ("/", mb 1 2 Div) :: 
  ("%", mb 1 2 Mod) :: 
  ("^^", mb 1 2 Exp) :: (* Underlying op not implemented *)
  ("lg2", mb 1 2 lg2) :: (* Underlying op not implemented *)
  ("True", mb 0 0 true_builtin) :: (* TESTED *)
  ("False", mb 0 0 false_builtin) :: (* TESTED *)
  ("negate", mb 1 1 Neg) :: 
  ("complement", mb 1 1 Compl) :: 
  ("<", mb 1 2 Lt) :: 
  (">", mb 1 2 Gt) :: 
  ("<=", mb 1 2 Le) ::
  (">=", mb 1 2 Ge) ::
  ("==", mb 1 2 Eq) ::
  ("!=", mb 1 2 Neq) ::
  ("&&", mb 1 2 And) ::
  ("||", mb 1 2 Or) :: 
  ("^", mb 1 2 Xor) :: 
  ("zero", mb 1 0 Zero) :: 
  ("<<", mb 1 2 Shiftl) :: 
  (">>", mb 1 2 Shiftr) :: 
  ("<<<", mb 3 2 Rotl) :: 
  (">>>", mb 3 2 Rotr) :: 
  ("#", mb 3 2 Append) :: 
  ("splitAt", mb 3 1 splitAt) :: 
  ("join", mb 9 9 join) :: (* Not yet implemented *)
  ("split", mb 3 1 split) :: 
  ("reverse", mb 9 9 reverse) :: (* Not yet implemented *)
  ("transpose", mb 9 9 transpose) :: (* Not yet implemented *)
  ("@", mb 3 2 At) :: 
  ("@@", mb 9 9 AtAt) :: (* Not yet implemented *)
  ("!", mb 9 9 Bang) :: (* Not yet implemented *)
  ("!!", mb 9 9 BangBang) :: (* Not yet implemented *)
  ("update", mb 9 9 update) ::(* Not yet implemented *)
  ("updateEnd", mb 9 9 updateEnd) :: (* Not yet implemented *)
  ("fromThen", mb 9 9 fromThen) :: (* Not yet implemented *)
  ("fromTo", mb 9 9 fromTo) :: (* Not yet implemented *)
  ("fromThenTo", mb 9 9 fromThenTo) :: (* Not yet implemented *)
  ("infFrom", mb 9 9 infFrom) :: (* Not yet implemented *)
  ("infFromThen", mb 9 9 infFromThen) :: (* Not yet implemented *)
(*  ("error", mb 9 9 error) :: (* Not yet implemented *)*)
  ("pmult", mb 9 9 pmult) :: (* Not yet implemented *)
  ("pdiv", mb 9 9 pdiv) :: (* Not yet implemented *)
  ("pmod", mb 9 9 pmod) :: (* Not yet implemented *)
(*  ("random", mb 9 9 random) :: (* Not going to be implemented *)*)
(*  ("trace", mb 9 9 trace) :: (* Not going to be implemented *)*)
  nil.

Fixpoint lookup {A : Type} (s : string) (t : list (string * A)) : option A :=
  match t with
  | nil => None
  | (n,a) :: r => if string_dec n s then Some a else lookup s r
  end.

Definition find_builtin (s : string) : option Expr :=
  lookup s table.

Definition lookup_prim (id : ident) : option Expr :=
  let (_,n) := id in
  find_builtin n.
