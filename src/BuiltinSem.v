Require Import List.
Require Import String.

Require Import Coqlib.

Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import Bitvectors.

Open Scope string.

Fixpoint make_arg_list (n : nat) : list Expr :=
  match n with
  | O => nil
  | S n' => (EVar (Z.of_nat n, "")) :: make_arg_list n'
  end.

Fixpoint iter {A : Type} (n : nat) (f : nat -> A -> A) (b : A) : A :=
  match n with
  | O => b
  | S n' => f n (iter n' f b)
  end.

Definition mb (num_type_args : nat) (num_args : nat) (b : builtin) : Expr :=
  let l := make_arg_list (num_args + num_type_args) in 
  let raw_e := iter num_args (fun n => fun x => EAbs (Z.of_nat n, "") x) (EBuiltin b l) in
  let t_e := iter num_type_args (fun n => fun x => ETAbs ((Z.of_nat (n + num_args )), "") x) raw_e in
  t_e.


(* table of builtins, along with their arity *)
Definition table : list (string * Expr) :=
  ("demote", mb 2 0 Demote) :: (* TESTED *)
  ("+", mb 1 2 Plus) :: (* TESTED *)
  ("-", mb 1 2 Minus) :: (* TESTED *)
  ("*", mb 1 2 Times) :: (* TESTED *)
  ("/", mb 1 2 Div) :: (* TESTED *)
  ("%", mb 1 2 Mod) :: (* TESTED *)
  ("^^", mb 1 2 Exp) :: (* Underlying op not implemented *)
  ("lg2", mb 1 2 lg2) :: (* Underlying op not implemented *)
  ("True", mb 0 0 true_builtin) :: (* TESTED *)
  ("False", mb 0 0 false_builtin) :: (* TESTED *)
  ("negate", mb 1 1 Neg) :: (* TESTED *)
  ("complement", mb 1 1 Compl) :: (* TESTED *)
  ("<", mb 1 2 Lt) :: (* Implemented, needs testing *)
  (">", mb 1 2 Gt) :: (* Implemented, needs testing *)
  ("<=", mb 1 2 Le) :: (* Implemented, needs testing *)
  (">=", mb 1 2 Ge) :: (* Implemented, needs testing *)
  ("==", mb 1 2 Eq) :: (* Implemented, needs testing *)
  ("!=", mb 1 2 Neq) :: (* Implemented, needs testing *)
  ("&&", mb 1 2 And) :: (* Implemented, needs testing *)
  ("||", mb 1 2 Or) :: (* Implemented, needs testing *)
  ("^", mb 1 2 Xor) :: (* Implemented, needs testing *)
  ("zero", mb 1 0 Zero) :: (* Partially implemented, needs testing (and full implementation) *)
  ("<<", mb 1 2 Shiftl) :: (* Implemented, needs testing *)
  (">>", mb 1 2 Shiftr) :: (* Implemented, needs testing *)
  ("<<<", mb 1 2 Rotl) :: (* Implemented, needs testing *)
  (">>>", mb 1 2 Rotr) :: (* Implemented, needs testing *)
  ("#", mb 3 2 Append) :: (* TESTED *)
  ("splitAt", mb 3 1 splitAt) :: (* TESTED *)
  ("join", mb 9 9 join) :: (* Not yet implemented *)
  ("split", mb 3 1 split) :: (* TESTED *)
  ("reverse", mb 9 9 reverse) :: (* Not yet implemented *)
  ("transpose", mb 9 9 transpose) :: (* Not yet implemented *)
  ("@", mb 3 2 At) :: (* TESTED *)
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
  ("error", mb 9 9 error) :: (* Not yet implemented *)
  ("pmult", mb 9 9 pmult) :: (* Not yet implemented *)
  ("pdiv", mb 9 9 pdiv) :: (* Not yet implemented *)
  ("pmod", mb 9 9 pmod) :: (* Not yet implemented *)
  ("random", mb 9 9 random) :: (* Not yet implemented *)
  ("trace", mb 9 9 trace) :: (* Not yet implemented *)
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

