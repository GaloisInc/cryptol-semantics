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
  ("^^", mb 1 2 Exp) ::
  ("lg2", mb 1 2 lg2) ::
  ("True", mb 0 0 true_builtin) :: (* TESTED *)
  ("False", mb 0 0 false_builtin) :: (* TESTED *)
  ("negate", mb 1 1 Neg) :: (* TESTED *)
  ("complement", mb 1 1 Compl) :: (* TESTED *)
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
  ("<<<", mb 1 2 Rotl) ::
  (">>>", mb 1 2 Rotr) ::
  ("#", mb 3 2 Append) ::
  ("splitAt", mb 3 1 splitAt) ::
  ("join", mb 9 9 join) ::
  ("split", mb 3 1 split) ::
  ("reverse", mb 9 9 reverse) ::
  ("transpose", mb 9 9 transpose) ::
  ("@", mb 3 2 At) ::
  ("@@", mb 9 9 AtAt) ::
  ("!", mb 9 9 Bang) ::
  ("!!", mb 9 9 BangBang) ::
  ("update", mb 9 9 update) ::
  ("updateEnd", mb 9 9 updateEnd) ::
  ("fromThen", mb 9 9 fromThen) ::
  ("fromTo", mb 9 9 fromTo) ::
  ("fromThenTo", mb 9 9 fromThenTo) ::
  ("infFrom", mb 9 9 infFrom) ::
  ("infFromThen", mb 9 9 infFromThen) ::
  ("error", mb 9 9 error) ::
  ("pmult", mb 9 9 pmult) ::
  ("pdiv", mb 9 9 pdiv) ::
  ("pmod", mb 9 9 pmod) ::
  ("random", mb 9 9 random) ::
  ("trace", mb 9 9 trace) ::
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

