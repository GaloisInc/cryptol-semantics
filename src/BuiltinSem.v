Require Import List.
Require Import String.

Require Import Coqlib.

Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import Integers.

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


(* table of builtins, along with their type and val level arity *)
Definition table : list (string * Expr) :=
  ("demote", mb 2 0 Demote) ::
  ("+", mb 1 2 Plus) ::
  ("-", mb 1 2 Minus) ::
  ("*", mb 1 2 Times) ::
  ("/", mb 1 2 Div) ::
  ("negate", mb 1 1 Neg) ::
  ("==", mb 1 2 Eq) ::
  nil.

(* Here we have the semantics of all builtins *)
Inductive eval_builtin : builtin -> list val -> val -> Prop :=
| eval_plus :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @add w nz b1 b2 ->
      eval_builtin Plus (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_minus :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @sub w nz b1 b2 ->
      eval_builtin Minus (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_times :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @mul w nz b1 b2 ->
      eval_builtin Times (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_div :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @divu w nz b1 b2 -> (* I assume that division is unsigned in cryptol *)
      eval_builtin Div (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_mod :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @modu w nz b1 b2 ->
      eval_builtin Mod (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
(* | eval_exp : *) (* TODO: write pow over bits, or implement in Cryptol *)
(*     forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @exp w nz b1 b2 -> *)
(*       eval_builtin Exp (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
    
| eval_eq :
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @eq w b1 b2 ->
      eval_builtin Eq (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_neg :
    forall {w : nat} {nz : w <> O} (b1 b2 : BitV w) t,
      b2 = @neg w nz b1 ->
      eval_builtin Neg (t :: (bits b1) :: nil) (bits b2)
| eval_demote :
    forall {ws : nat} {nz : ws <> O} (w n : Z) (b : BitV ws),
      ws = Z.to_nat w ->
      b = @repr ws nz n ->
      eval_builtin Demote ((typ (TCon (TC (TCNum n)) nil)) :: (typ (TCon (TC (TCNum w)) nil)) :: nil) (bits b)
.

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
              
