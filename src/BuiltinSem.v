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
  ("@", mb 9 9 At) ::
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

(* Here we have the semantics of all builtins *)
Inductive eval_builtin : builtin -> list val -> val -> Prop :=
| eval_demote :
    forall {ws : nat} {nz : ws <> O} (w n : Z) (b : BitV ws),
      ws = Z.to_nat w ->
      b = @repr ws nz n ->
      eval_builtin Demote ((typ (TCon (TC (TCNum n)) nil)) :: (typ (TCon (TC (TCNum w)) nil)) :: nil) (bits b)
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
(* | eval_lg2 : *) (* TODO: what is lg2? log base 2? *)
(*     forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t, *)
(*       b3 = @lg2 w nz b1 b2 -> *)
(*       eval_builtin lg2 (t :: (bits b1) :: (bits b2) :: nil) (bits b3) *)
| eval_true :
    eval_builtin true_builtin nil (bit true)
| eval_false :
    eval_builtin false_builtin nil (bit false)
| eval_negate :
    forall {w : nat} {nz : w <> O} (b1 b2 : BitV w) t,
      b2 = @neg w nz b1 ->
      eval_builtin Neg (t :: (bits b1) :: nil) (bits b2)
| eval_compl :
    forall {w : nat} {nz : w <> O} (b1 b2 : BitV w) t,
      b2 = @not w nz b1 ->
      eval_builtin Compl (t :: (bits b1) :: nil) (bits b2)
| eval_lt :
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @ltu w b1 b2 ->
      eval_builtin Lt (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_gt :
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @gtu w b1 b2 ->
      eval_builtin Gt (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_le :  
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @leu w b1 b2 ->
      eval_builtin Le (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_ge :
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @geu w b1 b2 ->
      eval_builtin Ge (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_eq :
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @eq w b1 b2 ->
      eval_builtin Eq (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_neq :
    forall {w : nat} (b1 b2 : BitV w) (b : bool) t,
      b = @neq w b1 b2 ->
      eval_builtin Neq (t :: (bits b1) :: (bits b2) :: nil) (bit b)
| eval_and :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @and w nz b1 b2 ->
      eval_builtin And (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_or :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @or w nz b1 b2 ->
      eval_builtin Or (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_xor :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @xor w nz b1 b2 ->
      eval_builtin Xor (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_zero : (* TODO: cryptol's builtin zero works in more cases than this *)
    forall {ws : nat} {nz : ws <> O} (w : Z) (b : BitV ws),
      ws = Z.to_nat w ->
      b = @repr ws nz 0 -> 
      eval_builtin Zero ((typ (TCon (TC (TCNum w)) nil)) :: nil) (bits b)
| eval_shiftl :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @shl w nz b1 b2 ->
      eval_builtin Shiftl (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_shiftr :
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @shru w nz b1 b2 ->
      eval_builtin Shiftr (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_rotl :    
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @rol w nz b1 b2 ->
      eval_builtin Rotl (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
| eval_rotr :    
    forall {w : nat} {nz : w <> O} (b1 b2 b3 : BitV w) t,
      b3 = @ror w nz b1 b2 ->
      eval_builtin Rotr (t :: (bits b1) :: (bits b2) :: nil) (bits b3)
(*| eval_append :*)
(*| eval_splitAt : *)
(*| eval_split : *)
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

