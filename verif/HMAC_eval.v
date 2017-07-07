Require Import List.
Import ListNotations.
Require Import String.

(* Borrow from CompCert *)
Require Import Coqlib.
Require Import Bitvectors.

Require Import AST.
Require Import Semantics.
Require Import Utils.
Require Import Builtins.
Require Import BuiltinSem.
Require Import Values.        

Require Import EvalTac.

Import HaskellListNotations.
Open Scope string.

Require Import HMAC.

Definition z : Expr := EList (EValue (thunk_list (repeat (bit false) 8)) :: nil).

Definition t : Expr := ETyp (TCon (TC (TCNum 1)) nil).

(* Convert a hex string to a list of bits *)
Definition hex_digits := match collect [get 0 "0",get 0 "1",get 0 "2",get 0 "3",
                                        get 0 "4",get 0 "5",get 0 "6",get 0 "7",
                                        get 0 "8",get 0 "9",get 0 "a",get 0 "b",
                                        get 0 "c",get 0 "d",get 0 "e",get 0 "f"] with
                         | Some l => l
                         | None => nil
                         end.

Lemma hex_digits_not_nil :
  hex_digits <> nil.
Proof.
  unfold hex_digits. simpl.
  congruence.
Qed.

Fixpoint lookup_h {A : Type} (eq_dec : forall (a b : A), {a = b} + {a <> b}) (x : A) (l : list A) : option nat :=
  match l with
  | nil => None
  | f :: r =>
    if eq_dec f x then Some O else
      match lookup_h eq_dec x r with
      | Some n => Some (S n)
      | None => None
      end
  end.

Definition lookup (a : Ascii.ascii) : option nat :=
  lookup_h Ascii.ascii_dec a hex_digits.

Definition to_bits (a : Ascii.ascii) : option (list val) :=
  match lookup a with
  | Some n =>
    Some (@from_bitv 4 (@repr 4 (Z.of_nat n)))
  | None => None
  end.

Fixpoint val_of_hex_string (s : string) : option (list val) :=
  match s with
  | EmptyString => Some nil
  | String a s' =>
    match val_of_hex_string s' with
    | Some l =>
      match to_bits a with
      | Some bs => Some (bs ++ l)%list
      | None => None
      end
    | None => None
    end
  end.


Definition val_of_hex_lit (s : string) : option (list val) :=
  val_of_hex_string (substring 2 (length s) s).

Definition result_hex := "0x6620b31f2924b8c01547745f41825d322336f83ebb13d723678789d554d8a3ef".

Definition result : list val.
  destruct (val_of_hex_lit result_hex) eqn:?.
  Focus 2. cbv in Heqo. congruence.
  cbv in Heqo. inversion Heqo.
  exact l.
Defined.

Lemma eval_at_zero :
  exists v,
    eval_expr ge empty (EApp (EApp (ETApp (ETApp (EVar hmacSHA256) t) t) z) z) v /\ (force_list ge empty v result).
Proof.
  init_globals ge.
  eexists; split.
  e.
  e. e. e. g.
  e. e. e. e. e. e.
  e. e. e. e. e. e.
  e. g.
  e. e. e. e. e. e. e. e. e.
  e. e. e. e. e. g.
  e. e. e. e. e. e.
  e. e. g.
  e. e. e. e.
  e. e. g.
  e. e. e. e. e. e.
  e. e. e. e. e. e. e.
  e. e. e.
  e. e. e. e. e.
  e. g. e. e. e.
  e. e. e. e. e.
  e. e. e. e. e.
  g. e. e. e. e. e.
  g. e. e. e. e. e. g.
  e. e. e. e.
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  e. e. e. e. g.
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).
  repeat (progress e).  
  
  
  

  
Admitted.
  