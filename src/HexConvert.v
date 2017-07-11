Require Import String.

Require Import Coqlib.

Require Import Utils.
Import HaskellListNotations.
Open Scope string.

Require Import Values.
Require Import AST.
Require Import Bitvectors.

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


Definition val_of_hex_lit (s : string) : list val :=
  match val_of_hex_string (substring 2 (String.length s) s) with
  | Some l => l
  | None => nil
  end.
