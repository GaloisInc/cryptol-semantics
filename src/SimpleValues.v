Require Import Cryptol.AST.
Require Import Cryptol.Coqlib.
Require Import Cryptol.Utils. 
Require Import Omega. 

Section conversion.
  Variable valtype : Type.
  Variable isBit : valtype -> option bool.
  Variable makebit : bool -> valtype.

(* convert Z to bits and back *)
(* no dependent types this time *)
Fixpoint to_bitlist (width : nat) (l : list valtype) : option Z :=
  match l,width with
  | nil,O => Some 0
  | f :: r,S n =>
    match isBit f with
    | Some b => 
      match to_bitlist n r with
      | Some z => Some (z + if b then (two_power_nat n) else 0)
      | None => None
      end
    | _ => None
    end
  | _,_ => None
  end.

Fixpoint from_bitlist (width : nat) (z : Z) : list valtype :=
  match width with
  | O => nil
  | S n' => (makebit (Z.testbit z (Z.of_nat n')) :: from_bitlist n' z)
  end.

Definition binop (op : Z -> Z -> Z) (width : nat) (a b : list valtype) : option (list valtype) :=
  match to_bitlist width a, to_bitlist width b with
  | Some za, Some zb =>
    Some (from_bitlist width (op za zb))
  | _ , _ => None
  end.

(* These are all unsigned operations *)
Definition add := binop Z.add.
Definition sub := binop Z.sub.
Definition mul := binop Z.mul.

End conversion.


