Require Import List.
Require Import String.

Require Import Coqlib.

Require Import AST.
Require Import Builtins.
Require Import Values.
Require Import Bitvectors.

Require Import BuiltinSyntax.

Open Scope string.


(* It is safe to force evaluation of all the arguments to this builtin *)
Definition strict_builtin (b : builtin) : Prop :=
  match b with
  | Demote => True (* purely type leve computation *)
  | Plus => False (* lazily lifts pointwise over streams *)
  | Minus => False (* lazily lifts pointwise over streams *)
  | Times => False (* lazily lifts pointwise over streams *)
  | Div => False (* lazily lifts pointwise over streams *)
  | Mod => False (* lazily lifts pointwise over streams *)
  | Exp => False (* lazily lifts pointwise over streams *)
  | lg2 => False (* lazily lifts pointwise over streams *)
  | true_builtin => True (* no arguments to be lazy/strict *)
  | false_builtin => True (* no arguments to be lazy/strict *)
  | Neg => False (* lazily lifts pointwise over streams *)
  | Compl => False (* lazily lifts pointwise over streams *)
  | Lt => True (* Lexicographically lifts, thus forces everything *)
  | Gt => True (* Lexicographically lifts, thus forces everything *)
  | Le => True (* Lexicographically lifts, thus forces everything *)
  | Ge => True (* Lexicographically lifts, thus forces everything *)
  | Eq => True (* Lexicographically lifts, thus forces everything *)
  | Neq => True (* Lexicographically lifts, thus forces everything *)
  | And => False (* lazily lifts pointwise over streams *)
  | Or => False (* lazily lifts pointwise over streams *)
  | Xor => False (* lazily lifts pointwise over streams *)
  | Zero => True (* only one argument, that is the result type *)
  | Shiftl => False (* can shift infinite streams, s << 2 is just (rest (rest s)) *)
  | Shiftr => False (* can shift infinite streams, just inserts 0 at beginning *)
  | Rotl => True (* can't lazily rotate in either direction *)
  | Rotr => True (* can't lazily rotate in either direction *)
  | Append => False (* a # b works as long as a is finite (though why both can't be infinite I don't know)*)
  | splitAt => False (* You can split a stream into some elements and another stream *)
  | join => False (* Input can't be infinite in both dimensions, but can be in one *)
  | split => False (* You can split an infinite stream into a stream of lists of elements *)
  | reverse => False (* You can reverse a finite list of infinite streams *)
  | transpose => False (* I don't know how to build [inf][inf]a, but you could transpose it *)
  | At => False (* just take the 3rd element of a stream *)
  | AtAt => False (* same argument for At. Why is this a primitive at all? *)
  | Bang => False (* subtle one: you can reverse index into a finite list of streams *)
  | BangBang => False (* same as for Bang *)
  | update => False (* again, like At or Bang, polymorphic over the contained type, which could be a stream *)
  | updateEnd => False (* same as update *)
  | fromThen => True (* I'm not sure about this, but probably *)
  | fromTo => True
  | fromThenTo => True
  | infFrom => True
  | infFromThen => True
  | pmult => True (* according to the types, must be finite *)
  | pdiv => True (* according to the types, must be finite *)
  | pmod => True (* according to the types, must be finite *)
  end.

Definition binary (b : builtin) : Prop :=
  match b with
  | Plus => True
  | Minus => True
  | Times => True
  | Div => True
  | Mod => True
  | Exp => True
  | Lt => True 
  | Gt => True 
  | Le => True 
  | Ge => True 
  | Eq => True 
  | Neq => True
  | And => True
  | Or => True
  | Xor => True
  | Shiftl => True
  | Shiftr => True
  | Rotl => True (* can't lazily rotate in either direction *)
  | Rotr => True (* can't lazily rotate in either direction *)
  | Append => True
  | At => True
  | AtAt => True
  | Bang => True
  | BangBang => True
  | pmult => True
  | pdiv => True
  | pmod => True
  | _ => False
  end.

Definition unary (b : builtin) : Prop :=
  match b with
  | Neg => True
  | Compl => True
  | lg2 => True
  | _ => False
  end.

Definition other_arity (b : builtin) : Prop :=
  match b with
  | Demote => True
  | true_builtin => True
  | false_builtin => True
  | Zero => True
  | splitAt => True
  | join => True
  | split => True
  | reverse => True
  | transpose => True
  | update => True
  | updateEnd => True
  | fromThen => True
  | fromTo => True
  | fromThenTo => True
  | infFrom => True
  | infFromThen => True
  | _ => False
  end.

Lemma binary_dec (b : builtin) :
  { binary b } + { ~ binary b }.
Proof.
  destruct b; simpl; auto.
Defined.

Lemma unary_dec (b : builtin) :
  { unary b } + { ~ unary b }.
Proof.
  destruct b; simpl; auto.
Defined.

Lemma arity_complete ( b : builtin) :
  { binary b } + { unary b } + { other_arity b }.
Proof.
  destruct b; simpl; try solve [left; auto]; right; auto.
Defined.

Fixpoint last_two {A : Type} (l : list A) : option (A * A) :=
  match l with
  | nil => None
  | f :: nil => None
  | a :: b :: nil => Some (a,b)
  | a :: b => last_two b
  end.

Fixpoint last_one {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | f :: nil => Some f
  | f :: r => last_one r
  end.

(* TODO: This might be a good way to define the correct lifting of binary operations over values *)
Definition evaluate_binary (bi : builtin) (a b : val) : option val := None.
  
Definition evaluate_unary (bi : builtin) (a : val) : option val := None.

Definition evaluate_builtin (bi : builtin) (lv : list val) : option val :=
  if binary_dec bi then
    match last_two lv with
    | Some (a,b) => evaluate_binary bi a b
    | None => None
    end
  else if unary_dec bi then
         match last_one lv with
         | Some a => evaluate_unary bi a
         | None => None
         end
       else None
.
                    